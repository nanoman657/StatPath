// The relay: a WebSocket server that opens TCP connections for a browser page (PROTOCOL.md).
// Default-deny: it connects only to the destinations in its configuration (relay/config.ts), and
// only for a WebSocket that presented a token and came from an allowed origin.
//
//   bun relay/relay.ts relay/config.json      (or the example config)

import { readFileSync } from "node:fs";
import { createHash, timingSafeEqual } from "node:crypto";
import { type Config, type Allow, readConfig, ConfigError } from "./config.ts";
// The arithmetic of the connection's counts is the proven model's (core/tcp_transitions.bend, compiled to
// core/tcp_transitions.mjs): every change to a count the invariants talk about is one of its functions.
import M from "../core/tcp_transitions.mjs";

export const OP = {
  CONNECT: 1, SEND: 2, CLOSE: 3, DISCARD: 4, READ: 5, AUTH: 15,
  OK: 10, FAIL: 11, DATA: 12, EOF: 13, WRITTEN: 14, AUTHOK: 16, CLOSED: 17,
} as const;
export const MAX_BODY = 65535;
// bytes a connection may hold in the relay: sent by the page, not yet taken by the socket
export const SEND_WINDOW = 131072;
// bytes the page grants a connection to read ahead of what the page has taken
export const READ_WINDOW = 131072;
// the most a connection moves in one direction: counts are four bytes
export const MAX_COUNT = 0xffffffff;
// the largest chunk the socket delivers in one read: the model's C (a read past it fails the connection)
export const CHUNK_MAX = 1 << 20;
// the longest token the page may send in AUTH
export const MAX_TOKEN = 256;

export const ERR = {
  EIO: 5, EACCES: 13, EAGAIN: 11, EMFILE: 24, EINVAL: 22, EFBIG: 27, EPIPE: 32, ECONNRESET: 104,
  EADDRNOTAVAIL: 99, ENETUNREACH: 101, ETIMEDOUT: 110, ECONNREFUSED: 111, EHOSTUNREACH: 113,
} as const;

// one frame, as bytes: op, id, the length (high, low), the body
export function encodeFrame(op: number, id: number, body: Uint8Array = new Uint8Array(0)): Uint8Array {
  if (body.length > MAX_BODY) throw new RangeError("frame body longer than 65535 bytes");
  const out = new Uint8Array(4 + body.length);
  out[0] = op;
  out[1] = id;
  out[2] = body.length >> 8;
  out[3] = body.length & 255;
  out.set(body, 4);
  return out;
}

// the frame in a whole message, or null when the message is not exactly one frame
export function decodeFrame(msg: Uint8Array): { op: number; id: number; body: Uint8Array } | null {
  if (msg.length < 4) return null;
  const len = (msg[2] << 8) | msg[3];
  if (msg.length !== 4 + len) return null;
  return { op: msg[0], id: msg[1], body: msg.subarray(4) };
}

// a four-byte count, big-endian
export function u32(n: number): Uint8Array {
  return new Uint8Array([n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
}

export function readU32(b: Uint8Array): number {
  return b[0] * 0x1000000 + (b[1] << 16) + (b[2] << 8) + b[3];
}

// the destination is allowed: its host, exactly as the page gives it, and its port
export function allowed(cfg: { allow: Allow[] }, host: string, port: number): boolean {
  return cfg.allow.some((a) => a.host === host && a.ports.includes(port));
}

// the Linux errno for a failed connect or I/O error, from the code Bun gives
export function errnoOf(err: unknown): number {
  const code = (err as { code?: string })?.code ?? "";
  switch (code) {
    case "ECONNREFUSED": return ERR.ECONNREFUSED;
    case "ETIMEDOUT": return ERR.ETIMEDOUT;
    case "EHOSTUNREACH": return ERR.EHOSTUNREACH;
    case "ENETUNREACH": return ERR.ENETUNREACH;
    case "EADDRNOTAVAIL": return ERR.EADDRNOTAVAIL;
    case "EINVAL": return ERR.EINVAL;
    case "EPIPE": return ERR.EPIPE;
    case "ECONNRESET": return ERR.ECONNRESET;
    default: return ERR.EIO;
  }
}

// What the relay reports: { time, event, ...fields }, one JSON line. Never a token or payload.
export type Log = (event: string, fields: Record<string, unknown>) => void;
const stdoutLog: Log = (event, fields) =>
  console.log(JSON.stringify({ time: new Date().toISOString(), event, ...fields }));

const enc = new TextEncoder();
const dec = new TextDecoder();

function failBody(errno: number, message: string): Uint8Array {
  const text = enc.encode(message);
  const body = new Uint8Array(2 + text.length);
  body[0] = errno >> 8;
  body[1] = errno & 255;
  body.set(text, 2);
  return body;
}

type Conn = {
  id: number;
  tcp?: any;            // the Bun socket, once connected
  open: boolean;        // the connect has succeeded, and OK was sent
  closed: boolean;      // the page closed it, or it failed
  peerClosed: boolean;  // the socket is closed for good (the peer closed it)
  queue: Uint8Array[];  // SEND bytes the socket has not taken yet, in order
  queued: number;       // their total length
  written: number;      // bytes the socket has taken since the connect
  rd: number;           // bytes read from the socket since the connect
  gr: number;           // bytes the page has granted to be read, clamped to the window
  paused: boolean;      // the socket's reads are paused
  wsPaused: boolean;    // paused because the WebSocket's send buffer is full
};

type Session = {
  ws: any;              // the WebSocket, once open
  origin: string;
  address: string;      // the client's address, for the log
  name: string | null;  // the token's name, once authenticated
  authed: boolean;
  closed: boolean;
  conns: Map<number, Conn>;
  known: Uint8Array;    // the ids this WebSocket has connected before
  budget: number;       // bytes the session may still move; refilled over time
  connects: number;     // CONNECTs it may still make; refilled over time
  refilled: number;     // the time of the last refill (ms)
  authTimer: ReturnType<typeof setTimeout> | null;
};

// Test hooks, with the defaults the relay runs with: connect (how a TCP connection is opened) and
// ticker (whether the 50 ms timer runs: it refills the budgets and flushes the writes the socket held).
export function startRelay(
  cfg: Config,
  opts: { log?: Log; maxCount?: number; connect?: (o: any) => Promise<unknown>; ticker?: boolean } = {},
) {
  const log = opts.log ?? stdoutLog;
  const connect = opts.connect ?? ((o: any) => Bun.connect(o));
  // the most a connection moves in one direction: MAX_COUNT in production, lower only in tests
  const cap = opts.maxCount ?? MAX_COUNT;
  if (!Number.isInteger(cap) || cap < 1 || cap > MAX_COUNT) throw new RangeError("maxCount out of range");
  const lim = cfg.limits;
  const digests = cfg.tokens.map((t) => ({ name: t.name, digest: Buffer.from(t.sha256, "hex") }));
  const sessions = new Set<Session>();
  const upgrades = new Map<string, number[]>();

  // an upgrade from this address is admitted unless the address has used its quota this minute
  function admit(address: string): boolean {
    const now = Date.now();
    const recent = (upgrades.get(address) ?? []).filter((t) => now - t < 60000);
    const ok = recent.length < lim.upgradesPerMinute;
    if (ok) recent.push(now);
    upgrades.set(address, recent);
    return ok;
  }

  const server = Bun.serve({
    hostname: cfg.host,
    port: cfg.port,
    tls: cfg.tls ? { cert: readFileSync(cfg.tls.cert), key: readFileSync(cfg.tls.key) } : undefined,
    fetch(req, server) {
      const url = new URL(req.url);
      if (url.pathname === "/healthz" && req.method === "GET" && !req.headers.get("upgrade")) {
        return new Response("ok\n");
      }
      if (!req.headers.get("upgrade")) {
        return new Response("relay: connect with a WebSocket", { status: 426 });
      }
      const origin = req.headers.get("origin");
      if (origin === null || !cfg.origins.includes(origin)) {
        log("origin_denied", { origin: origin?.slice(0, 200) ?? null });
        return new Response("origin not allowed\n", { status: 403 });
      }
      const address = server.requestIP(req)?.address ?? "unknown";
      if (!admit(address)) {
        log("upgrade_limited", { address });
        return new Response("too many connections from this address\n", { status: 429 });
      }
      if (sessions.size >= lim.maxSessions) {
        log("sessions_full", { address });
        return new Response("the relay is full\n", { status: 503 });
      }
      const data: Session = {
        ws: null, origin, address, name: null, authed: false, closed: false,
        conns: new Map(), known: new Uint8Array(256),
        budget: lim.bytesPerSecond, connects: 2 * lim.connectsPerSecond, refilled: Date.now(),
        authTimer: null,
      };
      if (server.upgrade(req, { data })) return undefined;
      return new Response("upgrade failed\n", { status: 400 });
    },
    websocket: {
      maxPayloadLength: 1 << 20,
      idleTimeout: lim.idleSeconds,
      sendPings: true,
      open(ws) {
        const s = ws.data as Session;
        s.ws = ws;
        sessions.add(s);
        log("session_open", { origin: s.origin, address: s.address });
        s.authTimer = setTimeout(() => {
          if (!s.authed) ws.close(1008, "authenticate in time");
        }, lim.authSeconds * 1000);
      },
      message(ws, message) {
        const s = ws.data as Session;
        const bytes = typeof message === "string" ? enc.encode(message) : new Uint8Array(message as ArrayBuffer);
        const f = decodeFrame(bytes);
        if (!f) return ws.close(1002, "not one frame");
        if (!s.authed) {
          if (f.op !== OP.AUTH) return ws.close(1008, "authenticate first");
          return authenticate(s, f.body);
        }
        if (f.op === OP.AUTH) return ws.close(1002, "already authenticated");
        handle(s, f.op, f.id, f.body);
      },
      drain(ws) {
        const s = ws.data as Session;
        for (const c of s.conns.values()) {
          if (!c.wsPaused) continue;
          c.wsPaused = false;
          sync(s, c);
          flush(s, c);
        }
      },
      close(ws, code) {
        const s = ws.data as Session;
        s.closed = true;
        if (s.authTimer) clearTimeout(s.authTimer);
        for (const c of s.conns.values()) end(c);
        s.conns.clear();
        sessions.delete(s);
        log("session_close", { name: s.name, origin: s.origin, code });
      },
    },
  });

  function sendFrame(s: Session, op: number, id: number, body?: Uint8Array) {
    if (!s.closed) s.ws.sendBinary(encodeFrame(op, id, body));
  }

  // How many bytes the socket has taken. A reply to DISCARD has flag 1, so the page can tell it
  // from the counts that came before it.
  function sendWritten(s: Session, c: Conn, reply: boolean) {
    const body = new Uint8Array(5);
    body.set(u32(c.written));
    body[4] = reply ? 1 : 0;
    sendFrame(s, OP.WRITTEN, c.id, body);
  }

  function end(c: Conn) {
    c.closed = true;
    c.queue = [];
    c.queued = 0;
    c.tcp?.end?.();
  }

  // The connection failed: the page hears how much of its send was taken, then the failure.
  // A connection gets at most one FAIL. The connection is named by its object, not its id: an id may
  // have been closed and reused since, and a late callback of the old socket must not act on the new
  // connection that has it now.
  function fail(s: Session, c: Conn, errno: number, message: string) {
    if (c.closed || s.conns.get(c.id) !== c) return;
    if (c.open) sendWritten(s, c, false);
    sendFrame(s, OP.FAIL, c.id, failBody(errno, message));
    end(c);
    s.conns.delete(c.id);
  }

  // The reads of a connection run only while the page has credit, the session has bytes to spare,
  // and the WebSocket's send buffer has room.
  function sync(s: Session, c: Conn) {
    if (!c.tcp || c.closed) return;
    const want = c.gr > c.rd && s.budget > 0 && !c.wsPaused;
    if (want && c.paused) {
      c.paused = false;
      c.tcp.resume();
    } else if (!want && !c.paused) {
      c.paused = true;
      c.tcp.pause();
    }
  }

  // Writes what the socket takes now. Bun's write takes part of a buffer and keeps none of the
  // rest, so the rest stays in the queue until the socket drains. Writes wait for the budget.
  function flush(s: Session, c: Conn) {
    if (!c.tcp || c.closed) return;
    let moved = 0;
    while (c.queue.length > 0 && s.budget > 0) {
      const head = c.queue[0];
      const n: number = c.tcp.write(head);
      if (n <= 0) break;
      if (n > head.length) {
        fail(s, c, ERR.EIO, "the socket took more than it was given");
        return;
      }
      moved += n;
      c.queued = M.rl_unqueue(c.queued, n);
      c.written = M.rl_written(c.written, n);
      s.budget -= n;
      if (n < head.length) {
        c.queue[0] = head.subarray(n);
        break;
      }
      c.queue.shift();
    }
    if (moved > 0) sendWritten(s, c, false);
  }

  function refill(s: Session, now: number) {
    const dt = now - s.refilled;
    s.refilled = now;
    s.budget = Math.min(lim.bytesPerSecond, s.budget + (dt * lim.bytesPerSecond) / 1000);
    s.connects = Math.min(2 * lim.connectsPerSecond, s.connects + (dt * lim.connectsPerSecond) / 1000);
  }

  // Every 50 ms: the budgets refill, and the connections that were held may run again. A
  // connection held for its WebSocket's send buffer runs again once the buffer has half drained
  // (this does not wait for the drain event alone, which Bun need not send). Addresses that have
  // not upgraded for a minute are forgotten.
  let lastForget = Date.now();
  const ticker = opts.ticker === false ? null : setInterval(() => {
    const now = Date.now();
    for (const s of sessions) {
      refill(s, now);
      const buffered = s.ws.getBufferedAmount();
      for (const c of s.conns.values()) {
        if (c.wsPaused && buffered <= lim.maxBufferedBytes / 2) c.wsPaused = false;
        sync(s, c);
        flush(s, c);
      }
    }
    if (now - lastForget >= 60000) {
      lastForget = now;
      for (const [address, times] of upgrades) {
        if (!times.some((t) => now - t < 60000)) upgrades.delete(address);
      }
    }
  }, 50);

  function totalConnections(): number {
    let n = 0;
    for (const s of sessions) n += s.conns.size;
    return n;
  }

  function authenticate(s: Session, body: Uint8Array) {
    const digest = createHash("sha256").update(body).digest();
    const hit = body.length > 0 && body.length <= MAX_TOKEN
      ? digests.find((d) => timingSafeEqual(d.digest, digest))
      : undefined;
    if (!hit) {
      log("auth_fail", { origin: s.origin, address: s.address });
      return s.ws.close(1008, "bad token");
    }
    s.authed = true;
    s.name = hit.name;
    if (s.authTimer) clearTimeout(s.authTimer);
    sendFrame(s, OP.AUTHOK, 0);
    log("auth_ok", { name: hit.name, origin: s.origin, address: s.address });
  }

  // A frame for an id with no connection. An id this WebSocket has used is freed: the page sent the
  // frame before it saw the FAIL or the CLOSE that freed it, so the frame is dropped. An id never
  // used is a protocol error.
  function unknownId(s: Session, id: number) {
    if (!s.known[id]) s.ws.close(1002, "no such connection");
  }

  function handle(s: Session, op: number, id: number, body: Uint8Array) {
    if (op === OP.CONNECT) {
      if (s.conns.has(id)) return s.ws.close(1002, "id in use");
      if (body.length < 3) return s.ws.close(1002, "CONNECT without a port and host");
      const port = (body[0] << 8) | body[1];
      const host = dec.decode(body.subarray(2));
      if (!allowed(cfg, host, port)) {
        log("connect_denied", { host: host.slice(0, 255), port, name: s.name });
        return sendFrame(s, OP.FAIL, id, failBody(ERR.EACCES, "destination not allowed"));
      }
      if (s.conns.size >= lim.maxConnections || totalConnections() >= lim.maxConnectionsTotal) {
        return sendFrame(s, OP.FAIL, id, failBody(ERR.EMFILE, "too many connections"));
      }
      refill(s, Date.now());
      if (s.connects < 1) {
        log("connect_limited", { name: s.name });
        return sendFrame(s, OP.FAIL, id, failBody(ERR.EAGAIN, "connect rate limit"));
      }
      s.connects -= 1;
      const conn: Conn = {
        id, open: false, closed: false, peerClosed: false, queue: [], queued: 0, written: 0,
        rd: 0, gr: 0, paused: false, wsPaused: false,
      };
      s.conns.set(id, conn);
      s.known[id] = 1;
      log("connect", { host: host.slice(0, 255), port, name: s.name });
      const message = (err: unknown) => String((err as Error)?.message ?? err);
      connect({
        hostname: host,
        port,
        socket: {
          open(tcp) {
            if (conn.closed) return tcp.end();
            conn.tcp = tcp;
            conn.open = true;
            sync(s, conn);   // no credit yet: the socket's reads wait for the page's READ
            sendFrame(s, OP.OK, id);
          },
          data(_tcp, chunk) {
            if (conn.closed) return;
            // the socket delivers only while the page has credit (its reads are paused otherwise), and
            // in chunks of at most CHUNK_MAX: the two assumptions of the model's bound
            if (conn.rd > conn.gr) return fail(s, conn, ERR.EIO, "data beyond the page's credit");
            if (chunk.length > CHUNK_MAX) return fail(s, conn, ERR.EIO, "a read past the chunk limit");
            if (conn.rd + chunk.length > cap) return fail(s, conn, ERR.EFBIG, "file too large");
            conn.rd = M.rl_read(conn.rd, chunk.length);
            for (let at = 0; at < chunk.length; at += MAX_BODY) {
              sendFrame(s, OP.DATA, id, chunk.subarray(at, Math.min(chunk.length, at + MAX_BODY)));
            }
            s.budget -= chunk.length;
            if (s.ws.getBufferedAmount() > lim.maxBufferedBytes) conn.wsPaused = true;
            sync(s, conn);
          },
          drain() {
            flush(s, conn);
          },
          end() {
            if (!conn.closed) sendFrame(s, OP.EOF, id);
          },
          close() {
            conn.peerClosed = true;
            // bytes queued for a socket that is closed can never be written
            if (!conn.closed && conn.queued > 0) fail(s, conn, ERR.EPIPE, "Broken pipe");
          },
          error(_tcp, err) {
            fail(s, conn, errnoOf(err), message(err));
          },
          connectError(_tcp, err) {
            fail(s, conn, errnoOf(err), message(err));
          },
        },
      }).catch((err: unknown) => fail(s, conn, errnoOf(err), message(err)));
      return;
    }
    const conn = s.conns.get(id);
    if (op === OP.SEND) {
      if (!conn) return unknownId(s, id);
      if (!conn.open) return s.ws.close(1002, "SEND before OK");
      if (body.length > MAX_BODY) return s.ws.close(1002, "SEND too long");
      if (M.rl_over(body.length, M.rl_room(SEND_WINDOW, conn.queued)) !== 0) {
        return s.ws.close(1002, "SEND past the window");
      }
      if (conn.written + conn.queued + body.length > cap) {
        return fail(s, conn, ERR.EFBIG, "file too large");
      }
      if (conn.peerClosed) return fail(s, conn, ERR.EPIPE, "Broken pipe");
      conn.queue.push(body.slice());
      conn.queued = M.rl_queue(conn.queued, body.length);
      flush(s, conn);
      return;
    }
    if (op === OP.DISCARD) {
      if (!conn) return unknownId(s, id);
      if (!conn.open) return s.ws.close(1002, "DISCARD before OK");
      conn.queue = [];
      conn.queued = 0;
      sendWritten(s, conn, true);
      return;
    }
    if (op === OP.READ) {
      if (!conn) return unknownId(s, id);
      if (!conn.open) return s.ws.close(1002, "READ before OK");
      if (body.length !== 4) return s.ws.close(1002, "READ needs four bytes");
      // the grant is clamped to the window past what was read (the model's rl_grant)
      conn.gr = M.rl_grant(conn.rd, conn.gr, READ_WINDOW, readU32(body));
      sync(s, conn);
      return;
    }
    if (op === OP.CLOSE) {
      if (conn) {
        s.conns.delete(id);
        end(conn);
      }
      // the page's id is free once it has this answer (PROTOCOL.md)
      if (s.known[id]) sendFrame(s, OP.CLOSED, id);
      return;
    }
    s.ws.close(1002, "unknown op");
  }

  return {
    port: server.port,
    url: `${cfg.tls ? "wss" : "ws"}://${cfg.host.includes(":") ? `[${cfg.host}]` : cfg.host}:${server.port}`,
    // closes every WebSocket (1001, going away), then stops listening
    stop() {
      if (ticker) clearInterval(ticker);
      for (const s of [...sessions]) s.ws?.close(1001, "relay stopping");
      server.stop(true);
    },
  };
}

// The command line: bun relay/relay.ts <config.json>
if (import.meta.main) {
  const path = process.argv[2] ?? "relay/config.example.json";
  let cfg: Config;
  try {
    cfg = await readConfig(path);
  } catch (e) {
    if (e instanceof ConfigError) {
      console.error(e.message);
      process.exit(2);
    }
    throw e;
  }
  const relay = startRelay(cfg);
  console.log(JSON.stringify({ time: new Date().toISOString(), event: "listening", url: relay.url, destinations: cfg.allow.length }));
  const stop = () => {
    relay.stop();
    setTimeout(() => process.exit(0), 100);
  };
  process.on("SIGINT", stop);
  process.on("SIGTERM", stop);
}
