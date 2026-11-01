// The relay: a WebSocket server that opens TCP connections for a browser page (PROTOCOL.md).
// Default-deny: it connects only to the destinations listed in its config.
//
//   bun relay/relay.ts relay/config.json      (or the example config)

export const OP = { CONNECT: 1, SEND: 2, CLOSE: 3, OK: 10, FAIL: 11, DATA: 12, EOF: 13 } as const;
export const MAX_BODY = 65535;

export const ERR = {
  EIO: 5, EACCES: 13, EMFILE: 24, EADDRNOTAVAIL: 99, ENETUNREACH: 101, ECONNREFUSED: 111,
  ETIMEDOUT: 110, EHOSTUNREACH: 113, EINVAL: 22,
} as const;

export type Allow = { host: string; ports: number[] };
export type Config = { port: number; maxConnections: number; allow: Allow[] };

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

// the destination is allowed: its host, exactly as the page gives it, and its port
export function allowed(cfg: Config, host: string, port: number): boolean {
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
    default: return ERR.EIO;
  }
}

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
  tcp?: any;             // the Bun socket, once connected
  open: boolean;         // the connect has succeeded
  closed: boolean;       // the page closed it, or it failed
};

type Session = { conns: Map<number, Conn> };

export function startRelay(cfg: Config) {
  const server = Bun.serve({
    port: cfg.port,
    fetch(req, server) {
      if (server.upgrade(req, { data: { conns: new Map() } satisfies Session })) return undefined;
      return new Response("relay: connect with a WebSocket", { status: 426 });
    },
    websocket: {
      maxPayloadLength: 1 << 20,
      message(ws, message) {
        const session = ws.data as Session;
        const bytes = typeof message === "string" ? enc.encode(message) : new Uint8Array(message as ArrayBuffer);
        const f = decodeFrame(bytes);
        if (!f) return ws.close(1002, "not one frame");
        handle(ws, session, f.op, f.id, f.body);
      },
      close(ws) {
        const session = ws.data as Session;
        for (const c of session.conns.values()) c.tcp?.end?.();
        session.conns.clear();
      },
    },
  });

  function send(ws: any, op: number, id: number, body?: Uint8Array) {
    ws.sendBinary(encodeFrame(op, id, body));
  }

  function fail(ws: any, session: Session, id: number, errno: number, message: string) {
    send(ws, OP.FAIL, id, failBody(errno, message));
    const c = session.conns.get(id);
    if (c) { c.tcp?.end?.(); c.closed = true; }
    session.conns.delete(id);
  }

  function handle(ws: any, session: Session, op: number, id: number, body: Uint8Array) {
    if (op === OP.CONNECT) {
      if (session.conns.has(id)) return ws.close(1002, "id in use");
      if (body.length < 3) return ws.close(1002, "CONNECT without a port and host");
      const port = (body[0] << 8) | body[1];
      const host = dec.decode(body.subarray(2));
      if (!allowed(cfg, host, port)) {
        return send(ws, OP.FAIL, id, failBody(ERR.EACCES, "destination not allowed"));
      }
      if (session.conns.size >= cfg.maxConnections) {
        return send(ws, OP.FAIL, id, failBody(ERR.EMFILE, "too many connections"));
      }
      const conn: Conn = { open: false, closed: false };
      session.conns.set(id, conn);
      Bun.connect({
        hostname: host,
        port,
        socket: {
          open(tcp) {
            if (conn.closed) return tcp.end();
            conn.tcp = tcp;
            conn.open = true;
            send(ws, OP.OK, id);
          },
          data(tcp, chunk) {
            if (conn.closed) return;
            for (let at = 0; at < chunk.length; at += MAX_BODY) {
              send(ws, OP.DATA, id, chunk.subarray(at, Math.min(chunk.length, at + MAX_BODY)));
            }
          },
          end() {
            if (!conn.closed) send(ws, OP.EOF, id);
          },
          close() {
            if (session.conns.get(id) === conn) session.conns.delete(id);
          },
          error(tcp, err) {
            if (conn.closed) return;
            if (!conn.open) return fail(ws, session, id, errnoOf(err), String((err as Error).message ?? err));
            fail(ws, session, id, errnoOf(err), String((err as Error).message ?? err));
          },
          connectError(tcp, err) {
            if (!conn.closed) fail(ws, session, id, errnoOf(err), String((err as Error).message ?? err));
          },
        },
      }).catch((err: unknown) => {
        if (!conn.closed && !conn.open) fail(ws, session, id, errnoOf(err), String((err as Error).message ?? err));
      });
      return;
    }
    const conn = session.conns.get(id);
    if (op === OP.SEND) {
      if (!conn || !conn.open) return ws.close(1002, "SEND before OK");
      if (body.length > MAX_BODY) return ws.close(1002, "SEND too long");
      conn.tcp.write(body);
      return;
    }
    if (op === OP.CLOSE) {
      if (conn) {
        conn.closed = true;
        conn.tcp?.end?.();
        session.conns.delete(id);
      }
      return;
    }
    ws.close(1002, "unknown op");
  }

  return server;
}

if (import.meta.main) {
  const path = process.argv[2] ?? "relay/config.example.json";
  const cfg = JSON.parse(await Bun.file(path).text()) as Config;
  const server = startRelay(cfg);
  console.log(`relay listening on ws://127.0.0.1:${server.port}, ${cfg.allow.length} allowed host(s)`);
}
