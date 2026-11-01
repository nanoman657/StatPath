// The page's side of the relay (PROTOCOL.md): TCP connections over one WebSocket. It is plain
// JavaScript, for a browser and for Bun (the tests). The page's effects (effs/web_tcp.js) use the
// callback calls, which answer once and never block; the promise calls wrap them for JavaScript.
//
//   const net = new RelayTcp("ws://127.0.0.1:8765");
//   await net.open(token);
//   const id = await net.connect("127.0.0.1", 4433);
//   await net.send(id, bytes);
//   const chunk = await net.recv(id, 4096);   // Uint8Array, or null at the end
//   net.close(id);

// The arithmetic of the connection's counts is the proven model's (core/tcp_transitions.bend, compiled to
// core/tcp_transitions.mjs): every change to a count the invariants talk about is one of its functions.
import M from "./core/tcp_transitions.mjs";

export const OP = {
  CONNECT: 1, SEND: 2, CLOSE: 3, DISCARD: 4, READ: 5, AUTH: 15,
  OK: 10, FAIL: 11, DATA: 12, EOF: 13, WRITTEN: 14, AUTHOK: 16,
};
export const MAX_BODY = 65535;
export const SEND_WINDOW = 131072;
export const READ_WINDOW = 131072;
export const MAX_COUNT = 0xffffffff;

export class TcpError extends Error {
  // written: for a failed send, how many of the connection's bytes the relay took (absolute,
  // counted from the connect), so the caller knows which bytes of its send were not taken
  constructor(errno, message, written = undefined) {
    super(message);
    this.name = "TcpError";
    this.errno = errno;
    this.written = written;
  }
}

// one frame as bytes: op, id, the length (high, low), the body
export function encodeFrame(op, id, body = new Uint8Array(0)) {
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
export function decodeFrame(msg) {
  if (msg.length < 4) return null;
  const len = (msg[2] << 8) | msg[3];
  if (msg.length !== 4 + len) return null;
  return { op: msg[0], id: msg[1], body: msg.subarray(4) };
}

function u32(n) {
  return new Uint8Array([n >>> 24, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
}

function readU32(b) {
  return b[0] * 0x1000000 + (b[1] << 16) + (b[2] << 8) + b[3];
}

const enc = new TextEncoder();
const dec = new TextDecoder();

function connectBody(port, host) {
  const text = enc.encode(host);
  const body = new Uint8Array(2 + text.length);
  body[0] = port >> 8;
  body[1] = port & 255;
  body.set(text, 2);
  return body;
}

export class RelayTcp {
  // WebSocketImpl is the WebSocket class to use (the browser's, or Bun's, or a test double)
  constructor(url, WebSocketImpl = globalThis.WebSocket, opts = {}) {
    this.url = url;
    this.WebSocketImpl = WebSocketImpl;
    // the most a connection moves in one direction: MAX_COUNT, lower only in tests (the relay's cap too)
    this.maxCount = opts.maxCount ?? MAX_COUNT;
    if (!Number.isInteger(this.maxCount) || this.maxCount < 1 || this.maxCount > MAX_COUNT) {
      throw new RangeError("maxCount out of range");
    }
    this.ws = null;
    this.conns = new Map();       // id -> connection (#newConn)
    this.connecting = new Map();  // id -> callback of its connect
    this.lastError = new Map();   // id -> the TcpError that ended it, while the id is not reused
    this.lost = null;             // the TcpError once the WebSocket has closed
    this.authWaiter = null;       // { resolve, reject } until the relay accepts the token
  }

  // Opens the WebSocket and presents the relay's token. Resolves once the relay has accepted it;
  // rejects with a TcpError (13) if the relay refuses the token or closes first.
  open(token) {
    return new Promise((resolve, reject) => {
      if (typeof token !== "string" || token.length === 0) {
        return reject(new TcpError(13, "no relay token"));
      }
      const ws = new this.WebSocketImpl(this.url);
      ws.binaryType = "arraybuffer";
      this.authWaiter = { resolve, reject };
      ws.onopen = () => ws.send(encodeFrame(OP.AUTH, 0, enc.encode(token)));
      ws.onerror = () => this.#authFailed("the relay could not be reached");
      ws.onmessage = (ev) => this.#message(new Uint8Array(ev.data));
      ws.onclose = () => {
        this.#authFailed("the relay refused the connection");
        this.#lost();
      };
      this.ws = ws;
    });
  }

  // Opens a connection; cb({ id }) once the relay has connected it, or cb({ error }).
  connectAt(host, port, cb) {
    if (this.lost) return cb({ error: this.lost });
    let id;
    try {
      id = this.#freeId();
    } catch (e) {
      return cb({ error: e });
    }
    this.conns.set(id, this.#newConn());
    this.connecting.set(id, cb);
    this.lastError.delete(id);
    this.ws.send(encodeFrame(OP.CONNECT, id, connectBody(port, host)));
    return undefined;
  }

  connect(host, port) {
    return new Promise((resolve, reject) => {
      this.connectAt(host, port, (r) => (r.error ? reject(r.error) : resolve(r.id)));
    });
  }

  // Sends bytes on a connection, after whatever it has already been asked to send. cb() once the
  // relay has taken all of them, or cb({ error }) with error.written: how many of the connection's
  // bytes were taken, so the rest of these are the ones not sent. Returns where these bytes start
  // in the connection's count (the same count as error.written).
  startSend(id, bytes, cb) {
    const c = this.conns.get(id);
    if (!c || c.state !== "open") {
      cb({ error: c ? new TcpError(22, "send before the connection is open", c.written) : this.#missing(id) });
      return 0;
    }
    if (c.op || c.discard) throw new Error("a connection takes one send at a time");
    // refused here, before it reaches the wire: the relay would fail the connection for it
    if (c.tail + bytes.length > this.maxCount) {
      cb({ error: new TcpError(27, "file too large", c.written) });
      return 0;
    }
    const start = c.tail;
    c.tail = M.pg_start(c.tail, bytes.length);
    if (bytes.length === 0) {
      cb({ ok: true });
      return start;
    }
    c.op = { start, bytes, cb };
    this.#pump(id, c);
    return start;
  }

  send(id, bytes) {
    return new Promise((resolve, reject) => {
      this.startSend(id, bytes, (r) => (r.error ? reject(r.error) : resolve()));
    });
  }

  // Drops the bytes of the current send that the relay has not taken yet. cb({ written }) with the
  // final count (the bytes of the send after it were not taken), or cb({ error }).
  discard(id, cb) {
    const c = this.conns.get(id);
    if (!c || c.state !== "open") return cb({ error: this.#missing(id) });
    c.discard = cb;
    this.ws.send(encodeFrame(OP.DISCARD, id));
    return undefined;
  }

  // What the page can read now: { bytes } (at most max), { eof: true } once the remote end has
  // finished and nothing is left, or null when it has to wait. Throws the error that ended it.
  takeNow(id, max) {
    const c = this.conns.get(id);
    if (!c) throw this.#missing(id);
    if (c.received > c.taken) {
      const bytes = this.#take(c, max);
      this.ws.send(encodeFrame(OP.READ, id, u32(bytes.length)));
      return { bytes };
    }
    if (c.eof) return { eof: true };
    return null;
  }

  // Calls cb once when takeNow would answer (data, the end, or the error). Returns a function
  // that cancels the call; a cancelled call takes nothing.
  onReadable(id, cb) {
    const c = this.conns.get(id);
    if (!c) {
      cb();
      return () => {};
    }
    c.readers.push(cb);
    return () => {
      const i = c.readers.indexOf(cb);
      if (i >= 0) c.readers.splice(i, 1);
    };
  }

  // up to max bytes that have arrived; null once the remote end has finished and nothing is left
  recv(id, max) {
    return new Promise((resolve, reject) => {
      if (!(max > 0)) return reject(new TcpError(22, "Invalid argument"));
      const attempt = () => {
        let r;
        try {
          r = this.takeNow(id, max);
        } catch (e) {
          return reject(e);
        }
        if (r === null) return this.onReadable(id, attempt);
        return resolve(r.eof ? null : r.bytes);
      };
      attempt();
      return undefined;
    });
  }

  // bytes received and not yet read by the page (at most READ_WINDOW beyond what it has read)
  buffered(id) {
    const c = this.conns.get(id);
    return c ? c.received - c.taken : 0;
  }

  close(id) {
    const c = this.conns.get(id);
    if (!c) return;
    const err = new TcpError(9, "the connection is closed");
    this.#die(id, c, err);
    if (this.ws && this.ws.readyState === 1) this.ws.send(encodeFrame(OP.CLOSE, id));
  }

  shutdown() {
    for (const id of [...this.conns.keys()]) this.close(id);
    if (this.ws) this.ws.close();
  }

  // a free id: 0..255 that the page is not using
  #freeId() {
    for (let id = 0; id < 256; id++) if (!this.conns.has(id)) return id;
    throw new TcpError(24, "Too many open files");
  }

  #newConn() {
    return {
      state: "connecting",
      chunks: [],     // data received and not read: Uint8Array pieces, in order
      taken: 0,       // bytes the program has taken (each one granted to the relay by a READ)
      received: 0,    // bytes received as DATA: the bytes buffered are received - taken
      eof: false,     // the remote end has finished
      tail: 0,        // bytes given to startSend so far
      sent: 0,        // bytes framed as SEND so far
      written: 0,     // bytes the relay has taken (WRITTEN)
      op: null,       // the send in progress: { start, bytes, cb }
      discard: null,  // the callback of a DISCARD waiting for its reply
      readers: [],    // callbacks waiting for data (onReadable)
    };
  }

  #missing(id) {
    return this.lastError.get(id) ?? new TcpError(9, "no such connection");
  }

  // Frames as much of the current send as the window allows: SEND frames of at most MAX_BODY bytes,
  // and no more than SEND_WINDOW bytes beyond what the relay has taken.
  #pump(id, c) {
    const op = c.op;
    if (!op || c.discard || c.state !== "open") return;
    // the send in progress is the last one started, so its end is the tail
    if (op.start + op.bytes.length !== c.tail) throw new Error("a send is not the last one started");
    for (;;) {
      const n = M.pg_frame_n(c.sent, c.written, SEND_WINDOW, c.tail, MAX_BODY);
      if (n === 0) break;
      const off = c.sent - op.start;
      this.ws.send(encodeFrame(OP.SEND, id, op.bytes.subarray(off, off + n)));
      c.sent = M.pg_sent(c.sent, n);
    }
  }

  // The connection has ended with err: the send, the discard and the connect that were waiting on
  // it hear so, and so does every reader. The id is free after this.
  #die(id, c, err) {
    this.conns.delete(id);
    this.lastError.set(id, err);
    c.chunks = [];
    c.received = c.taken;
    const cb = this.connecting.get(id);
    this.connecting.delete(id);
    if (cb) cb({ error: err });
    const op = c.op;
    c.op = null;
    if (op) op.cb({ error: new TcpError(err.errno, err.message, c.written) });
    const d = c.discard;
    c.discard = null;
    if (d) d({ error: new TcpError(err.errno, err.message, c.written) });
    this.#wake(c);
  }

  #take(c, max) {
    const want = M.pg_take_n(c.taken, c.received, max);
    const out = new Uint8Array(want);
    let at = 0;
    while (at < want) {
      const first = c.chunks[0];
      const part = first.subarray(0, Math.min(first.length, want - at));
      out.set(part, at);
      at += part.length;
      if (part.length === first.length) c.chunks.shift();
      else c.chunks[0] = first.subarray(part.length);
    }
    c.taken = M.pg_taken(c.taken, want);
    return out;
  }

  #wake(c) {
    const readers = c.readers;
    c.readers = [];
    for (const r of readers) r();
  }

  #message(bytes) {
    const f = decodeFrame(bytes);
    if (!f) return; // a frame that does not fit is ignored; the relay closes the socket on its own errors
    const id = f.id;
    const c = this.conns.get(id);
    switch (f.op) {
      case OP.OK: {
        if (!c) return;
        const cb = this.connecting.get(id);
        this.connecting.delete(id);
        c.state = "open";
        this.ws.send(encodeFrame(OP.READ, id, u32(READ_WINDOW)));
        if (cb) cb({ id });
        return;
      }
      case OP.FAIL: {
        const err = new TcpError((f.body[0] << 8) | f.body[1], dec.decode(f.body.subarray(2)));
        if (c) this.#die(id, c, err);
        return;
      }
      case OP.WRITTEN: {
        if (!c || f.body.length !== 5) return;
        c.written = readU32(f.body);
        const reply = f.body[4] === 1;
        if (c.op && c.written >= c.op.start + c.op.bytes.length) {
          const op = c.op;
          c.op = null;
          op.cb({ ok: true });
        }
        if (reply && c.discard) {
          // the relay dropped what it had not taken: the page's count starts again from there
          const d = c.discard;
          c.discard = null;
          c.op = null;
          c.sent = c.written;
          c.tail = c.written;
          d({ written: c.written });
        }
        this.#pump(id, c);
        return;
      }
      case OP.DATA: {
        if (!c) return;
        // a relay that keeps to the cap never sends past it: data past it ends the connection
        if (c.received + f.body.length > this.maxCount) {
          this.#die(id, c, new TcpError(27, "file too large"));
          if (this.ws && this.ws.readyState === 1) this.ws.send(encodeFrame(OP.CLOSE, id));
          return;
        }
        c.chunks.push(f.body.slice());
        c.received = M.pg_recv_data(c.received, f.body.length);
        this.#wake(c);
        return;
      }
      case OP.EOF: {
        if (!c) return;
        c.eof = true;
        this.#wake(c);
        return;
      }
      case OP.AUTHOK: {
        const w = this.authWaiter;
        this.authWaiter = null;
        if (w) w.resolve();
        return;
      }
      default:
        return;
    }
  }

  #authFailed(message) {
    const w = this.authWaiter;
    this.authWaiter = null;
    if (w) w.reject(new TcpError(13, message));
  }

  #lost() {
    const err = new TcpError(5, "relay connection closed");
    this.lost = err;
    for (const [id, c] of [...this.conns]) this.#die(id, c, err);
  }
}
