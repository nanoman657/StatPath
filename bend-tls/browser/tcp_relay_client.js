// The page's side of the relay (PROTOCOL.md): TCP connections over one WebSocket.
// It is plain JavaScript that runs in a browser and under Bun (for the tests).
//
//   const net = new RelayTcp("ws://127.0.0.1:8765");
//   await net.open();
//   const id = await net.connect("127.0.0.1", 4433);
//   await net.send(id, bytes);
//   const chunk = await net.recv(id, 4096);   // Uint8Array, or null at the end
//   net.close(id);

export const OP = { CONNECT: 1, SEND: 2, CLOSE: 3, OK: 10, FAIL: 11, DATA: 12, EOF: 13 };
export const MAX_BODY = 65535;

export class TcpError extends Error {
  constructor(errno, message) {
    super(message);
    this.name = "TcpError";
    this.errno = errno;
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
  constructor(url, WebSocketImpl = globalThis.WebSocket) {
    this.url = url;
    this.WebSocketImpl = WebSocketImpl;
    this.ws = null;
    this.conns = new Map();          // id -> { state, waiters, chunks, eof, error }
    this.connectWaiters = new Map(); // id -> { resolve, reject }
    this.readers = new Map();        // id -> array of { resolve, reject, max }
  }

  open() {
    return new Promise((resolve, reject) => {
      const ws = new this.WebSocketImpl(this.url);
      ws.binaryType = "arraybuffer";
      ws.onopen = () => resolve();
      ws.onerror = (e) => reject(new TcpError(5, "relay connection failed"));
      ws.onmessage = (ev) => this.#message(new Uint8Array(ev.data));
      ws.onclose = () => this.#lost();
      this.ws = ws;
    });
  }

  // a free id: 0..255 that the page is not using
  #freeId() {
    for (let id = 0; id < 256; id++) if (!this.conns.has(id)) return id;
    throw new TcpError(24, "too many connections");
  }

  connect(host, port) {
    const id = this.#freeId();
    this.conns.set(id, { state: "connecting", chunks: [], eof: false, error: null });
    return new Promise((resolve, reject) => {
      this.connectWaiters.set(id, { resolve: () => resolve(id), reject });
      this.ws.send(encodeFrame(OP.CONNECT, id, connectBody(port, host)));
    });
  }

  send(id, bytes) {
    const c = this.conns.get(id);
    if (!c || c.state !== "open") return Promise.reject(new TcpError(22, "send before the connection is open"));
    for (let at = 0; at < bytes.length; at += MAX_BODY) {
      this.ws.send(encodeFrame(OP.SEND, id, bytes.subarray(at, Math.min(bytes.length, at + MAX_BODY))));
    }
    return Promise.resolve();
  }

  // up to max bytes that have arrived; null once the remote end has finished and nothing is left
  recv(id, max) {
    const c = this.conns.get(id);
    if (!c) return Promise.reject(new TcpError(22, "no such connection"));
    if (c.chunks.length > 0) return Promise.resolve(this.#take(c, max));
    if (c.error) return Promise.reject(c.error);
    if (c.eof) return Promise.resolve(null);
    return new Promise((resolve, reject) => {
      const list = this.readers.get(id) ?? [];
      list.push({ resolve, reject, max });
      this.readers.set(id, list);
    });
  }

  close(id) {
    const c = this.conns.get(id);
    if (!c) return;
    if (this.ws && this.ws.readyState === 1) this.ws.send(encodeFrame(OP.CLOSE, id));
    this.#forget(id);
  }

  shutdown() {
    for (const id of [...this.conns.keys()]) this.close(id);
    if (this.ws) this.ws.close();
  }

  #take(c, max) {
    const total = c.chunks.reduce((n, x) => n + x.length, 0);
    const want = Math.min(max, total);
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
    return out;
  }

  #wake(id) {
    const list = this.readers.get(id);
    if (!list) return;
    const c = this.conns.get(id);
    while (list.length > 0) {
      const r = list[0];
      if (c && c.chunks.length > 0) {
        list.shift();
        r.resolve(this.#take(c, r.max));
      } else if (c && c.error) {
        list.shift();
        r.reject(c.error);
      } else if (c && c.eof) {
        list.shift();
        r.resolve(null);
      } else {
        break;
      }
    }
    if (list.length === 0) this.readers.delete(id);
  }

  #forget(id) {
    const c = this.conns.get(id);
    this.conns.delete(id);
    this.connectWaiters.delete(id);
    const list = this.readers.get(id);
    this.readers.delete(id);
    if (list) for (const r of list) r.resolve(null);
    return c;
  }

  #message(bytes) {
    const f = decodeFrame(bytes);
    if (!f) return; // a frame that does not fit is ignored; the relay closes the socket on its own errors
    const c = this.conns.get(f.id);
    if (f.op === OP.OK) {
      const w = this.connectWaiters.get(f.id);
      if (c) c.state = "open";
      this.connectWaiters.delete(f.id);
      if (w) w.resolve();
      return;
    }
    if (f.op === OP.FAIL) {
      const errno = (f.body[0] << 8) | f.body[1];
      const err = new TcpError(errno, dec.decode(f.body.subarray(2)));
      const w = this.connectWaiters.get(f.id);
      if (w) {
        this.#forget(f.id);
        w.reject(err);
        return;
      }
      if (c) {
        c.error = err;
        this.#wake(f.id);
        this.conns.delete(f.id);
      }
      return;
    }
    if (!c) return;
    if (f.op === OP.DATA) {
      c.chunks.push(f.body.slice());
      this.#wake(f.id);
      return;
    }
    if (f.op === OP.EOF) {
      c.eof = true;
      this.#wake(f.id);
    }
  }

  #lost() {
    for (const id of [...this.conns.keys()]) {
      const c = this.conns.get(id);
      c.error = new TcpError(5, "relay connection closed");
      this.#wake(id);
      const w = this.connectWaiters.get(id);
      if (w) w.reject(c.error);
    }
    this.conns.clear();
    this.connectWaiters.clear();
  }
}
