// Flow control, partial writes and the ends of a connection (PROTOCOL.md): a slow peer, a peer
// that never reads, a peer that closes, and the frames the relay must refuse or drop.
import { test, expect } from "bun:test";
import { RelayTcp, TcpError, encodeFrame, decodeFrame, OP, SEND_WINDOW, READ_WINDOW, MAX_BODY } from "../tcp_relay_client.js";
import { testRelay, PageSocket, TEST_TOKEN, rawSocket } from "./support.ts";

const MB = 1024 * 1024;
const enc = new TextEncoder();
const dec = new TextDecoder();
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

async function waitFor(cond: () => boolean, ms: number) {
  const until = Date.now() + ms;
  while (!cond() && Date.now() < until) await sleep(10);
}

function relay(allow: { host: string; ports: number[] }[], opts: { maxCount?: number } = {}) {
  return testRelay(allow, {}, {}, opts);
}

// A peer that counts the bytes it reads. It reads nothing for pauseMs (Infinity: never, until
// got.sock.resume() is called by the test).
function sink(pauseMs = 0) {
  const got: { n: number; sock: any } = { n: 0, sock: null };
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open(s) {
        got.sock = s;
        if (pauseMs > 0) {
          s.pause();
          if (pauseMs !== Infinity) setTimeout(() => s.resume(), pauseMs);
        }
      },
      data(_s, d) {
        got.n += d.length;
      },
      close() {},
      error() {},
    },
  });
  return { port: server.port, got, stop: () => server.stop(true) };
}

// A peer that sends bytes as soon as it is connected, and ends the connection after them if close.
// It writes what the socket takes, and the rest on drain (Bun's write keeps none of it).
function source(bytes: Uint8Array, close: boolean) {
  let off = 0;
  const pump = (s: any) => {
    while (off < bytes.length) {
      const n = s.write(bytes.subarray(off));
      if (n <= 0) return;
      off += n;
    }
    if (close) s.end();
  };
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open: pump,
      drain: pump,
      data() {},
      close() {},
      error() {},
    },
  });
  return { port: server.port, stop: () => server.stop(true) };
}

function echo() {
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      data(s, d) {
        s.write(d);
      },
      open() {},
      close() {},
      error() {},
    },
  });
  return { port: server.port, stop: () => server.stop(true) };
}

// the connect body: the port, then the host
function connectBody(port: number, host: string) {
  const text = enc.encode(host);
  const body = new Uint8Array(2 + text.length);
  body[0] = port >> 8;
  body[1] = port & 255;
  body.set(text, 2);
  return body;
}

test("bytes the socket does not take at once are written later: none are lost", async () => {
  const peer = sink(400); // reads nothing for 400 ms, so the socket's buffers fill
  const r = relay([{ host: "127.0.0.1", ports: [peer.port] }]);
  const net = new RelayTcp(r.url, PageSocket);
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", peer.port);
  const data = new Uint8Array(16 * MB).fill(9); // more than the socket buffers hold
  await net.send(id, data);
  await waitFor(() => peer.got.n === data.length, 5000);
  expect(peer.got.n).toBe(data.length);
  net.shutdown();
  r.stop();
  peer.stop();
});

test("a dropped send reports exactly the bytes the socket took; the page's flow stays within its window", async () => {
  const peer = sink(Infinity); // never reads
  let framed = 0; // the SEND payload bytes this page has put on the WebSocket
  class Counting extends PageSocket {
    send(data: any) {
      const f = decodeFrame(new Uint8Array(data));
      if (f && f.op === OP.SEND) framed += f.body.length;
      return super.send(data);
    }
  }
  const r = relay([{ host: "127.0.0.1", ports: [peer.port] }]);
  const net = new RelayTcp(r.url, Counting as any);
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", peer.port);
  const total = 16 * MB;
  let outcome: any = null;
  net.startSend(id, new Uint8Array(total).fill(3), (res: any) => (outcome = res));
  await sleep(500);
  const d: any = await new Promise((res) => net.discard(id, res));
  expect(d.error).toBeUndefined();
  const written: number = d.written;
  expect(outcome).toBeNull(); // dropped: the send never completed
  expect(written).toBeGreaterThan(0);
  expect(written).toBeLessThan(total);
  expect(framed).toBeGreaterThanOrEqual(written);
  expect(framed).toBeLessThanOrEqual(written + SEND_WINDOW);
  // the peer gets exactly the bytes the relay took, and no others
  peer.got.sock.resume();
  await waitFor(() => peer.got.n === written, 5000);
  await sleep(300);
  expect(peer.got.n).toBe(written);
  // the page carries on from where the relay stopped
  await net.send(id, new Uint8Array([1, 2, 3, 4, 5]));
  await waitFor(() => peer.got.n === written + 5, 5000);
  expect(peer.got.n).toBe(written + 5);
  net.shutdown();
  r.stop();
  peer.stop();
});

test("the relay reads no further ahead of the page than the read window", async () => {
  const bytes = new Uint8Array(2 * MB).fill(5);
  const src = source(bytes, true);
  const r = relay([{ host: "127.0.0.1", ports: [src.port] }]);
  const net = new RelayTcp(r.url, PageSocket);
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", src.port);
  await sleep(500); // the page reads nothing for a while
  const ahead = net.buffered(id);
  expect(ahead).toBeGreaterThan(0);
  expect(ahead).toBeLessThanOrEqual(READ_WINDOW + 256 * 1024);
  let got = 0;
  for (;;) {
    const c = await net.recv(id, 64 * 1024);
    if (c === null) break;
    got += c.length;
  }
  expect(got).toBe(bytes.length);
  net.shutdown();
  r.stop();
  src.stop();
});

test("a send after the peer has closed fails with the broken pipe (EPIPE), and the WebSocket serves on", async () => {
  const src = source(enc.encode("bye"), true);
  const other = echo();
  const r = relay([
    { host: "127.0.0.1", ports: [src.port] },
    { host: "127.0.0.1", ports: [other.port] },
  ]);
  const net = new RelayTcp(r.url, PageSocket);
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", src.port);
  expect(dec.decode(await net.recv(id, 100))).toBe("bye");
  expect(await net.recv(id, 100)).toBeNull(); // the peer has finished
  // the first write after the peer closed can still be taken; a later one fails
  let err: any = null;
  for (let i = 0; i < 20 && err === null; i++) {
    try {
      await net.send(id, new Uint8Array(1024));
      await sleep(50);
    } catch (e) {
      err = e;
    }
  }
  expect(err).toBeInstanceOf(TcpError);
  expect([32, 104]).toContain(err.errno); // EPIPE, or the reset the peer's close causes
  // the id is free: the WebSocket still serves another connection
  const id2 = await net.connect("127.0.0.1", other.port);
  await net.send(id2, enc.encode("again"));
  expect(dec.decode(await net.recv(id2, 100))).toBe("again");
  net.shutdown();
  r.stop();
  src.stop();
  other.stop();
});

test("a READ whose count is not four bytes is a protocol error", async () => {
  const other = echo();
  const r = relay([{ host: "127.0.0.1", ports: [other.port] }]);
  const { ws, next, closed } = await rawSocket(r.url);
  ws.send(encodeFrame(OP.CONNECT, 1, connectBody(other.port, "127.0.0.1")));
  expect(decodeFrame(await next())?.op).toBe(OP.OK);
  ws.send(encodeFrame(OP.READ, 1, new Uint8Array(3)));
  expect(await closed).toBe(1002);
  r.stop();
  other.stop();
});

test("a frame for an id never connected is a protocol error; for a freed id it is dropped", async () => {
  const other = echo();
  const r = relay([{ host: "127.0.0.1", ports: [other.port] }]);

  // never connected: an error
  const a = await rawSocket(r.url);
  a.ws.send(encodeFrame(OP.DISCARD, 7));
  expect(await a.closed).toBe(1002);

  // connected, then closed by the page: a SEND still in flight after the CLOSE is dropped
  const b = await rawSocket(r.url);
  b.ws.send(encodeFrame(OP.CONNECT, 2, connectBody(other.port, "127.0.0.1")));
  expect(decodeFrame(await b.next())?.op).toBe(OP.OK);
  b.ws.send(encodeFrame(OP.CLOSE, 2));
  b.ws.send(encodeFrame(OP.SEND, 2, enc.encode("late")));
  await sleep(200);
  expect(b.ws.readyState).toBe(1); // still open
  b.ws.close();
  r.stop();
  other.stop();
});

// The count limit (PROTOCOL.md: a connection moves at most MAX_COUNT bytes each way). The tests lower
// it to CAP on both the relay and the page, so the limit is reached without moving 4 GiB. CAP is not
// a multiple of the frame size, so the limit falls inside a frame.
const CAP = 300 * 1024 + 17;

test("a connection can read exactly the count limit: the bytes arrive whole, then the end", async () => {
  const src = source(new Uint8Array(CAP).fill(7), true);
  const r = relay([{ host: "127.0.0.1", ports: [src.port] }], { maxCount: CAP });
  const net = new RelayTcp(r.url, PageSocket);
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", src.port);
  let got = 0;
  for (;;) {
    const c = await net.recv(id, 64 * 1024);
    if (c === null) break;
    got += c.length;
  }
  expect(got).toBe(CAP);
  net.shutdown();
  r.stop();
  src.stop();
});

test("a read past the count limit fails the connection with EFBIG, after the bytes within the limit", async () => {
  const src = source(new Uint8Array(CAP + 5000).fill(7), true);
  const r = relay([{ host: "127.0.0.1", ports: [src.port] }], { maxCount: CAP });
  const net = new RelayTcp(r.url, PageSocket);
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", src.port);
  let got = 0;
  let err: any = null;
  try {
    for (;;) {
      const c = await net.recv(id, 64 * 1024);
      if (c === null) break;
      got += c.length;
    }
  } catch (e) {
    err = e;
  }
  expect(err).toBeInstanceOf(TcpError);
  expect(err.errno).toBe(27); // EFBIG
  expect(got).toBeLessThanOrEqual(CAP);
  net.shutdown();
  r.stop();
  src.stop();
});

test("a send that would pass the count limit is refused before it is sent; the connection stays open", async () => {
  const peer = sink(0);
  const r = relay([{ host: "127.0.0.1", ports: [peer.port] }], { maxCount: CAP });
  const net = new RelayTcp(r.url, PageSocket, { maxCount: CAP });
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", peer.port);
  await net.send(id, new Uint8Array(CAP - 10).fill(1));
  let err: any = null;
  try {
    await net.send(id, new Uint8Array(11));
  } catch (e) {
    err = e;
  }
  expect(err).toBeInstanceOf(TcpError);
  expect(err.errno).toBe(27);
  // the refused bytes were not counted: the send up to the limit still goes through
  await net.send(id, new Uint8Array(10).fill(2));
  await waitFor(() => peer.got.n === CAP, 5000);
  await sleep(200);
  expect(peer.got.n).toBe(CAP);
  net.shutdown();
  r.stop();
  peer.stop();
});

test("the page's client refuses a limit that is not a count", () => {
  expect(() => new RelayTcp("ws://x", PageSocket, { maxCount: 0 })).toThrow(RangeError);
  expect(() => new RelayTcp("ws://x", PageSocket, { maxCount: 2 ** 32 })).toThrow(RangeError);
  expect(() => new RelayTcp("ws://x", PageSocket, { maxCount: 1.5 })).toThrow(RangeError);
});

// A WebSocket that stands for the relay: it answers AUTH, OK and AUTHOK as a relay would, and the test
// pushes any other frame into the page.
class ScriptedRelay {
  static last: ScriptedRelay | null = null;
  readyState = 0;
  binaryType = "";
  onopen: any = null;
  onmessage: any = null;
  onclose: any = null;
  onerror: any = null;
  constructor(_url: string) {
    ScriptedRelay.last = this;
    queueMicrotask(() => {
      this.readyState = 1;
      this.onopen?.();
    });
  }
  send(data: Uint8Array) {
    const f = decodeFrame(new Uint8Array(data));
    if (!f) return;
    if (f.op === OP.AUTH) this.push(OP.AUTHOK, 0);
    if (f.op === OP.CONNECT) this.push(OP.OK, f.id);
  }
  push(op: number, id: number, body: Uint8Array = new Uint8Array(0)) {
    this.onmessage?.({ data: encodeFrame(op, id, body).buffer });
  }
  // n bytes of DATA, in frames of the largest body
  pushData(id: number, n: number) {
    for (let at = 0; at < n; at += MAX_BODY) this.push(OP.DATA, id, new Uint8Array(Math.min(MAX_BODY, n - at)));
  }
  close() {
    this.readyState = 3;
  }
}

test("data past the count limit from the relay ends the connection with EFBIG", async () => {
  const net = new RelayTcp("ws://scripted", ScriptedRelay as any, { maxCount: CAP });
  await net.open(TEST_TOKEN);
  const id = await net.connect("127.0.0.1", 9);
  const w = ScriptedRelay.last!;
  w.pushData(id, CAP); // exactly the limit: accepted
  w.pushData(id, 1); // one byte past it: the relay must not have sent it
  let err: any = null;
  try {
    await net.recv(id, 1024);
  } catch (e) {
    err = e;
  }
  expect(err).toBeInstanceOf(TcpError);
  expect(err.errno).toBe(27);
  net.shutdown();
});
