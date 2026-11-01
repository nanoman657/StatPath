// Flow control, partial writes and the ends of a connection (PROTOCOL.md): a slow peer, a peer
// that never reads, a peer that closes, and the frames the relay must refuse or drop.
import { test, expect } from "bun:test";
import { startRelay } from "../relay/relay.ts";
import { RelayTcp, TcpError, encodeFrame, decodeFrame, OP, SEND_WINDOW, READ_WINDOW } from "../tcp_relay_client.js";

const MB = 1024 * 1024;
const enc = new TextEncoder();
const dec = new TextDecoder();
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

async function waitFor(cond: () => boolean, ms: number) {
  const until = Date.now() + ms;
  while (!cond() && Date.now() < until) await sleep(10);
}

function relay(allow: { host: string; ports: number[] }[]) {
  const server = startRelay({ port: 0, maxConnections: 256, allow });
  return { url: `ws://127.0.0.1:${server.port}`, stop: () => server.stop(true) };
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
  const net = new RelayTcp(r.url);
  await net.open();
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
  class Counting extends WebSocket {
    send(data: any) {
      const f = decodeFrame(new Uint8Array(data));
      if (f && f.op === OP.SEND) framed += f.body.length;
      return super.send(data);
    }
  }
  const r = relay([{ host: "127.0.0.1", ports: [peer.port] }]);
  const net = new RelayTcp(r.url, Counting as any);
  await net.open();
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
  const net = new RelayTcp(r.url);
  await net.open();
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
  const net = new RelayTcp(r.url);
  await net.open();
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
  const ws = new WebSocket(r.url);
  ws.binaryType = "arraybuffer";
  await new Promise((res) => (ws.onopen = res));
  const reply = new Promise<any>((res) => (ws.onmessage = (e) => res(new Uint8Array(e.data as ArrayBuffer))));
  ws.send(encodeFrame(OP.CONNECT, 1, connectBody(other.port, "127.0.0.1")));
  expect(decodeFrame(await reply)?.op).toBe(OP.OK);
  const closed = new Promise<number>((res) => (ws.onclose = (e) => res(e.code)));
  ws.send(encodeFrame(OP.READ, 1, new Uint8Array(3)));
  expect(await closed).toBe(1002);
  r.stop();
  other.stop();
});

test("a frame for an id never connected is a protocol error; for a freed id it is dropped", async () => {
  const other = echo();
  const r = relay([{ host: "127.0.0.1", ports: [other.port] }]);

  // never connected: an error
  const a = new WebSocket(r.url);
  a.binaryType = "arraybuffer";
  await new Promise((res) => (a.onopen = res));
  const aClosed = new Promise<number>((res) => (a.onclose = (e) => res(e.code)));
  a.send(encodeFrame(OP.DISCARD, 7));
  expect(await aClosed).toBe(1002);

  // connected, then closed by the page: a SEND still in flight after the CLOSE is dropped
  const b = new WebSocket(r.url);
  b.binaryType = "arraybuffer";
  await new Promise((res) => (b.onopen = res));
  let opened = false;
  b.onmessage = (e) => {
    if (decodeFrame(new Uint8Array(e.data as ArrayBuffer))?.op === OP.OK) opened = true;
  };
  b.send(encodeFrame(OP.CONNECT, 2, connectBody(other.port, "127.0.0.1")));
  await waitFor(() => opened, 2000);
  expect(opened).toBe(true);
  b.send(encodeFrame(OP.CLOSE, 2));
  b.send(encodeFrame(OP.SEND, 2, enc.encode("late")));
  await sleep(200);
  expect(b.readyState).toBe(1); // still open
  b.close();
  a.close();
  r.stop();
  other.stop();
});
