// Tests of the relay and the page's client over real TCP sockets (bun test browser/test).
// The frames are checked against the Bend definitions' encodings (frame_vectors.json).
import { test, expect } from "bun:test";
import { startRelay, encodeFrame as relayFrame, decodeFrame as relayDecode, OP as RELAY_OP } from "../relay/relay.ts";
import { RelayTcp, TcpError, encodeFrame, decodeFrame, OP } from "../tcp_relay_client.js";
import vectors from "./frame_vectors.json";

// a TCP server that echoes what it reads, on a free port
function echoServer() {
  const listener = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      data(s, d) { s.write(d); },
      open() {},
      close() {},
      error() {},
    },
  });
  return { port: listener.port, stop: () => listener.stop(true) };
}

// a free port with nothing listening on it
function closedPort(): number {
  const l = Bun.listen({ hostname: "127.0.0.1", port: 0, socket: { data() {}, open() {}, close() {}, error() {} } });
  const port = l.port;
  l.stop(true);
  return port;
}

// a relay on a free port with the given allowlist and connection limit
function relay(allow: { host: string; ports: number[] }[], maxConnections = 256) {
  const server = startRelay({ port: 0, maxConnections, allow });
  return { url: `ws://127.0.0.1:${server.port}`, stop: () => server.stop(true) };
}

async function client(url: string) {
  const net = new RelayTcp(url);
  await net.open();
  return net;
}

async function readAll(net: RelayTcp, id: number): Promise<Uint8Array> {
  const parts: Uint8Array[] = [];
  for (;;) {
    const chunk = await net.recv(id, 65536);
    if (chunk === null) break;
    parts.push(chunk);
  }
  const total = parts.reduce((n, p) => n + p.length, 0);
  const out = new Uint8Array(total);
  let at = 0;
  for (const p of parts) { out.set(p, at); at += p.length; }
  return out;
}

test("frames agree with the Bend definitions (frame_vectors.json)", () => {
  for (const c of vectors.cases) {
    const body = new Uint8Array(c.body);
    const got = encodeFrame(c.op, c.id, body);
    expect(Array.from(got)).toEqual(c.bytes);
    expect(Array.from(relayFrame(c.op, c.id, body))).toEqual(c.bytes);
    const back = decodeFrame(got);
    expect(back.op).toBe(c.op);
    expect(back.id).toBe(c.id);
    expect(Array.from(back.body)).toEqual(c.body);
  }
});

test("a message that is not exactly one frame is not decoded", () => {
  expect(decodeFrame(new Uint8Array([2, 7, 0]))).toBeNull();
  expect(decodeFrame(new Uint8Array([2, 7, 0, 2, 1]))).toBeNull();
  expect(relayDecode(new Uint8Array([2, 7, 0, 0, 9]))).toBeNull();
});

test("echo: connect, send, receive, close", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port] }]);
  const net = await client(r.url);
  const id = await net.connect("127.0.0.1", echo.port);
  await net.send(id, new TextEncoder().encode("hello, relay"));
  const got = await net.recv(id, 64);
  expect(new TextDecoder().decode(got)).toBe("hello, relay");
  net.close(id);
  net.shutdown();
  r.stop();
  echo.stop();
});

test("a large payload both ways arrives intact (it is split into frames)", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port] }]);
  const net = await client(r.url);
  const id = await net.connect("127.0.0.1", echo.port);
  const data = new Uint8Array(300_000);
  let seed = 12345;
  for (let i = 0; i < data.length; i++) { seed = (seed * 1103515245 + 12345) & 0x7fffffff; data[i] = seed & 255; }
  const sending = net.send(id, data);
  const got = new Uint8Array(data.length);
  let at = 0;
  while (at < data.length) {
    const chunk = await net.recv(id, data.length - at);
    got.set(chunk, at);
    at += chunk.length;
  }
  await sending;
  expect(Buffer.compare(Buffer.from(got), Buffer.from(data))).toBe(0);
  net.shutdown();
  r.stop();
  echo.stop();
});

test("default-deny: a destination not in the allowlist is refused with errno 13", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port + 1] }]); // a different port
  const net = await client(r.url);
  const err = await net.connect("127.0.0.1", echo.port).catch((e) => e);
  expect(err).toBeInstanceOf(TcpError);
  expect(err.errno).toBe(13);
  net.shutdown();
  r.stop();
  echo.stop();
});

test("a listed host and port with nothing listening is refused with errno 111", async () => {
  const port = closedPort();
  const r = relay([{ host: "127.0.0.1", ports: [port] }]);
  const net = await client(r.url);
  const err = await net.connect("127.0.0.1", port).catch((e) => e);
  expect(err).toBeInstanceOf(TcpError);
  expect(err.errno).toBe(111);
  net.shutdown();
  r.stop();
});

test("the remote end's EOF reads as the bytes it sent, then null", async () => {
  const listener = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open(s) { s.write(new TextEncoder().encode("bye")); s.end(); },
      data() {},
      close() {},
      error() {},
    },
  });
  const r = relay([{ host: "127.0.0.1", ports: [listener.port] }]);
  const net = await client(r.url);
  const id = await net.connect("127.0.0.1", listener.port);
  const all = await readAll(net, id);
  expect(new TextDecoder().decode(all)).toBe("bye");
  expect(await net.recv(id, 10)).toBeNull();
  net.shutdown();
  r.stop();
  listener.stop(true);
});

test("many connections at once, each echoes its own bytes", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port] }]);
  const net = await client(r.url);
  const ids = await Promise.all(Array.from({ length: 20 }, () => net.connect("127.0.0.1", echo.port)));
  expect(new Set(ids).size).toBe(20);
  await Promise.all(ids.map((id) => net.send(id, new TextEncoder().encode(`conn ${id}`))));
  const got = await Promise.all(ids.map((id) => net.recv(id, 64)));
  got.forEach((g, i) => expect(new TextDecoder().decode(g)).toBe(`conn ${ids[i]}`));
  net.shutdown();
  r.stop();
  echo.stop();
});

test("an id is reused after it is closed", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port] }]);
  const net = await client(r.url);
  const first = await net.connect("127.0.0.1", echo.port);
  net.close(first);
  const second = await net.connect("127.0.0.1", echo.port);
  expect(second).toBe(first);
  await net.send(second, new TextEncoder().encode("again"));
  expect(new TextDecoder().decode(await net.recv(second, 16))).toBe("again");
  net.shutdown();
  r.stop();
  echo.stop();
});

test("the connection limit answers the next connect with errno 24", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port] }], 2);
  const net = await client(r.url);
  await net.connect("127.0.0.1", echo.port);
  await net.connect("127.0.0.1", echo.port);
  const err = await net.connect("127.0.0.1", echo.port).catch((e) => e);
  expect(err.errno).toBe(24);
  net.shutdown();
  r.stop();
  echo.stop();
});

test("a SEND before OK is a protocol error: the relay closes the WebSocket", async () => {
  const echo = echoServer();
  const r = relay([{ host: "127.0.0.1", ports: [echo.port] }]);
  const ws = new WebSocket(r.url);
  ws.binaryType = "arraybuffer";
  await new Promise((res) => (ws.onopen = res));
  const closed = new Promise((res) => (ws.onclose = (e) => res(e.code)));
  ws.send(encodeFrame(OP.SEND, 5, new Uint8Array([1, 2, 3])));
  expect(await closed).toBe(1002);
  r.stop();
  echo.stop();
});

test("the relay's frames are the same as the page's", () => {
  expect(RELAY_OP.CONNECT).toBe(OP.CONNECT);
  expect(RELAY_OP.DATA).toBe(OP.DATA);
});
