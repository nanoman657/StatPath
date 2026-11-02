// The WebSocket behaviour the relay relies on, beyond the socket assumptions of bun_assumptions.test.ts: one
// message per frame and whole (in order, for any size up to a frame), a close code that reaches the peer, and a
// backlog that getBufferedAmount reports until it has drained. A change in Bun shows here first.
import { test, expect } from "bun:test";

const KB = 1024;
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

test("each binary message arrives whole and in order, at any size up to a frame", async () => {
  const server = Bun.serve({
    hostname: "127.0.0.1",
    port: 0,
    fetch(req, srv) {
      if (srv.upgrade(req)) return undefined;
      return new Response("no", { status: 400 });
    },
    websocket: {
      message(ws, msg) {
        ws.sendBinary(msg);
      },
    },
  });
  const ws = new WebSocket(`ws://127.0.0.1:${server.port}/`);
  ws.binaryType = "arraybuffer";
  const received: Uint8Array[] = [];
  ws.onmessage = (e) => received.push(new Uint8Array(e.data as ArrayBuffer));
  await new Promise((r) => (ws.onopen = r));
  // sizes from 0 to a frame's worth and a bit past it, each message filled with its own index
  const sizes: number[] = [];
  for (let i = 0; i < 300; i++) sizes.push((i * 7919) % 65540);
  for (let i = 0; i < sizes.length; i++) ws.send(new Uint8Array(sizes[i]).fill(i & 255));
  const until = Date.now() + 10000;
  while (received.length < sizes.length && Date.now() < until) await sleep(5);
  expect(received.length).toBe(sizes.length);
  for (let i = 0; i < sizes.length; i++) {
    expect(received[i].length).toBe(sizes[i]);
    expect(received[i].every((b) => b === (i & 255))).toBe(true);
  }
  ws.close();
  server.stop(true);
}, 30000);

test("a close with a code reaches the peer with that code", async () => {
  const server = Bun.serve({
    hostname: "127.0.0.1",
    port: 0,
    fetch(req, srv) {
      if (srv.upgrade(req)) return undefined;
      return new Response("no", { status: 400 });
    },
    websocket: {
      message(ws) {
        ws.close(1002, "a protocol error");
      },
    },
  });
  const ws = new WebSocket(`ws://127.0.0.1:${server.port}/`);
  const closed = new Promise<{ code: number; reason: string }>((res) => (ws.onclose = (e) => res({ code: e.code, reason: e.reason })));
  await new Promise((r) => (ws.onopen = r));
  ws.send(new Uint8Array([1]));
  const got = await closed;
  expect(got.code).toBe(1002);
  expect(got.reason).toBe("a protocol error");
  server.stop(true);
}, 15000);

test("getBufferedAmount reports a backlog while it is unsent, and reaches zero once the peer has it", async () => {
  const size = 8 * 1024 * KB;
  let serverWs: any = null;
  const server = Bun.serve({
    hostname: "127.0.0.1",
    port: 0,
    fetch(req, srv) {
      if (srv.upgrade(req)) return undefined;
      return new Response("no", { status: 400 });
    },
    websocket: {
      open(ws) {
        serverWs = ws;
        const chunk = new Uint8Array(64 * KB).fill(4);
        for (let sent = 0; sent < size; sent += chunk.length) ws.sendBinary(chunk);
      },
      message() {},
    },
  });
  const ws = new WebSocket(`ws://127.0.0.1:${server.port}/`);
  ws.binaryType = "arraybuffer";
  let got = 0;
  ws.onmessage = (e) => (got += (e.data as ArrayBuffer).byteLength);
  await new Promise((r) => (ws.onopen = r));
  // right after the sends, most of the backlog is still the server's
  await sleep(0);
  const backlog = serverWs.getBufferedAmount();
  expect(backlog).toBeGreaterThan(0);
  const until = Date.now() + 15000;
  while (got < size && Date.now() < until) await sleep(10);
  expect(got).toBe(size);
  // once the peer has everything, the backlog has drained
  expect(serverWs.getBufferedAmount()).toBe(0);
  ws.close();
  server.stop(true);
}, 30000);
