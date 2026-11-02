// The limits the model leaves to the environment, checked against the real relay and real sockets with the real
// clock (README, "Not checked by this"): the reads of a page's socket stop while its byte budget is empty, the
// connects and the bytes a page moves are within the burst plus the rate for the real time that has passed, and
// the relay accepts every SEND that the page client frames, including at the window's edges into a stalled peer.
import { test, expect } from "bun:test";
import { RelayTcp, encodeFrame, decodeFrame, OP } from "../tcp_relay_client.js";
import { testRelay, PageSocket, TEST_TOKEN, rawSocket, connectBody } from "./support.ts";

const KB = 1024;
const MB = 1024 * KB;
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

// a peer that sends bytes as soon as it is connected (its writes wait on drain), then ends the connection
function source(bytes: Uint8Array) {
  let off = 0;
  const pump = (s: any) => {
    while (off < bytes.length) {
      const n = s.write(bytes.subarray(off));
      if (n <= 0) return;
      off += n;
    }
    s.end();
  };
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: { open: pump, drain: pump, data() {}, close() {}, error() {} },
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

// the model's chunk bound: one socket read may take up to this much past the budget (Bun delivers 512 KiB reads here)
const CHUNK = 1024 * KB;

test("the relay reads a page's socket no faster than the byte budget, in real time", async () => {
  const size = 3 * MB;
  const rate = 512 * KB;
  const src = source(new Uint8Array(size).fill(9));
  const relayStarted = Date.now();
  const r = testRelay([{ host: "127.0.0.1", ports: [src.port] }], { bytesPerSecond: rate });
  const net = new RelayTcp(r.url, PageSocket);
  try {
    await net.open(TEST_TOKEN);
    const id = await net.connect("127.0.0.1", src.port);
    const t0 = Date.now();
    let got = 0;
    for (;;) {
      const chunk = await net.recv(id, 64 * KB);
      if (chunk === null) break;
      got += chunk.length;
      // the budget starts with a second's worth and refills at the rate; one read may overshoot it by a chunk
      const elapsed = (Date.now() - relayStarted) / 1000;
      expect(got).toBeLessThanOrEqual(rate * (1 + elapsed) + CHUNK);
    }
    const took = (Date.now() - t0) / 1000;
    expect(got).toBe(size);
    // the bytes beyond the first second's worth and one chunk could only be read at the rate
    expect(took).toBeGreaterThanOrEqual((size - rate - CHUNK) / rate - 0.5);
  } finally {
    net.shutdown();
    r.stop();
    src.stop();
  }
}, 60000);

test("the connects a page makes are at most the burst plus the rate for the real time that has passed", async () => {
  const target = echo();
  const cps = 5;
  const relayStarted = Date.now();
  const r = testRelay([{ host: "127.0.0.1", ports: [target.port] }], {
    connectsPerSecond: cps,
    maxConnections: 200,
    maxConnectionsTotal: 200,
  });
  const { ws, next } = await rawSocket(r.url);
  try {
    const n = 150;
    for (let id = 1; id <= n; id++) {
      ws.send(encodeFrame(OP.CONNECT, id, connectBody(target.port)));
      await sleep(20); // about 50 a second: far above the rate
    }
    let accepted = 0;
    for (let i = 0; i < n; i++) {
      const f = decodeFrame(await next())!;
      if (f.op === OP.OK) accepted++;
      else expect(f.op).toBe(OP.FAIL);
    }
    const elapsed = (Date.now() - relayStarted) / 1000;
    // the tokens start with two seconds' worth and refill at the rate: never more than that by the time of the
    // last reply, and not far fewer than that either
    expect(accepted).toBeLessThanOrEqual(2 * cps + cps * elapsed);
    expect(accepted).toBeGreaterThanOrEqual(2 * cps + cps * elapsed - 2 * cps);
  } finally {
    ws.close();
    r.stop();
    target.stop();
  }
}, 60000);

test("the relay accepts every SEND the page client frames, at the window's and the frame's edges, into a stalled peer", async () => {
  // the peer reads nothing for a second, so the relay's queue fills to the send window and the page waits
  const sizes = [1, 65535, 65536, 131072, 131073, 262144, 1, 8 * MB];
  const total = sizes.reduce((a, b) => a + b, 0);
  let got = 0;
  const peer = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open(s) {
        s.pause();
        setTimeout(() => s.resume(), 1000);
      },
      data(_s, d) {
        got += d.length;
      },
      close() {},
      error() {},
    },
  });
  const r = testRelay([{ host: "127.0.0.1", ports: [peer.port] }], {});
  const net = new RelayTcp(r.url, PageSocket);
  try {
    await net.open(TEST_TOKEN);
    const id = await net.connect("127.0.0.1", peer.port);
    for (const n of sizes) await net.send(id, new Uint8Array(n).fill(n & 255));
    const until = Date.now() + 30000;
    while (got < total && Date.now() < until) await sleep(20);
    // every send was accepted (a send the relay refused would have closed the WebSocket, and the next would fail)
    expect(got).toBe(total);
  } finally {
    net.shutdown();
    r.stop();
    peer.stop(true);
  }
}, 60000);
