// The browser relay's latency over real sockets, on loopback: a page's WebSocket to the relay (127.0.0.1), the
// relay's TCP connection to a local echo server. Run with `bun bench/relay_latency.ts` (not part of `bun test`).
// The relay runs with its default limits; the connects are paced at 60 ms, under the default 20 a second, so the
// connects-a-second limit does not shape the connect figures. The byte budget (16 MiB a second, both ways together)
// does shape the transfers: the first two 4 MiB echoes use the burst, the third waits for the budget.
import { testRelay, PageSocket, TEST_TOKEN } from "../test/support.ts";
import { RelayTcp } from "../tcp_relay_client.js";

const echo = Bun.listen({
  hostname: "127.0.0.1",
  port: 0,
  socket: { data(s, d) { s.write(d); }, open() {}, close() {}, error() {} },
});
const relay = testRelay([{ host: "127.0.0.1", ports: [echo.port] }], { maxConnections: 256 });

const pct = (xs: number[], p: number) => {
  const s = [...xs].sort((a, b) => a - b);
  return s[Math.min(s.length - 1, Math.floor((p / 100) * s.length))];
};
const stats = (name: string, xs: number[]) =>
  console.log(`${name}: n=${xs.length} p50=${pct(xs, 50).toFixed(2)} ms p95=${pct(xs, 95).toFixed(2)} ms ` +
    `p99=${pct(xs, 99).toFixed(2)} ms max=${Math.max(...xs).toFixed(2)} ms`);
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

const net = new RelayTcp(relay.url, PageSocket);
await net.open(TEST_TOKEN);

const connectMs: number[] = [];
const ids: number[] = [];
for (let i = 0; i < 200; i++) {
  await sleep(60);
  const t0 = performance.now();
  ids.push(await net.connect("127.0.0.1", echo.port));
  connectMs.push(performance.now() - t0);
}
stats("connect: page request to the relay's TCP up (paced)", connectMs);

const rtt: number[] = [];
const one = new Uint8Array([7]);
for (let i = 0; i < 300; i++) {
  const t0 = performance.now();
  await net.send(ids[0], one);
  let got = 0;
  while (got < 1) {
    const c = await net.recv(ids[0], 64);
    if (c === null) break;
    got += c.length;
  }
  rtt.push(performance.now() - t0);
}
stats("round trip, 1 byte, through the echo", rtt);

const size = 4 << 20;
const data = new Uint8Array(size);
for (let run = 1; run <= 3; run++) {
  const id = ids[run];
  const t0 = performance.now();
  const sending = net.send(id, data);
  let total = 0;
  while (total < size) {
    const c = await net.recv(id, 65536);
    if (c === null) break;
    total += c.length;
  }
  await sending;
  const ms = performance.now() - t0;
  console.log(`drain run ${run}: 4 MiB echoed in ${ms.toFixed(0)} ms = ${(size / 1048576 / (ms / 1000)).toFixed(2)} MiB/s`);
}

for (const id of ids) net.close(id);
relay.stop();
echo.stop(true);
process.exit(0);
