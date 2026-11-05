// The time a fair environment takes to serve a client, measured on loopback with the relay at its default limits.
// Three scenarios, each run against one relay and one echo server:
//   1. sessions contend: K sessions connect at once, each doing 60 connects; the per-connect time to service and
//      each session's finish time show whether one session delays another;
//   2. one session under a connect burst: 100 connects requested at once; a refused connect (EAGAIN, the connect
//      rate) is retried after 10 ms; the time to service is compared with the token bucket's bound;
//   3. sessions contend for bytes: K sessions each echo 4 MiB at once.
// The relay's connect rate is per WebSocket (a bucket of 2 x connectsPerSecond, refilled at connectsPerSecond), and
// its byte budget is per WebSocket too, so sessions do not share either. Scenario 3 therefore measures CPU sharing:
// the relay, the clients and the echo server all run in this one process. Run with
// `bun bench/relay_contention.ts` (not part of `bun test`).
import { testRelay, PageSocket, TEST_TOKEN } from "../test/support.ts";
import { RelayTcp, TcpError } from "../tcp_relay_client.js";

const EAGAIN = 11;
const CONNECTS_PER_SECOND = 20; // the relay's default
const BURST = 2 * CONNECTS_PER_SECOND; // the bucket starts full

const echo = Bun.listen({
  hostname: "127.0.0.1",
  port: 0,
  socket: { data(s, d) { s.write(d); }, open() {}, close() {}, error() {} },
});
// Only the per-address upgrade limit is raised: the benchmark opens about 30 sessions from one address.
const relay = testRelay([{ host: "127.0.0.1", ports: [echo.port] }], { maxConnections: 256, upgradesPerMinute: 600 });

const pct = (xs: number[], p: number) => {
  const s = [...xs].sort((a, b) => a - b);
  return s[Math.min(s.length - 1, Math.floor((p / 100) * s.length))];
};
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

async function openSession(): Promise<RelayTcp> {
  const net = new RelayTcp(relay.url, PageSocket);
  await net.open(TEST_TOKEN);
  return net;
}

// Connects, retrying after the connect-rate refusal. Returns the id and how many refusals it took.
async function connectRetry(net: RelayTcp, port: number): Promise<{ id: number; refusals: number }> {
  let refusals = 0;
  for (;;) {
    try {
      return { id: await net.connect("127.0.0.1", port), refusals };
    } catch (e) {
      if (e instanceof TcpError && e.errno === EAGAIN) {
        refusals++;
        await sleep(10);
        continue;
      }
      throw e;
    }
  }
}

// Scenario 1: K sessions, each doing 60 connects, all at once.
for (const K of [1, 4, 16]) {
  const sessions = await Promise.all(Array.from({ length: K }, () => openSession()));
  const t0 = performance.now();
  const per: { ms: number[]; refusals: number; finished: number }[] = [];
  await Promise.all(sessions.map(async (net) => {
    const row = { ms: [] as number[], refusals: 0, finished: 0 };
    per.push(row);
    for (let i = 0; i < 60; i++) {
      const a = performance.now();
      const { id, refusals } = await connectRetry(net, echo.port);
      row.ms.push(performance.now() - a);
      row.refusals += refusals;
      net.close(id);
    }
    row.finished = performance.now() - t0;
  }));
  const all = per.flatMap((r) => r.ms);
  const fin = per.map((r) => r.finished);
  const refused = per.reduce((n, r) => n + r.refusals, 0);
  console.log(
    `sessions contend, K=${K}: 60 connects each, time to service p50=${pct(all, 50).toFixed(1)} ms ` +
      `p95=${pct(all, 95).toFixed(1)} ms max=${Math.max(...all).toFixed(1)} ms; ` +
      `session finish min=${Math.min(...fin).toFixed(0)} ms max=${Math.max(...fin).toFixed(0)} ms; ` +
      `refusals=${refused}`,
  );
}

// Scenario 2: one session, 100 connects requested at once.
{
  const net = await openSession();
  const N = 100;
  const t0 = performance.now();
  const results = await Promise.all(Array.from({ length: N }, async () => {
    const r = await connectRetry(net, echo.port);
    return { ms: performance.now() - t0, refusals: r.refusals, id: r.id };
  }));
  const served = results.map((r) => r.ms);
  const refused = results.reduce((n, r) => n + r.refusals, 0);
  // Bound from the token bucket: the first BURST connects are immediate, then one every 1/CONNECTS_PER_SECOND.
  const bound = ((N - BURST) / CONNECTS_PER_SECOND) * 1000;
  console.log(
    `one session, ${N} connects at once: time to service p50=${pct(served, 50).toFixed(0)} ms ` +
      `p95=${pct(served, 95).toFixed(0)} ms last=${Math.max(...served).toFixed(0)} ms; ` +
      `refusals=${refused}; bucket bound for the last=${bound.toFixed(0)} ms`,
  );
  for (const r of results) net.close(r.id);
}

// Scenario 3: K sessions, each echoing 4 MiB at once.
for (const K of [1, 4]) {
  const sessions = await Promise.all(Array.from({ length: K }, () => openSession()));
  const size = 4 << 20;
  const data = new Uint8Array(size);
  const ids = await Promise.all(sessions.map((net) => connectRetry(net, echo.port).then((r) => r.id)));
  const t0 = performance.now();
  const done = await Promise.all(sessions.map(async (net, k) => {
    const id = ids[k];
    const sending = net.send(id, data);
    let total = 0;
    while (total < size) {
      const c = await net.recv(id, 65536);
      if (c === null) break;
      total += c.length;
    }
    await sending;
    return performance.now() - t0;
  }));
  const mib = (K * size * 2) / (1 << 20);
  const wall = Math.max(...done);
  console.log(
    `sessions echo 4 MiB at once, K=${K}: finish min=${Math.min(...done).toFixed(0)} ms ` +
      `max=${wall.toFixed(0)} ms; aggregate ${(mib / (wall / 1000)).toFixed(1)} MiB/s both ways`,
  );
}

relay.stop();
echo.stop(true);
process.exit(0);
