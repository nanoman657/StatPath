// The page's TCP effects, run as Bend programs (tests/web/*.bend.tpl) over the relay. Each program
// runs under the Bend runtime with the asynchronous scheduler (BEND_MAIN: its main.ts), with the
// relay the page would have open (preload.js). A program with no relay gets ENOTCONN.
import { test, expect } from "bun:test";
import { startRelay } from "../relay/relay.ts";
import { resolve, join } from "node:path";
import { existsSync, readFileSync, writeFileSync, unlinkSync } from "node:fs";

const HERE = import.meta.dir;
const WEB = resolve(HERE, "../tests/web");
const PRELOAD = resolve(HERE, "preload.js");
const MAIN = process.env.BEND_MAIN ?? "/tmp/claude-0/src/bend-async/bend2/main.ts";
const runnable = existsSync(MAIN);

// peers: an echo, a peer that never writes, one that closes at once, and a port nothing listens on
function peers() {
  const echo = Bun.listen({
    hostname: "127.0.0.1", port: 0,
    socket: { open() {}, data(s, d) { s.write(d); }, close() {}, error() {} },
  });
  const silent = Bun.listen({
    hostname: "127.0.0.1", port: 0,
    socket: { open() {}, data() {}, close() {}, error() {} },
  });
  const closer = Bun.listen({
    hostname: "127.0.0.1", port: 0,
    socket: { open(s) { s.end(); }, data() {}, close() {}, error() {} },
  });
  const denied = Bun.listen({
    hostname: "127.0.0.1", port: 0,
    socket: { open() {}, data() {}, close() {}, error() {} },
  });
  const closed = Bun.listen({ hostname: "127.0.0.1", port: 0, socket: { open() {}, data() {}, close() {}, error() {} } });
  const refused = closed.port;
  closed.stop(true);
  const ports = { ECHO: echo.port, SILENT: silent.port, CLOSER: closer.port, DENIED: denied.port, REFUSED: refused };
  return { ports, stop: () => [echo, silent, closer, denied].forEach((s) => s.stop(true)) };
}

async function bendRun(name: string, ports: Record<string, number>, relayUrl?: string) {
  const src = readFileSync(join(WEB, `${name}.bend.tpl`), "utf8")
    .replace(/__([A-Z]+)__/g, (_, k: string) => String(ports[k]));
  const file = join(WEB, `_run_${name}.bend`);
  writeFileSync(file, src);
  try {
    const env: Record<string, string> = { ...(process.env as Record<string, string>) };
    delete env.BEND_RELAY;
    if (relayUrl) env.BEND_RELAY = relayUrl;
    const p = Bun.spawn([process.execPath, "--preload", PRELOAD, MAIN, file], { env, stdout: "pipe", stderr: "pipe" });
    const [out, err] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
    await p.exited;
    return { out: out.trim(), err };
  } finally {
    unlinkSync(file);
  }
}

// one relay for a program: it allows the echo, silent, closer and refused peers, not denied
function withRelay(p: ReturnType<typeof peers>) {
  const server = startRelay({
    port: 0,
    maxConnections: 256,
    allow: [
      { host: "127.0.0.1", ports: [p.ports.ECHO, p.ports.SILENT, p.ports.CLOSER, p.ports.REFUSED] },
    ],
  });
  return { url: `ws://127.0.0.1:${server.port}`, stop: () => server.stop(true) };
}

const cases: [string, string][] = [
  ["echo", "recv: hé"],
  ["refused", "connect failed: 111 Connection refused"],
  ["denied", "connect failed: 13 Permission denied"],
  ["silent", "timeout"],
  ["closer", "recv: none"],
  ["bytes", "bytes: 3"],
];

for (const [name, expected] of cases) {
  test.skipIf(!runnable)(`page program ${name}: prints "${expected}"`, async () => {
    const p = peers();
    const r = withRelay(p);
    try {
      const got = await bendRun(name, p.ports, r.url);
      expect(got.out).toBe(expected);
    } finally {
      r.stop();
      p.stop();
    }
  }, 120000);
}

test.skipIf(!runnable)("page program with no relay: the connect fails with ENOTCONN", async () => {
  const p = peers();
  try {
    const got = await bendRun("echo", p.ports);
    expect(got.out).toBe("connect failed: 107 Transport endpoint is not connected");
  } finally {
    p.stop();
  }
}, 120000);
