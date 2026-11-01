// The relay's safety for real use (RELAY.md): the configuration is checked, a page must come from
// an allowed origin and present a token, TLS serves wss, the limits hold, shutdown is orderly, and
// no token reaches the log.
import { test, expect } from "bun:test";
import { mkdtempSync, writeFileSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { loadConfig, readConfig, ConfigError } from "../relay/config.ts";
import { startRelay, type Log } from "../relay/relay.ts";
import { newToken, digestOf } from "../relay/token.ts";
import { RelayTcp, TcpError, encodeFrame, decodeFrame, OP } from "../tcp_relay_client.js";
import { testRelay, rawSocket, PageSocket, TEST_TOKEN, TEST_ORIGIN, authFrame, connectBody } from "./support.ts";

const HERE = import.meta.dir;
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

function echo() {
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: { open() {}, data(s, d) { s.write(d); }, close() {}, error() {} },
  });
  return { port: server.port, stop: () => server.stop(true) };
}

// how a WebSocket attempt ends: open, refused (the upgrade failed), or closed with a code
function outcome(ws: WebSocket): Promise<string> {
  return new Promise((res) => {
    ws.onopen = () => res("open");
    ws.onerror = () => res("refused");
    ws.onclose = (e) => res(`closed ${e.code}`);
  });
}

const GOOD = {
  host: "127.0.0.1",
  port: 0,
  origins: [TEST_ORIGIN],
  tokens: [{ name: "a", sha256: digestOf("x") }],
  allow: [{ host: "127.0.0.1", ports: [80] }],
};

function problemsOf(patch: Record<string, unknown>): string {
  try {
    loadConfig({ ...GOOD, ...patch });
    return "accepted";
  } catch (e) {
    return e instanceof ConfigError ? e.message : String(e);
  }
}

test("the configuration is accepted when it is right, and each mistake is named", () => {
  expect(problemsOf({})).toBe("accepted");
  expect(problemsOf({ extra: 1 })).toContain('unknown setting "extra"');
  expect(problemsOf({ origins: [] })).toContain("origins must list");
  expect(problemsOf({ origins: ["https://page.test/"] })).toContain("exactly scheme://host");
  expect(problemsOf({ tokens: [] })).toContain("tokens must list");
  expect(problemsOf({ tokens: [{ name: "a", sha256: "abc" }] })).toContain("sha256 must be 64");
  expect(problemsOf({ tokens: [{ name: "a", sha256: "0".repeat(64) }] })).toContain("placeholder");
  expect(problemsOf({ allow: [] })).toContain("allow must list");
  expect(problemsOf({ port: 70000 })).toContain("port must be");
  expect(problemsOf({ host: "0.0.0.0" })).toContain("needs tls");
  expect(problemsOf({ limits: { connectsPerSecnd: 3 } })).toContain('unknown limit "connectsPerSecnd"');
  expect(problemsOf({ limits: { bytesPerSecond: 0 } })).toContain("limit bytesPerSecond must be");
  expect(problemsOf({ limits: { idleSeconds: 300 } })).toContain("idleSeconds must be at most 255");
  // every problem is listed at once
  expect(problemsOf({ origins: [], port: -1 })).toContain("origins must list");
  expect(problemsOf({ origins: [], port: -1 })).toContain("port must be");
});

test("the example configuration is refused until a real token replaces its placeholder", async () => {
  let message = "";
  try {
    await readConfig(resolve(HERE, "../relay/config.example.json"));
  } catch (e) {
    message = (e as Error).message;
  }
  expect(message).toContain("placeholder");
});

test("a token from relay/token.ts is what the relay accepts", async () => {
  const proc = Bun.spawnSync([process.execPath, resolve(HERE, "../relay/token.ts"), "alice"]);
  expect(proc.exitCode).toBe(0);
  const out = proc.stdout.toString();
  const token = out.match(/token \(.*?\): (\S+)/)![1];
  const entry = JSON.parse(out.match(/config entry .*?: (\{.*\})/)![1]);
  expect(entry).toEqual({ name: "alice", sha256: digestOf(token) });
  expect(token.length).toBeGreaterThanOrEqual(40);
  const relay = startRelay(loadConfig({ ...GOOD, tokens: [entry] }), { log: () => {} });
  try {
    const sock = await rawSocket(relay.url, token);
    expect(sock.ws.readyState).toBe(1);
    sock.ws.close();
  } finally {
    relay.stop();
  }
});

test("a page from another origin is refused at the upgrade", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }]);
  try {
    expect(await outcome(new WebSocket(r.url, { headers: { Origin: "https://evil.test" } } as any))).toBe("refused");
    expect(await outcome(new WebSocket(r.url))).toBe("refused"); // no Origin at all
    expect(await outcome(new PageSocket(r.url))).toBe("open");
  } finally {
    r.stop();
  }
});

test("the first frame must be AUTH, and a wrong token closes the WebSocket", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }]);
  try {
    const first = new PageSocket(r.url);
    first.binaryType = "arraybuffer";
    const closedA = new Promise<number>((res) => (first.onclose = (e) => res(e.code)));
    await new Promise((res) => (first.onopen = res));
    first.send(encodeFrame(OP.CONNECT, 1, connectBody(80)));
    expect(await closedA).toBe(1008);

    const wrong = new PageSocket(r.url);
    wrong.binaryType = "arraybuffer";
    const closedB = new Promise<number>((res) => (wrong.onclose = (e) => res(e.code)));
    await new Promise((res) => (wrong.onopen = res));
    wrong.send(authFrame("not the token"));
    expect(await closedB).toBe(1008);

    const twice = await rawSocket(r.url);
    twice.ws.send(authFrame());
    expect(await twice.closed).toBe(1002);
  } finally {
    r.stop();
  }
});

test("a RelayTcp with a wrong token is refused by open()", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }]);
  try {
    const net = new RelayTcp(r.url, PageSocket);
    let err: unknown = null;
    try {
      await net.open("not the token");
    } catch (e) {
      err = e;
    }
    expect(err).toBeInstanceOf(TcpError);
    expect((err as TcpError).errno).toBe(13);
  } finally {
    r.stop();
  }
});

test("a WebSocket that does not authenticate within authSeconds is closed", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }], { authSeconds: 1 });
  try {
    const ws = new PageSocket(r.url);
    const closed = new Promise<number>((res) => (ws.onclose = (e) => res(e.code)));
    await new Promise((res) => (ws.onopen = res));
    expect(await closed).toBe(1008);
  } finally {
    r.stop();
  }
});

test("a token longer than the limit is refused", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }]);
  try {
    const ws = new PageSocket(r.url);
    const closed = new Promise<number>((res) => (ws.onclose = (e) => res(e.code)));
    await new Promise((res) => (ws.onopen = res));
    ws.send(authFrame("x".repeat(300)));
    expect(await closed).toBe(1008);
  } finally {
    r.stop();
  }
});

test("the relay serves wss with its own certificate; a page trusts it through the certificate", async () => {
  const dir = mkdtempSync(join(tmpdir(), "relay-tls-"));
  const key = join(dir, "key.pem");
  const cert = join(dir, "cert.pem");
  try {
    const made = Bun.spawnSync([
      "openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-keyout", key, "-out", cert,
      "-days", "2", "-subj", "/CN=localhost", "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1",
    ], { stdout: "pipe", stderr: "pipe" });
    expect(made.exitCode).toBe(0);
    const target = echo();
    const relay = startRelay(
      loadConfig({
        host: "127.0.0.1",
        port: 0,
        tls: { cert, key },
        origins: [TEST_ORIGIN],
        tokens: [{ name: "test", sha256: digestOf(TEST_TOKEN) }],
        allow: [{ host: "127.0.0.1", ports: [target.port] }],
      }),
      { log: () => {} },
    );
    try {
      expect(relay.url.startsWith("wss://")).toBe(true);
      class TlsPageSocket extends WebSocket {
        constructor(url: string) {
          super(url, { headers: { Origin: TEST_ORIGIN }, tls: { ca: readFileSync(cert) } } as any);
        }
      }
      const net = new RelayTcp(relay.url, TlsPageSocket as any);
      await net.open(TEST_TOKEN);
      const id = await net.connect("127.0.0.1", target.port);
      await net.send(id, new TextEncoder().encode("over tls"));
      expect(new TextDecoder().decode(await net.recv(id, 100))).toBe("over tls");
      net.shutdown();
    } finally {
      relay.stop();
      target.stop();
    }
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}, 60000);

test("GET /healthz answers ok, and nothing else answers as a relay", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }]);
  try {
    const health = await fetch(`http://127.0.0.1:${r.port}/healthz`);
    expect(health.status).toBe(200);
    expect(await health.text()).toBe("ok\n");
    const other = await fetch(`http://127.0.0.1:${r.port}/`);
    expect(other.status).toBe(426);
  } finally {
    r.stop();
  }
});

test("a page may open at most connectsPerSecond (with a burst of twice that) connections a second", async () => {
  const target = echo();
  const r = testRelay([{ host: "127.0.0.1", ports: [target.port] }], { connectsPerSecond: 1 });
  try {
    const { ws, next } = await rawSocket(r.url);
    for (let id = 1; id <= 3; id++) ws.send(encodeFrame(OP.CONNECT, id, connectBody(target.port)));
    const replies: number[] = [];
    for (let i = 0; i < 3; i++) {
      const f = decodeFrame(await next())!;
      replies.push(f.op === OP.FAIL ? (f.body[0] << 8) | f.body[1] : f.op);
    }
    // two connects within the burst are OK; the third waits for the rate, and fails with EAGAIN
    expect(replies.filter((x) => x === OP.OK).length).toBe(2);
    expect(replies.filter((x) => x === 11).length).toBe(1);
    ws.close();
  } finally {
    r.stop();
    target.stop();
  }
});

test("the connections of the whole relay are capped, across pages", async () => {
  const target = echo();
  const r = testRelay([{ host: "127.0.0.1", ports: [target.port] }], { maxConnectionsTotal: 2 });
  try {
    const a = await rawSocket(r.url);
    const b = await rawSocket(r.url);
    a.ws.send(encodeFrame(OP.CONNECT, 1, connectBody(target.port)));
    b.ws.send(encodeFrame(OP.CONNECT, 1, connectBody(target.port)));
    expect(decodeFrame(await a.next())?.op).toBe(OP.OK);
    expect(decodeFrame(await b.next())?.op).toBe(OP.OK);
    a.ws.send(encodeFrame(OP.CONNECT, 2, connectBody(target.port)));
    const f = decodeFrame(await a.next())!;
    expect(f.op).toBe(OP.FAIL);
    expect((f.body[0] << 8) | f.body[1]).toBe(24);
    a.ws.close();
    b.ws.close();
  } finally {
    r.stop();
    target.stop();
  }
});

test("the sessions are capped: a page past the limit is refused", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }], { maxSessions: 1 });
  try {
    const first = await rawSocket(r.url);
    expect(await outcome(new PageSocket(r.url))).toBe("refused");
    first.ws.close();
  } finally {
    r.stop();
  }
});

test("a client address may open a limited number of WebSockets a minute", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }], { upgradesPerMinute: 2 });
  try {
    const a = await rawSocket(r.url);
    const b = await rawSocket(r.url);
    expect(await outcome(new PageSocket(r.url))).toBe("refused");
    a.ws.close();
    b.ws.close();
  } finally {
    r.stop();
  }
});

test("the bytes a page may move are limited to bytesPerSecond, each way together", async () => {
  const target = echo();
  const size = 1024 * 1024;
  const rate = 512 * 1024;
  const r = testRelay([{ host: "127.0.0.1", ports: [target.port] }], { bytesPerSecond: rate });
  try {
    const net = new RelayTcp(r.url, PageSocket);
    await net.open(TEST_TOKEN);
    const id = await net.connect("127.0.0.1", target.port);
    const data = new Uint8Array(size).fill(7);
    const started = Date.now();
    const sending = net.send(id, data);
    let got = 0;
    while (got < size) {
      const chunk = await net.recv(id, 65536);
      if (chunk === null) break;
      got += chunk.length;
    }
    await sending;
    const took = Date.now() - started;
    expect(got).toBe(size);
    // 2 MiB moved in all, with one second's worth allowed up front: at least 3 s at 512 KiB a second
    expect(took).toBeGreaterThanOrEqual(2500);
    net.shutdown();
  } finally {
    r.stop();
    target.stop();
  }
}, 60000);

test("stop() closes every WebSocket going away, and then stops listening", async () => {
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }]);
  const a = await rawSocket(r.url);
  r.stop();
  expect(await a.closed).toBe(1001);
  await sleep(50);
  expect(await outcome(new PageSocket(r.url))).toBe("refused");
});

test("the log names what happened and never carries a token", async () => {
  const lines: { event: string; fields: Record<string, unknown> }[] = [];
  const log: Log = (event, fields) => lines.push({ event, fields });
  const r = testRelay([{ host: "127.0.0.1", ports: [80] }], {}, {}, { log });
  try {
    const a = await rawSocket(r.url);
    const bad = new PageSocket(r.url);
    bad.binaryType = "arraybuffer";
    await new Promise((res) => (bad.onopen = res));
    bad.send(authFrame("wrong"));
    await sleep(100);
    a.ws.close();
    await sleep(100);
    const events = lines.map((l) => l.event);
    expect(events).toContain("auth_ok");
    expect(events).toContain("auth_fail");
    expect(events).toContain("session_close");
    expect(JSON.stringify(lines)).not.toContain(TEST_TOKEN);
    expect(JSON.stringify(lines)).not.toContain("wrong");
  } finally {
    r.stop();
  }
});
