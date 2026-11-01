// What the relay tests share: a token and an origin the relay accepts, a WebSocket that presents
// the origin (a page's browser does that itself), and a relay built from a configuration that went
// through the same validation a real one does.
import { startRelay, type Log } from "../relay/relay.ts";
import { loadConfig, type Allow, type Config } from "../relay/config.ts";
import { digestOf } from "../relay/token.ts";
import { encodeFrame, OP } from "../tcp_relay_client.js";

export const TEST_TOKEN = "test-token-for-the-browser-tests";
export const TEST_ORIGIN = "https://page.test";

const enc = new TextEncoder();

// A WebSocket that presents the test origin, as a page's browser does.
export class PageSocket extends WebSocket {
  constructor(url: string) {
    super(url, { headers: { Origin: TEST_ORIGIN } } as any);
  }
}

// The AUTH frame a client sends first. The relay answers AUTHOK when it accepts the token.
export function authFrame(token = TEST_TOKEN): Uint8Array {
  return encodeFrame(OP.AUTH, 0, enc.encode(token));
}

// A configuration for tests: the test token and origin, the given destinations and limits.
export function testConfig(
  allow: Allow[],
  limits: Record<string, number> = {},
  extra: Record<string, unknown> = {},
): Config {
  return loadConfig({
    host: "127.0.0.1",
    port: 0,
    origins: [TEST_ORIGIN],
    tokens: [{ name: "test", sha256: digestOf(TEST_TOKEN) }],
    allow,
    limits,
    ...extra,
  });
}

// A relay on a free port. Its url is the one a page would use.
export function testRelay(
  allow: Allow[],
  limits: Record<string, number> = {},
  extra: Record<string, unknown> = {},
  opts: Parameters<typeof startRelay>[1] = {},
) {
  const server = startRelay(testConfig(allow, limits, extra), opts);
  return { url: server.url, port: server.port, stop: () => server.stop() };
}

// A raw WebSocket to the relay, authenticated: resolves once AUTHOK has arrived. Its messages are
// queued in order, and next() takes the next one. closed resolves to the close code.
export async function rawSocket(url: string, token = TEST_TOKEN) {
  const ws = new PageSocket(url);
  ws.binaryType = "arraybuffer";
  const queue: Uint8Array[] = [];
  const waiters: ((m: Uint8Array) => void)[] = [];
  ws.onmessage = (e) => {
    const m = new Uint8Array(e.data as ArrayBuffer);
    const w = waiters.shift();
    if (w) w(m);
    else queue.push(m);
  };
  const next = () =>
    new Promise<Uint8Array>((res) => {
      const m = queue.shift();
      if (m) res(m);
      else waiters.push(res);
    });
  const closed = new Promise<number>((res) => (ws.onclose = (e) => res(e.code)));
  await new Promise((res) => (ws.onopen = res));
  ws.send(authFrame(token));
  const answer = await next();
  if (answer[0] !== OP.AUTHOK) throw new Error("the relay did not accept the token");
  return { ws, next, closed };
}

// the connect body: the port, then the host, as the page sends it
export function connectBody(port: number, host = "127.0.0.1"): Uint8Array {
  const text = enc.encode(host);
  const body = new Uint8Array(2 + text.length);
  body[0] = port >> 8;
  body[1] = port & 255;
  body.set(text, 2);
  return body;
}
