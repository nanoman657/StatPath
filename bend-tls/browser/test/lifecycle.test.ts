// The lifecycle of a connection id (PROTOCOL.md: an id is used from CONNECT until CLOSE or FAIL, then
// free). The relay's callbacks for a socket must not act on a later connection that reuses its id.
import { test, expect } from "bun:test";
import { encodeFrame, decodeFrame, OP } from "../tcp_relay_client.js";
import { testRelay, TEST_TOKEN, rawSocket } from "./support.ts";
import { createServer } from "node:net";

const enc = new TextEncoder();

function connectBody(port: number, host: string) {
  const text = enc.encode(host);
  const body = new Uint8Array(2 + text.length);
  body[0] = port >> 8;
  body[1] = port & 255;
  body.set(text, 2);
  return body;
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

// a port that nothing listens on: a connect to it is refused
async function refusedPort(): Promise<number> {
  const s = createServer();
  await new Promise<void>((res) => s.listen(0, "127.0.0.1", () => res()));
  const port = (s.address() as { port: number }).port;
  await new Promise<void>((res) => s.close(() => res()));
  return port;
}

test("a connect that fails after its id was closed and reused does not fail the new connection", async () => {
  const dead = await refusedPort();
  const other = echo();
  const r = testRelay([{ host: "127.0.0.1", ports: [dead, other.port] }]);
  const { ws, next } = await rawSocket(r.url);
  // the first connect is refused, but the page closes its id before the refusal arrives and reuses it
  ws.send(encodeFrame(OP.CONNECT, 1, connectBody(dead, "127.0.0.1")));
  ws.send(encodeFrame(OP.CLOSE, 1));
  ws.send(encodeFrame(OP.CONNECT, 1, connectBody(other.port, "127.0.0.1")));
  // the second connection must be OK; nothing for the first may reach the page after its CLOSE
  const first = decodeFrame(await next());
  expect(first?.op).toBe(OP.OK);
  expect(first?.id).toBe(1);
  // and the connection really works
  ws.send(encodeFrame(OP.READ, 1, new Uint8Array([0, 2, 0, 0])));
  ws.send(encodeFrame(OP.SEND, 1, enc.encode("hi")));
  const got = decodeFrame(await next());
  expect(got?.op).toBe(OP.WRITTEN);
  ws.close();
  r.stop();
  other.stop();
});
