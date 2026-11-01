// The socket behaviours the relay's model assumes of Bun (README, "The code, proven against its model", the
// assumptions 1 to 4). Each is checked here against real sockets, so that a change in Bun shows here first.
//   1. write takes at most the bytes it is given, and keeps none of the rest: the relay queues the rest itself.
//   2. drain comes after a partial write, when the socket can take more.
//   3. pause stops the socket's data callbacks; resume starts them again.
//   4. the data of a connection comes before its end.
import { test, expect } from "bun:test";

const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
const MB = 1024 * 1024;

// a listener that reads nothing until told to: its socket is paused on accept
function quietServer(pauseFirst: boolean) {
  const got = { n: 0, socket: null as any };
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open(s) {
        got.socket = s;
        if (pauseFirst) s.pause();
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

test("1. a partial write keeps none of its remainder: the peer gets what write took, and no more", async () => {
  const peer = quietServer(true); // reads nothing: the socket buffers fill
  let took = -1;
  let offered = 0;
  const data = new Uint8Array(32 * MB).fill(1);
  const client = await Bun.connect({
    hostname: "127.0.0.1",
    port: peer.port,
    socket: {
      open(s) {
        took = s.write(data);
        offered = data.length;
      },
      data() {},
      close() {},
      error() {},
    },
  });
  await sleep(300);
  expect(took).toBeGreaterThan(0);
  expect(took).toBeLessThan(offered); // the socket did not take everything
  // now the peer reads: it must get what write took, and nothing else (the rest was not sent behind the
  // caller's back). Wait until the peer's count stops growing.
  peer.got.socket.resume();
  let last = -1;
  let quiet = 0;
  const until = Date.now() + 10000;
  while (quiet < 10 && Date.now() < until) {
    await sleep(50);
    if (peer.got.n === last) quiet++;
    else {
      quiet = 0;
      last = peer.got.n;
    }
  }
  expect(peer.got.n).toBe(took);
  client.end();
  peer.stop();
});

test("2. drain comes after a partial write, once the socket can take more", async () => {
  const peer = quietServer(true);
  const data = new Uint8Array(32 * MB).fill(2);
  let drained = 0;
  let offset = 0;
  let total = 0;
  const pump = (s: any) => {
    while (offset < data.length) {
      const n = s.write(data.subarray(offset));
      if (n <= 0) return;
      offset += n;
    }
  };
  const client = await Bun.connect({
    hostname: "127.0.0.1",
    port: peer.port,
    socket: {
      open: pump,
      drain(s) {
        drained++;
        pump(s);
      },
      data() {},
      close() {},
      error() {},
    },
  });
  total = 0;
  await sleep(200);
  expect(offset).toBeLessThan(data.length); // the first writes were partial
  // the peer starts reading: the socket drains, and the drain callback runs the rest
  peer.got.socket.resume();
  const until = Date.now() + 10000;
  while (peer.got.n < data.length && Date.now() < until) await sleep(20);
  expect(drained).toBeGreaterThan(0);
  expect(offset).toBe(data.length);
  expect(peer.got.n).toBe(data.length);
  client.end();
  peer.stop();
});

test("3. pause stops the data callbacks; resume starts them again", async () => {
  // the peer sends a lot, straight away, and writes the rest on drain (write keeps none of it: assumption 1);
  // the client pauses its socket as it opens
  const payload = new Uint8Array(4 * MB).fill(3);
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open(s) {
        let off = 0;
        const pump = () => {
          while (off < payload.length) {
            const n = s.write(payload.subarray(off));
            if (n <= 0) return;
            off += n;
          }
        };
        pump();
        (s as any).pumpMore = pump;
      },
      drain(s) {
        (s as any).pumpMore?.();
      },
      data() {},
      close() {},
      error() {},
    },
  });
  let got = 0;
  let paused = true;
  let during = 0;
  let clientSocket: any = null;
  const client = await Bun.connect({
    hostname: "127.0.0.1",
    port: server.port,
    socket: {
      open(s) {
        clientSocket = s;
        s.pause();
      },
      data(_s, d) {
        if (paused) during += d.length;
        got += d.length;
      },
      close() {},
      error() {},
    },
  });
  await sleep(400);
  expect(during).toBe(0); // nothing was delivered while paused
  paused = false;
  clientSocket.resume();
  const until = Date.now() + 10000;
  while (got < 4 * MB && Date.now() < until) await sleep(20);
  expect(got).toBe(4 * MB);
  client.end();
  server.stop(true);
});

test("4. the data of a connection comes before its end", async () => {
  const server = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: {
      open(s) {
        s.write(new Uint8Array(200000).fill(4));
        s.end();
      },
      data() {},
      close() {},
      error() {},
    },
  });
  const events: string[] = [];
  let bytes = 0;
  const client = await Bun.connect({
    hostname: "127.0.0.1",
    port: server.port,
    socket: {
      open() {},
      data(_s, d) {
        bytes += d.length;
        events.push("data");
      },
      end() {
        events.push(`end@${bytes}`);
      },
      close() {},
      error() {},
    },
  });
  const until = Date.now() + 5000;
  while (!events.some((e) => e.startsWith("end")) && Date.now() < until) await sleep(10);
  expect(events[events.length - 1]).toBe(`end@200000`); // every byte came before the end
  expect(bytes).toBe(200000);
  client.end();
  server.stop(true);
});
