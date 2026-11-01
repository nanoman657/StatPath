// Conformance of the relay to its Lean model (Relay.lean, in this folder).
//
// Random traces of page frames and socket events are run twice: through the relay, and through the model
// (`lean --run`). The relay's TCP connections are scripted: the test calls the handlers the relay gave to
// Bun.connect, so the order of events is the trace's order. After each step a sentinel (a CONNECT to a
// destination that is not allowed, answered with FAIL 13) shows that the relay has done with the step, so the
// frames the page receives can be compared, line for line, with the model's output for the same trace.
//
// The traces include the bugs this checks for: CLOSE and then reuse of the id, with a late event of the old
// socket; FAIL and reuse; events of a socket that the page has closed; the count limit (a small cap in some
// traces); and protocol violations (the relay closes the WebSocket, and the model says so).
//
// Needs the Lean 4.34.0 toolchain (LEAN, or the elan toolchain). Skipped without it.
import { test, expect } from "bun:test";
import { existsSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { encodeFrame, decodeFrame, OP, MAX_BODY } from "../../tcp_relay_client.js";
import { testRelay, PageSocket, TEST_TOKEN } from "../../test/support.ts";

const here = dirname(fileURLToPath(import.meta.url));
const MODEL = join(here, "Relay.lean");
const PINNED_LEAN = join(homedir(), ".elan", "toolchains", "leanprover--lean4---v4.34.0", "bin", "lean");
const LEAN = [process.env.LEAN, PINNED_LEAN, Bun.which("lean")].find((c) => c && existsSync(c)) ?? null;

const PORT = 4242; // the allowed destination's port
const ALLOWED = "127.0.0.1";
const DENIED = "10.0.0.1"; // not on the allow list: a CONNECT to it is answered with FAIL 13
const SENTINEL = 250; // an id no trace uses, for the CONNECT that marks the end of a step
const TRACES = Number(process.env.RELAY_TRACES ?? 300);
const STEPS = 60; // operations per trace (a choice that does nothing is not counted)

const enc = new TextEncoder();

// ---- the traces ----

function prng(seed: number) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function connectBody(port: number, host: string): Uint8Array {
  const text = enc.encode(host);
  const body = new Uint8Array(2 + text.length);
  body[0] = port >> 8;
  body[1] = port & 255;
  body.set(text, 2);
  return body;
}

function u32(n: number): Uint8Array {
  return new Uint8Array([(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
}

// one step of a trace: a page frame, or an event of a scripted socket
type Op =
  | { kind: "tick"; line: string; ms: number } // the clock goes on by ms, and the relay's timer runs once
  | { kind: "page"; line: string; frame: Uint8Array }
  | { kind: "sock"; line: string; id: number; gen: number; ev: "open" | "data" | "eof" | "peerclose" | "error" | "drain"; arg: number };

interface Trace {
  cap: number | null;
  cps: number; // connects per second: a low rate makes the connect tokens run out
  ops: Op[];
  stale: number; // socket events of a connection the page has closed, or of an id it has reused
}

// The errors a socket can report: each maps to the errno the model is given (see errnoOf in relay.ts)
const ERRORS = [111, 104, 110, 5];
const CODE_OF: Record<number, string> = { 111: "ECONNREFUSED", 104: "ECONNRESET", 110: "ETIMEDOUT", 5: "" };

// A trace as the page would plausibly send it, with some that it should not: the page believes what it has
// done, not what the relay has answered, so a socket can be reported after its id was freed, and a
// connection can be used after it failed.
function genTrace(seed: number): Trace {
  const r = prng(seed);
  const int = (n: number) => Math.floor(r() * n);
  const cap = r() < 0.4 ? 300 + int(1200) : null; // small enough for the traces to reach it
  // a low rate (two connects a second) makes the connect tokens run out; the clock steps are then multiples of
  // half a second, which keeps the relay's arithmetic exact
  const cps = r() < 0.5 ? 2 : 100000;
  const ops: Op[] = [];
  const alive = new Map<number, number>(); // id -> the generation the page believes is in use
  const opened = new Map<number, boolean>(); // generation -> the socket has opened
  const genId = new Map<number, number>(); // generation -> its id
  const gens: number[] = [];
  let next = 0;
  let stale = 0;
  const isStale = (g: number) => alive.get(genId.get(g)!) !== g;
  for (let i = 0; ops.length < STEPS && i < 20 * STEPS; i++) {
    const id = 1 + int(3);
    // a low rate: connect and close churn, so the tokens run out (the connects are what they take)
    if (cps === 2 && r() < 0.35) {
      if (!alive.has(id)) {
        next++;
        alive.set(id, next);
        opened.set(next, false);
        genId.set(next, id);
        gens.push(next);
        ops.push({ kind: "page", line: `connect ${id}`, frame: encodeFrame(OP.CONNECT, id, connectBody(PORT, ALLOWED)) });
      } else {
        const g = alive.get(id)!;
        alive.delete(id);
        ops.push({ kind: "page", line: `close ${id}`, frame: encodeFrame(OP.CLOSE, id) });
      }
      continue;
    }
    const x = r();
    if (x < 0.05 && cps !== 2) {
      const ms = 500 * (1 + int(3));
      ops.push({ kind: "tick", line: `tick ${ms}`, ms });
      continue;
    }
    const anyGen = gens.length > 0 ? gens[int(gens.length)] : 0;
    const openGens = gens.filter((g) => opened.get(g));
    if (x < 0.1) {
      if (!alive.has(id)) {
        next++;
        alive.set(id, next);
        opened.set(next, false);
        genId.set(next, id);
        gens.push(next);
        ops.push({ kind: "page", line: `connect ${id}`, frame: encodeFrame(OP.CONNECT, id, connectBody(PORT, ALLOWED)) });
      }
    } else if (x < 0.12) {
      if (!alive.has(id)) ops.push({ kind: "page", line: `deny ${id}`, frame: encodeFrame(OP.CONNECT, id, connectBody(PORT, DENIED)) });
    } else if (x < 0.22) {
      const cands = [...alive.values()].filter((g) => !opened.get(g));
      if (cands.length > 0) {
        const g = cands[int(cands.length)];
        opened.set(g, true);
        ops.push({ kind: "sock", line: `sock ${genId.get(g)} ${g} open`, id: genId.get(g)!, gen: g, ev: "open", arg: 0 });
      }
    } else if (x < 0.34) {
      const id2 = 1 + int(3);
      const g = alive.get(id2);
      if (g !== undefined && opened.get(g)) {
        const n = 1 + int(1500);
        ops.push({ kind: "page", line: `send ${id2} ${n}`, frame: encodeFrame(OP.SEND, id2, new Uint8Array(n).fill(7)) });
      } else if (r() < 0.2) {
        // a violation: a SEND before OK, or to an id that is not in use
        const n = 1 + int(50);
        ops.push({ kind: "page", line: `send ${id2} ${n}`, frame: encodeFrame(OP.SEND, id2, new Uint8Array(n).fill(7)) });
      }
    } else if (x < 0.42) {
      if (openGens.length > 0) {
        const g = openGens[int(openGens.length)];
        const n = 1 + int(1500);
        if (isStale(g)) stale++;
        ops.push({ kind: "sock", line: `sock ${genId.get(g)} ${g} data ${n}`, id: genId.get(g)!, gen: g, ev: "data", arg: n });
      }
    } else if (x < 0.5) {
      if (openGens.length > 0) {
        const g = openGens[int(openGens.length)];
        const a = int(2000);
        if (isStale(g)) stale++;
        ops.push({ kind: "sock", line: `sock ${genId.get(g)} ${g} drain ${a}`, id: genId.get(g)!, gen: g, ev: "drain", arg: a });
      }
    } else if (x < 0.56) {
      if (anyGen) {
        if (isStale(anyGen)) stale++;
        ops.push({ kind: "sock", line: `sock ${genId.get(anyGen)} ${anyGen} eof`, id: genId.get(anyGen)!, gen: anyGen, ev: "eof", arg: 0 });
      }
    } else if (x < 0.6) {
      if (anyGen) {
        if (isStale(anyGen)) stale++;
        ops.push({ kind: "sock", line: `sock ${genId.get(anyGen)} ${anyGen} peerclose`, id: genId.get(anyGen)!, gen: anyGen, ev: "peerclose", arg: 0 });
      }
    } else if (x < 0.66) {
      if (anyGen) {
        const e = ERRORS[int(ERRORS.length)];
        if (isStale(anyGen)) stale++;
        ops.push({ kind: "sock", line: `sock ${genId.get(anyGen)} ${anyGen} error ${e}`, id: genId.get(anyGen)!, gen: anyGen, ev: "error", arg: e });
      }
    } else if (x < 0.72) {
      const k = [131072, 131072, 4096, 1024][int(4)];
      if (alive.get(id) !== undefined && opened.get(alive.get(id)!)) {
        ops.push({ kind: "page", line: `read ${id} ${k}`, frame: encodeFrame(OP.READ, id, u32(k)) });
      }
    } else if (x < 0.76) {
      if (alive.get(id) !== undefined && opened.get(alive.get(id)!) && r() < 0.5) {
        ops.push({ kind: "page", line: `discard ${id}`, frame: encodeFrame(OP.DISCARD, id) });
      }
    } else if (x < 0.82) {
      if (alive.has(id)) {
        alive.delete(id);
        ops.push({ kind: "page", line: `close ${id}`, frame: encodeFrame(OP.CLOSE, id) });
      }
    } else if (x < 0.86) {
      // a page frame for an id that was never used
      ops.push({ kind: "page", line: `close ${id}`, frame: encodeFrame(OP.CLOSE, id) });
    }
  }
  return { cap, cps, ops, stale };
}

// ---- the model ----

// the trace as the model reads it: "trace", the cap, the events; a sentinel follows every step
function modelInput(traces: Trace[]): string {
  const out: string[] = [];
  for (const t of traces) {
    out.push("trace");
    out.push(`rate ${t.cps}`);
    if (t.cap !== null) out.push(`cap ${t.cap}`);
    for (const op of t.ops) {
      out.push(op.line);
      out.push(`deny ${SENTINEL}`);
    }
  }
  return out.join("\n") + "\n";
}

async function leanOutputs(input: string): Promise<string[][]> {
  const proc = Bun.spawn([LEAN!, "--run", MODEL], { stdin: new Blob([input]), stdout: "pipe", stderr: "pipe" });
  const [out, err, code] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
    proc.exited,
  ]);
  if (code !== 0) throw new Error(`lean --run failed (${code}): ${err}`);
  const traces: string[][] = [];
  let cur: string[] = [];
  for (const line of out.split("\n")) {
    if (line === "") continue;
    if (line === "end") {
      traces.push(cur);
      cur = [];
    } else cur.push(line);
  }
  return traces;
}

// ---- the relay ----

// a socket as the relay gave it to Bun.connect: its handlers, and the object the handlers get
interface Scripted {
  handlers: any;
  tcp: { accept: number; write(b: Uint8Array): number; end(): void; pause(): void; resume(): void };
  opened: boolean;
}

function lineOf(f: { op: number; id: number; body: Uint8Array }): string {
  switch (f.op) {
    case OP.OK:
      return `ok ${f.id}`;
    case OP.DATA:
      return `data ${f.id} ${f.body.length}`;
    case OP.EOF:
      return `eof ${f.id}`;
    case OP.WRITTEN: {
      const count = f.body[0] * 2 ** 24 + (f.body[1] << 16) + (f.body[2] << 8) + f.body[3];
      return `written ${f.id} ${count} ${f.body[4]}`;
    }
    case OP.FAIL:
      return `fail ${f.id} ${(f.body[0] << 8) | f.body[1]}`;
    case OP.CLOSED:
      return `closed ${f.id}`;
    default:
      return `unknown ${f.op}`;
  }
}

// The page: a WebSocket that logs the frames it receives, in order, and the close code
class PageLog {
  lines: string[] = [];
  closed: number | null = null;
  authed = false;
  ws: PageSocket;
  constructor(url: string) {
    this.ws = new PageSocket(url);
    this.ws.binaryType = "arraybuffer";
    this.ws.onmessage = (e: MessageEvent) => {
      const f = decodeFrame(new Uint8Array(e.data as ArrayBuffer));
      if (!f) return;
      if (!this.authed) {
        this.authed = f.op === OP.AUTHOK;
        return;
      }
      this.lines.push(lineOf(f));
    };
    this.ws.onclose = (e: CloseEvent) => {
      this.closed = e.code;
    };
  }
  async open(token: string) {
    await new Promise<void>((res) => (this.ws.onopen = () => res()));
    this.ws.send(encodeFrame(OP.AUTH, 0, enc.encode(token)));
    await until(() => this.authed || this.closed !== null, 5000);
    if (!this.authed) throw new Error("the relay did not accept the token");
  }
  // waits until the sentinel's answer has arrived for the n-th step, or the relay has closed the WebSocket
  async settle(n: number) {
    await until(() => this.closed !== null || this.lines.filter((l) => l === `fail ${SENTINEL} 13`).length >= n, 5000);
  }
}

async function until(cond: () => boolean, ms: number) {
  const end = Date.now() + ms;
  while (!cond() && Date.now() < end) await new Promise((r) => setTimeout(r, 0));
}

// the relay's frames for one trace, run through the relay with scripted sockets
async function relayOutputs(t: Trace): Promise<string[]> {
  const sockets: Scripted[] = [];
  const connect = (o: any) => {
    const sock: Scripted = {
      handlers: o.socket,
      tcp: {
        accept: Infinity,
        write(b: Uint8Array) {
          const n = Math.min(b.length, this.accept);
          this.accept -= n;
          return n;
        },
        end() {},
        pause() {},
        resume() {},
      },
      opened: false,
    };
    sockets.push(sock);
    return Promise.resolve(undefined);
  };
  const cfg = {
    connectsPerSecond: 100000,
    bytesPerSecond: 1e9,
    maxConnections: 1000,
    maxConnectionsTotal: 100000,
    maxBufferedBytes: 1e9,
    upgradesPerMinute: 100000,
  };
  let clockNow = 0;
  const relay = testRelay(
    [{ host: ALLOWED, ports: [PORT] }],
    { ...cfg, connectsPerSecond: t.cps },
    {},
    { log: () => {}, maxCount: t.cap ?? undefined, connect, ticker: false, now: () => clockNow },
  );
  try {
    const page = new PageLog(relay.url);
    await page.open(TEST_TOKEN);
    let step = 0;
    for (const op of t.ops) {
      if (page.closed !== null) break; // the relay closed the WebSocket: nothing more is sent
      if (op.kind === "tick") {
        clockNow += op.ms;
        relay.tick();
      } else if (op.kind === "page") {
        page.ws.send(op.frame);
      } else {
        const s = sockets[op.gen - 1];
        if (s) {
          if (op.ev === "open") {
            s.opened = true;
            s.handlers.open(s.tcp);
          } else if (op.ev === "data") {
            s.handlers.data(s.tcp, new Uint8Array(op.arg));
          } else if (op.ev === "eof") {
            s.handlers.end(s.tcp);
          } else if (op.ev === "peerclose") {
            s.handlers.close(s.tcp);
          } else if (op.ev === "error") {
            const err = { code: CODE_OF[op.arg] ?? "" };
            // an unopened socket reports through connectError, as Bun does
            if (s.opened) s.handlers.error(s.tcp, err);
            else s.handlers.connectError(s.tcp, err);
          } else {
            s.tcp.accept = op.arg;
            s.handlers.drain(s.tcp);
            s.tcp.accept = Infinity;
          }
        }
      }
      step++;
      page.ws.send(encodeFrame(OP.CONNECT, SENTINEL, connectBody(PORT, DENIED)));
      await page.settle(step);
    }
    const lines = [...page.lines];
    if (page.closed !== null) lines.push(`wsclose ${page.closed}`);
    return lines;
  } finally {
    relay.stop();
  }
}

// ---- the test ----

test.skipIf(LEAN === null)(
  "the relay sends the frames the model says, on random traces, for every step",
  async () => {
    const traces: Trace[] = [];
    for (let seed = 1; seed <= TRACES; seed++) traces.push(genTrace(seed));
    const expected = await leanOutputs(modelInput(traces));
    expect(expected.length).toBe(traces.length);

    let frames = 0;
    let closes = 0;
    const kinds = new Map<string, number>();
    for (const e of expected) {
      for (const l of e) {
        const parts = l.split(" ");
        const key = parts[0] === "fail" ? `fail ${parts[2]}` : parts[0] === "written" ? `written ${parts[3]}` : parts[0];
        kinds.set(key, (kinds.get(key) ?? 0) + 1);
      }
    }
    const want = ["ok", "data", "eof", "written 0", "written 1", "fail 5", "fail 13", "fail 27", "fail 32", "fail 111", "fail 11", "closed", "wsclose"];
    for (const k of want) expect(kinds.get(k) ?? 0, `frames of kind ${k}`).toBeGreaterThan(0);
    const staleOps = traces.reduce((n, t) => n + t.stale, 0);
    expect(staleOps).toBeGreaterThan(0);
    for (let i = 0; i < traces.length; i++) {
      const actual = await relayOutputs(traces[i]);
      frames += actual.length;
      if (actual.some((l) => l.startsWith("wsclose"))) closes++;
      if (JSON.stringify(actual) !== JSON.stringify(expected[i])) {
        // the first line that differs, for the report
        let at = 0;
        while (at < actual.length && at < expected[i].length && actual[at] === expected[i][at]) at++;
        throw new Error(
          `trace ${i + 1} differs at frame ${at}: relay ${JSON.stringify(actual.slice(at, at + 3))}, ` +
            `model ${JSON.stringify(expected[i].slice(at, at + 3))}`,
        );
      }
    }
    const tally = [...kinds].sort().map(([k, n]) => `${k}:${n}`).join(" ");
    console.log(
      `relay conformance: ${traces.length} traces, ${frames} frames, ${closes} sessions closed by a violation, ` +
        `${staleOps} socket events of a closed or reused connection\n  frames: ${tally}`,
    );
  },
  600_000,
);

// ---- every trace up to a length, over a small alphabet: the bounded exhaustive check ----
// The alphabet: the page's calls on id 1, and the events of the sockets of its first two connections (the
// second reuses the id after a CLOSE). With RELAY_EXHAUSTIVE=n the test runs every trace of up to n steps.
const EXHAUSTIVE = Number(process.env.RELAY_EXHAUSTIVE ?? 0);

const ALPHABET: Op[] = [
  { kind: "page", line: "connect 1", frame: encodeFrame(OP.CONNECT, 1, connectBody(PORT, ALLOWED)) },
  { kind: "page", line: "close 1", frame: encodeFrame(OP.CLOSE, 1) },
  { kind: "page", line: "send 1 2", frame: encodeFrame(OP.SEND, 1, new Uint8Array(2).fill(7)) },
  { kind: "page", line: "read 1 131072", frame: encodeFrame(OP.READ, 1, u32(131072)) },
  { kind: "page", line: "discard 1", frame: encodeFrame(OP.DISCARD, 1) },
  { kind: "sock", line: "sock 1 1 open", id: 1, gen: 1, ev: "open", arg: 0 },
  { kind: "sock", line: "sock 1 2 open", id: 1, gen: 2, ev: "open", arg: 0 },
  { kind: "sock", line: "sock 1 1 data 2", id: 1, gen: 1, ev: "data", arg: 2 },
  { kind: "sock", line: "sock 1 2 data 2", id: 1, gen: 2, ev: "data", arg: 2 },
  { kind: "sock", line: "sock 1 1 eof", id: 1, gen: 1, ev: "eof", arg: 0 },
  { kind: "sock", line: "sock 1 1 peerclose", id: 1, gen: 1, ev: "peerclose", arg: 0 },
  { kind: "sock", line: "sock 1 1 error 111", id: 1, gen: 1, ev: "error", arg: 111 },
  { kind: "sock", line: "sock 1 2 error 111", id: 1, gen: 2, ev: "error", arg: 111 },
  { kind: "sock", line: "sock 1 1 drain 1", id: 1, gen: 1, ev: "drain", arg: 1 },
];

// every sequence of up to maxLen letters
function allTraces(maxLen: number): Trace[] {
  const out: Trace[] = [];
  const walk = (prefix: Op[]) => {
    out.push({ cap: null, cps: 100000, ops: prefix, stale: 0 });
    if (prefix.length === maxLen) return;
    for (const letter of ALPHABET) walk([...prefix, letter]);
  };
  walk([]);
  return out;
}

// the same relay for all the traces: each trace is a session of its own, and its sockets are its own
async function relayOutputsShared(t: Trace, shared: { sockets: Scripted[]; url: string }): Promise<string[]> {
  shared.sockets.length = 0;
  const page = new PageLog(shared.url);
  try {
    await page.open(TEST_TOKEN);
    let step = 0;
    for (const op of t.ops) {
      if (page.closed !== null) break;
      if (op.kind === "page") page.ws.send(op.frame);
      else {
        const s = shared.sockets[op.gen - 1];
        if (s) {
          if (op.ev === "open") {
            s.opened = true;
            s.handlers.open(s.tcp);
          } else if (op.ev === "data") s.handlers.data(s.tcp, new Uint8Array(op.arg));
          else if (op.ev === "eof") s.handlers.end(s.tcp);
          else if (op.ev === "peerclose") s.handlers.close(s.tcp);
          else if (op.ev === "error") {
            const err = { code: CODE_OF[op.arg] ?? "" };
            if (s.opened) s.handlers.error(s.tcp, err);
            else s.handlers.connectError(s.tcp, err);
          } else {
            s.tcp.accept = op.arg;
            s.handlers.drain(s.tcp);
            s.tcp.accept = Infinity;
          }
        }
      }
      step++;
      page.ws.send(encodeFrame(OP.CONNECT, SENTINEL, connectBody(PORT, DENIED)));
      await page.settle(step);
    }
    const lines = [...page.lines];
    if (page.closed !== null) lines.push(`wsclose ${page.closed}`);
    return lines;
  } finally {
    page.ws.close();
  }
}

test.skipIf(LEAN === null || EXHAUSTIVE === 0)(
  `the relay matches the model on every trace of up to ${EXHAUSTIVE || "n"} steps over the alphabet`,
  async () => {
    const traces = allTraces(EXHAUSTIVE);
    const expected = await leanOutputs(modelInput(traces));
    expect(expected.length).toBe(traces.length);
    // one relay for all of them; its connect adds to the sockets of the trace that runs now
    const shared: { sockets: Scripted[]; url: string } = { sockets: [], url: "" };
    const connect = (o: any) => {
      shared.sockets.push({
        handlers: o.socket,
        tcp: {
          accept: Infinity,
          write(b: Uint8Array) {
            const n = Math.min(b.length, this.accept);
            this.accept -= n;
            return n;
          },
          end() {},
          pause() {},
          resume() {},
        },
        opened: false,
      });
      return Promise.resolve(undefined);
    };
    const relay = testRelay(
      [{ host: ALLOWED, ports: [PORT] }],
      {
        connectsPerSecond: 100000,
        bytesPerSecond: 1e9,
        maxConnections: 1000,
        maxConnectionsTotal: 100000,
        maxBufferedBytes: 1e9,
        upgradesPerMinute: 1000000,
      },
      {},
      { log: () => {}, connect, ticker: false },
    );
    shared.url = relay.url;
    try {
      for (let i = 0; i < traces.length; i++) {
        const actual = await relayOutputsShared(traces[i], shared);
        if (JSON.stringify(actual) !== JSON.stringify(expected[i])) {
          throw new Error(
            `trace ${i + 1} (${traces[i].ops.map((o) => o.line).join(" | ")}) differs: ` +
              `relay ${JSON.stringify(actual)}, model ${JSON.stringify(expected[i])}`,
          );
        }
      }
      console.log(`relay exhaustive: all ${traces.length} traces of up to ${EXHAUSTIVE} steps over ${ALPHABET.length} letters`);
    } finally {
      relay.stop();
    }
  },
  6 * 3600 * 1000,
);
