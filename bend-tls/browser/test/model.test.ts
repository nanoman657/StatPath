// The proven model: the transitions (core/tcp_transitions.bend, compiled to core/tcp_transitions.mjs, which the
// code calls) and the lemmas about them (core/tcp_model.bend). Tested in three ways.
// 1. Its functions compute the arithmetic the code means, on random inputs (Nat subtraction truncates
//    at 0, as Math.max(0, a - b) does for the counts here).
// 2. Random protocol traces, run with the model's functions as the code runs them, keep every
//    invariant the lemmas prove, after every step. The window, the chunk and the read window are small,
//    so the boundary cases come up often.
import { test, expect } from "bun:test";
import { resolve } from "node:path";
import M from "../core/tcp_transitions.mjs";

const CORE = resolve(import.meta.dir, "../core");
const sub = (a: number, b: number) => Math.max(0, a - b);

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

test("the model's arithmetic is the intended arithmetic, on random inputs", () => {
  const r = prng(1);
  const int = (lo: number, hi: number) => lo + Math.floor(r() * (hi - lo + 1));
  for (let i = 0; i < 4000; i++) {
    const sent = int(0, 60), wp = int(0, 60), win = int(0, 60), tail = int(0, 80), mx = int(0, 30);
    expect(M.pg_frame_n(sent, wp, win, tail, mx)).toBe(Math.min(mx, sub(win, sub(sent, wp)), sub(tail, sent)));
    const taken = int(0, 60), recvd = int(0, 60);
    expect(M.pg_take_n(taken, recvd, mx)).toBe(Math.min(mx, sub(recvd, taken)));
    const q = int(0, 40), n = int(0, 40), win2 = int(0, 40);
    expect(M.rl_over(n, M.rl_room(win2, q)) === 0).toBe(n <= sub(win2, q));
    const rd = int(0, 60), gr = int(0, 60), w = int(0, 60), k = int(0, 40);
    expect(M.rl_grant(rd, gr, w, k)).toBe(Math.min(rd + w, gr + k));
    expect(M.rl_unqueue(q, n)).toBe(sub(q, n));
  }
});

// one random trace: the page and the relay, joined by two FIFO channels. Each step is one event of
// the model; the invariants are checked after each.
// rogue: the page may also send READs it has not earned (a page that over-asks). The relay's own
// invariants must still hold; the page's bounds, which assume an honest page, are then not checked.
function trace(seed: number, steps: number, WIN: number, MAX: number, C: number, rogue = false) {
  const r = prng(seed);
  const pick = (n: number) => Math.floor(r() * n);
  const s = {
    tail: 0, sent: 0, wp: 0, taken: 0, recvd: 0, // page
    wr: 0, q: 0, rd: 0, gr: 0, ti: 0,            // relay
    dp: false, opOpen: false, opEnd: 0,          // page: discard pending, a send in progress and where it ends
  };
  type Up = { t: "SEND"; n: number } | { t: "DISCARD" } | { t: "READ"; n: number };
  type Down = { t: "WRITTEN"; w: number; reply: boolean } | { t: "DATA"; k: number };
  const up: Up[] = [{ t: "READ", n: WIN }];   // the page's grant of the window, at OK
  const down: Down[] = [];
  const invariants = (where: string) => {
    const fail = (name: string) => { throw new Error(`${name} after ${where}: ${JSON.stringify(s)}`); };
    if (!(s.wp <= s.sent)) fail("wp <= sent");
    if (!(s.sent - s.wp <= WIN)) fail("page window: sent - wp <= WIN");
    if (!(s.sent <= s.tail)) fail("sent <= tail");
    if (!(s.taken <= s.recvd)) fail("taken <= recvd");
    if (!(s.recvd <= s.rd)) fail("recvd <= rd");
    if (!(s.wp <= s.wr)) fail("wp <= wr");
    if (!(s.wr + s.q <= s.sent)) fail("wr + q <= sent");
    if (!(s.q <= WIN)) fail("relay queue <= WIN");
    if (!(s.gr <= s.rd + WIN)) fail("credit <= WIN");
    if (!(s.rd <= s.gr + C)) fail("read <= grant + C");
    if (!(s.gr <= s.ti)) fail("grant <= applied");
    if (!rogue) {
      if (!(s.ti <= WIN + s.taken)) fail("applied <= issued");
      if (!(s.rd - s.taken <= WIN + C)) fail("held <= WIN + C");
    }
  };
  invariants("start");
  let fits = 0, discards = 0, reads = 0, writes = 0;
  for (let step = 0; step < steps; step++) {
    const choices: string[] = [];
    if (!s.opOpen) choices.push("start");
    if (!s.dp && s.opOpen && M.pg_frame_n(s.sent, s.wp, WIN, s.tail, MAX) > 0) choices.push("frame");
    if (!s.dp && s.opOpen) choices.push("discard");
    if (s.recvd > s.taken) choices.push("take");
    if (s.dp === false && s.taken < 1000) choices.push("grantless");  // placeholder, removed below
    choices.pop();
    if (down.length > 0) choices.push("deliver-down");
    if (up.length > 0) choices.push("deliver-up");
    if (s.q > 0) choices.push("write");
    if (s.rd <= s.gr && s.rd + C <= 10 ** 9) choices.push("read");
    if (rogue) choices.push("rogue");
    const act = choices[pick(choices.length)];
    const where = `${step}:${act}`;
    if (act === "start") {
      const len = 1 + pick(3 * WIN);
      s.tail = M.pg_start(s.tail, len);
      s.opEnd = s.tail;
      s.opOpen = true;
    } else if (act === "frame") {
      const n = M.pg_frame_n(s.sent, s.wp, WIN, s.tail, MAX);
      up.push({ t: "SEND", n });
      s.sent = M.pg_sent(s.sent, n);
    } else if (act === "discard") {
      up.push({ t: "DISCARD" });
      s.dp = true;
      discards++;
    } else if (act === "take") {
      const n = M.pg_take_n(s.taken, s.recvd, 1 + pick(MAX));
      if (n > 0) {
        s.taken = M.pg_taken(s.taken, n);
        up.push({ t: "READ", n });
      }
    } else if (act === "deliver-down") {
      const m = down.shift()!;
      if (m.t === "DATA") {
        s.recvd = M.pg_recv_data(s.recvd, m.k);
      } else if (m.reply) {
        // the discard's reply: the page's count starts again from what the relay took
        s.sent = m.w;
        s.tail = m.w;
        s.wp = m.w;
        s.dp = false;
        s.opOpen = false;
      } else {
        expect(m.w >= s.wp).toBe(true);
        s.wp = m.w;
        if (s.opOpen && s.wp >= s.opEnd) s.opOpen = false;
      }
    } else if (act === "deliver-up") {
      const m = up.shift()!;
      if (m.t === "SEND") {
        // a conforming page's frame always fits the relay's room
        if (M.rl_over(m.n, M.rl_room(WIN, s.q)) !== 0) throw new Error(`a frame does not fit after ${where}`);
        s.q = M.rl_queue(s.q, m.n);
        fits++;
      } else if (m.t === "DISCARD") {
        s.q = 0;
        down.push({ t: "WRITTEN", w: s.wr, reply: true });
      } else {
        s.gr = M.rl_grant(s.rd, s.gr, WIN, m.n);
        s.ti = M.pg_taken(s.ti, m.n);
      }
    } else if (act === "write") {
      const m = 1 + pick(s.q);
      s.wr = M.rl_written(s.wr, m);
      s.q = M.rl_unqueue(s.q, m);
      down.push({ t: "WRITTEN", w: s.wr, reply: false });
      writes++;
    } else if (act === "rogue") {
      up.push({ t: "READ", n: 1 + pick(3 * WIN) });
    } else if (act === "read") {
      // the socket delivers a chunk only while the relay's credit is positive (its reads are paused
      // otherwise), and in chunks of at most C
      const k = 1 + pick(C);
      s.rd = M.rl_read(s.rd, k);
      down.push({ t: "DATA", k });
      reads++;
    }
    invariants(where);
  }
  return { fits, discards, reads, writes };
}

test("random protocol traces keep every invariant the lemmas prove, after every step", () => {
  let totals = { fits: 0, discards: 0, reads: 0, writes: 0 };
  for (let seed = 1; seed <= 300; seed++) {
    const t = trace(seed, 400, 6, 3, 4);
    for (const k of Object.keys(totals) as (keyof typeof totals)[]) totals[k] += t[k];
  }
  // the traces exercised every kind of event, many times
  expect(totals.fits).toBeGreaterThan(1000);
  expect(totals.discards).toBeGreaterThan(50);
  expect(totals.reads).toBeGreaterThan(1000);
  expect(totals.writes).toBeGreaterThan(1000);
});

test("random traces of an over-asking page keep the relay's own invariants", () => {
  for (let seed = 1; seed <= 200; seed++) trace(seed, 400, 6, 3, 4, true);
});

test("the proofs check, and the committed JavaScript is the compiler's output for the proven file", async () => {
  const proc = Bun.spawnSync(["bend", resolve(CORE, "tcp_model.bend")], { stdout: "pipe", stderr: "pipe" });
  expect(proc.stdout.toString()).toContain("ALL PROOFS CHECK");
  const out = `/tmp/tcp_transitions_check_${process.pid}.mjs`;
  const gen = Bun.spawnSync(["bend", resolve(CORE, "tcp_transitions.bend"), "-o", out], { stdout: "pipe", stderr: "pipe" });
  expect(gen.exitCode).toBe(0);
  const fresh = await Bun.file(out).text();
  const committed = await Bun.file(resolve(CORE, "tcp_transitions.mjs")).text();
  expect(fresh === committed).toBe(true);
}, 600000);
