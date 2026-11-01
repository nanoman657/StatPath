// Differential test: the Lean model of the compiled transitions (Transitions.lean, in this folder) and
// the compiled JavaScript (../tcp_transitions.mjs) must agree on every input, and on the throws. The
// inputs run past the proven bound (2^33) up to the largest host number (2^53), so the test also checks
// the code where the model claims nothing. Skipped when no Lean 4 toolchain is found; set LEAN to choose one.
import { test, expect } from "bun:test";
import { existsSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const MODEL = join(here, "Transitions.lean");
const COMPILED = join(here, "..", "tcp_transitions.mjs");

// the thirteen transitions and their arities (the names and the order of Transitions.lean's dispatch)
const ARITY: Record<string, number> = {
  pg_start: 2, pg_frame_n: 5, pg_sent: 2, pg_take_n: 3, pg_taken: 2, pg_recv_data: 2,
  rl_room: 2, rl_over: 2, rl_queue: 2, rl_written: 2, rl_unqueue: 2, rl_read: 2, rl_grant: 4,
};

const EDGE = [
  0, 1, 2, 3, 7, 4096, 65535, 65536, 131072, 1048576,
  2 ** 32 - 2, 2 ** 32 - 1, 2 ** 32, 2 ** 33 - 1, 2 ** 33,
  2 ** 48 - 2, 2 ** 48 - 1, 2 ** 48, 2 ** 53 - 1, 2 ** 53,
];

// a seeded generator (mulberry32), so every run tests the same inputs
function prng(seed: number) {
  let a = seed >>> 0;
  const next32 = () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return (t ^ (t >>> 14)) >>> 0;
  };
  // an integer from 0 up to 2^bits (bits <= 53)
  const below = (bits: number) => Math.floor(((next32() * 2 ** 21 + (next32() >>> 11)) / 2 ** 53) * 2 ** bits);
  const pick = () => {
    const r = next32() % 4;
    if (r < 2) return EDGE[next32() % EDGE.length]; // half the draws are edges
    if (r === 2) return below(33); // the bound's range
    return below(53); // the whole host-number range
  };
  return { pick };
}

// the inputs for one transition: every pair of edges for the two-argument ones, sampled otherwise
function casesFor(name: string, arity: number, gen: ReturnType<typeof prng>): number[][] {
  if (arity === 2) {
    const out: number[][] = [];
    for (const a of EDGE) for (const b of EDGE) out.push([a, b]);
    for (let i = 0; i < 200; i++) out.push([gen.pick(), gen.pick()]);
    return out;
  }
  const out: number[][] = [];
  for (let i = 0; i < 4000; i++) out.push(Array.from({ length: arity }, () => gen.pick()));
  return out;
}

// The Lean 4.34.0 toolchain, the version the Bend verdict uses, as elan installs it. Its binary is
// used directly: the elan proxy needs a default toolchain configured.
const PINNED_LEAN = join(homedir(), ".elan", "toolchains", "leanprover--lean4---v4.34.0", "bin", "lean");

function findLean(): string | null {
  const candidates = [process.env.LEAN, PINNED_LEAN, Bun.which("lean")];
  for (const c of candidates) if (c && existsSync(c)) return c;
  return null;
}

// What the compiled code gives for one call: its value, or THROW
async function jsResults(calls: [string, number[]][]): Promise<string[]> {
  const M = (await import(COMPILED)).default as Record<string, (...a: number[]) => unknown>;
  return calls.map(([name, args]) => {
    try {
      const v = M[name](...args);
      if (typeof v !== "number") throw new Error(`${name} did not return a number`);
      return String(v);
    } catch {
      return "THROW";
    }
  });
}

// What the Lean model gives for the same calls, one line each
async function leanResults(lean: string, model: string, calls: [string, number[]][]): Promise<string[]> {
  const input = calls.map(([name, args]) => [name, ...args.map(String)].join(" ")).join("\n") + "\n";
  const proc = Bun.spawn([lean, "--run", model], {
    stdin: new Blob([input]),
    stdout: "pipe",
    stderr: "pipe",
  });
  const [out, err, code] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
    proc.exited,
  ]);
  if (code !== 0) throw new Error(`lean --run failed (${code}): ${err}`);
  return out.split("\n").filter((l) => l.length > 0);
}

const lean = findLean();

test.skipIf(lean === null)(
  "the Lean model and the compiled code agree on every input, past the bound and throws included",
  async () => {
    const gen = prng(20260601);
    const calls: [string, number[]][] = [];
    for (const [name, arity] of Object.entries(ARITY)) {
      for (const args of casesFor(name, arity, gen)) calls.push([name, args]);
    }
    const expected = await leanResults(lean!, MODEL, calls);
    const actual = await jsResults(calls);
    expect(expected.length).toBe(calls.length);
    const mismatches: string[] = [];
    let throws = 0;
    for (let i = 0; i < calls.length; i++) {
      if (expected[i] === "THROW") throws++;
      if (expected[i] !== actual[i]) {
        if (mismatches.length < 10) {
          const [name, args] = calls[i];
          mismatches.push(`${name}(${args.join(", ")}): lean ${expected[i]}, js ${actual[i]}`);
        }
      }
    }
    console.log(`transitions: ${calls.length} calls, ${throws} throw, ${calls.length - throws} values`);
    expect(mismatches).toEqual([]);
  },
  600_000,
);
