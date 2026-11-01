// Differential test of the compiled transitions against BendTT's own evaluator. The transitions
// (../tcp_transitions.bend) are elaborated to kernel text by the bend CLI, then run on probe calls by the
// kernel's `eval` mode, and each result is compared with the compiled JavaScript (../tcp_transitions.mjs).
//
// BendTT's numbers are unary (a chain of Succ), so the probes use the values 0..59. The large range is
// checked by transitions.test.ts (the Lean model), not here.
//
// Needs two tools, and the test is skipped if either is missing:
//   BENDTT_EVAL  the kernel built by build-bendtt-eval.sh (default: .build/bendtt-eval next to this file)
//   BEND         the bend CLI (default: `bend` on PATH)
import { test, expect } from "bun:test";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const SOURCE = process.env.TRANSITIONS_BEND ?? join(here, "..", "tcp_transitions.bend");
const COMPILED = join(here, "..", "tcp_transitions.mjs");
const KERNEL = process.env.BENDTT_EVAL ?? join(here, ".build", "bendtt-eval");
const BEND = process.env.BEND ?? Bun.which("bend");
const PER_TRANSITION = 100;

// the thirteen transitions and their arities
const ARITY: Record<string, number> = {
  pg_start: 2, pg_frame_n: 5, pg_sent: 2, pg_take_n: 3, pg_taken: 2, pg_recv_data: 2,
  rl_room: 2, rl_over: 2, rl_queue: 2, rl_written: 2, rl_unqueue: 2, rl_read: 2, rl_grant: 4,
};

// a seeded generator, so every run tests the same probes
function prng(seed: number) {
  let s = seed >>> 0;
  return () => ((s = (Math.imul(s, 1103515245) + 12345) >>> 0) / 4294967296);
}

// a Nat as BendTT's constructors: Zero, and Succ of the rest
function num(n: number): string {
  let t = "(.Zero, ())";
  for (let i = 0; i < n; i++) t = `(.Succ, (${t}, ()))`;
  return t;
}

test.skipIf(!BEND || !existsSync(KERNEL))(
  "the compiled transitions agree with BendTT's evaluator on every probe",
  async () => {
    const dir = mkdtempSync(join(tmpdir(), "bendtt-diff-"));
    try {
      // 1. the transitions, as kernel text
      const tt = join(dir, "transitions.bendtt");
      const elab = Bun.spawnSync([BEND!, SOURCE, "-o", tt], { stdout: "pipe", stderr: "pipe" });
      expect(elab.exitCode, elab.stderr.toString()).toBe(0);

      // 2. the probes: every transition on PER_TRANSITION argument tuples of small numbers
      const rnd = prng(12345);
      const probes: { name: string; args: number[]; js: string }[] = [];
      const M = (await import(COMPILED)).default as Record<string, (...a: number[]) => unknown>;
      for (const [name, arity] of Object.entries(ARITY)) {
        for (let i = 0; i < PER_TRANSITION; i++) {
          const args = Array.from({ length: arity }, () => Math.floor(rnd() * 60));
          const js = (() => {
            try {
              const v = M[name](...args);
              return typeof v === "number" ? String(v) : "?";
            } catch {
              return "THROW";
            }
          })();
          probes.push({ name, args, js });
        }
      }
      const probeFile = join(dir, "probes.bendtt");
      const defs = probes.map((p, i) => `probe_${i} : Nat = (${p.name} ${p.args.map(num).join(" ")})`);
      writeFileSync(probeFile, readFileSync(tt, "utf8") + "\n" + defs.join("\n") + "\n");

      // 3. the kernel's results
      const run = Bun.spawnSync(
        [KERNEL, "eval", probeFile, ...probes.map((_, i) => `probe_${i}`)],
        { stdout: "pipe", stderr: "pipe" },
      );
      expect(run.exitCode, run.stderr.toString()).toBe(0);
      const lines = run.stdout.toString().trim().split("\n");
      expect(lines.length).toBe(probes.length);

      // 4. compare
      const mismatches: string[] = [];
      let stuck = 0;
      probes.forEach((p, i) => {
        const got = (lines[i] ?? "").split(" ")[1] ?? "";
        if (got === "stuck") stuck++;
        if (got !== p.js && mismatches.length < 10) {
          mismatches.push(`${p.name}(${p.args.join(", ")}): kernel ${got}, js ${p.js}`);
        }
      });
      console.log(`bendtt: ${probes.length} probes, ${stuck} stuck`);
      expect(stuck).toBe(0);
      expect(mismatches).toEqual([]);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  },
  600_000,
);
