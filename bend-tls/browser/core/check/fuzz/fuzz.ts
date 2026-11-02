// The differential test of the Bend compiler. Each batch is a random program (gen.ts) of definitions over Nat. The
// bend CLI checks it and compiles it to JavaScript; the compiled definitions are called on random arguments; each
// result is compared with the reference (ref.ts): the same value, or a throw exactly where the reference refuses.
// Every `kernel-every` batches, the program (small literals only) is elaborated to BendTT's kernel text, and the
// kernel's own evaluator is compared with the reference on small arguments too: a third opinion on the reference.
//
//   bun fuzz.ts --batches 200 --defs 30 --calls 20 --seed 1 --kernel-every 10 --dir <scratch> --log <file>
import { mkdirSync, rmSync, writeFileSync, existsSync, appendFileSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { genBatch, printProgram, rng, BIG_LITERAL, type Def } from "./gen.ts";
import { evalDef, Refuse, LIMIT } from "./ref.ts";

const argv = Bun.argv.slice(2);
const opt = (name: string, dflt: string) => {
  const i = argv.indexOf(`--${name}`);
  return i >= 0 ? argv[i + 1] : dflt;
};
const BATCHES = Number(opt("batches", "100"));
const FIRST = Number(opt("first", "0"));
const DEFS = Number(opt("defs", "30"));
const CALLS = Number(opt("calls", "20"));
const SEED = Number(opt("seed", "1"));
const KERNEL_EVERY = Number(opt("kernel-every", "10"));
const DIR = resolve(opt("dir", "/tmp/bend-fuzz"));
const LOG = opt("log", join(DIR, "fuzz.log"));
const BEND = process.env.BEND ?? Bun.which("bend") ?? "bend";
const KERNEL = process.env.BENDTT_EVAL ?? resolve(import.meta.dir, "..", ".build", "bendtt-eval");

mkdirSync(join(DIR, "failures"), { recursive: true });

const stats = { batches: 0, invalid: 0, compileFailed: 0, defs: 0, calls: 0, values: 0, refusals: 0, mismatches: 0, kernelProbes: 0, kernelMismatches: 0 };
const log = (s: string) => appendFileSync(LOG, s + "\n");

// the arguments: mostly small, some large, some at the limit, and the edges
function randArg(r: () => number): bigint {
  const c = r();
  const int = (lo: number, hi: number) => lo + Math.floor(r() * (hi - lo + 1));
  if (c < 0.6) return BigInt(int(0, 30));
  if (c < 0.8) return BigInt(int(0, 1 << 20));
  if (c < 0.9) return LIMIT - BigInt(int(0, 1 << 16));
  return [0n, 1n, LIMIT, BIG_LITERAL, 4294967295n + 1n][int(0, 4)];
}

function runBatch(b: number): void {
  const r = rng(SEED * 1000003 + b);
  const kernel = KERNEL_EVERY > 0 && b % KERNEL_EVERY === 0;
  const defs: Def[] = genBatch(r, { defs: DEFS, bigLiterals: !kernel });
  const src = printProgram(defs);
  const stem = join(DIR, `b${b}`);
  writeFileSync(`${stem}.bend`, src);
  stats.batches++;
  stats.defs += defs.length;

  const check = Bun.spawnSync([BEND, `${stem}.bend`, "--check-only"], { stdout: "pipe", stderr: "pipe" });
  if (check.exitCode !== 0) {
    stats.invalid++;
    writeFileSync(join(DIR, "failures", `b${b}.invalid.txt`), check.stdout.toString() + check.stderr.toString());
    log(`batch ${b}: generated program is not valid Bend (kept in failures/)`);
    return;
  }
  const build = Bun.spawnSync([BEND, `${stem}.bend`, "-o", `${stem}.mjs`], { stdout: "pipe", stderr: "pipe" });
  if (build.exitCode !== 0) {
    stats.compileFailed++;
    writeFileSync(join(DIR, "failures", `b${b}.compile.txt`), build.stdout.toString() + build.stderr.toString());
    log(`batch ${b}: the compiler failed (kept in failures/)`);
    return;
  }

  return compareCalls(b, defs, src, stem, r, kernel);
}

async function compareCalls(b: number, defs: Def[], src: string, stem: string, r: () => number, kernel: boolean): Promise<void> {
  const table = (await import(`${stem}.mjs`)).default as Record<string, (...a: number[]) => unknown>;
  const mismatches: unknown[] = [];
  const kernelCases: { def: number; args: bigint[] }[] = [];
  for (const d of defs) {
    for (let c = 0; c < CALLS; c++) {
      const args = d.params.map(() => randArg(r));
      let expected: bigint | "refused";
      try {
        expected = evalDef(defs, d.index, args);
      } catch (e) {
        if (!(e instanceof Refuse)) throw e;
        expected = "refused";
      }
      let actual: unknown;
      try {
        actual = table[d.name](...args.map((x) => Number(x)));
      } catch (e) {
        // only the runtime's own immediate-limit refusal counts as one; any other throw is a mismatch
        actual = String(e).includes("immediate") ? "refused" : `threw: ${String(e).slice(0, 200)}`;
      }
      stats.calls++;
      if (expected === "refused") {
        stats.refusals++;
        if (actual !== "refused") mismatches.push({ def: d.name, args: args.map(String), expected: "refused", actual });
      } else {
        stats.values++;
        if (actual !== Number(expected)) mismatches.push({ def: d.name, args: args.map(String), expected: String(expected), actual });
      }
    }
    if (kernel && kernelCases.length < 60) {
      for (let c = 0; c < 3; c++) kernelCases.push({ def: d.index, args: d.params.map(() => BigInt(Math.floor(r() * 9))) });
    }
  }
  if (kernel) checkKernel(b, defs, stem, kernelCases);
  if (mismatches.length > 0) {
    stats.mismatches += mismatches.length;
    const file = join(DIR, "failures", `b${b}.mismatch.json`);
    writeFileSync(file, JSON.stringify({ source: src, mismatches: mismatches.slice(0, 20) }, null, 2));
    log(`batch ${b}: ${mismatches.length} mismatches, first ${JSON.stringify(mismatches[0])} (kept in failures/)`);
  } else {
    rmSync(`${stem}.bend`, { force: true });
    rmSync(`${stem}.mjs`, { force: true });
  }
}

function num(n: bigint): string {
  let t = "(.Zero, ())";
  for (let i = 0n; i < n; i++) t = `(.Succ, (${t}, ()))`;
  return t;
}

function checkKernel(b: number, defs: Def[], stem: string, cases: { def: number; args: bigint[] }[]): void {
  if (!existsSync(KERNEL)) return;
  const tt = `${stem}.bendtt`;
  const before = stats.kernelMismatches;
  const elab = Bun.spawnSync([BEND, `${stem}.bend`, "-o", tt], { stdout: "pipe", stderr: "pipe" });
  if (elab.exitCode !== 0) {
    log(`batch ${b}: the kernel text was not produced: ${elab.stderr.toString().slice(0, 200)}`);
    return;
  }
  const probes = cases.map((c, i) => `probe_${i} : Nat = (f${c.def} ${c.args.map(num).join(" ")})`);
  writeFileSync(`${tt}.probes`, readFileSync(tt, "utf8") + "\n" + probes.join("\n") + "\n");
  const run = Bun.spawnSync([KERNEL, "eval", `${tt}.probes`, ...cases.map((_, i) => `probe_${i}`)], { stdout: "pipe", stderr: "pipe" });
  const lines = run.stdout.toString().trim().split("\n");
  cases.forEach((c, i) => {
    stats.kernelProbes++;
    const got = (lines[i] ?? "").split(" ")[1] ?? "missing";
    let want: string;
    try {
      want = String(evalDef(defs, c.def, c.args));
    } catch {
      want = "refused";
    }
    if (got !== want) {
      stats.kernelMismatches++;
      log(`batch ${b}: kernel says ${got} for f${c.def}(${c.args.join(", ")}), reference ${want}`);
    }
  });
  // a batch the kernel agrees on leaves no files behind; a disagreeing one keeps its kernel text for the record
  if (stats.kernelMismatches === before) {
    rmSync(tt, { force: true });
    rmSync(`${tt}.probes`, { force: true });
  }
}


const started = Date.now();
for (let b = FIRST; b < FIRST + BATCHES; b++) {
  await runBatch(b);
  if ((b - FIRST + 1) % 50 === 0) {
    log(JSON.stringify({ t: Math.round((Date.now() - started) / 1000), ...stats }));
  }
}
log(`FINAL ${JSON.stringify({ t: Math.round((Date.now() - started) / 1000), ...stats })}`);
console.log(JSON.stringify(stats));
