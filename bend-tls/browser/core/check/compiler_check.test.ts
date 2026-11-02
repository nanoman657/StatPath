// The compiler check (CompilerCheck.lean): the data it reads is the current source and output, the kernel accepts
// the check, and the check refuses each of the changes it is meant to catch. The check is a proof of the
// translation of the transitions (see the header of CompilerCheck.lean): a change to the Bend source, or to the
// JavaScript the compiler emits for it, must make the kernel reject the proof.
import { test, expect } from "bun:test";
import { existsSync, readFileSync, writeFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { BEGIN, END, LEAN_BIN, LEAN_FILE, dataSection, headOf, replaceData } from "./compiler_check.ts";

const HERE = import.meta.dir;
const BEND = join(HERE, "..", "tcp_transitions.bend");
const JS = join(HERE, "..", "tcp_transitions.mjs");
const haveLean = existsSync(LEAN_BIN);

function leanOn(file: string): { code: number; out: string } {
  const run = Bun.spawnSync([LEAN_BIN, file], { stdout: "pipe", stderr: "pipe" });
  return { code: run.exitCode ?? -1, out: run.stdout.toString() + run.stderr.toString() };
}

// the check file with the data of the given texts (the readers run on the texts, as the generator runs them)
function checkFileFor(bend: string, js: string): string {
  const lean = readFileSync(LEAN_FILE, "utf8");
  return replaceData(lean, dataSection(headOf(lean), bend, js));
}

test("the data section is the current texts, read by the current readers", () => {
  const lean = readFileSync(LEAN_FILE, "utf8");
  const bend = readFileSync(BEND, "utf8");
  const js = readFileSync(JS, "utf8");
  expect(replaceData(lean, dataSection(headOf(lean), bend, js))).toBe(lean);
}, 60000);

test.skipIf(!haveLean)("the kernel accepts the check: every transition's JavaScript is its Bend definition", () => {
  const { code, out } = leanOn(LEAN_FILE);
  expect(out).not.toContain("error");
  expect(code).toBe(0);
}, 600000);

// each mutation: a changed text the kernel must reject. The texts are changed in memory; the check file is written
// to a temporary directory, and the kernel reads it.
const mutations: { name: string; bend?: (s: string) => string; js?: (s: string) => string }[] = [
  {
    name: "the JavaScript subtracts the other way round (pg_take_n)",
    js: (s) => s.replace("(_recvd_0 < _taken_0 ? 0 : _recvd_0 - _taken_0)", "(_recvd_0 < _taken_0 ? 0 : _taken_0 - _recvd_0)"),
  },
  {
    name: "the JavaScript takes the larger of the two (pg_frame_n)",
    js: (s) => s.replace("return (_mx_0 < _x_3 ? _mx_0 : _x_3);", "return (_mx_0 < _x_3 ? _x_3 : _mx_0);"),
  },
  {
    name: "the JavaScript drops the immediate-limit check (rl_queue)",
    js: (s) => s.replace("return nat_chk(_q_0 + _n_0);", "return _q_0 + _n_0;"),
  },
  {
    name: "the Bend source subtracts the other way round (pg_take_n)",
    bend: (s) => s.replace("Nat.min(mx, Nat.sub(recvd, taken))", "Nat.min(mx, Nat.sub(taken, recvd))"),
  },
  {
    name: "the export of rl_grant takes three arguments, not four",
    js: (s) => s.replace('"rl_grant": run_lib((a0,a1,a2,a3)', '"rl_grant": run_lib((a0,a1,a2)').replace(
      'run_loop($rl_grant(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3))), 4)', 'run_loop($rl_grant(nat_in(a0),nat_in(a1),nat_in(a2))), 3)'),
  },
  {
    name: "the runtime's immediate limit is one more than nat_chk's",
    js: (s) => s.replace("if (n > 281474976710655) {", "if (n > 281474976710656) {"),
  },
];

for (const m of mutations) {
  test.skipIf(!haveLean)(`the kernel rejects a change: ${m.name}`, () => {
    const bend = m.bend ? m.bend(readFileSync(BEND, "utf8")) : readFileSync(BEND, "utf8");
    const js = m.js ? m.js(readFileSync(JS, "utf8")) : readFileSync(JS, "utf8");
    const dir = mkdtempSync(join(tmpdir(), "compiler-check-neg-"));
    try {
      const file = join(dir, "CompilerCheckNeg.lean");
      writeFileSync(file, checkFileFor(bend, js));
      const { code } = leanOn(file);
      expect(code).not.toBe(0);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 600000);
}
