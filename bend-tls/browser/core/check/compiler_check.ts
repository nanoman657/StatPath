// Writes the data section of CompilerCheck.lean, from the two files the check is about:
//   - the lines of the Bend source and of the transitions' JavaScript (the module's region from its first
//     transition on), and of the runtime helpers, as Lean string lists (the kernel looks lines up in them);
//   - the parsed Bend definitions and transitions: the readers (parseBend, parseJS, in CompilerCheck.lean) are
//     run with `lean --run` on these lines, and their output (Lean terms) is written in. The kernel checks the
//     translation on these terms; it does not read the texts.
// `bun compiler_check.ts` writes the section; `bun compiler_check.ts --check` regenerates it and fails when the
// file is not current, so a changed source, output or reader is noticed before the proof is run.
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const HERE = import.meta.dir;
export const LEAN_FILE = join(HERE, "CompilerCheck.lean");
const BEND = join(HERE, "..", "tcp_transitions.bend");
const JS = join(HERE, "..", "tcp_transitions.mjs");
export const BEGIN = "-- BEGIN-DATA";
export const END = "-- END-DATA";
export const LEAN_BIN = process.env.LEAN ?? "/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean";

// a Lean string literal for one line (ASCII, as both files are)
export function leanString(text: string): string {
  let out = '"';
  for (const ch of text) {
    if (ch === "\\") out += "\\\\";
    else if (ch === '"') out += '\\"';
    else if (ch === "\t") out += "\\t";
    else if (ch === "\r") out += "\\r";
    else if (ch.charCodeAt(0) < 32 || ch.charCodeAt(0) > 126) throw new Error(`not ASCII: ${ch.charCodeAt(0)}`);
    else out += ch;
  }
  return out + '"';
}

// a text as its lines: split on newline, the empty line after a final newline left out
export function linesOf(text: string): string[] {
  const ls = text.split("\n");
  if (ls.length > 0 && ls[ls.length - 1] === "") ls.pop();
  return ls;
}

function leanList(ls: string[]): string {
  return "[\n" + ls.map((l) => "  " + leanString(l)).join(",\n") + "\n]";
}

// The JavaScript the check reads: the runtime helpers (nat_chk, nat_in, run_lib, run_loop), each as the block the
// file has, and every line from the first transition ($-function) to the end. The kernel is given these, not the
// whole file: it cannot read a long text with its readers (its memory grows with the text it reads). The other
// lines are runtime code that the transitions do not use. Two conditions this relies on are asserted: each
// helper's header is a line of the file exactly once, and no transition is defined before the first one.
export const HELPERS = ["nat_chk(n)", "nat_in(n)", "run_lib(f, n)", "run_loop(r)"];

export function jsCheckParts(js: string): { region: string[]; helpers: string[] } {
  const lines = linesOf(js);
  const first = lines.findIndex((l) => l.startsWith("function $"));
  if (first < 0) throw new Error("no transition in the JavaScript");
  for (const l of lines.slice(0, first)) {
    if (l.startsWith("function $")) throw new Error("a transition before the first region");
  }
  const blocks: string[] = [];
  for (const h of HELPERS) {
    const header = `function ${h} {`;
    const at = lines.map((l, i) => (l === header ? i : -1)).filter((i) => i >= 0);
    if (at.length !== 1) throw new Error(`${header} occurs ${at.length} times, not once`);
    let end = at[0];
    while (lines[end] !== "}") end++;
    blocks.push(...lines.slice(at[0], end + 1));
  }
  return { region: lines.slice(first), helpers: blocks };
}

function textDefs(bend: string, js: string): string {
  const { region, helpers } = jsCheckParts(js);
  return [
    `def bendText : List String :=\n${leanList(linesOf(bend))}`,
    `def jsText : List String :=\n${leanList(region)}`,
    `def helperText : List String :=\n${leanList(helpers)}`,
  ].join("\n\n");
}

function lineIndexOf(lean: string, marker: string): number {
  const i = lean.indexOf(marker);
  if (i < 0) throw new Error(`the marker ${marker} is missing from CompilerCheck.lean`);
  return i;
}

// the file's head: everything before the data section (the semantics, the proofs, the readers, the check)
export function headOf(lean: string): string {
  return lean.slice(0, lineIndexOf(lean, BEGIN));
}

// runs the readers on the texts: the parsed terms, as Lean source (between the markers the program prints)
export function parsedTerms(head: string, bend: string, js: string): { bend: string; js: string } {
  const dir = mkdtempSync(join(tmpdir(), "compiler-check-"));
  try {
    const file = join(dir, "CompilerCheckExtract.lean");
    const main = [
      "end CompilerCheck",
      "",
      "open CompilerCheck",
      "",
      "def main : IO Unit := do",
      "  match parseBend bendText, parseJS jsText with",
      "  | some defs, some fns =>",
      '    IO.println "-- BEND-BEGIN"',
      "    IO.println (toString (repr defs))",
      '    IO.println "-- BEND-END"',
      '    IO.println "-- JS-BEGIN"',
      "    IO.println (toString (repr fns))",
      '    IO.println "-- JS-END"',
      "  | _, _ => IO.println \"-- PARSE-FAILED\"",
      "",
    ].join("\n");
    writeFileSync(file, head + "\n" + textDefs(bend, js) + "\n\n" + main);
    const run = Bun.spawnSync([LEAN_BIN, "--run", file], { stdout: "pipe", stderr: "pipe" });
    const out = run.stdout.toString();
    if (run.exitCode !== 0) throw new Error(`lean --run failed: ${run.stderr.toString().slice(0, 2000)}`);
    if (out.includes("-- PARSE-FAILED")) throw new Error("the readers do not parse the texts");
    const between = (a: string, b: string) => {
      const i = out.indexOf(a), j = out.indexOf(b);
      if (i < 0 || j < 0) throw new Error(`the reader's output has no ${a}`);
      return out.slice(i + a.length, j).trim();
    };
    return {
      bend: between("-- BEND-BEGIN", "-- BEND-END"),
      js: between("-- JS-BEGIN", "-- JS-END"),
    };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

function indent(text: string): string {
  return text.split("\n").map((l) => "  " + l).join("\n");
}

// the whole data section: the texts, then the parsed terms
export function dataSection(head: string, bend: string, js: string): string {
  const terms = parsedTerms(head, bend, js);
  return [
    textDefs(bend, js),
    `def bendAST : List BendDef :=\n${indent(terms.bend)}`,
    `def jsAST : List JSFn :=\n${indent(terms.js)}`,
  ].join("\n\n");
}

export function replaceData(lean: string, data: string): string {
  const b = lean.indexOf(BEGIN);
  const e = lean.indexOf(END);
  if (b < 0 || e < 0 || e < b) throw new Error("the data markers are missing from CompilerCheck.lean");
  return lean.slice(0, b + BEGIN.length) + "\n" + data + "\n" + lean.slice(e);
}

if (import.meta.main) {
  const bend = readFileSync(BEND, "utf8");
  const js = readFileSync(JS, "utf8");
  const lean = readFileSync(LEAN_FILE, "utf8");
  const next = replaceData(lean, dataSection(headOf(lean), bend, js));
  if (process.argv.includes("--check")) {
    if (next !== lean) {
      console.error("CompilerCheck.lean's data is not the current texts and readers: run compiler_check.ts");
      process.exit(1);
    }
    console.log("the data is current");
  } else {
    writeFileSync(LEAN_FILE, next);
    console.log("the data section is written");
  }
}
