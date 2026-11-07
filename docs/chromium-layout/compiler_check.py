#!/usr/bin/env python3
"""Runs the extended translation-validation reader and checker of docs/chromium-layout/CompilerCheck.lean
on the compiled JavaScript functions in docs/chromium-layout/layout.mjs (and $lp_max in bend-engine/merge.mjs),
and writes the report to docs/chromium-layout/compiler_check_report.txt.

Run from anywhere: python3 docs/chromium-layout/compiler_check.py [--out PATH]
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LAYOUT_MJS = os.path.join(HERE, "layout.mjs")
MERGE_MJS = os.path.join(ROOT, "bend-engine", "merge.mjs")
CORE_LEAN = os.path.join(HERE, "CompilerCheckCore.lean")
CHECK_LEAN = os.path.join(HERE, "CompilerCheck.lean")
REPORT = os.path.join(HERE, "compiler_check_report.txt")
LEAN_BIN = os.environ.get("LEAN_BIN", "/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin")
OLEAN_DIR = os.environ.get("OLEAN_DIR", "/root/agy-scratch/chromium-layout/olean")

LAYOUT_FN_NAMES = [
    "$box_strut_zero",
    "$box_strut_inline_sum",
    "$box_strut_block_sum",
    "$box_strut_add",
    "$margin_strut_empty",
    "$margin_strut_append",
    "$margin_strut_sum",
    "$margin_strut_apply_offset",
    "$font_height_line_height",
    "$font_height_merge",
]


def sha(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()[:16]


def function_lines(src_lines, name):
    """The lines of `function NAME(...) {` up to its closing `}` at column 0."""
    start = next(i for i, l in enumerate(src_lines) if l.startswith(f"function {name}("))
    end = next(i for i in range(start + 1, len(src_lines)) if src_lines[i] == "}")
    return src_lines[start:end + 1]


def extract_mjs_lines():
    layout_src = open(LAYOUT_MJS).read().split("\n")
    merge_src = open(MERGE_MJS).read().split("\n")
    extracted = []
    for nm in LAYOUT_FN_NAMES:
        extracted.extend(function_lines(layout_src, nm))
    extracted.extend(function_lines(merge_src, "$lp_max"))
    return extracted


def ensure_oleans(env):
    os.makedirs(OLEAN_DIR, exist_ok=True)
    for mod, src in [("CompilerCheckCore", CORE_LEAN), ("CompilerCheck", CHECK_LEAN)]:
        olean = os.path.join(OLEAN_DIR, f"{mod}.olean")
        if not os.path.exists(olean) or os.path.getmtime(olean) < os.path.getmtime(src):
            res = subprocess.run(
                ["lean", "-j", "1", "-R", HERE, "-o", olean, src],
                capture_output=True,
                text=True,
                env=env,
                timeout=900,
            )
            if res.returncode != 0:
                sys.stderr.write(res.stdout + res.stderr)
                sys.exit(res.returncode)


def make_eval_harness(extracted_lines):
    lean_list = "[" + ", ".join(json.dumps(l) for l in extracted_lines) + "]"
    return f"""import CompilerCheck

open CompilerCheck

def extractedMJS : List String := {lean_list}

def runReport : IO Unit := do
  let textMatch := decide (extractedMJS = layoutJSText)
  let parsed := parseRecJS extractedMJS
  let astMatch := decide (parsed = some layoutJSRecAST)
  let checked := checkAllRec layoutBendRecDefs layoutJSRecAST
  IO.println s!"extractedMJS == layoutJSText: {{textMatch}}"
  IO.println s!"parseRecJS extractedMJS == some layoutJSRecAST: {{astMatch}}"
  IO.println s!"checkAllRec layoutBendRecDefs layoutJSRecAST: {{checked}}"
  for b in layoutBendRecDefs do
    match layoutJSRecAST.find? (fun j => j.name == b.name) with
    | none => IO.println s!"fn {{b.name}}: MISSING"
    | some j => IO.println s!"fn {{b.name}}: checkRecFn = {{checkRecFn b j}}"
  let bendMax := parseBend ["def max_crowns(+c1: Nat, +c2: Nat) -> Nat:", "  Nat.max(c1, c2)"]
  IO.println s!"parseBend Nat.max(c1, c2): {{repr bendMax}}"
  let jsMax := parseJS ["function $max_crowns(_c1_0, _c2_0) {{", "  return (_c1_0 > _c2_0 ? _c1_0 : _c2_0);", "}}"]
  IO.println s!"parseJS (_c1_0 > _c2_0 ? _c1_0 : _c2_0): {{repr jsMax}}"

#eval runReport
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=REPORT)
    args = ap.parse_args()
    env = dict(
        os.environ,
        PATH=LEAN_BIN + os.pathsep + os.environ.get("PATH", ""),
        LEAN_PATH=OLEAN_DIR,
    )
    ensure_oleans(env)
    extracted = extract_mjs_lines()
    tmp = tempfile.mkdtemp(prefix="cl-cc-")
    try:
        lean_file = os.path.join(tmp, "RunCompilerCheck.lean")
        with open(lean_file, "w") as f:
            f.write(make_eval_harness(extracted))
        run = subprocess.run(["lean", "-j", "1", lean_file], capture_output=True, text=True, env=env, timeout=900)
        if run.returncode != 0:
            sys.stderr.write(run.stdout + run.stderr)
            return run.returncode
        body = [l for l in (run.stdout + run.stderr).split("\n") if l.strip()]
        report = [
            "Extended translation validation report (docs/chromium-layout/CompilerCheck.lean)",
            "(generated by docs/chromium-layout/compiler_check.py; do not edit by hand)",
            f"layout.mjs sha256/16: {sha(LAYOUT_MJS)}",
            f"merge.mjs sha256/16: {sha(MERGE_MJS)}",
            f"CompilerCheckCore.lean sha256/16: {sha(CORE_LEAN)}",
            f"CompilerCheck.lean sha256/16: {sha(CHECK_LEAN)}",
            "",
            "== Lean evaluation output",
            *body,
            "",
            f"lean exit status: {run.returncode}",
        ]
        with open(args.out, "w") as f:
            f.write("\n".join(report) + "\n")
        print("\n".join(report))
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
