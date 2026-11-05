#!/usr/bin/env python3
"""Runs the translation-validation reader of browser/core/check/CompilerCheck.lean on the lesson-level
maximum functions as the Bend compiler emitted them in bend-engine/merge.mjs, and writes the result to
bend-engine/compiler_check_report.txt.

The repository's CompilerCheck.lean is not modified. The check copies it to a temporary directory, appends
a section that calls its own reader (`parseJS`) on each candidate, and runs `lean` on that copy.

The candidates are taken from merge.mjs, not written by hand:
  * the lesson maximum expressions of `$lp_max` (crowns, attempts, best, played), each as a one-line
    function with the parameters the compiler gave it;
  * the XP maximum expression of `$xins_c` as a one-line function;
  * the whole `$lp_max` function, as emitted (it returns a record, so it is not a Nat transition);
  * a control: a less-than maximum, `return (a < b ? a : b)`, which is the shape the reader is written for.

Run from anywhere: python3 bend-engine/compiler_check.py
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
MJS = os.path.join(HERE, "merge.mjs")
CHECK = os.path.join(ROOT, "bend-tls", "browser", "core", "check", "CompilerCheck.lean")
REPORT = os.path.join(HERE, "compiler_check_report.txt")
LEAN_BIN = os.environ.get("LEAN_BIN", "/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin")
GREATER = re.compile(r"\((_\w+) > (_\w+) \? \1 : \2\)")


def sha(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()[:16]


def function_lines(src_lines, name):
    """The lines of `function NAME(...) {` up to its closing `}` at column 0."""
    start = next(i for i, l in enumerate(src_lines) if l.startswith(f"function {name}("))
    end = next(i for i in range(start + 1, len(src_lines)) if src_lines[i] == "}")
    return src_lines[start:end + 1]


def one_line_max(params_a, params_b, cmp):
    head = f"function $cand({params_a}, {params_b}) {{"
    if cmp == ">":
        body = f"  return ({params_a} > {params_b} ? {params_a} : {params_b});"
    else:
        body = f"  return ({params_a} < {params_b} ? {params_a} : {params_b});"
    return [head, body, "}"]


def candidates():
    src = open(MJS).read().split("\n")
    lp = function_lines(src, "$lp_max")
    xins = function_lines(src, "$xins_c")
    out = []
    # the lesson maxima, from the body of $lp_max as emitted
    for field in ["crowns", "attempts", "best", "played"]:
        m = None
        for line in lp:
            if f'"{field}": ' in line:
                m = GREATER.search(line)
                break
        if m is None:
            sys.exit(f"no compiled maximum for field {field} in $lp_max")
        a, b = m.group(1), m.group(2)
        out.append((f"lesson maximum, field {field} (compiled from lp_max)",
                    one_line_max(a, b, ">"), "as emitted: " + m.group(0)))
        if field == "crowns":
            out.append(("compiled crowns maximum with '>' changed to '<' (parse-only: the guard is the only change)",
                        one_line_max(a, b, "<"), "operator changed"))
    # the XP maximum, from the body of $xins_c as emitted
    xm = None
    for line in xins:
        if '"XEntry"' in line and '"val": ' in line:
            xm = GREATER.search(line)
            if xm:
                break
    if xm is None:
        sys.exit("no compiled XP maximum in xins_c")
    out.append(("XP maximum (compiled from xins_c)",
                one_line_max(xm.group(1), xm.group(2), ">"), "as emitted: " + xm.group(0)))
    out.append(("compiled XP maximum with '>' changed to '<' (parse-only: the guard is the only change)",
                one_line_max(xm.group(1), xm.group(2), "<"), "operator changed"))
    out.append(("whole function $lp_max, as emitted (returns a record)", lp, "as emitted"))
    out.append(("control: less-than maximum, the shape the reader is written for",
                one_line_max("_a_0", "_b_0", "<"), "control"))
    return out


def lean_string(lines):
    return "[" + ", ".join(json.dumps(l) for l in lines) + "]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=REPORT)
    args = ap.parse_args()
    cands = candidates()
    tmp = tempfile.mkdtemp(prefix="cc-")
    lean_file = os.path.join(tmp, "CompilerCheck.lean")
    with open(CHECK) as f:
        base = f.read()
    lines = ["", "open CompilerCheck",
             "def showRes (ls : List String) : String :=",
             "  match parseJS ls with",
             "  | none => \"refused: no function parsed\"",
             "  | some fs => \"parsed: \" ++ toString (repr fs)"]
    for i, (name, text, _) in enumerate(cands):
        lines.append(f"#eval IO.println (\"CANDIDATE {i}\")")
        lines.append(f"#eval IO.println (\"{name}\")")
        lines.append(f"#eval IO.println (showRes {lean_string(text)})")
    # the Bend side: the checker's parseBend on the Bend definitions of the same maxima
    bend_cands = [
        ("Bend definition of the crowns maximum, Nat.max(c1, c2), as lp_max writes it in merge.bend",
         ["def max_crowns(+c1: Nat, +c2: Nat) -> Nat:", "  Nat.max(c1, c2)"]),
        ("control: Bend minimum, Nat.min(c1, c2)",
         ["def min_crowns(+c1: Nat, +c2: Nat) -> Nat:", "  Nat.min(c1, c2)"]),
    ]
    lines.append("def showBend (ls : List String) : String := toString ((parseBend ls).map List.length)")
    for j, (name, text) in enumerate(bend_cands):
        lines.append(f"#eval IO.println (\"BEND {j}\")")
        lines.append(f"#eval IO.println (\"{name}\")")
        lines.append(f"#eval IO.println (\"parseBend: \" ++ showBend {lean_string(text)})")
    with open(lean_file, "w") as f:
        f.write(base + "\n" + "\n".join(lines) + "\n")
    env = dict(os.environ, PATH=LEAN_BIN + os.pathsep + os.environ.get("PATH", ""))
    run = subprocess.run(["lean", lean_file], capture_output=True, text=True, env=env, timeout=900)
    body = [l for l in (run.stdout + run.stderr).split("\n")
            if not l.startswith("warning") and "deprecated" not in l and l.strip()]
    report = [
        "Translation validation: the reader of CompilerCheck.lean on the lesson-level maxima",
        "(generated by bend-engine/compiler_check.py; do not edit by hand)",
        f"merge.mjs sha256/16: {sha(MJS)}",
        f"CompilerCheck.lean sha256/16 (repository file, not modified): {sha(CHECK)}",
        "",
    ]
    for i, (name, text, origin) in enumerate(cands):
        report.append(f"== {name}")
        report.append(f"   source: {origin}")
        report.append("   text: " + " / ".join(text))
    report.append("")
    for j, (name, text) in enumerate(bend_cands):
        report.append(f"== Bend side: {name}")
        report.append("   text: " + " / ".join(text))
    report.append("")
    report.append("== reader results (lean output, in order; 'parseBend: none' means refused)")
    report.extend(body)
    report.append("")
    report.append(f"lean exit status: {run.returncode}")
    with open(args.out, "w") as f:
        f.write("\n".join(report) + "\n")
    print("\n".join(report))
    return run.returncode


if __name__ == "__main__":
    sys.exit(main())
