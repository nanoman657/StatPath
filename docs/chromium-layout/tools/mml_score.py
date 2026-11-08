#!/usr/bin/env python3
"""Two-part message length (MML proxy) for a lane's Lean layout model.

    total = model + inputs + exceptions

model       tokens in every def/abbrev/structure/inductive/instance/class/opaque/axiom/
            macro/notation declaration in the Lean modules the tests import (transitively).
            Theorems (laws and proofs) are not counted: they check the model, they are not it.
inputs      tokens in definitions inside tests/*.lean (the test inputs written as model values,
            and anything else hidden there).
exceptions  for every manifest row that is not `formalized` (and not `internal`): the tokens of
            that test's EXPECT_*/ASSERT_* statements in the pinned Chromium source, i.e. the cost
            of stating its results literally because the model does not produce them.

A `formalized` row whose named theorem is not found in tests/*.lean counts as an exception.
Every token costs 1 (identifiers of any length, numerals of any length, each symbol), so short
names and moving code between files do not change the score; only the amount of structure does.

    mml_score.py <lane dir>                 # score the working tree
    mml_score.py <lane dir> --rev HEAD~1    # score a committed revision
    mml_score.py <lane dir> --gate BASE     # compare working tree with BASE; exit 1 if it fails
    mml_score.py ... --heldout FILE         # rows listed in FILE (file:line, one per line) must not be formalized

<lane dir> is the git worktree root (it contains docs/chromium-layout/).
CHROMIUM_LAYOUT (env) is third_party/blink/renderer/core/layout in a Chromium checkout at the pin.
"""
from __future__ import annotations

import argparse
import functools
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from io import BytesIO
from pathlib import Path

CHROMIUM_LAYOUT = Path(os.environ.get("CHROMIUM_LAYOUT",
    "/root/agy-scratch/chromium-layout/chromium/third_party/blink/renderer/core/layout"))
SUB = "docs/chromium-layout"
MODEL_KINDS = {"def", "abbrev", "structure", "inductive", "instance", "class", "opaque", "axiom",
               "macro", "macro_rules", "notation", "infix", "infixl", "infixr", "prefix", "syntax",
               "elab", "mutual"}
PROOF_KINDS = {"theorem", "lemma", "example"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local"}
TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[^\W\d][\w.\'!?]*|\d+(?:\.\d+)?|\S')


def tokens(text: str) -> int:
    return len(TOKEN.findall(text))


def strip_lean_comments(src: str) -> str:
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n":
                out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append(src[i:j + 1]); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)


def declarations(src: str):
    """Yield (kind, name, text) for each top-level declaration (column-0 start)."""
    src = strip_lean_comments(src)
    starts = []
    for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?((?:\w+\s+)*?)(\w+)\b(.*)$", src, re.M):
        mods = m.group(1).split()
        kind = m.group(2)
        if all(x in MODIFIERS for x in mods) and (kind in MODEL_KINDS or kind in PROOF_KINDS):
            name = (m.group(3).split() or [""])[0]
            starts.append((m.start(), kind, name))
    boundary = [m.start() for m in re.finditer(
        r"^(?:namespace|end|section|open|variable|universe|set_option|import|attribute|#)\b", src, re.M)]
    for k, (pos, kind, name) in enumerate(starts):
        nxt = [p for p in boundary if p > pos] + ([starts[k + 1][0]] if k + 1 < len(starts) else []) + [len(src)]
        yield kind, name, src[pos:min(nxt)]


def read_tree(lane: Path, rev: str | None) -> dict[str, str]:
    """Return {path relative to docs/chromium-layout: text} for .lean and MANIFEST files."""
    files = {}
    if rev is None:
        base = lane / SUB
        for p in base.rglob("*"):
            if p.is_file() and (p.suffix == ".lean" or p.name.startswith("MANIFEST")) and ".lake" not in p.parts:
                files[str(p.relative_to(base))] = p.read_text(errors="replace")
        return files
    data = subprocess.run(["git", "-C", str(lane), "archive", rev, SUB], capture_output=True, check=True).stdout
    with tarfile.open(fileobj=BytesIO(data)) as tar:
        for m in tar.getmembers():
            rel = m.name[len(SUB) + 1:]
            if m.isfile() and (rel.endswith(".lean") or Path(rel).name.startswith("MANIFEST")):
                files[rel] = tar.extractfile(m).read().decode(errors="replace")
    return files


def import_closure(files: dict[str, str], roots: list[str]) -> list[str]:
    seen, todo = [], list(roots)
    while todo:
        f = todo.pop()
        for mod in re.findall(r"^import\s+([\w.]+)", files.get(f, ""), re.M):
            rel = mod.replace(".", "/") + ".lean"
            if rel in files and rel not in seen and not rel.startswith("tests/"):
                seen.append(rel); todo.append(rel)
    return sorted(seen)


_src_cache: dict[str, list[str] | None] = {}


def chromium_lines(path: str):
    if path not in _src_cache:
        cand = CHROMIUM_LAYOUT / path
        if not cand.is_file():
            hits = [p for p in CHROMIUM_LAYOUT.rglob(Path(path).name) if str(p).endswith(path)]
            cand = hits[0] if len(hits) == 1 else None
        _src_cache[path] = cand.read_text(errors="replace").splitlines() if cand else None
    return _src_cache[path]


def scan_test(lines: list[str], line: int) -> tuple[str, list[str]]:
    """Code of the test body starting at `line` (strings blanked) and the contents of its strings."""
    src = "\n".join(lines[line - 1:line + 600])
    code, strings, i, n, depth, started = [], [], 0, len(src), 0, False
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src.startswith("/*", i):
            j = src.find("*/", i + 2); i = n if j < 0 else j + 2; continue
        m = re.match(r'R"([^(\s]*)\(', src[i:i + 40])
        if m:
            close = ")" + m.group(1) + '"'
            j = src.find(close, i + m.end())
            j = n if j < 0 else j
            strings.append(src[i + m.end():j]); code.append('""'); i = j + len(close); continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            strings.append(src[i + 1:j]); code.append('""'); i = j + 1; continue
        c = src[i]
        code.append(c)
        if c == "{":
            depth += 1; started = True
        elif c == "}":
            depth -= 1
            if started and depth <= 0:
                break
        i += 1
    return "".join(code), strings


@functools.lru_cache(maxsize=None)
def expect_cost(file_line: str) -> int | None:
    """Cost of stating a test's results literally: its EXPECT_/ASSERT_ statements plus the contents
    of every string in the test (expected dumps and the HTML input, which an unexplained test has to
    carry as written)."""
    path, _, line = file_line.strip().strip("`").rpartition(":")
    lines = chromium_lines(path)
    if lines is None or not line.isdigit():
        return None
    code, strings = scan_test(lines, int(line))
    expects = sum(tokens(m) for m in re.findall(r"\b(?:EXPECT|ASSERT)_\w+\s*\([^;]*\);", code))
    return expects + sum(tokens(x) for x in strings)


MANIFEST = "MANIFEST"


def manifest_rows(files: dict[str, str]):
    for name, text in sorted(files.items()):
        if not Path(name).name.startswith(MANIFEST):
            continue
        header = None
        for ln in text.splitlines():
            if not ln.startswith("|"):
                continue
            cells = [c.strip() for c in ln.strip().strip("|").split("|")]
            if header is None:
                header = [c.lower() for c in cells]
                continue
            if set(ln) <= set("|-: "):
                continue
            row = dict(zip(header, cells))
            yield {"file_line": cells[0], "test": cells[1],
                   "class": row.get("class", "").lower(), "status": row.get("status", "").lower(),
                   "evidence": " ".join(cells[4:])}


def score(lane: Path, rev: str | None, heldout: set[str]) -> dict:
    files = read_tree(lane, rev)
    test_files = sorted(f for f in files if f.startswith("tests/") and f.endswith(".lean"))
    model_files = import_closure(files, test_files)

    model_tok, laws, numeral_heavy = 0, 0, []
    for f in model_files:
        for kind, name, text in declarations(files[f]):
            if kind in MODEL_KINDS:
                t = tokens(text)
                model_tok += t
                nums = len(re.findall(r"(?<![\w.])\d{2,}(?![\w.])", text))
                if nums >= 6:
                    numeral_heavy.append({"decl": f"{f}:{name}", "multi_digit_numerals": nums, "tokens": t})
            elif kind in PROOF_KINDS:
                laws += 1

    input_tok, theorem_names = 0, set()
    for f in test_files:
        for kind, name, text in declarations(files[f]):
            if kind in PROOF_KINDS:
                theorem_names.add(name.split(".")[-1])
            else:
                input_tok += tokens(text)

    per_row, missing_src, unbacked, held_bad = {}, [], [], []
    for r in manifest_rows(files):
        key = r["file_line"]
        if key in per_row:
            continue
        status = r["status"]
        if r["class"] == "internal" or status == "internal":
            per_row[key] = "internal"
            continue
        if status == "formalized":
            names = [n.split(".")[-1] for n in re.findall(r"`([^`]+)`", r["evidence"])]
            if key in heldout:
                held_bad.append(key)
            if names and any(n in theorem_names for n in names):
                per_row[key] = "explained"
                continue
            unbacked.append(r["test"])
        per_row[key] = "unexplained"
        if expect_cost(key) is None:
            missing_src.append(key)
    counts = {}
    for v in per_row.values():
        counts[v] = counts.get(v, 0) + 1
    exc_tok = sum(expect_cost(k) or 0 for k, v in per_row.items() if v == "unexplained")

    return {"rev": rev or "worktree", "model_files": model_files, "model": model_tok, "inputs": input_tok,
            "exceptions": exc_tok, "total": model_tok + input_tok + exc_tok, "rows": counts,
            "model_theorems": laws, "per_row": per_row, "formalized_without_theorem": unbacked[:30],
            "n_formalized_without_theorem": len(unbacked), "heldout_formalized": held_bad,
            "source_not_found": missing_src[:20], "numeral_heavy_defs": numeral_heavy[:15]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("lane", type=Path)
    ap.add_argument("--rev")
    ap.add_argument("--gate", metavar="BASE")
    ap.add_argument("--heldout", type=Path)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--manifest", default="MANIFEST",
                    help="score only manifests whose file name starts with this, e.g. MANIFEST-flex")
    a = ap.parse_args()
    global MANIFEST
    MANIFEST = a.manifest
    held = set()
    if a.heldout:
        held = {ln.split()[0] for ln in a.heldout.read_text().splitlines() if ln.strip() and not ln.startswith("#")}
    now = score(a.lane, a.rev, held)
    if a.json:
        print(json.dumps(now, indent=1))
    else:
        print(f"{now['rev']}: total {now['total']} = model {now['model']} + inputs {now['inputs']} "
              f"+ exceptions {now['exceptions']}  rows {now['rows']}")
        for k in ("formalized_without_theorem", "heldout_formalized", "source_not_found", "numeral_heavy_defs"):
            if now[k]:
                print(f"  {k}: {now[k]}")
    if not a.gate:
        return
    base = score(a.lane, a.gate, held)
    # Compare on one row set: every row in either revision. A row counts as internal only if both
    # revisions call it internal (reclassifying a row as internal does not make it free), and a row
    # missing from one revision is unexplained there. So adding rows to the manifest is neutral.
    keys = set(now["per_row"]) | set(base["per_row"])
    newly_internal = sorted(k for k in keys if now["per_row"].get(k) == "internal"
                            and base["per_row"].get(k, "internal") != "internal")
    def exc(r):
        return sum(expect_cost(k) or 0 for k in keys
                   if r["per_row"].get(k, "unexplained") != "explained"
                   and not (now["per_row"].get(k) == "internal" and base["per_row"].get(k) == "internal"))
    xn, xb = exc(now), exc(base)
    tn, tb = now["model"] + now["inputs"] + xn, base["model"] + base["inputs"] + xb
    e_now = sum(1 for k in keys if now["per_row"].get(k) == "explained")
    e_base = sum(1 for k in keys if base["per_row"].get(k) == "explained")
    lost = sorted(k for k in keys if base["per_row"].get(k) == "explained" and now["per_row"].get(k) != "explained")
    dm = now["model"] + now["inputs"] - base["model"] - base["inputs"]
    print(f"common rows {len(keys)}: {a.gate} total {tb} -> {tn} (delta {tn - tb:+d}: "
          f"model+inputs {dm:+d}, exceptions {xn - xb:+d}); explained rows {e_base} -> {e_now}")
    if xb != xn:
        print(f"model tokens added per exception token removed: {dm / (xb - xn):.2f}"
              "  (a lookup table costs about 1 or more; a general rule well under 1)")
    fail, review = [], []
    if lost:
        fail.append(f"{len(lost)} rows no longer explained: {lost[:10]}")
    if now["heldout_formalized"]:
        fail.append("held-out rows marked formalized")
    if now["n_formalized_without_theorem"] > base["n_formalized_without_theorem"]:
        fail.append("new 'formalized' rows without a matching theorem")
    if dm > 0 and e_now <= e_base:
        fail.append("model grew but explains no new rows (a definition must arrive with its tests)")
    if newly_internal:
        review.append(f"{len(newly_internal)} rows newly marked internal (still counted): {newly_internal[:10]}")
    if tn == tb and e_now == e_base and not fail:
        print("GATE NO CHANGE")
        sys.exit(0)
    if tn >= tb and not fail:
        review.append("total length went up: the model added costs more than the test results it explains so far; "
                      "acceptable only for a spec-cited definition that later tests reuse")
    for r in review:
        print("REVIEW: " + r)
    print("GATE " + ("FAIL: " + "; ".join(fail) if fail else "PASS" if tn < tb else "PASS WITH REVIEW"))
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
