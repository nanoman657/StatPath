#!/usr/bin/env bash
# Manifest gate for the block lane (docs/chromium-layout/tests/MANIFEST-Block.md).
# Checks: every row's file:line is a TEST/TEST_F/TEST_P in the pinned Chromium checkout; every
# test of each file that has rows has exactly one row; class and status are valid; blocked rows
# give a reason; every formalized / partly formalized row names theorems or defs that exist in
# a .lean file under docs/chromium-layout/. Lean compilation and `#print axioms` are done by
# check.sh itself over all modules (including tests/).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CHROMIUM_LAYOUT="${CHROMIUM_LAYOUT:-/root/agy-scratch/chromium-layout/chromium/third_party/blink/renderer/core/layout}"
python3 - "$HERE" "$CHROMIUM_LAYOUT" <<'PY'
import os, re, sys
here, root = sys.argv[1], sys.argv[2]
model = os.path.dirname(here)
manifest = os.path.join(here, "MANIFEST-Block.md")
names = set()
for base, _, files in os.walk(model):
    for fn in files:
        if fn.endswith(".lean"):
            src = open(os.path.join(base, fn), encoding="utf-8").read()
            for m in re.finditer(r"^\s*(?:private\s+|protected\s+)?(?:theorem|def|lemma|abbrev)\s+([A-Za-z0-9_'.]+)", src, re.M):
                names.add(m.group(1))
def exists(q):
    last = q.split(".")[-1]
    return any(n == q or n.split(".")[-1] == last for n in names)
CLASSES = {"geometry", "behaviour", "internal"}
STATUSES = {"formalized", "partly formalized", "blocked", "internal"}
rows = {}
errs = []
for ln, line in enumerate(open(manifest, encoding="utf-8"), 1):
    if not line.startswith("| ") or line.startswith("| file:line") or line.startswith("|---") or line.startswith("| ---"):
        continue
    c = [x.strip() for x in line.strip().strip("|").split("|")]
    if len(c) < 5 or ":" not in c[0] or not re.match(r"^[\w/.\-]+:\d+$", c[0]):
        continue
    loc, name, cls, st, ev = c[0], c[1], c[2], c[3], "|".join(c[4:])
    f, n = loc.rsplit(":", 1)
    rows.setdefault(f, []).append((int(n), name, cls, st, ev, ln))
nform = nblock = nint = 0
for f, rs in rows.items():
    src = open(os.path.join(root, f), encoding="utf-8").read().split("\n")
    macros = {i + 1 for i, l in enumerate(src) if re.match(r"^[ \t]*(TEST|TEST_F|TEST_P)\(", l)}
    got = [r[0] for r in rs]
    if sorted(got) != sorted(macros):
        errs.append(f"{f}: manifest lines {sorted(set(macros)-set(got))} missing / {sorted(set(got)-macros)} not TEST macros / duplicates")
    for n, name, cls, st, ev, ln in rs:
        if cls not in CLASSES: errs.append(f"{f}:{n}: bad class {cls}")
        if st not in STATUSES: errs.append(f"{f}:{n}: bad status {st}")
        if (cls == "internal") != (st == "internal"): errs.append(f"{f}:{n}: class/status internal mismatch")
        if st in ("formalized", "partly formalized"):
            nform += 1
            refs = re.findall(r"`([^`]+)`", ev)
            if not refs: errs.append(f"{f}:{n}: formalized row names no theorem/vector")
            for q in refs:
                if not exists(q): errs.append(f"{f}:{n}: `{q}` not found in any .lean file")
        elif st == "blocked":
            nblock += 1
            if len(ev.strip()) < 8: errs.append(f"{f}:{n}: blocked row without reason")
        else:
            nint += 1
            if len(ev.strip()) < 8: errs.append(f"{f}:{n}: internal row without reason")
if errs:
    print("\n".join(errs)); sys.exit("FAIL: manifest check")
total = sum(len(r) for r in rows.values())
print(f"OK: MANIFEST-Block.md: {len(rows)} test files, {total} rows ({nform} formalized/partly, {nblock} blocked, {nint} internal); every formalized row names an existing theorem or vector")
PY
