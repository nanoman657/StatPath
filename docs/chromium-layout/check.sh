#!/usr/bin/env bash
# Check script for docs/chromium-layout/ (Roadmap P0.4):
# 1. Runs `bend <file> --verdict` on each Bend file and requires `ALL PROOFS CHECK`.
# 2. Runs `lean <file>` on each Lean file and requires exit 0.
# 3. Appends `#print axioms` for every `theorem` in each Lean file and fails on `sorryAx`.
# 4. Fails on any axiom outside `propext`, `Classical.choice`, `Quot.sound`.

set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BEND_BIN="${BEND_BIN:-/root/.bend/bin/bend}"
LEAN_BIN="${LEAN_BIN:-/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean}"
LEAN_STACK_CAP_KB="${LEAN_STACK_SIZE_KB:-262144}"

if [[ ! -x "$BEND_BIN" ]]; then
  echo "FAIL: bend binary not found at $BEND_BIN" >&2
  exit 1
fi

if [[ ! -x "$LEAN_BIN" ]]; then
  echo "FAIL: lean binary not found at $LEAN_BIN" >&2
  exit 1
fi

LEAN_VER="$("$LEAN_BIN" --version | head -n 1)"
if [[ "$LEAN_VER" != *"version 4.34.0"* ]]; then
  echo "FAIL: expected Lean 4.34.0, got: $LEAN_VER" >&2
  exit 1
fi
echo "== Toolchain: $LEAN_VER"

TMP_DIR="$(mktemp -d /tmp/chromium-layout-check.XXXXXX)"
cleanup() {
  rm -rf "$TMP_DIR"
}
trap cleanup EXIT

# Set up BENDTT stack-size wrapper (Roadmap P0.1 Q5) so `bend --verdict`'s
# hardcoded LEAN_STACK_SIZE_KB=4194304 does not exceed the 900 MB cgroup cap.
if [[ -z "${BENDTT:-}" ]]; then
  BENDTT_BIN="$(find /root/.bend/bendtt -name 'bendtt.bin' -type f 2>/dev/null | head -n 1 || true)"
  if [[ -n "$BENDTT_BIN" ]]; then
    WRAPPER="$TMP_DIR/bendtt-wrapper.sh"
    cat > "$WRAPPER" <<EOF
#!/bin/sh
export LEAN_STACK_SIZE_KB="$LEAN_STACK_CAP_KB"
exec "$BENDTT_BIN" "\$@"
EOF
    chmod +x "$WRAPPER"
    export BENDTT="$WRAPPER"
  fi
fi

# 1. Check all .bend files with `bend <file> --verdict`
mapfile -t BEND_FILES < <(find "$HERE" -name '*.bend' -type f | sort)
if [[ "${#BEND_FILES[@]}" -eq 0 ]]; then
  echo "FAIL: no .bend files found under $HERE" >&2
  exit 1
fi

for bf in "${BEND_FILES[@]}"; do
  rel="${bf#"$HERE"/}"
  echo "== Checking Bend file (verdict): $rel"
  out="$(nice -n 19 "$BEND_BIN" "$bf" --verdict 2>&1)" || {
    echo "$out" >&2
    echo "FAIL: bend --verdict exited non-zero on $rel" >&2
    exit 1
  }
  echo "$out"
  if [[ "$out" != *"ALL PROOFS CHECK"* ]]; then
    echo "FAIL: bend --verdict did not print ALL PROOFS CHECK on $rel" >&2
    exit 1
  fi
done

# 2, 3, 4. Check all .lean files one at a time in topological import order with
# `lean -j 1 -o <OLEAN_DIR>/<Mod>.olean <Mod>.lean` and `LEAN_PATH=<OLEAN_DIR>`
# (keeping every single `lean` invocation well below 600 MB peak RSS),
# and verify `#print axioms` on every theorem.
OLEAN_DIR="${OLEAN_DIR:-/root/agy-scratch/chromium-layout/olean}"
mkdir -p "$OLEAN_DIR"
export LEAN_PATH="$OLEAN_DIR"

python3 - "$HERE" "$LEAN_BIN" "$TMP_DIR" "$OLEAN_DIR" <<'PY'
import os
import re
import subprocess
import sys

here, lean_bin, tmp_dir, olean_dir = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]

# Discover all .lean files under `here`
lean_files = []
for root, _, files in os.walk(here):
    for fn in files:
        if fn.endswith(".lean"):
            lean_files.append(os.path.join(root, fn))
lean_files.sort()

if not lean_files:
    sys.exit(f"FAIL: no .lean files found under {here}")

# Build module map and topological order by `import <Mod>`
mod_to_path = {}
deps = {}
for lf in lean_files:
    mod = os.path.splitext(os.path.basename(lf))[0]
    mod_to_path[mod] = lf
    with open(lf, "r", encoding="utf-8") as f:
        src = f.read()
    imp = []
    for raw_line in src.splitlines():
        line = re.sub(r"--.*$", "", raw_line).strip()
        m_imp = re.match(r"^import\s+([A-Za-z0-9_'.]+)", line)
        if m_imp:
            imp.append(m_imp.group(1))
    deps[lf] = imp

visited = set()
ordered_files = []

def visit(lf):
    if lf in visited:
        return
    visited.add(lf)
    for d in deps.get(lf, []):
        if d in mod_to_path:
            visit(mod_to_path[d])
    ordered_files.append(lf)

for lf in lean_files:
    visit(lf)

env = dict(os.environ, LEAN_PATH=olean_dir)
allowed = {"propext", "Classical.choice", "Quot.sound"}

for lf in ordered_files:
    rel = os.path.relpath(lf, here)
    mod = os.path.splitext(os.path.basename(lf))[0]
    olean_out = os.path.join(olean_dir, f"{mod}.olean")
    print(f"== Checking Lean file: {rel} -> {olean_out}", flush=True)
    with open(lf, "r", encoding="utf-8") as f:
        src = f.read()

    # Extract theorems and track namespace stack so `#print axioms` can be appended at EOF
    ns_stack = []
    theorems = []
    for raw_line in src.splitlines():
        line = re.sub(r"--.*$", "", raw_line).strip()
        m_ns = re.match(r"^namespace\s+([A-Za-z0-9_.]+)", line)
        if m_ns:
            ns_stack.append(m_ns.group(1))
            continue
        m_end = re.match(r"^end\s+([A-Za-z0-9_.]+)", line)
        if m_end and ns_stack:
            ns_stack.pop()
            continue
        m_thm = re.match(r"^(?:private\s+|protected\s+)?theorem\s+([A-Za-z0-9_']+)", line)
        if m_thm:
            tname = m_thm.group(1)
            prefix = ".".join(ns_stack)
            fqname = f"{prefix}.{tname}" if prefix else tname
            theorems.append(fqname)

    if theorems:
        aug_path = os.path.join(tmp_dir, os.path.basename(lf))
        extra = "\n".join(f"#print axioms {t}" for t in theorems)
        with open(aug_path, "w", encoding="utf-8") as f:
            f.write(src + "\n\n" + extra + "\n")
        cmd = ["nice", "-n", "19", lean_bin, "-j", "1", "-R", tmp_dir, "-o", olean_out, aug_path]
    else:
        cmd = ["nice", "-n", "19", lean_bin, "-j", "1", "-R", os.path.dirname(lf), "-o", olean_out, lf]

    res = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        env=env,
    )
    out = res.stdout + res.stderr
    if res.returncode != 0:
        sys.stderr.write(out)
        sys.exit(f"FAIL: lean exited with {res.returncode} on {lf}")

    if "sorryAx" in out or "declaration uses 'sorry'" in out:
        sys.stderr.write(out)
        sys.exit(f"FAIL: sorryAx detected in {lf}")

    seen_theorems = set()
    for line in out.splitlines():
        m_none = re.match(r"^'([^']+)' does not depend on any axioms$", line.strip())
        if m_none:
            seen_theorems.add(m_none.group(1))
            continue
        m_dep = re.match(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]$", line.strip())
        if m_dep:
            tname = m_dep.group(1)
            seen_theorems.add(tname)
            axioms = [a.strip() for a in m_dep.group(2).split(",") if a.strip()]
            bad = [a for a in axioms if a not in allowed]
            if bad:
                sys.stderr.write(out)
                sys.exit(f"FAIL: disallowed axioms {bad} on theorem {tname} in {lf}")

    missing = [t for t in theorems if t not in seen_theorems]
    if missing:
        sys.stderr.write(out)
        sys.exit(f"FAIL: missing #print axioms output for theorems {missing} in {lf}")

    print(
        f"OK: {rel} ({len(theorems)} theorems checked; no sorryAx; allowed axioms only)",
        flush=True,
    )
PY

if [[ -f "$HERE/verify_transcription.py" ]]; then
  echo "== Checking Phase 6 transcription audit table"
  python3 "$HERE/verify_transcription.py"
fi

if [[ -f "$HERE/tests/check_tests.sh" ]]; then
  echo "== Checking block-lane test manifest"
  bash "$HERE/tests/check_tests.sh"
fi

echo "== ALL CHECKS PASSED"
