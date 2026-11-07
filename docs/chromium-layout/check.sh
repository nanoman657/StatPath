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

# 2, 3, 4. Check all .lean files with `lean <file>` and verify `#print axioms` on every theorem
mapfile -t LEAN_FILES < <(find "$HERE" -name '*.lean' -type f | sort)
if [[ "${#LEAN_FILES[@]}" -eq 0 ]]; then
  echo "FAIL: no .lean files found under $HERE" >&2
  exit 1
fi

for lf in "${LEAN_FILES[@]}"; do
  rel="${lf#"$HERE"/}"
  echo "== Checking Lean file: $rel"
  python3 - "$lf" "$LEAN_BIN" "$TMP_DIR" <<'PY'
import os
import re
import subprocess
import sys

lean_file, lean_bin, tmp_dir = sys.argv[1], sys.argv[2], sys.argv[3]
with open(lean_file, "r", encoding="utf-8") as f:
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

# Compile the file with `#print axioms` appended for every theorem in a single pass
if theorems:
    aug_path = os.path.join(tmp_dir, os.path.basename(lean_file))
    extra = "\n".join(f"#print axioms {t}" for t in theorems)
    with open(aug_path, "w", encoding="utf-8") as f:
        f.write(src + "\n\n" + extra + "\n")
    res = subprocess.run(["nice", "-n", "19", lean_bin, aug_path], capture_output=True, text=True)
    out = res.stdout + res.stderr
    if res.returncode != 0:
        sys.stderr.write(out)
        sys.exit(f"FAIL: lean exited with {res.returncode} on {lean_file}")
else:
    res = subprocess.run(["nice", "-n", "19", lean_bin, lean_file], capture_output=True, text=True)
    out = res.stdout + res.stderr
    if res.returncode != 0:
        sys.stderr.write(out)
        sys.exit(f"FAIL: lean exited with {res.returncode} on {lean_file}")

if "sorryAx" in out or "declaration uses 'sorry'" in out:
    sys.stderr.write(out)
    sys.exit(f"FAIL: sorryAx detected in {lean_file}")

allowed = {"propext", "Classical.choice", "Quot.sound"}
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
            sys.exit(f"FAIL: disallowed axioms {bad} on theorem {tname} in {lean_file}")

missing = [t for t in theorems if t not in seen_theorems]
if missing:
    sys.stderr.write(out)
    sys.exit(f"FAIL: missing #print axioms output for theorems {missing} in {lean_file}")

print(f"OK: {os.path.basename(lean_file)} ({len(theorems)} theorems checked; no sorryAx; allowed axioms only)")
PY
done

echo "== ALL CHECKS PASSED"
