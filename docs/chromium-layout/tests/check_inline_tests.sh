#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAYOUT_DIR="$(cd "$HERE/.." && pwd)"
MANIFEST="$HERE/MANIFEST-Inline.md"

if [[ ! -f "$MANIFEST" ]]; then
  echo "FAIL: Manifest not found at $MANIFEST" >&2
  exit 1
fi

python3 - "$LAYOUT_DIR" "$MANIFEST" <<'PY'
import sys
import os
import re

layout_dir, manifest_path = sys.argv[1], sys.argv[2]

# Collect all declared symbols in .lean files under layout_dir
declared_symbols = set()
for root, _, files in os.walk(layout_dir):
    for f in files:
        if f.endswith(".lean"):
            path = os.path.join(root, f)
            with open(path, "r", encoding="utf-8") as lf:
                for line in lf:
                    # Match def, theorem, inductive, structure, class declarations
                    m = re.match(r"^(?:private\s+|protected\s+)?(?:def|theorem|inductive|structure|class|abbrev)\s+([A-Za-z0-9_']+)", line.strip())
                    if m:
                        declared_symbols.add(m.group(1))

# Parse manifest
with open(manifest_path, "r", encoding="utf-8") as mf:
    lines = mf.readlines()

valid_classes = {"geometry", "behaviour", "internal"}
valid_statuses = {"formalized", "partly formalized", "blocked", "internal"}

total_rows = 0
counts = {
    "classes": {"geometry": 0, "behaviour": 0, "internal": 0},
    "statuses": {"formalized": 0, "partly formalized": 0, "blocked": 0, "internal": 0}
}
errors = []

in_table = False
header_found = False

for line_no, raw_line in enumerate(lines, 1):
    line = raw_line.strip()
    if not line.startswith("|"):
        continue
    parts = [p.strip() for p in line.split("|")[1:-1]]
    if len(parts) < 5:
        continue
    if parts[0] == "File:Line" or parts[0] == "---" or "---" in parts[0]:
        header_found = True
        continue
    if not header_found:
        continue

    # Table row: File:Line | Test Name | Class | Status | Theorem / Vector | Notes (optional)
    file_line = parts[0]
    test_name = parts[1]
    cls = parts[2].lower()
    status = parts[3].lower()
    thm = parts[4] if len(parts) > 4 else ""

    total_rows += 1
    if cls not in valid_classes:
        errors.append(f"Line {line_no}: Invalid class '{cls}' for test '{test_name}'. Must be one of {valid_classes}")
    else:
        counts["classes"][cls] += 1

    if status not in valid_statuses:
        errors.append(f"Line {line_no}: Invalid status '{status}' for test '{test_name}'. Must be one of {valid_statuses}")
    else:
        counts["statuses"][status] += 1

    if status == "formalized":
        if not thm or thm == "-":
            errors.append(f"Line {line_no}: Status is 'formalized' but no Theorem / Vector specified for test '{test_name}'")
        else:
            # thm may contain multiple comma-separated symbols or backtick symbols
            symbols = re.findall(r"([A-Za-z0-9_']+)", thm)
            missing = [s for s in symbols if s not in declared_symbols]
            if missing:
                errors.append(f"Line {line_no}: Formalized symbol(s) {missing} for test '{test_name}' not found in any Lean module under {layout_dir}")

if errors:
    print(f"FAILED with {len(errors)} error(s):", file=sys.stderr)
    for err in errors:
        print(f"  - {err}", file=sys.stderr)
    sys.exit(1)

print(f"OK: Manifest verified. Total tests: {total_rows}")
print(f"  Classes: geometry: {counts['classes']['geometry']}, behaviour: {counts['classes']['behaviour']}, internal: {counts['classes']['internal']}")
print(f"  Statuses: formalized: {counts['statuses']['formalized']}, partly formalized: {counts['statuses']['partly formalized']}, blocked: {counts['statuses']['blocked']}, internal: {counts['statuses']['internal']}")
PY
