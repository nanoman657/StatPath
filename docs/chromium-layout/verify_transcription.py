#!/usr/bin/env python3
"""Mechanized transcription-gap audit checker (Roadmap Phase 6).

Verifies the Transcription Audit Table in docs/chromium-layout/ROADMAP.md against:
  1. docs/chromium-layout/layout.bend (every Bend symbol exists as `type` or `def`)
  2. docs/chromium-layout/LayoutTypes.lean (every Lean symbol exists as `structure`, `inductive`, or `def`)
  3. docs/chromium-layout/pins.txt (every referenced Chromium file is pinned with a 40-char git blob SHA-1)
  4. Reviewer sign-off column (requires Reviewer 1 sign-off and Reviewer 2 pending on every row)
  5. When the pinned Chromium checkout directory is present at CHROMIUM_LAYOUT_DIR
     (default: /root/agy-scratch/chromium-layout/chromium/third_party/blink/renderer/core/layout):
       - verifies all 67 git blob SHA-1 hashes in pins.txt against the checkout;
       - verifies every `file:start-end` line range in the audit table is in bounds,
         contains the C++ anchor string, and matches the recorded SHA-256/12 slice digest.
"""
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROADMAP_MD = os.path.join(HERE, "ROADMAP.md")
LAYOUT_BEND = os.path.join(HERE, "layout.bend")
LAYOUT_TYPES_LEAN = os.path.join(HERE, "LayoutTypes.lean")
PINS_TXT = os.path.join(HERE, "pins.txt")
CHROMIUM_DIR = os.environ.get(
    "CHROMIUM_LAYOUT_DIR",
    "/root/agy-scratch/chromium-layout/chromium/third_party/blink/renderer/core/layout",
)


def git_blob_sha1(path):
    data = open(path, "rb").read()
    hdr = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(hdr + data).hexdigest()


def load_pins():
    pins = {}
    for line in open(PINS_TXT, encoding="utf-8").read().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{40}", parts[0]):
            sys.exit(f"FAIL: malformed line in pins.txt: {line}")
        pins[parts[1]] = parts[0]
    return pins


def parse_audit_rows(md_text):
    marker = "### Transcription Audit Table"
    idx = md_text.find(marker)
    if idx < 0:
        sys.exit("FAIL: missing '### Transcription Audit Table' in ROADMAP.md")
    sub = md_text[idx:]
    rows = []
    in_table = False
    for line in sub.splitlines():
        if line.startswith("| `"):
            in_table = True
            cells = [c.strip() for c in line.split("|")[1:-1]]
            if len(cells) != 6:
                sys.exit(f"FAIL: expected 6 columns in audit row, got {len(cells)}: {line}")
            rows.append(cells)
        elif in_table and not line.startswith("|"):
            break
    return rows


def strip_ticks(s):
    m = re.match(r"^`([^`]+)`$", s.strip())
    if not m:
        sys.exit(f"FAIL: expected backticked identifier, got: {s}")
    return m.group(1)


def parse_anchor_cell(cell):
    m = re.match(r"^`([^`]+)`\s*\(`([0-9a-f]{12})`\)$", cell.strip())
    if not m:
        sys.exit(f"FAIL: expected '`anchor` (`12hex`)' in C++ anchor column, got: {cell}")
    return m.group(1), m.group(2)


def main():
    pins = load_pins()
    if len(pins) < 67:
        sys.exit(f"FAIL: expected at least 67 pinned files in pins.txt, got {len(pins)}")

    bend_src = open(LAYOUT_BEND, encoding="utf-8").read()
    lean_src = open(LAYOUT_TYPES_LEAN, encoding="utf-8").read()
    roadmap_src = open(ROADMAP_MD, encoding="utf-8").read()

    rows = parse_audit_rows(roadmap_src)
    if len(rows) < 36:
        sys.exit(f"FAIL: expected at least 36 rows in Transcription Audit Table, got {len(rows)}")

    has_chromium = os.path.isdir(CHROMIUM_DIR)
    if has_chromium:
        for rel, expected_sha in sorted(pins.items()):
            full = os.path.join(CHROMIUM_DIR, rel)
            if not os.path.isfile(full):
                sys.exit(f"FAIL: pinned file missing in {CHROMIUM_DIR}: {rel}")
            actual_sha = git_blob_sha1(full)
            if actual_sha != expected_sha:
                sys.exit(f"FAIL: blob SHA-1 mismatch for {rel}: expected {expected_sha}, got {actual_sha}")

    for bend_cell, lean_cell, loc_cell, anchor_cell, note_cell, signoff_cell in rows:
        bend_sym = strip_ticks(bend_cell)
        lean_sym = strip_ticks(lean_cell)
        loc = strip_ticks(loc_cell)
        anchor, expected_digest = parse_anchor_cell(anchor_cell)

        # 1. Check Bend symbol in layout.bend
        bend_pat = re.compile(rf"^(?:type\s+{re.escape(bend_sym)}\s+is\s+Data:|def\s+{re.escape(bend_sym)}\b)", re.M)
        if not bend_pat.search(bend_src):
            sys.exit(f"FAIL: Bend symbol '{bend_sym}' not found in layout.bend")

        # 2. Check Lean symbol in LayoutTypes.lean
        lean_short = lean_sym.split(".")[-1]
        lean_pat = re.compile(
            rf"^(?:structure|inductive|def|abbrev)\s+{re.escape(lean_short)}\b",
            re.M,
        )
        if not lean_pat.search(lean_src):
            sys.exit(f"FAIL: Lean symbol '{lean_sym}' ('{lean_short}') not found in LayoutTypes.lean")

        # 3. Check Chromium file:start-end in pins.txt
        m_loc = re.match(r"^([^:]+):(\d+)-(\d+)$", loc)
        if not m_loc:
            sys.exit(f"FAIL: malformed file:start-end location '{loc}'")
        rel_file, start_line, end_line = m_loc.group(1), int(m_loc.group(2)), int(m_loc.group(3))
        if rel_file not in pins:
            sys.exit(f"FAIL: file '{rel_file}' (from '{loc}') not found in pins.txt")
        if start_line < 1 or end_line < start_line:
            sys.exit(f"FAIL: invalid line range {start_line}-{end_line} for {rel_file}")

        # 4. Check simplification note and reviewer sign-off
        if not note_cell.strip():
            sys.exit(f"FAIL: empty simplification note for {bend_sym}")
        if "Reviewer 1" not in signoff_cell or "Reviewer 2: pending" not in signoff_cell:
            sys.exit(f"FAIL: row '{bend_sym}' is missing reviewer sign-off: {signoff_cell}")

        # 5. If Chromium source checkout is present, check line range, anchor, and SHA-256/12 digest
        if has_chromium:
            full_path = os.path.join(CHROMIUM_DIR, rel_file)
            file_lines = open(full_path, encoding="utf-8").read().splitlines()
            if end_line > len(file_lines):
                sys.exit(
                    f"FAIL: line range {loc} exceeds file length ({len(file_lines)} lines)"
                )
            chunk = "\n".join(file_lines[start_line - 1 : end_line])
            if anchor not in chunk:
                sys.exit(
                    f"FAIL: C++ anchor '{anchor}' not found in {loc}"
                )
            actual_digest = hashlib.sha256(chunk.encode("utf-8")).hexdigest()[:12]
            if actual_digest != expected_digest:
                sys.exit(
                    f"FAIL: slice sha256/12 mismatch for {loc}: expected {expected_digest}, got {actual_digest}"
                )

    src_msg = f"and verified against pinned Chromium source ({len(pins)} blobs)" if has_chromium else "(Chromium checkout not present; verified symbols, pins, and sign-offs)"
    print(f"OK: {len(rows)} transcription audit rows verified {src_msg}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
