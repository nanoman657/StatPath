#!/usr/bin/env python3
"""Re-pin report for the Chromium layout model (Roadmap Phase 9).

Compares the files pinned in pins.txt with a checkout of another Chromium revision and lists
which model functions need review. It reads only; it never edits the model, pins.txt or ROADMAP.md.

Usage:
  repin.py --new-dir NEW/third_party/blink/renderer/core/layout [--old-dir OLD/...core/layout]
           [--pins pins.txt] [--roadmap ROADMAP.md] [--manifest tests/MANIFEST-Block.md]
           [--revision SHA --write-pins OUT]

Without --old-dir, a changed file is reported by blob SHA-1 only. With --old-dir (a checkout of
the old pin), each audit row whose `file:start-end` range overlaps a changed hunk is marked
CHANGED RANGE; the other rows citing that file are marked file changed, range untouched.
Exit status: 0 = nothing pinned changed, 1 = changes to review, 2 = bad input.
"""
import argparse
import difflib
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def die(msg):
    print(f"repin.py: {msg}", file=sys.stderr)
    sys.exit(2)


def blob_sha1(path):
    data = open(path, "rb").read()
    return hashlib.sha1(f"blob {len(data)}\0".encode("ascii") + data).hexdigest()


def load_pins(path):
    pins = {}
    for line in open(path, encoding="utf-8").read().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{40}", parts[0]):
            die(f"bad line in {path}: {line}")
        pins[parts[1]] = parts[0]
    return pins


def audit_rows(roadmap_path):
    """(bend_symbol, lean_symbol, file, start, end) for each audit table row."""
    text = open(roadmap_path, encoding="utf-8").read()
    idx = text.find("### Transcription Audit Table")
    if idx < 0:
        die(f"no audit table in {roadmap_path}")
    rows, in_table = [], False
    for line in text[idx:].splitlines():
        if line.startswith("| `"):
            in_table = True
            cells = [c.strip().strip("`") for c in line.split("|")[1:-1]]
            m = re.fullmatch(r"(.+):(\d+)-(\d+)", cells[2])
            if len(cells) == 6 and m:
                rows.append((cells[0], cells[1], m.group(1), int(m.group(2)), int(m.group(3))))
        elif in_table and not line.startswith("|"):
            break
    return rows


def manifest_rows(path):
    """(file, line, test name) for each manifest row; empty if the manifest is absent."""
    if not os.path.isfile(path):
        return []
    rows = []
    for line in open(path, encoding="utf-8"):
        if not line.startswith("| "):
            continue
        c = [x.strip() for x in line.strip().strip("|").split("|")]
        if len(c) >= 2 and re.fullmatch(r"[\w/.\-]+:\d+", c[0]):
            f, n = c[0].rsplit(":", 1)
            rows.append((f, int(n), c[1]))
    return rows


def changed_old_lines(old_path, new_path):
    """Set of 1-based line numbers of the old file that were replaced or deleted."""
    old = open(old_path, encoding="utf-8", errors="replace").read().split("\n")
    new = open(new_path, encoding="utf-8", errors="replace").read().split("\n")
    out = set()
    for tag, i1, i2, _, _ in difflib.SequenceMatcher(None, old, new, autojunk=False).get_opcodes():
        if tag in ("replace", "delete"):
            out.update(range(i1 + 1, i2 + 1))
        elif tag == "insert":
            # An insertion inside a range changes it; mark the neighbouring old lines.
            out.update({i1, i1 + 1})
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--new-dir", required=True)
    ap.add_argument("--old-dir")
    ap.add_argument("--pins", default=os.path.join(HERE, "pins.txt"))
    ap.add_argument("--roadmap", default=os.path.join(HERE, "ROADMAP.md"))
    ap.add_argument("--manifest", default=os.path.join(HERE, "tests", "MANIFEST-Block.md"))
    ap.add_argument("--revision", help="new revision SHA, used only with --write-pins")
    ap.add_argument("--write-pins", help="write a pins file for the new checkout to this path")
    a = ap.parse_args()

    if not os.path.isdir(a.new_dir):
        die(f"--new-dir is not a directory: {a.new_dir}")
    if a.old_dir and not os.path.isdir(a.old_dir):
        die(f"--old-dir is not a directory: {a.old_dir}")
    if a.write_pins and not re.fullmatch(r"[0-9a-f]{40}", a.revision or ""):
        die("--write-pins needs --revision with a 40-character SHA")

    pins = load_pins(a.pins)
    rows = audit_rows(a.roadmap)
    mrows = manifest_rows(a.manifest)

    changed, missing, same = [], [], 0
    new_sha = {}
    for rel, old_sha in sorted(pins.items()):
        p = os.path.join(a.new_dir, rel)
        if not os.path.isfile(p):
            missing.append(rel)
            continue
        new_sha[rel] = blob_sha1(p)
        if new_sha[rel] == old_sha:
            same += 1
        else:
            changed.append(rel)

    print(f"pinned files: {len(pins)}  unchanged: {same}  changed: {len(changed)}  missing: {len(missing)}")
    for rel in missing:
        print(f"MISSING  {rel}  (renamed or removed: find its new location, update pins.txt and the audit rows)")

    for rel in changed:
        print(f"CHANGED  {rel}")
        lines = None
        if a.old_dir and os.path.isfile(os.path.join(a.old_dir, rel)):
            lines = changed_old_lines(os.path.join(a.old_dir, rel), os.path.join(a.new_dir, rel))
        for bend, lean, f, s, e in rows:
            if f != rel:
                continue
            if lines is None:
                state = "review"
            elif any(s <= n <= e for n in lines):
                state = "CHANGED RANGE"
            else:
                state = "file changed, range untouched (line numbers may have moved)"
            print(f"    audit row  {bend} / {lean}  {f}:{s}-{e}  [{state}]")
        for f, n, name in mrows:
            if f == rel:
                moved = "" if lines is None else ("  [CHANGED LINE]" if n in lines else "")
                print(f"    manifest   {f}:{n}  {name}{moved}")

    if a.write_pins:
        with open(a.write_pins, "w", encoding="utf-8") as fh:
            fh.write(f"# Pinned Chromium revision: {a.revision}\n")
            fh.write("# Subtree: third_party/blink/renderer/core/layout/\n")
            fh.write("# Format: <git-blob-sha1>  <path-under-core/layout>\n")
            for rel in sorted(new_sha):
                fh.write(f"{new_sha[rel]}  {rel}\n")
        print(f"wrote {a.write_pins} ({len(new_sha)} files)")

    if changed or missing:
        print("Next: update the C++ anchors and slice digests of every flagged audit row, re-run "
              "check.sh and model_vectors.py against the new pin, then add a changelog line to ROADMAP.md.")
        return 1
    print("No pinned file changed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
