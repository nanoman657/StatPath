#!/usr/bin/env python3
"""
Chunk the OpenStax *Introductory Statistics 2e* PDF and extract its structure.

The PDF is about 22 MB and ~900 pages, so it is processed page by page and
written out in chunks. The script produces, under data/extracted/:

  chunks/chunk_NNN.txt   plain text, CHUNK_PAGES pages per file
  toc.json               every "N.M Title" section heading found, with page
  key_terms.json         glossary-style "Term: definition" lines per chapter
  coverage_report.md     which sections in the PDF have (or lack) a lesson in
                         src/content, so the curriculum can be audited

Usage:
  pip install pypdf
  python scripts/ingest_pdf.py data/introductory-statistics-2e.pdf

Download the book (CC BY 4.0) from:
  https://assets.openstax.org/oscms-prodcms/media/documents/introductory-statistics-2e_-_WEB.pdf
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

CHUNK_PAGES = 25
SECTION_RE = re.compile(r"^(1[0-3]|[1-9])\.(\d{1,2})\s+([A-Z][^\n]{3,80})$")
CHAPTER_RE = re.compile(r"^(1[0-3]|[1-9])\s+\|\s+([A-Z][A-Z ,\-]{5,})$")
TERM_RE = re.compile(r"^([A-Z][A-Za-z' \-()]{2,40})\s+(?:—|–|-)?\s*([a-z][^\n]{20,})$")


def load_pdf(path: Path):
    try:
        from pypdf import PdfReader
    except ImportError:  # pragma: no cover
        sys.exit("pypdf is required: pip install pypdf")
    return PdfReader(str(path))


def lesson_sections_in_repo(root: Path) -> set[str]:
    """Collect section numbers (e.g. '3.2') declared in src/content/*.ts."""
    found: set[str] = set()
    for f in (root / "src" / "content").glob("ch*.ts"):
        for m in re.finditer(r'lesson\("u\d+\.\d+",\s*"(\d+\.\d+)"', f.read_text(encoding="utf-8")):
            found.add(m.group(1))
    return found


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 1
    pdf_path = Path(argv[1])
    root = Path(__file__).resolve().parent.parent
    out = root / "data" / "extracted"
    (out / "chunks").mkdir(parents=True, exist_ok=True)

    reader = load_pdf(pdf_path)
    n = len(reader.pages)
    print(f"Reading {pdf_path.name}: {n} pages, {CHUNK_PAGES} pages per chunk")

    toc: list[dict] = []
    terms: dict[str, list[dict]] = {}
    current_chapter = "0"
    buffer: list[str] = []
    chunk_idx = 0

    for i in range(n):
        try:
            text = reader.pages[i].extract_text() or ""
        except Exception as e:  # noqa: BLE001
            text = f"[extraction failed on page {i + 1}: {e}]"
        buffer.append(f"\n\n===== PAGE {i + 1} =====\n{text}")

        for line in text.splitlines():
            line = line.strip()
            ch = CHAPTER_RE.match(line)
            if ch:
                current_chapter = ch.group(1)
            sec = SECTION_RE.match(line)
            if sec:
                num = f"{sec.group(1)}.{sec.group(2)}"
                title = sec.group(3).strip()
                if not any(t["section"] == num for t in toc):
                    toc.append({"section": num, "title": title, "page": i + 1})
            term = TERM_RE.match(line)
            if term and "KEY TERMS" in text.upper():
                terms.setdefault(current_chapter, []).append({"term": term.group(1).strip(), "definition": term.group(2).strip(), "page": i + 1})

        if len(buffer) >= CHUNK_PAGES or i == n - 1:
            chunk_idx += 1
            (out / "chunks" / f"chunk_{chunk_idx:03d}.txt").write_text("".join(buffer), encoding="utf-8")
            buffer = []
            print(f"  wrote chunk {chunk_idx} (through page {i + 1})", end="\r")

    print()
    toc.sort(key=lambda t: (int(t["section"].split(".")[0]), int(t["section"].split(".")[1])))
    (out / "toc.json").write_text(json.dumps(toc, indent=2), encoding="utf-8")
    (out / "key_terms.json").write_text(json.dumps(terms, indent=2), encoding="utf-8")

    have = lesson_sections_in_repo(root)
    lines = ["# Coverage report", "", f"Sections found in PDF: {len(toc)}", f"Lessons in repo: {len(have)}", "", "| Section | Title | Lesson in StatPath? |", "|---|---|---|"]
    for t in toc:
        lines.append(f"| {t['section']} | {t['title']} | {'yes' if t['section'] in have else 'NO'} |")
    missing = [t for t in toc if t["section"] not in have]
    lines += ["", f"Missing lessons: {len(missing)}"] + [f"- {t['section']} {t['title']} (p. {t['page']})" for t in missing]
    (out / "coverage_report.md").write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {chunk_idx} chunks, {len(toc)} sections, {sum(len(v) for v in terms.values())} key terms to {out}")
    print(f"Coverage: {len(toc) - len(missing)}/{len(toc)} PDF sections have a lesson (see coverage_report.md)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
