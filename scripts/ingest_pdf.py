#!/usr/bin/env python3
"""
Chunk the OpenStax *Introductory Statistics 2e* PDF (whole, or split into
parts) and extract its structure for grounding StatPath.

Outputs under data/extracted/:

  chunks/chunk_NNN.txt   plain text, CHUNK_PAGES pages per file
  book_pages.json        chapter and section start pages from the table of
                         contents (printed page numbers)
  sections/<num>.txt     each section's text, split using the running headers
                         (only for the pages that were supplied)
  key_terms.json         "Key Terms" entries per chapter (term names only)
  coverage_report.md     sections and terms vs. the lessons in src/content

Usage:
  pip install pymupdf            # or pypdf
  python scripts/ingest_pdf.py part1.pdf part2.pdf ...   # parts in order
  python scripts/ingest_pdf.py book.pdf --write-ts      # also regenerate
                                                        # src/content/bookPages.ts

The book is CC BY 4.0. Its text is used for auditing only and is not copied
into the repository (data/ is git-ignored).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import OrderedDict
from pathlib import Path

CHUNK_PAGES = 25
SEC_TOC = re.compile(r"^\s*(1[0-3]|[1-9])\.(\d{1,2})\s+(.+?)\s+(\d{1,3})\s*$")
HDR_ODD = re.compile(r"^(\d{1,2}\.\d{1,2}) • (.+?)\s+(\d{1,3})\s*$")
HDR_EVEN = re.compile(r"^(\d{1,3})\s+(\d{1,2}) • (.+?)\s*$")
HDR_END = re.compile(r"^(\d{1,2}) • (Key Terms|Chapter Review|Formula Review|Practice|Homework|References|Solutions|Bringing It Together: Practice|Bringing It Together: Homework)\s+(\d{1,3})\s*$")
# A key-term entry is a Title-Case term (small connecting words allowed) followed
# by a lowercase definition on the same line, e.g. "Error Bound for a Population Mean (EBM) the margin…".
KEY_TERM = re.compile(r"^((?:[A-Z][A-Za-z'’\-]*|of|for|a|an|the|and|or|to|in|with|vs\.?|\([A-Za-z]+\))(?: (?:[A-Z][A-Za-z'’\-]*|of|for|a|an|the|and|or|to|in|with|vs\.?|\([A-Za-z]+\))){0,6})\s+(?:[a-z(]|[A-Z][a-z]+ [a-z])")
SENTENCE_STARTERS = {"An", "A", "The", "To", "If", "In", "For", "When", "This", "These", "There", "It", "We", "You", "As", "By", "On", "At"}


def page_texts(path: Path) -> list[str]:
    try:
        import pymupdf  # type: ignore
        doc = pymupdf.open(str(path))
        return [page.get_text() for page in doc]
    except ImportError:
        pass
    try:
        from pypdf import PdfReader  # type: ignore
    except ImportError:
        sys.exit("Install pymupdf (preferred) or pypdf: pip install pymupdf")
    r = PdfReader(str(path))
    return [(p.extract_text() or "") for p in r.pages]


def running_header(text: str) -> tuple[int | None, str | None]:
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    for l in lines[-3:]:
        m = HDR_ODD.match(l) or HDR_END.match(l)
        if m:
            return int(m.group(3)), f"{m.group(1)} {m.group(2)}"
        m = HDR_EVEN.match(l)
        if m:
            return int(m.group(1)), f"ch{m.group(2)} {m.group(3)}"
    return None, None


def parse_toc(pages: list[str]) -> tuple[dict[int, dict], dict[str, dict]]:
    chapters: dict[int, dict] = {}
    sections: dict[str, dict] = {}
    for text in pages[:15]:
        lines = [l.strip() for l in text.splitlines() if l.strip()]
        for i, l in enumerate(lines):
            m = SEC_TOC.match(l)
            if m:
                sections.setdefault(f"{m.group(1)}.{m.group(2)}", {"title": m.group(3).strip(), "start": int(m.group(4))})
            m = re.match(r"^Introduction (\d{1,3})$", l)
            if m and i >= 2 and re.match(r"^\d{1,2}$", lines[i - 1]):
                chapters[int(lines[i - 1])] = {"title": lines[i - 2].rsplit(" ", 1)[0], "start": int(m.group(1))}
    order = sorted(sections, key=lambda k: (int(k.split(".")[0]), int(k.split(".")[1])))
    for i, k in enumerate(order):
        ch = int(k.split(".")[0])
        nxt = order[i + 1] if i + 1 < len(order) else None
        if nxt and int(nxt.split(".")[0]) == ch:
            end = sections[nxt]["start"] - 1
        elif ch + 1 in chapters:
            end = chapters[ch + 1]["start"] - 1
        else:
            end = sections[k]["start"]
        sections[k]["end"] = max(end, sections[k]["start"])
    return chapters, sections


def write_ts(root: Path, chapters: dict[int, dict], sections: dict[str, dict]) -> None:
    def slug(num: str, title: str) -> str:
        s = num.replace(".", "-") + "-" + "".join(c if c.isalnum() else "-" for c in title.lower()).strip("-")
        while "--" in s:
            s = s.replace("--", "-")
        return s
    order = sorted(sections, key=lambda k: (int(k.split(".")[0]), int(k.split(".")[1])))
    rows = "\n".join(f'  "{k}": {{ title: {json.dumps(sections[k]["title"])}, start: {sections[k]["start"]}, end: {sections[k]["end"]}, url: "https://openstax.org/books/introductory-statistics-2e/pages/{slug(k, sections[k]["title"])}" }},' for k in order)
    ch = "\n".join(f"  {k}: {v['start']}," for k, v in sorted(chapters.items()))
    src = f'''/**
 * Page index for OpenStax *Introductory Statistics 2e* (WEB PDF), generated by
 * scripts/ingest_pdf.py from the book's table of contents. `start`/`end` are
 * printed page numbers. The URL points at the same section online.
 */
export interface BookSection {{
  title: string;
  start: number;
  end: number;
  url: string;
}}

export const BOOK_TITLE = "Introductory Statistics 2e (OpenStax)";
export const BOOK_URL = "https://openstax.org/books/introductory-statistics-2e";

export const bookSections: Record<string, BookSection> = {{
{rows}
}};

export const chapterStart: Record<number, number> = {{
{ch}
}};

/** Page range covered by a whole chapter (its numbered sections). */
export const chapterPages = (n: number): {{ start: number; end: number }} | undefined => {{
  const secs = Object.entries(bookSections).filter(([k]) => k.startsWith(`${{n}}.`)).map(([, v]) => v);
  if (!secs.length) return undefined;
  return {{ start: Math.min(...secs.map((s) => s.start)), end: Math.max(...secs.map((s) => s.end)) }};
}};
'''
    (root / "src" / "content" / "bookPages.ts").write_text(src, encoding="utf-8")


def repo_lessons(root: Path) -> dict[str, str]:
    found: dict[str, str] = {}
    for f in sorted((root / "src" / "content").glob("ch*.ts")):
        for m in re.finditer(r'lesson\("u\d+\.\d+",\s*"(\d+\.\d+)",\s*"([^"]+)"', f.read_text(encoding="utf-8")):
            found[m.group(1)] = m.group(2)
    return found


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pdfs", nargs="+", type=Path, help="the PDF, or its parts in order")
    ap.add_argument("--write-ts", action="store_true", help="regenerate src/content/bookPages.ts from the TOC")
    args = ap.parse_args(argv[1:])
    root = Path(__file__).resolve().parent.parent
    out = root / "data" / "extracted"
    (out / "chunks").mkdir(parents=True, exist_ok=True)
    (out / "sections").mkdir(parents=True, exist_ok=True)

    pages: list[str] = []
    for p in args.pdfs:
        t = page_texts(p)
        print(f"{p.name}: {len(t)} pages")
        pages += t
    for i in range(0, len(pages), CHUNK_PAGES):
        (out / "chunks" / f"chunk_{i // CHUNK_PAGES + 1:03d}.txt").write_text("".join(f"\n\n===== PDF PAGE {i + j + 1} =====\n{t}" for j, t in enumerate(pages[i:i + CHUNK_PAGES])), encoding="utf-8")

    chapters, sections = parse_toc(pages)
    if sections:
        (out / "book_pages.json").write_text(json.dumps({"chapters": chapters, "sections": sections}, indent=1), encoding="utf-8")
        if args.write_ts:
            write_ts(root, chapters, sections)
            print("wrote src/content/bookPages.ts")
    else:
        print("No table of contents found in these pages (supply the part containing the front matter to get page ranges).")

    by_label: OrderedDict[str, list[str]] = OrderedDict()
    printed: list[int] = []
    key_terms: dict[str, list[str]] = {}
    for t in pages:
        pg, label = running_header(t)
        if pg is None:
            continue
        printed.append(pg)
        by_label.setdefault(label, []).append(t)
        m = re.match(r"^(?:ch)?(\d{1,2}) Key Terms$", label or "")
        if m:
            # only the glossary itself: stop at the Chapter Review heading that shares the page
            glossary = t.split("\nChapter Review")[0]
            for line in glossary.splitlines():
                km = KEY_TERM.match(line.strip())
                if km and not line.strip().startswith("Key Terms"):
                    words = km.group(1).strip().split()
                    # the definition's first article can be swallowed by the term match; trim trailing small words
                    while words and words[-1].islower():
                        words.pop()
                    if not words or len(words) > 6:
                        continue
                    # skip ordinary sentences ("An important parameter…", "To assess whether…")
                    if words[0] in SENTENCE_STARTERS and (len(words) < 2 or words[1][0].islower()):
                        continue
                    if not any(w[0].isupper() and len(w) >= 3 for w in words):
                        continue
                    key_terms.setdefault(m.group(1), []).append(" ".join(words))
    for label, texts in by_label.items():
        fn = re.sub(r"[^A-Za-z0-9.]+", "_", label)[:60]
        (out / "sections" / f"{fn}.txt").write_text("\n\n".join(texts), encoding="utf-8")
    (out / "key_terms.json").write_text(json.dumps(key_terms, indent=1), encoding="utf-8")

    lessons = repo_lessons(root)
    src_text = "\n".join(f.read_text(encoding="utf-8") for f in (root / "src").rglob("*.ts")).lower()
    present = {l.split(" ")[0] for l in by_label if re.match(r"^\d+\.\d+ ", l)}
    lines = ["# Coverage report (from PDF)", ""]
    if printed:
        lines.append(f"Pages supplied: printed pp. {min(printed)}–{max(printed)} ({len(pages)} PDF pages).")
    lines += ["", "| Section | Title | Book pages | In supplied PDF? | StatPath lesson |", "|---|---|---|---|---|"]
    order = sorted(sections, key=lambda k: (int(k.split(".")[0]), int(k.split(".")[1])))
    for k in order:
        s = sections[k]
        lines.append(f"| {k} | {s['title']} | {s['start']}–{s['end']} | {'yes' if k in present else ''} | {lessons.get(k, '_challenge_')} |")
    missing_terms = [(c, t) for c, ts in key_terms.items() for t in ts if t.lower() not in src_text]
    lines += ["", f"Key terms found in supplied chapters: {sum(len(v) for v in key_terms.values())}; not mentioned in src/: {len(missing_terms)}", ""]
    lines += [f"- ch {c}: {t}" for c, t in missing_terms]
    (out / "coverage_report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Sections in TOC: {len(sections)}; supplied pages cover {len(present)} numbered sections; wrote {out}")
    print(f"Key terms: {sum(len(v) for v in key_terms.values())} found, {len(missing_terms)} not mentioned in src/ (see coverage_report.md)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
