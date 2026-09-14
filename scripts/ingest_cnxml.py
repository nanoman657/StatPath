#!/usr/bin/env python3
"""
Audit StatPath's curriculum against the OpenStax *Introductory Statistics 2e*
source, fetched from the book's public GitHub repository
(openstax/osbooks-introductory-statistics-bundle, CNXML modules).

This is an alternative to ingest_pdf.py that needs no PDF: it downloads the
collection file (the table of contents) and every module it references, then
writes to data/extracted/:

  toc.json             chapters -> numbered sections (title, module id, word count)
  key_terms.json       glossary term names per section (names only)
  coverage_report.md   which sections and glossary terms are covered by the
                       lessons and exercises in src/content

Usage:
  python scripts/ingest_cnxml.py            # fetch + audit
  python scripts/ingest_cnxml.py --cache data/cnxml   # reuse downloaded modules

Only stdlib is used. The book text is used for the audit and is not copied
into the repository.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

RAW = "https://raw.githubusercontent.com/openstax/osbooks-introductory-statistics-bundle/main"
COLLECTION = "collections/introductory-statistics-2e.collection.xml"
CNXML = "{http://cnx.rice.edu/cnxml}"
NS = {"c": "http://cnx.rice.edu/cnxml", "col": "http://cnx.rice.edu/collxml", "md": "http://cnx.rice.edu/mdml"}

# Sections that are hands-on labs / appendices in the book; StatPath folds them
# into each unit's "Chapter challenge" rather than giving them a lesson.
LAB_PATTERNS = re.compile(r"^(lab\b|.*experiment\)?$|.*\(.*\)$|descriptive statistics$|probability topics$|continuous distribution$|hypothesis testing (of|for) .*$|review exercises|practice tests|data sets|group and partner|solution sheets|mathematical phrases|notes for the ti|tables$)", re.I)


def fetch(path: str, cache: Path | None) -> str:
    if cache:
        f = cache / path
        if f.exists():
            return f.read_text(encoding="utf-8")
    with urllib.request.urlopen(f"{RAW}/{path}", timeout=60) as r:
        text = r.read().decode("utf-8")
    if cache:
        f = cache / path
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text, encoding="utf-8")
    return text


def parse_collection(xml_text: str) -> list[dict]:
    root = ET.fromstring(xml_text)
    out: list[dict] = []

    def walk(node, chapter):
        for child in node:
            tag = child.tag.split("}")[1]
            if tag == "subcollection":
                title = child.find("md:title", NS).text
                out.append({"type": "chapter", "title": title})
                walk(child.find("col:content", NS), title)
            elif tag == "module":
                out.append({"type": "module", "doc": child.get("document"), "chapter": chapter})

    walk(root.find("col:content", NS), None)
    return out


def parse_module(xml_text: str) -> dict:
    root = ET.fromstring(xml_text)
    t = root.find("c:title", NS)
    title = (t.text or "").strip() if t is not None else "?"
    glossary = []
    for d in root.iter(CNXML + "definition"):
        term = d.find("c:term", NS)
        if term is not None:
            glossary.append(" ".join("".join(term.itertext()).split()))
    words = len("".join(root.itertext()).split())
    return {"title": title, "glossary": glossary, "words": words}


def build_toc(entries: list[dict], cache: Path | None) -> list[dict]:
    docs = [e["doc"] for e in entries if e["type"] == "module"]
    with ThreadPoolExecutor(max_workers=8) as ex:
        texts = dict(zip(docs, ex.map(lambda d: fetch(f"modules/{d}/index.cnxml", cache), docs)))
    chapters: list[dict] = []
    ch = None
    n = 0
    for e in entries:
        if e["type"] == "chapter":
            ch = {"number": len(chapters) + 1, "title": e["title"], "sections": []}
            chapters.append(ch)
            n = 0
            continue
        if ch is None:
            continue  # preface
        m = parse_module(texts[e["doc"]])
        if m["title"].lower().startswith("introduction"):
            num = None
        else:
            n += 1
            num = f"{ch['number']}.{n}"
        ch["sections"].append({"num": num, "doc": e["doc"], **m})
    return chapters


def repo_lessons(root: Path) -> dict[str, str]:
    """section number -> lesson title from src/content/ch*.ts"""
    found: dict[str, str] = {}
    for f in sorted((root / "src" / "content").glob("ch*.ts")):
        for m in re.finditer(r'lesson\("u\d+\.\d+",\s*"(\d+\.\d+)",\s*"([^"]+)"', f.read_text(encoding="utf-8")):
            found[m.group(1)] = m.group(2)
    return found


def repo_text(root: Path) -> str:
    return "\n".join(f.read_text(encoding="utf-8") for f in (root / "src").rglob("*.ts")).lower()


def term_key(term: str) -> list[str]:
    """Search keys for a glossary term: the full term and its main head word(s)."""
    t = term.lower()
    t = re.sub(r"\(.*?\)", "", t).strip()
    keys = [t]
    if " or " in t:
        keys += [p.strip() for p in t.split(" or ")]
    keys += [k[:-1] for k in list(keys) if k.endswith("s") and len(k) > 4]
    return [k for k in keys if k]


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache", type=Path, default=None, help="directory to cache downloaded CNXML")
    args = ap.parse_args(argv[1:])
    root = Path(__file__).resolve().parent.parent
    out = root / "data" / "extracted"
    out.mkdir(parents=True, exist_ok=True)

    print("Fetching collection…")
    chapters = build_toc(parse_collection(fetch(COLLECTION, args.cache)), args.cache)
    (out / "toc.json").write_text(json.dumps(chapters, indent=1), encoding="utf-8")
    key_terms = {s["num"] or f"{c['number']}.intro": s["glossary"] for c in chapters for s in c["sections"] if s["glossary"]}
    (out / "key_terms.json").write_text(json.dumps(key_terms, indent=1), encoding="utf-8")

    lessons = repo_lessons(root)
    text = repo_text(root)
    lines = ["# Coverage report: StatPath vs. OpenStax Introductory Statistics 2e", "",
             "Source: openstax/osbooks-introductory-statistics-bundle (CNXML modules).", ""]
    missing_sections, lab_sections, covered = [], [], 0
    all_terms, missing_terms = 0, []
    lines += ["## Sections", "", "| Section | Book title | StatPath lesson |", "|---|---|---|"]
    for c in chapters:
        lines.append(f"| **{c['number']}** | **{c['title']}** | Unit {c['number']} |")
        for s in c["sections"]:
            if not s["num"]:
                continue
            if s["num"] in lessons:
                covered += 1
                status = lessons[s["num"]]
            elif LAB_PATTERNS.match(s["title"]):
                lab_sections.append(s)
                status = "_lab / appendix → chapter challenge_"
            else:
                missing_sections.append(s)
                status = "**MISSING**"
            lines.append(f"| {s['num']} | {s['title']} | {status} |")
            for term in s["glossary"]:
                all_terms += 1
                if not any(k in text for k in term_key(term)):
                    missing_terms.append((s["num"], term))
    numbered = sum(1 for c in chapters for s in c["sections"] if s["num"])
    lines += ["", f"Numbered sections in book: {numbered}. With a lesson: {covered}. Labs/appendices folded into challenges: {len(lab_sections)}. Missing: {len(missing_sections)}.", ""]
    if missing_sections:
        lines += ["### Missing sections", ""] + [f"- {s['num']} {s['title']}" for s in missing_sections] + [""]
    lines += ["## Glossary terms", "", f"Glossary terms in book: {all_terms}. Not mentioned anywhere in src/: {len(missing_terms)}.", ""]
    lines += [f"- {n}: {t}" for n, t in missing_terms]
    (out / "coverage_report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"Sections: {covered}/{numbered} with a lesson, {len(lab_sections)} labs/appendices, {len(missing_sections)} missing")
    print(f"Glossary terms: {all_terms - len(missing_terms)}/{all_terms} mentioned; see {out / 'coverage_report.md'}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
