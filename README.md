# StatPath

A Duolingo-style game for learning introductory statistics, end to end.

The course follows the 13 chapters of **[Introductory Statistics 2e](https://openstax.org/details/books/introductory-statistics-2e)** by OpenStax (Rice University, CC BY 4.0). Every numbered section of the book is a lesson; every chapter is a unit that ends with a mixed "Chapter challenge".

## What's inside

| | |
|---|---|
| **13 units, 71 lessons** | Sampling & data → descriptive statistics → probability → discrete & continuous random variables → normal distribution → central limit theorem → confidence intervals → hypothesis testing (one and two samples) → chi-square → regression & correlation → F distribution & ANOVA |
| **500+ hand-written exercises** | Multiple choice, true/false, typed numeric and short answers, match-the-pairs, put-the-steps-in-order, and sort-into-categories |
| **64 randomized generators** | Numeric drills (means, z-scores, binomial and normal probabilities, confidence intervals, test statistics, χ², regression, ANOVA…) that produce fresh numbers every time, with a worked solution |
| **Game loop** | XP, daily goals, streaks, hearts (lost on mistakes, refill over time or with a perfect lesson), crowns per lesson (up to 5), achievements |
| **Spaced repetition** | Every exercise you answer gets an SM-2 style schedule; missed items come back sooner, and "Practice" modes target due and weak items |
| **Second chances** | Like Duolingo, a missed exercise is re-queued at the end of the lesson |
| **Grounded in the book** | Every lesson's tip card links to its section of the textbook with printed page numbers. Chapters 1, 2, and 6 through 13 have been checked line by line against the book's key terms, chapter reviews, and formula reviews; conventions follow the book (quartiles as medians of the halves, 1.5·IQR fences, percentile position i = (k/100)(n+1), midpoint means for grouped data, the ≥ 2s residual rule, Cohen's d, the equal-group-size F ratio, and the five-step hypothesis test) |

Progress is stored in the browser (`localStorage`); there is no backend and no account.

## Run it

```bash
npm install
npm run dev        # http://localhost:5173
npm test           # content validation + engine tests
npm run build      # production build in dist/
```

Requires Node 18+.

## Deploy

A GitHub Actions workflow (`.github/workflows/deploy.yml`) runs the tests and publishes `dist/` to GitHub Pages on every push to `main`. Pull requests run the tests and build but never publish.

One manual step is required once, before the first deploy: open Settings, then Pages, and set **Source** to **GitHub Actions**. The workflow cannot do this itself, because the default `GITHUB_TOKEN` is not permitted to create a Pages site.

The site is a **project site**, served from a subfolder named after the repository:

```
https://<owner>.github.io/StatPath/
```

That path is the only thing the workflow writes. A user site (the repo named `<owner>.github.io`) and every other repository's Pages are untouched. The Vite base path comes from the deployment's own `base_path`, so renaming the repository or adding a custom domain keeps the asset URLs correct with no edit.

## Project layout

```
src/
  engine/
    types.ts        exercise, lesson, unit types
    stats.ts        mean/SD, binomial, Poisson, normal, t, χ², F, regression
    generators.ts   randomized exercise generators
    lesson.ts       session builder, grading, answer parsing
    progress.ts     XP, streaks, hearts, crowns, spaced repetition, achievements
  content/
    helpers.ts      compact authoring helpers (mc, tf, num, match, order, classify)
    ch01.ts … ch13.ts   one file per textbook chapter
    index.ts        the assembled curriculum
  ui/               React components (path map, lesson player, exercise views, profile)
tests/              vitest suites (every exercise is validated and graded)
scripts/
  ingest_cnxml.py   fetch the OpenStax source from GitHub and audit lesson coverage
  ingest_pdf.py     chunk the textbook PDF and audit lesson coverage
docs/coverage.md    latest coverage report (from the GitHub source)
docs/coverage-pdf.md  coverage report from the PDF parts supplied so far
```

## Auditing coverage against the textbook

Two scripts check the curriculum against the book itself. Neither copies book text into the repository.

**From the OpenStax source on GitHub (no PDF needed):**

```bash
python scripts/ingest_cnxml.py --cache data/cnxml
```

This downloads the book's collection file and its 102 CNXML modules from `openstax/osbooks-introductory-statistics-bundle`, then writes `data/extracted/toc.json`, `key_terms.json`, and `coverage_report.md`. The report lists every numbered section with the StatPath lesson that covers it and every glossary term that is not mentioned anywhere in `src/`. A committed copy of the latest report is in `docs/coverage.md`; the report produced from the PDF parts is in `docs/coverage-pdf.md`.

**From the PDF (~22 MB, whole or split into parts):** `scripts/ingest_pdf.py` extracts the text (pymupdf or pypdf), writes 25-page chunks, reads the table of contents for every section's printed page range, splits the supplied pages into sections using the running headers, collects each chapter's key terms, and produces the same kind of coverage report. With `--write-ts` it regenerates `src/content/bookPages.ts`, the page index the app shows on every lesson's tip card ("In the book: Section 2.3, pp. 86–93").

```bash
pip install pymupdf
python scripts/ingest_pdf.py part1.pdf part2.pdf --write-ts     # parts in order
```

The PDF, the downloaded CNXML, and the extracted text are git-ignored.

**How the book maps onto the game.** Every numbered content section is a lesson. The hands-on lab sections (for example 1.5 Data Collection Experiment, 6.3 Normal Distribution (Lap Times), 13.5 Lab: One-Way ANOVA) and the appendix material the source numbers as 13.6 through 13.13 (review exercises, practice tests, data sets, formula and calculator notes, tables) do not get their own lessons; their skills are exercised by the randomized generators and each unit's Chapter challenge.

## Adding content

Add exercises to the relevant `src/content/chNN.ts` using the helpers; the first option of an `mc(...)` is the correct one (the UI shuffles). Add a generator to `src/engine/generators.ts` and register it in `allGenerators`. Run `npm test`: the suite checks that every exercise is well-formed, that its own correct answer grades as correct, that every generator is used by a lesson, and that every lesson can fill a 10-exercise session.

## License

Code: MIT. Course structure and topic coverage are based on OpenStax *Introductory Statistics 2e* (CC BY 4.0); all exercise text and explanations in this repository are original.
