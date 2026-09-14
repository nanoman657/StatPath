# StatPath

A Duolingo-style game for learning introductory statistics, end to end.

The course follows the 13 chapters of **[Introductory Statistics 2e](https://openstax.org/details/books/introductory-statistics-2e)** by OpenStax (Rice University, CC BY 4.0). Every numbered section of the book is a lesson; every chapter is a unit that ends with a mixed "Chapter challenge".

## What's inside

| | |
|---|---|
| **13 units, 71 lessons** | Sampling & data → descriptive statistics → probability → discrete & continuous random variables → normal distribution → central limit theorem → confidence intervals → hypothesis testing (one and two samples) → chi-square → regression & correlation → F distribution & ANOVA |
| **450+ hand-written exercises** | Multiple choice, true/false, typed numeric and short answers, match-the-pairs, put-the-steps-in-order, and sort-into-categories |
| **58 randomized generators** | Numeric drills (means, z-scores, binomial and normal probabilities, confidence intervals, test statistics, χ², regression, ANOVA…) that produce fresh numbers every time, with a worked solution |
| **Game loop** | XP, daily goals, streaks, hearts (lost on mistakes, refill over time or with a perfect lesson), crowns per lesson (up to 5), achievements |
| **Spaced repetition** | Every exercise you answer gets an SM-2 style schedule; missed items come back sooner, and "Practice" modes target due and weak items |
| **Second chances** | Like Duolingo, a missed exercise is re-queued at the end of the lesson |

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

A GitHub Actions workflow (`.github/workflows/deploy.yml`) runs the tests and publishes `dist/` to GitHub Pages on every push to `main`. Enable Pages with "GitHub Actions" as the source in the repository settings.

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
scripts/ingest_pdf.py   chunk the textbook PDF and audit lesson coverage
```

## Auditing coverage against the textbook PDF

The book is ~22 MB, so `scripts/ingest_pdf.py` reads it page by page and writes it out in 25-page chunks, extracts every section heading and key term, and produces `data/extracted/coverage_report.md` listing which sections do and do not have a lesson:

```bash
pip install pypdf
curl -L -o data/introductory-statistics-2e.pdf \
  https://assets.openstax.org/oscms-prodcms/media/documents/introductory-statistics-2e_-_WEB.pdf
python scripts/ingest_pdf.py data/introductory-statistics-2e.pdf
```

The PDF and extracted text are git-ignored.

## Adding content

Add exercises to the relevant `src/content/chNN.ts` using the helpers; the first option of an `mc(...)` is the correct one (the UI shuffles). Add a generator to `src/engine/generators.ts` and register it in `allGenerators`. Run `npm test`: the suite checks that every exercise is well-formed, that its own correct answer grades as correct, that every generator is used by a lesson, and that every lesson can fill a 10-exercise session.

## License

Code: MIT. Course structure and topic coverage are based on OpenStax *Introductory Statistics 2e* (CC BY 4.0); all exercise text and explanations in this repository are original.
