# Parallel lanes for the layout formalization

Goal: a Lean model of Chromium's layout (`third_party/blink/renderer/core/layout/`, pin
`36c121be58126ddbb0686965897b8c8ff9b246fb`) built from the CSS specifications and checked against
the Chromium unit tests, preferring the shortest model that explains them.

Several teams of agents work at once. Each lane owns a set of test files and a module name prefix.
**Nothing outside your lane is yours to edit.** That one rule is what keeps lanes from colliding.

## Lanes

| Lane | Branch | Owns these test files (under `core/layout/`) | Module prefix | Main spec |
|---|---|---|---|---|
| block (running) | `chromium-layout-tests-block` | everything not listed below or under inline | `Block*`, `Column*`, `Grid*` (not `GridLanes*`), `Table*` | CSS 2.1, Writing Modes, Fragmentation, Multi-column, Grid 2, Tables |
| inline (running) | `chromium-layout-tests-inline` | `inline/*`, `layout_text*`, `list/*`, `geometry/*` (shared with block, as now), `layout_inline_test.cc`, `layout_ruby*`, `exclusions/*`, `shapes/*`, `hit_testing_test.cc` | `Inline*` | CSS 2.1 §9–10 inline, CSS Text 3, Writing Modes (bidi), Lists, Ruby |
| flex | `chromium-layout-flex` | `flex/*`, `layout_flexible_box_test.cc` | `Flex*` | CSS Flexbox 1 |
| gridlanes | `chromium-layout-gridlanes` | `grid_lanes/*` | `GridLanes*` | CSS Grid 3 (grid lanes) |
| mapping | `chromium-layout-mapping` | `map_coordinates_test.cc`, `visual_rect_mapping_test.cc` | `Mapping*` | CSS Transforms 1, CSSOM View, Writing Modes §6 |
| anchor | `chromium-layout-anchor` | `anchor_evaluator_impl_test.cc`, `anchor_scope_test.cc`, `anchor_position_scroll_data_test.cc` | `Anchor*` | CSS Anchor Positioning 1 |
| forms | `chromium-layout-forms` | `forms/*` | `Forms*` | HTML Rendering §15.3 (fieldset/legend, form controls) |
| svg | `chromium-layout-svg` | `svg/*` | `Svg*` | SVG 2 (geometry, viewBox, text layout) |
| examiner | `chromium-layout-examiner` | no test files; writes only `docs/chromium-layout/exam/` | `Exam*` | — (see below) |

Parked for every lane: scrollbar themes, layout-result caching, scroll anchoring, layout-shift
tracking, paint and hit-testing internals.

Your branch starts from `origin/chromium-layout-tests-block`. You may **read and import** any other
lane's module: copy it unchanged with
`git checkout origin/<their branch> -- docs/chromium-layout/<Module>.lean` and never edit the copy
(refresh it the same way). If you need something changed in a module you don't own, write the
request in `docs/chromium-layout/REQUESTS-<your lane>.md` instead. Do not edit `Layout*.lean`,
`CompilerCheck*.lean`, `check.sh`, `tools/`, or another lane's `MANIFEST-*` file.

## Files you own

- `docs/chromium-layout/<Prefix>*.lean`: model modules.
- `docs/chromium-layout/tests/Tests<Lane>_<File>.lean`: test vectors.
- `docs/chromium-layout/tests/MANIFEST-<lane>.md`: one row per TEST/TEST_F/TEST_P in your files, same
  columns as `MANIFEST-Block.md`: `| file:line | test | class | status | evidence |`.
- `docs/chromium-layout/SPEC-DIFF-<lane>.md`: where Chromium and the spec disagree.

## Method

1. Work through your spec in dependency order, one section at a time. Fetch spec text into a
   `specs/` folder outside the repo; cite the section in each definition's doc comment
   (e.g. `-- CSS Flexbox 1 §9.7 resolving flexible lengths`).
2. A definition arrives together with: at least one general law about it proved for all inputs
   (not `decide` on fixed values), and the test rows it now explains, in the same commit.
3. Rule (a)-(c) for `formalized`: (a) the test's input is a value of a model input type; (b) a
   general model function that mentions no test computes the output; (c) the theorem compares it with
   the test's `EXPECT_*` values as literals. No lookup tables of a test's numbers, no branching on
   tests, no theorem that compares a value with itself.
4. Shortest explanation wins. Before every commit:

       CHROMIUM_LAYOUT=<chromium>/third_party/blink/renderer/core/layout \
       python3 docs/chromium-layout/tools/mml_score.py . --gate HEAD \
         --manifest MANIFEST-<lane> --heldout docs/chromium-layout/tools/heldout-<block|inline>.txt

   (use the held-out list of the lane your files came from: block for flex, gridlanes, anchor,
   forms; inline for mapping, forms text controls, svg.)
   GATE FAIL: don't commit. PASS WITH REVIEW: only for a spec-cited definition that later tests
   reuse; name them in the commit message and bring the total below its value three commits back
   by the third commit after. Put the gate's delta lines in each commit message.
5. When a test disagrees with the spec, keep the spec definition, add a named Chromium-specific
   rule, and log it in `SPEC-DIFF-<lane>.md` (row, spec section, spec says, Chromium does,
   deviation or open question).
6. `docs/chromium-layout/check.sh` must pass (Lean 4.34.0 and Bend 2; set `OLEAN_DIR` to a folder
   of your own). Commit and push to your branch after each passing section. No force-push, no model
   or product names in commits or files.

## Held-out rows

`tools/heldout-*.txt` list rows (file:line) kept back to test whether a model generalises. Building
lanes never open, transcribe or mark them formalized.

The **examiner** lane does open them: for each held-out row in a lane that has a model for it,
transcribe the test under rule (a)-(c) into `exam/Exam_<lane>.lean` against that lane's current
modules (copied unchanged), without changing any model, and record pass / fail / not yet modelled
in `exam/RESULTS.md` with the lane's commit. The examiner also audits each lane's `formalized`
rows for hollow theorems (same value on both sides, lookup tables, test-keyed branches) and lists
them in `exam/AUDIT.md`. It never edits another lane's files.

## Setup

- Repo: `git clone https://github.com/nanoman657/StatPath`, then
  `git checkout -b chromium-layout-<lane> origin/chromium-layout-tests-block` and
  `git checkout origin/chromium-layout-shared -- docs/chromium-layout/COORDINATION.md docs/chromium-layout/tools docs/chromium-layout/check.sh`.
  Without push access, push your branch to a fork and open a draft pull request into
  `chromium-layout-shared`.
- Chromium layout folder at the pin (863 files, 2.8 MB, plus Chromium's LICENSE files), as a release
  asset on this repo:

      curl -fsSLO https://github.com/nanoman657/StatPath/releases/download/chromium-layout-pin-36c121be/chromium-layout-36c121be.tar.gz
      echo "d379230d5377e229ba125ad67e93f3a539faff76cd6523fa69a08366091daea8  chromium-layout-36c121be.tar.gz" | sha256sum -c
      tar xzf chromium-layout-36c121be.tar.gz
      export CHROMIUM_LAYOUT=$PWD/chromium-36c121be/third_party/blink/renderer/core/layout
      export CHROMIUM_LAYOUT_DIR=$CHROMIUM_LAYOUT   # the name verify_transcription.py reads

  Every file was checked against the pinned commit's blob hashes. (Alternatively, a sparse clone of
  github.com/chromium/chromium at `36c121be58126ddbb0686965897b8c8ff9b246fb`.)
- Lean 4.34.0, from the official release (no elan needed):

      curl -fsSLO https://github.com/leanprover/lean4/releases/download/v4.34.0/lean-4.34.0-linux.tar.zst
      tar --zstd -xf lean-4.34.0-linux.tar.zst
      export LEAN_BIN=$PWD/lean-4.34.0-linux/bin/lean

  (or `elan toolchain install leanprover/lean4:v4.34.0`; `lean-4.34.0-linux_aarch64` on ARM.)
- Bend 2 is not needed. It only checks `layout.bend` and `proof.bend`, which no new lane edits.
  Run the check without it:

      SKIP_BEND=1 OLEAN_DIR=$PWD/olean-<lane> bash docs/chromium-layout/check.sh

  `check.sh` compiles every Lean file, so it takes a while and wants about 600 MB of memory per
  `lean` process.
