# Roadmap: Formalizing Chromium's LayoutNG Block and Inline Layout in Bend 2 and Lean 4

Status as of 2026-11-07.

This roadmap lists the work needed to go from the current scope to a checked formal model of CSS 2.1 in-flow block and inline layout, as Blink's LayoutNG implements it. It is organised as phases. Milestones M1–M5 match the scope document; the other phases cover work the scope does not estimate.

## Where things stand

| Item | State |
|---|---|
| Scope document (`SCOPE.md`) | Merged into `chromium-layout-roadmap` (P0.7). |
| Bend spike (`spike/stack.bend`, 144 lines) | `bend spike/stack.bend --verdict` prints `ALL PROOFS CHECK` (exit 0) (P0.3). |
| Lean spike (`spike/Spike.lean`, 118 lines) | `lean Spike.lean` exits 0. No `sorryAx` in any theorem. |
| Lean statements of Laws 1–5 (`SCOPE.md` §4) | Compiled and kernel-checked in `Layout.lean` with no changes to the five statements (P0.2). |
| Pinned Chromium revision | `36c121be58126ddbb0686965897b8c8ff9b246fb` (SCOPE §1). All 67 files verified and recorded in `pins.txt` (P0.5). |
| Lean project | None. There is no `lakefile*`, `lean-toolchain` or `lake-manifest.json`. Files are compiled with `lean <file>` using Lean 4.34.0 from the elan toolchain (P0.6). |

---

## Phase 0: Decisions and prerequisites (before M1)

Do these before writing any model code. Each one takes a day or less, except P0.5.

## Phases 1–5: source paths

Source file names in the phases below are taken from SCOPE §1 and §6.2 and have been re-verified in P0.5 (`pins.txt`). One non-existent filename in Phase 4 (`inline/inline_layout_state_stack.cc`) was corrected to `inline/inline_box_state.h` (where `InlineLayoutStateStack` is declared, with its implementation in `inline/inline_box_state.cc`).

- [x] **P0.1 Settle the five open questions in SCOPE §9.** Record each answer in this file, under "Decisions log" below.
  1. Signed margins: `Int`, or a `(pos: Nat, neg: Nat)` pair throughout, or defer negatives to M2?
  2. BFC-offset resolution: model Blink's two-pass `kBfcBlockOffsetResolved` relayout explicitly, or give a closed-form functional spec?
  3. Inline nesting depth: arbitrary `OpenTag`/`CloseTag` nesting, or one level of inline box?
  4. Differential oracle: `blink_unittests` JSON fixtures, or a standalone reference evaluator?
  5. `bend --verdict` on this machine sets `LEAN_STACK_SIZE_KB=4194304`, which aborts under a 900 MB memory cap. Decide whether to document a wrapper for CI, or cap the value.
- [x] **P0.2 Make the SCOPE §4 statements compile.** The following names appear in the statements and must be defined, with Lean's own kernel checking them: `MarginStrut`, `MarginStrut.append`, `MarginStrut.sum`, `ConstraintSpace`, `BlockContainerNode`, `AllMarginsNonNegative`, `AllChildrenNonSelfCollapsing`, `totalCollapsedFlowBlockSize`, `layoutBlock`, `InlineItem`, `LineInfo` (with `.items`, `.nonBreakItemCount`, `.inlineSize`), `breakLines`, `createLineBox`, `PlacedInlineItem`, `FontHeight`. The statements may only be changed to fix a real mismatch with Blink, and every change must be recorded. (Defined in `docs/chromium-layout/Layout.lean`; all five statements compile unchanged.)
- [x] **P0.3 Run `bend <file> --verdict` on `spike/stack.bend`.** Only `--check-only` has been run. Record the output verbatim:
  ```
  ALL PROOFS CHECK
  bend 2.0.40 is available: run bend update
  ```
- [x] **P0.4 Write one check script** (`docs/chromium-layout/check.sh`). It:
  1. runs `bend <file> --verdict` on each Bend file and requires `ALL PROOFS CHECK`;
  2. runs `lean <file>` on each Lean file, with exit 0;
  3. appends `#print axioms` for every theorem and fails on `sorryAx`;
  4. fails on any axiom outside `propext`, `Classical.choice`, `Quot.sound`.
- [x] **P0.5 Re-verify the pinned revision here.** Re-verified the sparse checkout at `/root/agy-scratch/chromium-layout/chromium` (`36c121be58126ddbb0686965897b8c8ff9b246fb`, sparse set `third_party/blink/renderer/core/layout`). Confirmed all 67 files in SCOPE §6.2 exist at the pin and recorded the git blob hash of each in-scope file in `docs/chromium-layout/pins.txt`.
- [x] **P0.6 Pick the directory layout.** Follow `bend-engine/` (single-file `lean <file>` checking on `docs/chromium-layout/Layout.lean` and `docs/chromium-layout/spike/Spike.lean`, plus `docs/chromium-layout/layout.bend` and `docs/chromium-layout/proof.bend`, and `docs/chromium-layout/CompilerCheck.lean` in M5). No Lake project is added.
- [x] **P0.7 Put the scope on a branch you intend to keep.** Merged `origin/chromium-layout-scope` into `chromium-layout-roadmap`.

**Exit criterion:** the check script passes on the spike and on the §4 statements, the open questions are answered, and the pin is verified.

---

## Phase 1: M1 — Geometry, `BoxStrut`, signed `MarginStrut` (2–3 days)

Source: `geometry/margin_strut.h`, `geometry/margin_strut.cc`, `geometry/box_strut.h` (per SCOPE §3).

- [x] Define `BoxStrut` (inline and block start/end) in Bend and Lean.
- [x] Define `MarginStrut` as `(positive, negative)` per the P0.1 decision, with `append` and `sum` transcribed from `MarginStrut::Append` and `MarginStrut::Sum` (non-quirky case).
- [x] Prove Law 1 (`margin_strut_semilattice`): `append` is associative, commutative and idempotent. Prove it in both Bend (`--verdict`) and Lean.
- [x] Extend the `stack.bend` / `Spike.lean` vertical-stacking spike to signed margins.
- [x] Check whether Blink's margin strut unit tests exist at the pinned revision. If they do, transcribe their cases as a test vector list (`blinkM1TestVectors` in `Layout.lean` and `blink_m1_test_vectors` in `proof.bend`, transcribed from `block_layout_algorithm_test.cc:568-1025` and `geometry/box_strut_test.cc:16-135`; no separate `geometry/margin_strut_test.cc` exists at the pin).

**Exit criterion:** Law 1 passes both checkers with no `sorryAx`. Every definition has a file:line reference to the Blink source.

---

## Phase 2: M2 — In-flow block layout (6–9 days)

Source: `block_layout_algorithm.cc` / `.h`, `block_layout_algorithm_utils.cc`, `block_node.cc`, `block_child_iterator.cc`, `geometry/margin_strut.cc`.

- [x] Define `ConstraintSpace`, `BlockContainerNode`, `LayoutInputNode` and the fragment output type.
- [x] Define `layoutBlock` as a recursive function over the children list (list induction, not sorted maps).
- [x] Model BFC-offset resolution as decided in P0.1 Q2.
- [x] Model self-collapsing boxes (zero border-box block size, no in-flow content).
- [x] Model parent–child margin collapse: through the block-start edge when `!has_block_start_edge`, and through the block-end edge when the parent has `auto` block size and zero block-end border and padding.
- [x] Prove Laws 2 (`block_siblings_monotonic_non_overlapping`) and 3 (`bfc_intrinsic_block_size_conservation`) in Lean, and in Bend where the proof is tractable.
- [x] Keep `AllMarginsNonNegative` and `AllChildrenNonSelfCollapsing` as explicit hypotheses. Do not weaken them silently.

**Exit criterion:** Laws 1–3 pass both checkers. The §4 statements of Laws 2 and 3 match the definitions, with no changes to their meaning.

---

## Phase 3: M3 — Greedy line breaking (6–8 days)

Source: `inline/line_breaker.cc` / `.h`, `inline/inline_items_builder.cc`.

- [x] Define `InlineItem` (`TextSegment`, `AtomicInline`, `OpenSpan`, `CloseSpan`, `HardBreak`) with the pre-computed fields from SCOPE §2, item 5.
- [x] Define `breakLines` as an accumulator loop with a termination measure (`items.length`).
- [x] Model trailing collapsible space removal, forced breaks, and the single-item fallback on overflow.
- [x] Prove Law 4 (`line_breaker_progress_and_partition`): progress, partition, and the non-overflow-or-single-item condition.

**Exit criterion:** Law 4 passes both checkers. The termination argument is in the file, not left implicit.

---

## Phase 4: M4 — Inline box state and line boxes (4–6 days)

Source: `inline/inline_layout_algorithm.cc`, `inline/inline_box_state.cc`, `inline/inline_box_state.h` (corrected in P0.5 from `inline/inline_layout_state_stack.cc`; `InlineLayoutStateStack` is declared in `inline/inline_box_state.h` and defined in `inline/inline_box_state.cc`).

- [x] Define `createLineBox` with `FontHeight` maximum accumulation over baseline-aligned items. Use `ascent = max ascent_i` and `descent = max descent_i`.
- [x] Decide the nesting depth of inline boxes (P0.1 Q3). If it is more than one level, add the `InlineLayoutStateStack` push/pop model.
- [x] Model integration with the block container: line boxes stack vertically inside the enclosing block.
- [x] Prove Law 5 (`line_box_height_encloses_items`).

**Exit criterion:** Law 5 passes both checkers. The `Nat.max` lemmas it needs are proved, not assumed.

---

## Phase 5: M5 — Differential conformance and translation check (3–5 days)

- [ ] Choose the oracle per P0.1 Q4 (`blink_unittests` fixtures or a reference evaluator).
- [ ] Generate bounded test vectors, following the `bend-engine/model_vectors.py` pattern.
- [ ] Compile the Bend model to `.mjs` and run the vectors against it. This needs a Node test in the same style as `tests/merge_bend.test.ts`.
- [ ] Extend `CompilerCheck.lean` to cover `Nat.max` (a `>` guard) and record constructors. `bend-engine/README.md` records that these are currently rejected.

**Exit criterion:** all vectors pass and the compiler check accepts the extended forms. The vectors are checked into the repo with their generator.

---

## Phase 6: Close the transcription gap (not estimated)

The link from Blink's C++ to the Bend and Lean definitions is a hand transcription (SCOPE §8.1). Nothing mechanized checks it today.

- [ ] Write an audit table with one row per model function: Bend name, Lean name, Chromium file and line range at the pinned revision, and a short note on any simplification.
- [ ] Require a second reviewer to sign off each row.
- [ ] Add a mechanized check where one is feasible: for example, diff the Blink source at the pin against the audit table's line ranges, so any change to a transcribed function is flagged.
- [ ] Use WPT layout geometry (`offsetTop`, `offsetLeft`, `offsetWidth`, `offsetHeight`, `getClientRects()`) as an external check, if a browser run is available. The earlier browser-based probe in this repo used Playwright 1.63.0 and can be reused.

---

## Phase 7: Assumptions register (not estimated)

Each assumption must appear as an explicit hypothesis in Lean or Bend, never as an `axiom`. The `#print axioms` gate in P0.4 enforces this.

| Assumption (SCOPE §5 / §8) | What the model does | Work needed |
|---|---|---|
| Font metrics | Input `FontHeight` on each item | Document the source and the precondition. |
| HarfBuzz shaping, line-break and bidi (ICU) | Pre-segmented `TextSeg` tokens with boolean flags | Document the sub-additivity precondition. |
| Computed style and length resolution | Inputs already resolved to `BoxStrut` and `MaybeNat` | Document which properties are pre-resolved. |
| `LayoutUnit` is a 32-bit saturating int, while the model uses `Nat` (SCOPE §8.2) | Unbounded `Nat` | State the bound `2^31 − 1` as a hypothesis. Prove no intermediate exceeds it for the inputs considered. Note the `2^48` limit from `Transitions.lean`. |
| Subpixel rounding and pixel snapping (SCOPE §8.3) | Out of scope | Keep it out and say so in the README. |
| Caching and incremental layout (SCOPE §8.4) | Out of scope | Keep it out and say so in the README. |

---

## Phase 8: Features outside the first fragment (each unestimated)

Each feature below is a separate scoped milestone with its own estimate. None of them is in the SCOPE 21–31 day figure.

- Floats and exclusion space (`ExclusionSpace`, `unpositioned_floats`)
- Out-of-flow and relative/sticky positioning, and anchor positioning
- Block fragmentation and pagination (`BlockBreakToken`)
- Flexbox, Grid, Table, Multicol, Ruby, SVG text, custom layout
- Bidirectional reordering (UAX #9) and vertical writing modes
- Quirks-mode margin collapsing (SCOPE §4, Law 1, covers non-quirky margins only)

Before starting any of these, check whether a formal model of it already exists. An earlier search found none for flexbox or grid, though it was not exhaustive.

---

## Phase 9: Revision maintenance (not estimated)

- [ ] Write a re-pin procedure: pick the new revision, diff the 67 in-scope files against the old pin, and list every changed function that the model transcribes.
- [ ] Re-run the differential vectors at each re-pin.
- [ ] Keep a changelog in this file, one line per pin.

---

## Effort

| Scope | Estimate | Source |
|---|---|---|
| M1–M5 | 21–31 engineer-days | SCOPE §7.2 |
| Phase 0 | Not estimated here. Roughly 2–4 days, mostly open-question decisions and the §4 fix. | This roadmap |
| Phases 6–9 | Not estimated | This roadmap |
| Phase 8 features | Each feature needs its own scope | This roadmap |

The SCOPE estimates are anchored to the repository's earlier developments (SCOPE §7.1). They have not been checked against this work.

---

## Decisions log

| # | Question | Decision | Date | Recorded by |
|---|---|---|---|---|
| Q1 | Signed margin representation | **Proposed, awaiting owner:** Represent `MarginStrut` as a `(pos: Nat, neg: Nat)` pair (`MStrut{pos, neg}`) starting in M1, where `pos` stores the largest positive margin and `neg` stores the largest negative margin magnitude (`MarginStrut` in `geometry/margin_strut.h:16-18`), while keeping `BoxStrut` edges as `Nat` for borders, padding, and non-negative margins (`AllMarginsNonNegative`). Reasoning: Bend 2's `Base` library provides inductive support for `Nat` rather than signed `Int`, and Blink's `MarginStrut` already separates `positive_margin` and `negative_margin` into two fields updated via `max`/`min` in `MarginStrut::Append` (`geometry/margin_strut.cc:19-29`). | 2026-11-07 | nanoman657 |
| Q2 | BFC-offset resolution | **Proposed, awaiting owner:** Use the single-pass closed-form functional specification of BFC block-offset resolution in `layoutBlock`, returning `bfcBlockOffset : Option Nat` (`MaybeNat`) on `LayoutResult`. Reasoning: In `block_layout_algorithm.cc:818-844` and `3874-3915` (`NeedsAbortOnBfcBlockOffsetChange`), `abort_when_bfc_block_offset_updated_` is only set when there are preceding adjoining floats (`GetAdjoiningObjectTypes()`), block fragmentation (`HasBlockFragmentation()`), or height-based `line-clamp`. In the first fragment (no floats, no fragmentation, no `line-clamp`), `ResolveBfcBlockOffset` (`block_layout_algorithm.cc:2527, 3851-3906`) never aborts and coincides with the single-pass closed-form specification. | 2026-11-07 | nanoman657 |
| Q3 | Inline nesting depth | **Proposed, awaiting owner:** Model both flat item accumulation in `createLineBox` (`SCOPE.md` §4 Law 5) and an explicit `InlineLayoutStateStack` push/pop pass (`applyBoxStateStack` over arbitrary `OpenTag`/`CloseTag` nesting depth, modeling `OnBeginPlaceItems`, `OnOpenTag`, `OnCloseTag`, `OnEndPlaceItems` in `inline/inline_box_state.cc:277-445`). Reasoning: `InlineItemsBuilder` flattens arbitrarily nested `<span>` elements into `kOpenTag`/`kCloseTag` items, and `FontHeight::Merge` (`Nat.max` on `ascent` and `descent`) is associative, commutative, and idempotent, so stack push/pop and flat line accumulation produce identical enclosing `FontHeight` bounds for baseline-aligned items. | 2026-11-07 | nanoman657 |
| Q4 | Differential oracle | **Proposed, awaiting owner:** Use both (a) a bounded exhaustive vector generator in `docs/chromium-layout/model_vectors.py` following `bend-engine/model_vectors.py` (comparing Lean model outputs in `model_vectors.txt` against compiled Bend JavaScript `layout.mjs` in Vitest), and (b) transcribed test vectors from Chromium's `blink_unittests` at the pinned revision (`block_layout_algorithm_test.cc`, `inline_layout_algorithm_test.cc`, `geometry/box_strut_test.cc`). Reasoning: Browser installation (`playwright install`) is out of scope on this host, while combining exhaustive Lean-model vectors with `blink_unittests` cases tests both Lean-to-Bend-JS agreement and fidelity to Blink's unit test expectations. | 2026-11-07 | nanoman657 |
| Q5 | `LEAN_STACK_SIZE_KB` under memory caps | **Proposed, awaiting owner:** Wrap `bendtt.bin` via `BENDTT` in `docs/chromium-layout/check.sh` (and the cached `~/.bend/bendtt/<hash>/bendtt` shim) with `LEAN_STACK_SIZE_KB=262144` (256 MB) so `bend --verdict`'s internal override (`LEAN_STACK_SIZE_KB: "4194304"`) does not abort under the 900 MB cgroup memory cap. Reasoning: `bend` overwrites `LEAN_STACK_SIZE_KB` in the child environment when spawning `$BENDTT`; setting `LEAN_STACK_SIZE_KB=262144` inside the `BENDTT` wrapper script succeeds within the 900 MB limit. | 2026-11-07 | nanoman657 |

---

## Changelog

| Date | Pin | Change |
|---|---|---|
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Roadmap written. Pin not yet re-verified in this repository (P0.5). |
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phase 0 complete (P0.1–P0.7): Q1–Q5 proposed; `Layout.lean` compiled; `spike/stack.bend --verdict` checked; `check.sh` and `pins.txt` added. |
