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

- [x] Choose the oracle per P0.1 Q4 (`blink_unittests` fixtures or a reference evaluator).
- [x] Generate bounded test vectors, following the `bend-engine/model_vectors.py` pattern (`docs/chromium-layout/model_vectors.py` and `docs/chromium-layout/model_vectors.txt`, 650 vectors across M1–M4).
- [x] Compile the Bend model to `.mjs` (`docs/chromium-layout/layout.mjs` via `docs/chromium-layout/gen.sh`) and run the vectors against it (`tests/chromium_layout_bend.test.ts`).
- [x] Extend `CompilerCheck.lean` (`docs/chromium-layout/CompilerCheckCore.lean` and `docs/chromium-layout/CompilerCheck.lean`, with `docs/chromium-layout/compiler_check.py` and `docs/chromium-layout/compiler_check_report.txt`) to cover `Nat.max` (a `>` guard) and record constructors. `bend-engine/README.md` records that these are currently rejected.

**Exit criterion:** all vectors pass and the compiler check accepts the extended forms. The vectors are checked into the repo with their generator.

---

## Phase 6: Close the transcription gap (not estimated)

The link from Blink's C++ to the Bend and Lean definitions is a hand transcription (SCOPE §8.1). Nothing mechanized checks it today.

- [x] Write an audit table with one row per model function: Bend name, Lean name, Chromium file and line range at the pinned revision, and a short note on any simplification (36 rows below).
- [ ] Require a second reviewer to sign off each row (`Reviewer sign-off` column below). Not done: no second reviewer yet.
- [x] Add a mechanized check where one is feasible (`docs/chromium-layout/verify_transcription.py`, invoked by `docs/chromium-layout/check.sh` and `tests/chromium_layout_bend.test.ts`): checks every Bend symbol in `layout.bend`, every Lean symbol in `LayoutTypes.lean`, every file in `pins.txt`, and (when the pinned Chromium tree is present) verifies every file's git blob SHA-1, every `file:start-end` line range, C++ anchor string, and SHA-256/12 slice digest.
- [x] Use WPT layout geometry (`offsetTop`, `offsetLeft`, `offsetWidth`, `offsetHeight`, `getClientRects()`) as an external check (`docs/chromium-layout/wpt_geometry_check.cjs` and `tests/chromium_layout_bend.test.ts`, using Playwright 1.63.0 + headless Chromium against `docs/chromium-layout/layout.mjs`).

### Transcription Audit Table (Pin `36c121be58126ddbb0686965897b8c8ff9b246fb`)

| Bend symbol | Lean symbol | Chromium `core/layout/` file:lines | C++ anchor (`sha256/12`) | Simplification / model note | Reviewer sign-off |
|---|---|---|---|---|---|
| `BoxStrut` | `BoxStrut` | `geometry/box_strut.h:33-61` | `struct CORE_EXPORT BoxStrut` (`9bf696f9b6f1`) | 4 logical edges (`inline_start`, `inline_end`, `block_start`, `block_end`) modeled as `Nat`. | Reviewer 1 (model author); Reviewer 2: pending |
| `box_strut_zero` | `BoxStrut.zero` | `geometry/box_strut.h:34-48` | `LayoutUnit inline_start` (`d4dfd0ebc35d`) | Default-constructed zero `BoxStrut`. | Reviewer 1 (model author); Reviewer 2: pending |
| `box_strut_inline_sum` | `BoxStrut.inlineSum` | `geometry/box_strut.h:62-62` | `LayoutUnit InlineSum() const` (`51f762844cef`) | Exact transcription of `inline_start + inline_end`. | Reviewer 1 (model author); Reviewer 2: pending |
| `box_strut_block_sum` | `BoxStrut.blockSum` | `geometry/box_strut.h:63-63` | `LayoutUnit BlockSum() const` (`6c437ba6dbb6`) | Exact transcription of `block_start + block_end`. | Reviewer 1 (model author); Reviewer 2: pending |
| `box_strut_add` | `BoxStrut.add` | `geometry/box_strut.h:74-86` | `BoxStrut& operator+=(const BoxStrut& other)` (`f0ff1959f709`) | Pure functional version of `operator+=` / `operator+`. | Reviewer 1 (model author); Reviewer 2: pending |
| `MarginStrut` | `MarginStrut` | `geometry/margin_strut.h:16-39` | `struct CORE_EXPORT MarginStrut` (`f9dc947067ae`) | Stores `(pos: Nat, neg: Nat)` (magnitude of `negative_margin`); omits `is_quirky_container_start` (CSS 2.1 standards mode, SCOPE §4 Law 1). | Reviewer 1 (model author); Reviewer 2: pending |
| `margin_strut_empty` | `MarginStrut.empty` | `geometry/margin_strut.h:17-19` | `LayoutUnit positive_margin` (`3f4a13803501`) | Default zero `(0, 0)` margin strut. | Reviewer 1 (model author); Reviewer 2: pending |
| `margin_strut_append` | `MarginStrut.append` | `geometry/margin_strut.cc:11-30` | `void MarginStrut::Append` (`6e218ef2e082`) | Pointwise `Nat.max` on `pos` and `neg` (equivalent to `std::max` on `positive_margin` and `std::min` on negative `negative_margin`). | Reviewer 1 (model author); Reviewer 2: pending |
| `margin_strut_sum` | `MarginStrut.sum` | `geometry/margin_strut.h:40-44` | `LayoutUnit Sum() const` (`034a6d0ccc5d`) | `Nat.sub(pos, neg)` for non-negative net struts; signed offset application uses `margin_strut_apply_offset`. | Reviewer 1 (model author); Reviewer 2: pending |
| `margin_strut_apply_offset` | `MarginStrut.applyOffset` | `constraint_space.h:660-667` | `space.GetBfcOffset().block_offset + space.GetMarginStrut().Sum()` (`6a8ad66cc0b1`) | Computes `(y + pos) - neg` so negative margins pull `y` upward without intermediate unsigned underflow. | Reviewer 1 (model author); Reviewer 2: pending |
| `FontHeight` | `FontHeight` | `inline/inline_box_state.h:35-85` | `FontHeight metrics = FontHeight::Empty()` (`2361720a23f0`) | Baseline-relative `(ascent: Nat, descent: Nat)` pair used by `InlineBoxState`. | Reviewer 1 (model author); Reviewer 2: pending |
| `font_height_line_height` | `FontHeight.lineHeight` | `inline/inline_box_state.cc:120-160` | `text_height = text_metrics.LineHeight()` (`2f15062be358`) | Exact transcription of `ascent + descent`. | Reviewer 1 (model author); Reviewer 2: pending |
| `font_height_merge` | `FontHeight.merge` | `inline/inline_box_state.cc:455-471` | `parent_box.metrics.Unite(box->metrics)` (`05f7b40b7506`) | Pointwise `Nat.max` on `ascent` and `descent` (`FontHeight::Unite` / `Merge`). | Reviewer 1 (model author); Reviewer 2: pending |
| `LogicalSize` | `LogicalSize` | `geometry/logical_size.h:23-55` | `struct CORE_EXPORT LogicalSize` (`29525bc27c03`) | `(inline_size: Nat, block_size: Nat)`. | Reviewer 1 (model author); Reviewer 2: pending |
| `LogicalOffset` | `LogicalOffset` | `geometry/logical_offset.h:23-55` | `struct CORE_EXPORT LogicalOffset` (`ccb5dd64b8cd`) | `(inline_offset: Nat, block_offset: Nat)`. | Reviewer 1 (model author); Reviewer 2: pending |
| `ConstraintSpace` | `ConstraintSpace` | `constraint_space.h:106-190` | `class CORE_EXPORT ConstraintSpace final` (`33096a2b7ee1`) | First-fragment fields (`available_inline_size`, `available_block_size`, `bfc_line_offset`, `bfc_block_offset`, `margin_strut`, `is_new_bfc`). | Reviewer 1 (model author); Reviewer 2: pending |
| `InlineItem` | `InlineItem` | `inline/inline_item.h:30-80` | `class CORE_EXPORT InlineItem final` (`45962966408b`) | 5 constructors (`TextSeg`, `AtomicInline`, `OpenTag`, `CloseTag`, `ForcedBreak`) with pre-shaped widths and `FontHeight` (SCOPE §3). | Reviewer 1 (model author); Reviewer 2: pending |
| `LineInfo` | `LineInfo` | `inline/line_info.h:31-95` | `class CORE_EXPORT LineInfo` (`be59c0c5229f`) | Stores line `items`, `inline_size` (excluding hanging trailing space), and `non_break_item_count`. | Reviewer 1 (model author); Reviewer 2: pending |
| `PlacedInlineItem` | `PlacedInlineItem` | `inline/logical_line_item.h:27-95` | `struct LogicalLineItem` (`4f0b9a9a4410`) | Positioned inline item `(item_id, inline_offset, block_offset, inline_size, block_size)`. | Reviewer 1 (model author); Reviewer 2: pending |
| `LineBoxFragment` | `LineBoxFragment` | `inline/physical_line_box_fragment.h:17-65` | `class CORE_EXPORT PhysicalLineBoxFragment final` (`a76ed82f79e4`) | Immutable line box fragment `(bfc_offset, inline_size, metrics, items)`. | Reviewer 1 (model author); Reviewer 2: pending |
| `take_line_aux` | `takeLineAux` | `inline/line_breaker.cc:1024-1110` | `void LineBreaker::BreakLine` (`126e9d25af60`) | Pure greedy packing loop with `pending_space` deferral for trailing collapsible spaces (`RemoveTrailingCollapsibleSpace`). | Reviewer 1 (model author); Reviewer 2: pending |
| `take_line` | `takeLine` | `inline/line_breaker.cc:897-945` | `void LineBreaker::NextLine` (`001c81ca7ce1`) | Packs one line starting at `first`, always consuming `first` (single-item overflow fallback, `HandleOverflow`). | Reviewer 1 (model author); Reviewer 2: pending |
| `break_lines` | `breakLines` | `inline/inline_layout_algorithm.cc:1103-1210` | `const LayoutResult* InlineLayoutAlgorithm::Layout()` (`aa952cc99f77`) | Repeatedly invokes `take_line` bounded by `items.length` until `items` is empty. | Reviewer 1 (model author); Reviewer 2: pending |
| `accumulate_line_metrics` | `accumulateLineMetrics` | `inline/inline_box_state.cc:277-315` | `InlineLayoutStateStack::OnBeginPlaceItems` (`00a4f215e48c`) | Folds `font_height_merge` over line items starting from the line `strut`. | Reviewer 1 (model author); Reviewer 2: pending |
| `place_line_items` | `placeLineItems` | `inline/inline_box_state.cc:426-490` | `InlineLayoutStateStack::OnEndPlaceItems` (`29f57832bd0c`) | Computes baseline-relative `block_offset = line_metrics.ascent - item.ascent` and advances `inline_offset`. | Reviewer 1 (model author); Reviewer 2: pending |
| `step_box_state_stack` | `stepBoxStateStack` | `inline/inline_box_state.cc:364-425` | `InlineLayoutStateStack::OnOpenTag` (`1623267c7aae`) | Pushes active `FontHeight` on `OpenTag` (`OnOpenTag`) and pops/merges into parent on `CloseTag` (`OnCloseTag`). | Reviewer 1 (model author); Reviewer 2: pending |
| `apply_box_state_stack` | `applyBoxStateStack` | `inline/inline_box_state.h:178-235` | `class CORE_EXPORT InlineLayoutStateStack` (`76947c7a4174`) | Runs `step_box_state_stack` across all line items and flushes open spans (`OnEndPlaceItems`), proved equal to `accumulate_line_metrics`. | Reviewer 1 (model author); Reviewer 2: pending |
| `create_line_box` | `createLineBox` | `inline/inline_layout_algorithm.cc:378-435` | `void InlineLayoutAlgorithm::CreateLine` (`47506ab18b8e`) | Builds `LineBoxFragment` from `strut` and `LineInfo` (SCOPE §4 Law 5). | Reviewer 1 (model author); Reviewer 2: pending |
| `stack_line_boxes` | `stackLineBoxes` | `inline/inline_layout_algorithm.cc:540-585` | `line_box_metrics.LineHeight()` (`d408817a2b88`) | Stacks `LineBoxFragment`s vertically within an inline formatting context by advancing `block_off` by `lineHeight`. | Reviewer 1 (model author); Reviewer 2: pending |
| `child_is_self_collapsing` | `LayoutInputNode.isSelfCollapsing` | `block_layout_algorithm.cc:2862-2925` | `BlockLayoutAlgorithm::ComputeChildData` (`587e6e3c8b37`) | Checks zero block border+padding, `explicit_block_size = none`, no in-flow content, and `¬is_new_bfc`. | Reviewer 1 (model author); Reviewer 2: pending |
| `child_start_margin_strut` | `LayoutInputNode.startMarginStrut` | `block_layout_algorithm.cc:2303-2380` | `BlockLayoutAlgorithm::HandleInflow` (`aca7e95e3bf9`) | Collapses child outer `margin.block_start` with `inner_start_strut` when child has no block-start border/padding and is not a new BFC. | Reviewer 1 (model author); Reviewer 2: pending |
| `child_end_margin_strut` | `LayoutInputNode.endMarginStrut` | `block_layout_algorithm.cc:2382-2490` | `BlockLayoutAlgorithm::FinishInflow` (`97277dfbb2ac`) | Collapses child `inner_end_strut` with outer `margin.block_end` when child has no block-end edge, no explicit height, and is not a new BFC. | Reviewer 1 (model author); Reviewer 2: pending |
| `child_border_box_block_size` | `LayoutInputNode.borderBoxBlockSize` | `block_layout_algorithm.cc:1172-1260` | `BlockLayoutAlgorithm::FinishLayout` (`83ac0781b828`) | Resolves child border-box block size (including enclosed `inner_end_strut.sum` when `hasBlockEndEdge` holds). | Reviewer 1 (model author); Reviewer 2: pending |
| `layout_children` | `layoutChildren` | `block_layout_algorithm.cc:2927-3022` | `BlockLayoutAlgorithm::ComputeInflowPosition` (`e54f2a98600c`) | Pure state-passing fold over `children` tracking `bfc_resolved`, `first_resolved_strut`, `logical_block_offset`, and `margin_strut`. | Reviewer 1 (model author); Reviewer 2: pending |
| `layout_block` | `layoutBlock` | `block_layout_algorithm.cc:799-920` | `BlockLayoutAlgorithm::Layout(` (`5ebaeab6fca6`) | Single-pass closed-form `BlockLayoutAlgorithm::Layout` (P0.1 Q2) producing `LayoutResult` with `PhysicalBoxFragment`, `bfcBlockOffset`, `endMarginStrut`, and `intrinsicBlockSize`. | Reviewer 1 (model author); Reviewer 2: pending |
| `total_collapsed_flow_block_size` | `totalCollapsedFlowBlockSize` | `block_layout_algorithm.cc:3851-3915` | `BlockLayoutAlgorithm::ResolveBfcBlockOffset` (`71cccb3e32a9`) | Sums collapsed inter-sibling margin struts and child border-box block sizes across in-flow children (SCOPE §4 Law 3). | Reviewer 1 (model author); Reviewer 2: pending |

---

## Phase 7: Assumptions register (not estimated)

Each assumption must appear as an explicit hypothesis in Lean or Bend, never as an `axiom`. The `#print axioms` gate in P0.4 enforces this.

- [x] Document and formalize each assumption in [`docs/chromium-layout/README.md`](file:///root/github/StatPath/docs/chromium-layout/README.md) and [`docs/chromium-layout/Layout.lean`](file:///root/github/StatPath/docs/chromium-layout/Layout.lean) without any `axiom` declarations (`check.sh` verifies `#print axioms` on all theorems).

| Assumption (SCOPE §5 / §8) | What the model does | Work needed / Resolution |
|---|---|---|
| Font metrics | Input `FontHeight` on each item | **Done:** Documented in `README.md` (`platform/fonts/font_height.h`, `SimpleFontData`, `inline/inline_box_state.h:35-85`); precondition formalized as `FontMetricsBounded` (`h.ascent + h.descent ≤ kLayoutUnitMax`) with `font_height_merge_no_overflow` and `line_box_items_within_layout_unit` in `Layout.lean`. |
| HarfBuzz shaping, line-break and bidi (ICU) | Pre-segmented `TextSeg` tokens with boolean flags | **Done:** Documented in `README.md` (`harfbuzz_shaper.h`, `text_break_iterator.h`, `inline_items_builder.cc`); sub-additivity precondition formalized as `ShapingSubadditive` (`∀ s1 s2, shapeWidth (s1 ++ s2) = shapeWidth s1 + shapeWidth s2`) and `shaping_segments_width_conservation` in `Layout.lean`. |
| Computed style and length resolution | Inputs already resolved to `BoxStrut` and `MaybeNat` | **Done:** Documented in `README.md` (`computed_style.h`, `length_utils.cc`); pre-resolved properties formalized via `BoxStrutBounded`, `MarginStrutBounded`, `AllMarginsNonNegative`, and `AllChildrenNonSelfCollapsing` in `LayoutTypes.lean` and `Layout.lean`. |
| `LayoutUnit` is a 32-bit saturating int, while the model uses `Nat` (SCOPE §8.2) | Unbounded `Nat` | **Done:** Defined `kLayoutUnitMax := 2147483647` (`2^31 - 1`) and `kBendNatImmediateMax := 281474976710655` (`2^48 - 1`, matching `LIMIT` in `Transitions.lean` / `CompilerCheckCore.lean`), and proved `kLayoutUnitMax_le_kBendNatImmediateMax`, `margin_strut_append_no_overflow`, `margin_strut_apply_offset_no_overflow`, `font_height_merge_no_overflow`, `line_box_items_within_layout_unit`, `bfc_block_layout_within_layout_unit`, and `blink_test_vectors_within_layout_unit_max` in `Layout.lean`. |
| Subpixel rounding and pixel snapping (SCOPE §8.3) | Out of scope | **Done:** Explicitly kept out of scope and documented in `README.md` ("Assumptions Register" row 5). |
| Caching and incremental layout (SCOPE §8.4) | Out of scope | **Done:** Explicitly kept out of scope and documented in `README.md` ("Assumptions Register" row 6). |

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

- [x] Write a re-pin procedure: pick the new revision, diff the 67 in-scope files against the old pin, and list every changed function that the model transcribes. The procedure and its tool (`docs/chromium-layout/repin.py`) are below.
- [x] Re-run the differential vectors at each re-pin (step 5 of the procedure). This is a step to repeat at every re-pin, not a one-time task.
- [x] Keep a changelog in this file, one line per pin.


### Re-pin procedure

`repin.py` only reads: it never edits the model, `pins.txt` or this file. Run it from the repository root.

1. Check out the new revision's `third_party/blink/renderer/core/layout` (same sparse method as P0.5). Keep the old pin's checkout too, if you have it.
2. Run `python3 docs/chromium-layout/repin.py --new-dir NEW/third_party/blink/renderer/core/layout --old-dir OLD/third_party/blink/renderer/core/layout`. Without `--old-dir` it reports changes by blob SHA-1 only.
3. Read the report. Exit status 0 means no pinned file changed, 1 means there is something to review, 2 means bad input. For each pinned file it prints:
   - `MISSING`: renamed or removed. Find the new location, then update `pins.txt` and the audit rows.
   - `CHANGED`, with each audit row citing the file and whether the row's line range overlaps a changed hunk (`CHANGED RANGE`) or the file changed elsewhere (line numbers may have moved), plus the block-lane manifest rows citing the file.
4. For every flagged row, re-read the C++ and decide whether the model function still matches. Change the Bend and Lean definitions and proofs if not. Then update the line range, anchor and slice digest in the audit table, and reset the row's `Reviewer 2` sign-off to pending if the function changed.
5. Write the new pins with `--revision <40-char SHA> --write-pins OUT` and replace `pins.txt` with the result. Re-run `docs/chromium-layout/check.sh` (set `REQUIRE_CHROMIUM=1` and `CHROMIUM_LAYOUT` to the new checkout so the manifest and slice checks are not skipped), `python3 docs/chromium-layout/model_vectors.py`, and the vitest suite in `tests/chromium_layout_bend.test.ts`.
6. Add one line to the changelog below with the date, the new revision and the files that changed.

Limits: `repin.py` sees file changes, not semantic ones. A file that is unchanged cannot break a transcription, but a changed file whose changed hunk lies outside every audit row's line range can still affect a function through a header or helper it calls. Treat `file changed, range untouched` rows as needing a quick read, not as safe.

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
| Q1 | Signed margin representation | **Approved by owner:** Represent `MarginStrut` as a `(pos: Nat, neg: Nat)` pair (`MStrut{pos, neg}`) starting in M1, where `pos` stores the largest positive margin and `neg` stores the largest negative margin magnitude (`MarginStrut` in `geometry/margin_strut.h:16-18`), while keeping `BoxStrut` edges as `Nat` for borders, padding, and non-negative margins (`AllMarginsNonNegative`). Reasoning: Bend 2's `Base` library provides inductive support for `Nat` rather than signed `Int`, and Blink's `MarginStrut` already separates `positive_margin` and `negative_margin` into two fields updated via `max`/`min` in `MarginStrut::Append` (`geometry/margin_strut.cc:19-29`). | 2026-11-07 | owner (approved proposal) |
| Q2 | BFC-offset resolution | **Approved by owner:** Use the single-pass closed-form functional specification of BFC block-offset resolution in `layoutBlock`, returning `bfcBlockOffset : Option Nat` (`MaybeNat`) on `LayoutResult`. Reasoning: In `block_layout_algorithm.cc:818-844` and `3874-3915` (`NeedsAbortOnBfcBlockOffsetChange`), `abort_when_bfc_block_offset_updated_` is only set when there are preceding adjoining floats (`GetAdjoiningObjectTypes()`), block fragmentation (`HasBlockFragmentation()`), or height-based `line-clamp`. In the first fragment (no floats, no fragmentation, no `line-clamp`), `ResolveBfcBlockOffset` (`block_layout_algorithm.cc:2527, 3851-3906`) never aborts and coincides with the single-pass closed-form specification. | 2026-11-07 | owner (approved proposal) |
| Q3 | Inline nesting depth | **Approved by owner:** Model both flat item accumulation in `createLineBox` (`SCOPE.md` §4 Law 5) and an explicit `InlineLayoutStateStack` push/pop pass (`applyBoxStateStack` over arbitrary `OpenTag`/`CloseTag` nesting depth, modeling `OnBeginPlaceItems`, `OnOpenTag`, `OnCloseTag`, `OnEndPlaceItems` in `inline/inline_box_state.cc:277-445`). Reasoning: `InlineItemsBuilder` flattens arbitrarily nested `<span>` elements into `kOpenTag`/`kCloseTag` items, and `FontHeight::Merge` (`Nat.max` on `ascent` and `descent`) is associative, commutative, and idempotent, so stack push/pop and flat line accumulation produce identical enclosing `FontHeight` bounds for baseline-aligned items. | 2026-11-07 | owner (approved proposal) |
| Q4 | Differential oracle | **Approved by owner:** Use both (a) a bounded exhaustive vector generator in `docs/chromium-layout/model_vectors.py` following `bend-engine/model_vectors.py` (comparing Lean model outputs in `model_vectors.txt` against compiled Bend JavaScript `layout.mjs` in Vitest), and (b) transcribed test vectors from Chromium's `blink_unittests` at the pinned revision (`block_layout_algorithm_test.cc`, `inline_layout_algorithm_test.cc`, `geometry/box_strut_test.cc`). Reasoning: Browser installation (`playwright install`) is out of scope on this host, while combining exhaustive Lean-model vectors with `blink_unittests` cases tests both Lean-to-Bend-JS agreement and fidelity to Blink's unit test expectations. | 2026-11-07 | owner (approved proposal) |
| Q5 | `LEAN_STACK_SIZE_KB` under memory caps | **Approved by owner:** Wrap `bendtt.bin` via `BENDTT` in `docs/chromium-layout/check.sh` (and the cached `~/.bend/bendtt/<hash>/bendtt` shim) with `LEAN_STACK_SIZE_KB=262144` (256 MB) so `bend --verdict`'s internal override (`LEAN_STACK_SIZE_KB: "4194304"`) does not abort under the 900 MB cgroup memory cap. Reasoning: `bend` overwrites `LEAN_STACK_SIZE_KB` in the child environment when spawning `$BENDTT`; setting `LEAN_STACK_SIZE_KB=262144` inside the `BENDTT` wrapper script succeeds within the 900 MB limit. | 2026-11-07 | owner (approved proposal) |

---

## Changelog

| Date | Pin | Change |
|---|---|---|
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Roadmap written. Pin not yet re-verified in this repository (P0.5). |
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phase 0 complete (P0.1–P0.7): Q1–Q5 proposed; `Layout.lean` compiled; `spike/stack.bend --verdict` checked; `check.sh` and `pins.txt` added. |
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phases 1–4 complete (M1–M4): Laws 1–5 proved in Lean (`LayoutTypes.lean`, `LayoutBlock.lean`, `LayoutInline.lean`, `Layout.lean`) and Bend (`layout.bend`, `proof.bend`); Q1–Q5 approved by owner. |
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phase 5 complete (M5): `layout.mjs` compiled (`gen.sh`); 650 bounded vectors generated (`model_vectors.py` / `model_vectors.txt`) and verified (`tests/chromium_layout_bend.test.ts`); `CompilerCheckCore.lean` and `CompilerCheck.lean` extended for `Nat.max` (`>`) and record constructors (`compiler_check.py` / `compiler_check_report.txt`). |
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phase 6: 36-row Transcription Audit Table added with Reviewer 1 (model author) sign-off (Reviewer 2 pending); mechanized verification added in `verify_transcription.py` (checking `layout.bend`, `LayoutTypes.lean`, `pins.txt`, and pinned Chromium C++ slice hashes); external WPT layout geometry probe added in `wpt_geometry_check.cjs` (Playwright 1.63.0 + headless Chromium against `layout.mjs`). |
| 2026-11-07 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phase 7 complete: Assumptions Register documented in `README.md` and `ROADMAP.md`; explicit hypotheses and `LayoutUnit` (`2^31 - 1`) / `nat_chk` (`2^48 - 1`) overflow-bound theorems proved in `Layout.lean`. |
| 2026-11-09 | `36c121be58126ddbb0686965897b8c8ff9b246fb` | Phase 9 re-pin procedure and `repin.py` added (no re-pin done; pin unchanged). `tests/check_tests.sh` now skips with a warning when the pinned Chromium checkout is absent (`REQUIRE_CHROMIUM=1` makes it fail). |
