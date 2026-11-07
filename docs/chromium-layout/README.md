# docs/chromium-layout: Chromium Blink LayoutNG CSS 2.1 In-Flow Block & Inline Model

This directory contains the formal specification and mechanized proofs of Chromium Blink LayoutNG's CSS 2.1 in-flow block and inline formatting context algorithms (`BlockLayoutAlgorithm`, `LineBreaker`, `InlineLayoutStateStack`, `InlineLayoutAlgorithm`, `BoxStrut`, and `MarginStrut`), pinned at Chromium revision `36c121be58126ddbb0686965897b8c8ff9b246fb` (`third_party/blink/renderer/core/layout/`).

| File | What it is |
|------|------------|
| `SCOPE.md` | Scope definition, pinned Chromium revision, type inventory, the 5 mechanized laws (§4), assumptions (§5), SLOC count (§6), effort basis (§7), and boundaries (§8) |
| `ROADMAP.md` | Phase-by-phase execution roadmap (Phases 0–9), 36-row Transcription Audit Table (Phase 6), Assumptions Register (Phase 7), Decisions Log (Q1–Q5), and Changelog |
| `pins.txt` | The 67 in-scope C++ `.h` / `.cc` files under `third_party/blink/renderer/core/layout/` with their exact git blob SHA-1 hashes at `36c121be58126ddbb0686965897b8c8ff9b246fb` |
| `layout.bend` | Executable Bend 2 model of M1 (`BoxStrut`, `MarginStrut`, `FontHeight`), M2 (`layout_block`, `layout_children`), M3 (`break_lines`, `take_line`), and M4 (`create_line_box`, `apply_box_state_stack`, `stack_line_boxes`) |
| `proof.bend` | Mechanized Bend 2 proofs of Laws 1–5 (`bend proof.bend --verdict` prints `ALL PROOFS CHECK`) |
| `layout.mjs` | Compiled JavaScript module generated from `layout.bend` by `gen.sh` |
| `gen.sh` | Checks `layout.bend` (`--check-only`) and regenerates `layout.mjs` |
| `LayoutTypes.lean` | Lean 4.34.0 types, layout functions, exact `SCOPE.md` §4 theorem statements, Law 1 (`margin_strut_semilattice`), and `blink_m1_test_vectors_pass` |
| `LayoutBlock.lean` | Lean 4.34.0 proofs of Law 2 (`block_siblings_monotonic_non_overlapping`), Law 3 (`bfc_intrinsic_block_size_conservation`), and `blink_m2_test_vectors_pass` |
| `LayoutInline.lean` | Lean 4.34.0 proofs of Law 4 (`line_breaker_progress_and_partition`), Law 5 (`line_box_height_encloses_items`), `applyBoxStateStack_eq_accumulateLineMetrics`, `stackLineBoxes_monotonic_non_overlapping`, and `blink_m3_test_vectors_pass` / `blink_m4_test_vectors_pass` |
| `Layout.lean` | Top-level Lean 4.34.0 module (`all_five_laws_hold`) and Phase 7 Assumptions Register hypotheses and `LayoutUnit` (`2^31 - 1`) / `nat_chk` (`2^48 - 1`) overflow-bound theorems |
| `CompilerCheckCore.lean` | Extended translation-validation semantics and soundness proofs (`JE.condGt`, `BE.max`, `JRet.record`, `BRet.record`, `decomp_sound`, `rec_fn_correct`) |
| `CompilerCheck.lean` | Extended readers (`parseJS`, `parseRecJS`, `parseBend`) and kernel-checked validation (`layout_compiler_checked`, `layout_transitions_correct`) for `layout.mjs` and `$lp_max` |
| `model_vectors.py` / `model_vectors.txt` | Bounded vector generator and 650 committed test vectors across M1 (`M`), M2 (`B`), M3 (`L`), and M4 (`I`) |
| `compiler_check.py` / `compiler_check_report.txt` | Translation-validation runner and committed report extracting compiled functions from `layout.mjs` and `merge.mjs` |
| `verify_transcription.py` | Mechanized Phase 6 audit checker verifying every row of the Transcription Audit Table against `layout.bend`, `LayoutTypes.lean`, `pins.txt`, and the pinned Chromium C++ tree |
| `wpt_geometry_check.cjs` | External WPT layout geometry check running headless Chromium via Playwright 1.63.0 (`offsetTop`, `offsetLeft`, `offsetWidth`, `offsetHeight`, `getClientRects()`) against `layout.mjs` |
| `check.sh` | Full verification gate: runs `bend --verdict` on all `.bend` files, compiles all `.lean` modules sequentially under `<600 MB` RSS, verifies `#print axioms` on all theorems (no `sorryAx`), and runs `verify_transcription.py` |
| `../tests/chromium_layout_bend.test.ts` | Vitest suite running all 650 vectors in `model_vectors.txt`, `blink_unittests` vectors, `gen.sh` / `model_vectors.py` / `compiler_check.py` staleness checks, `verify_transcription.py`, and `wpt_geometry_check.cjs` |

## Commands

```sh
docs/chromium-layout/check.sh                              # Bend --verdict, Lean compilation & axiom gate, Phase 6 audit check
docs/chromium-layout/gen.sh                                # Regenerate layout.mjs from layout.bend
python3 docs/chromium-layout/model_vectors.py              # Regenerate model_vectors.txt (650 vectors)
python3 docs/chromium-layout/compiler_check.py             # Regenerate compiler_check_report.txt
python3 docs/chromium-layout/verify_transcription.py       # Verify Phase 6 Transcription Audit Table & Chromium blobs
node docs/chromium-layout/wpt_geometry_check.cjs           # Run Playwright + headless Chromium WPT geometry check
./node_modules/.bin/vitest run tests/chromium_layout_bend.test.ts
```

## Mechanized Laws (`SCOPE.md` §4)

| Law | Lean theorem | Bend theorem (`proof.bend`) | Compiled JS function (`layout.mjs`) | Verified in |
|---|---|---|---|---|
| **Law 1** (`MarginStrut` semilattice) | `margin_strut_semilattice` (`LayoutTypes.lean`) | `margin_strut_semilattice`, `margin_strut_append_assoc`, `margin_strut_append_comm`, `margin_strut_append_idem` | `margin_strut_append`, `margin_strut_sum`, `margin_strut_apply_offset` | Lean kernel, Bend `--verdict`, `CompilerCheck.lean`, 144 `M` vectors in `model_vectors.txt` |
| **Law 2** (Block siblings monotonic & non-overlapping) | `block_siblings_monotonic_non_overlapping` (`LayoutBlock.lean`) | `block_siblings_monotonic_non_overlapping_step`, `blink_m2_test_vectors` | `layout_block`, `layout_children` | Lean kernel, Bend `--verdict`, 416 `B` vectors in `model_vectors.txt`, `wpt_geometry_check.cjs` |
| **Law 3** (BFC intrinsic block-size conservation) | `bfc_intrinsic_block_size_conservation` (`LayoutBlock.lean`) | `bfc_intrinsic_block_size_conservation_step`, `blink_m2_test_vectors` | `layout_block`, `total_collapsed_flow_block_size` | Lean kernel, Bend `--verdict`, 416 `B` vectors in `model_vectors.txt`, `wpt_geometry_check.cjs` |
| **Law 4** (Line breaker progress, partition & non-overflow) | `line_breaker_progress_and_partition` (`LayoutInline.lean`) | `line_breaker_progress_bound`, `take_line_single_item_partition`, `take_line_single_item_non_break_count_le_one`, `blink_m3_test_vectors` | `break_lines`, `take_line`, `take_line_aux` | Lean kernel, Bend `--verdict`, 54 `L` vectors in `model_vectors.txt`, `wpt_geometry_check.cjs` |
| **Law 5** (Line box height encloses items & box-state equivalence) | `line_box_height_encloses_items`, `applyBoxStateStack_eq_accumulateLineMetrics` (`LayoutInline.lean`) | `line_box_height_encloses_items`, `line_box_height_encloses_font_heights`, `blink_m4_test_vectors` | `create_line_box`, `apply_box_state_stack`, `stack_line_boxes` | Lean kernel, Bend `--verdict`, 36 `I` vectors in `model_vectors.txt`, `wpt_geometry_check.cjs` |

## Assumptions Register (Phase 7, `SCOPE.md` §5 and §8)

No assumption is introduced as a Lean `axiom` (`check.sh` enforces that `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`). Instead, subsystem boundaries are represented as typed parameters and explicit hypotheses in `LayoutTypes.lean` and `Layout.lean`:

| Assumption | Source in Chromium | Model Representation & Precondition | Lean Hypothesis / Theorem (`Layout.lean`) |
|---|---|---|---|
| **1. Font metrics** (`SCOPE.md` §5.1) | `platform/fonts/font_height.h`, `SimpleFontData`, `inline/inline_box_state.h:35-85` | FreeType/Skia glyph tables are outside `core/layout/`. Each `InlineItem` and inline container carries a pre-computed `FontHeight { ascent : Nat, descent : Nat }` in `LayoutUnit`s (`1/64` px) with `ascent ≥ 0`, `descent ≥ 0`, and `ascent + descent ≤ 2^31 - 1`. | `FontMetricsBounded`, `font_height_merge_no_overflow`, `line_box_items_within_layout_unit` |
| **2. HarfBuzz text shaping, ICU line breaking & bidi** (`SCOPE.md` §5.2–5.3) | `platform/fonts/shaping/harfbuzz_shaper.h`, `platform/text/text_break_iterator.h`, `inline/inline_items_builder.cc` | Text is pre-segmented at candidate break opportunities into `TextSeg` tokens carrying shaped advance width `inline_size : Nat` and flags `can_break_after : Bool`, `is_trailing_space : Bool`. **Sub-additivity precondition:** joining adjacent unsplit text runs without hyphenation preserves width (`shapeWidth (s1 ++ s2) = shapeWidth s1 + shapeWidth s2`). | `ShapingSubadditive`, `shaping_segments_width_conservation` |
| **3. Computed style & length resolution** (`SCOPE.md` §5.4) | `core/style/computed_style.h`, `length_utils.cc` | CSS cascade, inheritance, `calc()`, `em`/`rem`/`vw`/`vh`, and percentage resolution are pre-resolved into `BoxStrut` (`border`, `padding`, `margin`), `Option Nat` (`explicitInlineSize`, `explicitBlockSize`), and `Bool` (`isNewBfc`) within `kLayoutUnitMax`. | `BoxStrutBounded`, `MarginStrutBounded`, `AllMarginsNonNegative`, `AllChildrenNonSelfCollapsing` |
| **4. `LayoutUnit` 32-bit saturating int vs. `Nat` and `2^48 - 1` JS limit** (`SCOPE.md` §8.2) | `platform/geometry/layout_unit.h` (`kLayoutUnitMax = 2^31 - 1 = 2,147,483,647`), `CompilerCheckCore.lean` (`LIMIT = 2^48 - 1`) | Blink's `LayoutUnit` saturates at `2^31 - 1`, whereas Lean/Bend `Nat` is unbounded and compiled Bend JS (`nat_chk`) checks `≤ 2^48 - 1`. The model agrees with Blink when inputs and sums stay within `kLayoutUnitMax = 2^31 - 1` (which also implies `≤ 2^48 - 1`). | `kLayoutUnitMax`, `kBendNatImmediateMax`, `kLayoutUnitMax_le_kBendNatImmediateMax`, `margin_strut_append_no_overflow`, `margin_strut_apply_offset_no_overflow`, `bfc_block_layout_within_layout_unit`, `blink_test_vectors_within_layout_unit_max` |
| **5. Subpixel rounding & physical pixel snapping** (`SCOPE.md` §8.3) | `LayoutUnit` division/rounding, `ToRoundedPoint`, `SnapSizeToPixel` | **Out of scope:** The model operates on exact integer `LayoutUnit`s after length resolution and before post-layout physical pixel snapping or zoom scaling. | Out of scope (documented here and in `ROADMAP.md` Phase 7) |
| **6. Caching & incremental layout** (`SCOPE.md` §8.4) | `BlockLayoutAlgorithm::TryReuseFragmentsFromCache`, `SimplifiedLayoutAlgorithm`, `InlineNodeData` caching | **Out of scope:** The model is a pure single-pass functional evaluator from `ConstraintSpace × BlockContainerNode` to `LayoutResult`; cache reuse across DOM mutations is out of scope. | Out of scope (documented here and in `ROADMAP.md` Phase 7) |

## What is Outside the First Fragment (Phase 8)

As documented in `SCOPE.md` §2 and `ROADMAP.md` Phase 8, the following subsystems are outside the first fragment and require separate scoped milestones:
- Floats and exclusion space (`ExclusionSpace`, `unpositioned_floats`)
- Out-of-flow (`position: absolute` / `fixed`), relative/sticky positioning, and CSS anchor positioning
- Block fragmentation, multi-column spanners, and pagination (`BlockBreakToken`)
- Flexbox, Grid, Table, Multicol, MathML, Ruby annotations, SVG text, and Custom layout
- Bidirectional reordering (UAX #9) and vertical writing modes
- Quirks-mode margin collapsing (`is_quirky_container_start`)
