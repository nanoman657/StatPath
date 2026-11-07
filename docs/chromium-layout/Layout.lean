/-
  docs/chromium-layout/Layout.lean

  Top-level module re-exporting the formal model of Chromium Blink LayoutNG's
  CSS 2.1 in-flow block and inline formatting contexts (`LayoutTypes`,
  `LayoutBlock`, `LayoutInline`), verifying all five laws in `SCOPE.md` §4,
  and formalizing the Phase 7 Assumptions Register (`SCOPE.md` §5 and §8)
  as explicit hypotheses and `LayoutUnit` / `nat_chk` overflow-bound theorems.

  Pinned Chromium revision: 36c121be58126ddbb0686965897b8c8ff9b246fb
  Subtree: third_party/blink/renderer/core/layout/
-/
import LayoutTypes
import LayoutBlock
import LayoutInline

namespace ChromiumLayout

/-- All five `SCOPE.md` §4 laws hold simultaneously without `sorryAx`. -/
theorem all_five_laws_hold :
    margin_strut_semilattice_stmt ∧
    block_siblings_monotonic_non_overlapping_stmt ∧
    bfc_intrinsic_block_size_conservation_stmt ∧
    line_breaker_progress_and_partition_stmt ∧
    line_box_height_encloses_items_stmt :=
  ⟨ margin_strut_semilattice
  , block_siblings_monotonic_non_overlapping
  , bfc_intrinsic_block_size_conservation
  , line_breaker_progress_and_partition
  , line_box_height_encloses_items ⟩

-- ==============================================================================
-- Phase 7: Assumptions Register & `LayoutUnit` / `2^48 - 1` Overflow Bounds
-- (`SCOPE.md` §5 and §8, `ROADMAP.md` Phase 7)
-- ==============================================================================

/-- Blink's 32-bit signed saturating `LayoutUnit` maximum (`2^31 - 1 = 2,147,483,647`
    raw units, i.e. `33,554,431.984375` CSS pixels at `1/64` px per `LayoutUnit`,
    `platform/geometry/layout_unit.h`). -/
def kLayoutUnitMax : Nat := 2147483647

/-- The Bend-to-JavaScript compiler's immediate `Nat` limit (`2^48 - 1 = 281,474,976,710,655`),
    enforced at runtime by `nat_chk` in `layout.mjs` and formalized as `LIMIT` in
    `bend-tls/browser/core/Transitions.lean` and `docs/chromium-layout/CompilerCheckCore.lean`. -/
def kBendNatImmediateMax : Nat := 281474976710655

/-- Every quantity bounded by `kLayoutUnitMax` (`2^31 - 1`) is strictly within the
    Bend JS runtime immediate bound `kBendNatImmediateMax` (`2^48 - 1`). -/
theorem kLayoutUnitMax_le_kBendNatImmediateMax :
    kLayoutUnitMax ≤ kBendNatImmediateMax := by
  unfold kLayoutUnitMax kBendNatImmediateMax
  omega

/-- Assumption 1 (`SCOPE.md` §5.1, Font Metrics):
    Input `FontHeight` on each item comes from `SimpleFontData` / `FontMetrics`
    with non-negative `ascent` and `descent` whose sum (`lineHeight`) does not
    exceed `kLayoutUnitMax` (`2^31 - 1`). -/
def FontMetricsBounded (h : FontHeight) : Prop :=
  h.ascent + h.descent ≤ kLayoutUnitMax

/-- Assumption 2 (`SCOPE.md` §5.2–5.3, HarfBuzz Shaping & ICU Line-Break / Bidi):
    Joining two adjacent unsplit text runs without hyphenation has shaped advance
    width equal to the sum of their segment widths (sub-additivity / additivity). -/
def ShapingSubadditive (shapeWidth : String → Nat) : Prop :=
  ∀ s1 s2 : String, shapeWidth (s1 ++ s2) = shapeWidth s1 + shapeWidth s2

/-- Concatenation of pre-segmented text tokens (`SCOPE.md` §5.2). -/
def concatSegments : List String → String
  | [] => ""
  | s :: rest => s ++ concatSegments rest

/-- Under `ShapingSubadditive`, the sum of segment widths across any list of
    pre-segmented text tokens equals the shaped width of their concatenation. -/
theorem shaping_segments_width_conservation
    (shapeWidth : String → Nat)
    (hEmpty : shapeWidth "" = 0)
    (hSub : ShapingSubadditive shapeWidth) :
    ∀ segs : List String,
      (segs.map shapeWidth).sum = shapeWidth (concatSegments segs)
  | [] => by simp [concatSegments, hEmpty]
  | s :: rest => by
    have ih := shaping_segments_width_conservation shapeWidth hEmpty hSub rest
    simp only [List.map_cons, List.sum_cons, concatSegments, ih]
    exact (hSub s (concatSegments rest)).symm

/-- Assumption 3 (`SCOPE.md` §5.4, Computed Style & Length Resolution):
    CSS lengths (`border`, `padding`, `margin`, `explicitInlineSize`, `explicitBlockSize`)
    are pre-resolved into `BoxStrut` and `Option Nat` within `kLayoutUnitMax`. -/
def BoxStrutBounded (s : BoxStrut) : Prop :=
  s.inlineSum ≤ kLayoutUnitMax ∧ s.blockSum ≤ kLayoutUnitMax

def MarginStrutBounded (s : MarginStrut) : Prop :=
  s.pos ≤ kLayoutUnitMax ∧ s.neg ≤ kLayoutUnitMax

/-- Assumption 4 (`SCOPE.md` §8.2, `LayoutUnit` `2^31 - 1` Bound):
    If two `MarginStrut`s are bounded by `kLayoutUnitMax`, then `MarginStrut.append`
    and `MarginStrut.sum` produce no intermediate or result exceeding `kLayoutUnitMax`
    (or `kBendNatImmediateMax`). -/
theorem margin_strut_append_no_overflow (s1 s2 : MarginStrut)
    (h1 : MarginStrutBounded s1) (h2 : MarginStrutBounded s2) :
    MarginStrutBounded (MarginStrut.append s1 s2) ∧
    (MarginStrut.append s1 s2).sum ≤ kLayoutUnitMax ∧
    (MarginStrut.append s1 s2).sum ≤ kBendNatImmediateMax := by
  rcases h1 with ⟨h1p, h1n⟩
  rcases h2 with ⟨h2p, h2n⟩
  have hlim := kLayoutUnitMax_le_kBendNatImmediateMax
  simp only [MarginStrutBounded, MarginStrut.append, MarginStrut.sum, Nat.max_def]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> (split <;> (try split) <;> omega)

/-- If `y + s.pos ≤ kLayoutUnitMax`, then `MarginStrut.applyOffset y s` has no
    intermediate or output exceeding `kLayoutUnitMax` or `kBendNatImmediateMax`. -/
theorem margin_strut_apply_offset_no_overflow (y : Nat) (s : MarginStrut)
    (hy : y + s.pos ≤ kLayoutUnitMax) :
    y + s.pos ≤ kBendNatImmediateMax ∧
    MarginStrut.applyOffset y s ≤ kLayoutUnitMax ∧
    MarginStrut.applyOffset y s ≤ kBendNatImmediateMax := by
  have hlim := kLayoutUnitMax_le_kBendNatImmediateMax
  simp only [MarginStrut.applyOffset]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- If two `FontHeight`s have `ascent ≤ A` and `descent ≤ D` with `A + D ≤ kLayoutUnitMax`,
    then `FontHeight.merge` preserves the bound and its `lineHeight` never exceeds
    `kLayoutUnitMax` or `kBendNatImmediateMax`. -/
theorem font_height_merge_no_overflow (A D : Nat) (h1 h2 : FontHeight)
    (hAD : A + D ≤ kLayoutUnitMax)
    (h1a : h1.ascent ≤ A) (h1d : h1.descent ≤ D)
    (h2a : h2.ascent ≤ A) (h2d : h2.descent ≤ D) :
    (FontHeight.merge h1 h2).ascent ≤ A ∧
    (FontHeight.merge h1 h2).descent ≤ D ∧
    (FontHeight.merge h1 h2).lineHeight ≤ kLayoutUnitMax ∧
    (FontHeight.merge h1 h2).lineHeight ≤ kBendNatImmediateMax := by
  have hlim := kLayoutUnitMax_le_kBendNatImmediateMax
  simp only [FontHeight.merge, FontHeight.lineHeight, Nat.max_def]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (split <;> (try split) <;> omega)

/-- For any line box whose accumulated `metrics` satisfies `FontMetricsBounded`
    (`line.metrics.ascent + line.metrics.descent ≤ kLayoutUnitMax`), every placed item's
    block end (`item.blockOffset + item.blockSize`) stays within `kLayoutUnitMax`
    (`2^31 - 1`) and `kBendNatImmediateMax` (`2^48 - 1`). -/
theorem line_box_items_within_layout_unit
    (strut : FontHeight) (lineInfo : LineInfo)
    (hBound : FontMetricsBounded (createLineBox strut lineInfo).metrics)
    (item : PlacedInlineItem)
    (hMem : item ∈ (createLineBox strut lineInfo).items) :
    item.blockOffset + item.blockSize ≤ kLayoutUnitMax ∧
    item.blockOffset + item.blockSize ≤ kBendNatImmediateMax := by
  have hEnc := line_box_height_encloses_items strut lineInfo item hMem
  have hlim := kLayoutUnitMax_le_kBendNatImmediateMax
  unfold FontMetricsBounded at hBound
  exact ⟨Nat.le_trans hEnc hBound, Nat.le_trans hEnc (Nat.le_trans hBound hlim)⟩

/-- Explicit `LayoutUnit` (`2^31 - 1`) input bound hypothesis for a BFC-root block container:
    when the total block-axis flow (`border.blockStart + padding.blockStart +
    totalCollapsedFlowBlockSize children + padding.blockEnd + border.blockEnd`) is at most
    `kLayoutUnitMax`, `layoutBlock`'s `intrinsicBlockSize` and `borderBoxSize.blockSize`
    stay within `kLayoutUnitMax` (`2^31 - 1`) and `kBendNatImmediateMax` (`2^48 - 1`). -/
theorem bfc_block_layout_within_layout_unit
    (space : ConstraintSpace) (node : BlockContainerNode)
    (hBfc : node.isNewBfc = true) (hAuto : node.explicitBlockSize = none)
    (hNonSelf : AllChildrenNonSelfCollapsing node)
    (hBound :
      node.border.blockStart + node.padding.blockStart +
      totalCollapsedFlowBlockSize node.children +
      node.padding.blockEnd + node.border.blockEnd ≤ kLayoutUnitMax) :
    (layoutBlock space node).intrinsicBlockSize ≤ kLayoutUnitMax ∧
    (layoutBlock space node).intrinsicBlockSize ≤ kBendNatImmediateMax := by
  have hLaw3 := bfc_intrinsic_block_size_conservation space node hBfc hAuto hNonSelf
  have hlim := kLayoutUnitMax_le_kBendNatImmediateMax
  rw [hLaw3]
  exact ⟨hBound, Nat.le_trans hBound hlim⟩

/-- Every transcribed `blink_unittests` test vector in M1, M2, M3, and M4 has both
    sides strictly below `kLayoutUnitMax` (`2^31 - 1`) and `kBendNatImmediateMax` (`2^48 - 1`). -/
theorem blink_test_vectors_within_layout_unit_max :
    ((blinkM1TestVectors ++ blinkM2TestVectors ++ blinkM3TestVectors ++ blinkM4TestVectors).all
      fun p => decide (p.1 ≤ kLayoutUnitMax ∧ p.2 ≤ kLayoutUnitMax ∧
                       p.1 ≤ kBendNatImmediateMax ∧ p.2 ≤ kBendNatImmediateMax)) = true := rfl

end ChromiumLayout
