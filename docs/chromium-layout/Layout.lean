/-
  docs/chromium-layout/Layout.lean

  Top-level module re-exporting the formal model of Chromium Blink LayoutNG's
  CSS 2.1 in-flow block and inline formatting contexts (`LayoutTypes`,
  `LayoutBlock`, `LayoutInline`) and verifying all five laws in `SCOPE.md` §4.

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

end ChromiumLayout
