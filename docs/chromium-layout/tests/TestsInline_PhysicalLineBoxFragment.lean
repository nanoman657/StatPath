/-
  docs/chromium-layout/tests/TestsInline_PhysicalLineBoxFragment.lean

  Formalized tests for CSS 2.1 §9.5, §9.3 and Blink PhysicalLineBoxFragment
  (`third_party/blink/renderer/core/layout/inline/physical_line_box_fragment_test.cc`).
-/
import LayoutTypes
import InlineLineBox

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test `PhysicalLineBoxFragmentTest.HasPropagatedDescendantsFloat` (`inline/physical_line_box_fragment_test.cc:44`).
    Line 1 has only normal text; Line 2 has a float, propagating descendants to containing block. -/
theorem physicalLineBoxFragment_hasPropagatedDescendantsFloat :
    let line1 := [LineItemKind.normalFlow]
    let line2 := [LineItemKind.normalFlow, LineItemKind.float]
    (hasPropagatedDescendants line1 = false) ∧
    (hasPropagatedDescendants line2 = true) := by
  decide

/-- Test `PhysicalLineBoxFragmentTest.HasPropagatedDescendantsOOF` (`inline/physical_line_box_fragment_test.cc:62`).
    Line 1 has only normal text; Line 2 has an out-of-flow positioned box, propagating descendants to containing block. -/
theorem physicalLineBoxFragment_hasPropagatedDescendantsOOF :
    let line1 := [LineItemKind.normalFlow]
    let line2 := [LineItemKind.normalFlow, LineItemKind.outOfFlow]
    (hasPropagatedDescendants line1 = false) ∧
    (hasPropagatedDescendants line2 = true) := by
  decide

end ChromiumLayout.TestsInline
