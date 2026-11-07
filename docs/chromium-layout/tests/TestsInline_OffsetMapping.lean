/-
  docs/chromium-layout/tests/TestsInline_OffsetMapping.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/offset_mapping_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineItemBuilder
import InlineOffsetMapping

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from offset_mapping_test.cc -/

/-- Test: CollapseSpaces (offset_mapping_test.cc:213) -/
theorem test_OffsetMapping_CollapseSpaces :
    let input := "text text  text   text"
    collapsedIndices .normal input = [10, 16, 17] ∧
    collapsedIndices .nowrap input = [10, 16, 17] ∧
    collapsedIndices .pre input = [] ∧
    collapsedIndices .preWrap input = [] := by
  decide

/-- Test: CollapseTabs (offset_mapping_test.cc:224) -/
theorem test_OffsetMapping_CollapseTabs :
    let input := "text text \ttext \t\ttext"
    collapsedIndices .normal input = [10, 16, 17] ∧
    collapsedIndices .pre input = [] ∧
    collapsedIndices .preWrap input = [] := by
  decide

/-- Test: CollapseNewLines (offset_mapping_test.cc:235) -/
theorem test_OffsetMapping_CollapseNewLines :
    let input := "text\ntext \n text\n\ntext"
    collapsedIndices .normal input = [10, 11, 17] ∧
    collapsedIndices .pre input = [] ∧
    collapsedIndices .preWrap input = [] := by
  decide

/-- Test: CollapseNewlinesAsSpaces (offset_mapping_test.cc:246) -/
theorem test_OffsetMapping_CollapseNewlinesAsSpaces :
    collapsedIndices .normal "text\ntext" = [] ∧
    collapsedIndices .normal "text\n\ntext" = [5] ∧
    collapsedIndices .normal "text \n\n text" = [5, 6, 7] ∧
    collapsedIndices .normal "text \n \n text" = [5, 6, 7, 8] := by
  decide

/-- Test: CollapseLeadingSpaces (offset_mapping_test.cc:258) -/
theorem test_OffsetMapping_CollapseLeadingSpaces :
    collapsedIndices .normal "  text" = [0, 1] := by
  decide

/-- Test: OneTextNode (offset_mapping_test.cc:429) -/
theorem test_OffsetMapping_OneTextNode :
    computeOffsetMappingUnits .normal "foo" =
      [{ unitType := .identity, domStart := 0, domEnd := 3, textStart := 0, textEnd := 3 }] := by
  decide

/-- Test: OneTextNodeWithCollapsedSpace (offset_mapping_test.cc:613) -/
theorem test_OffsetMapping_OneTextNodeWithCollapsedSpace :
    computeOffsetMappingUnits .normal "foo  bar" =
      [ { unitType := .identity, domStart := 0, domEnd := 4, textStart := 0, textEnd := 4 }
      , { unitType := .collapsed, domStart := 4, domEnd := 5, textStart := 4, textEnd := 4 }
      , { unitType := .identity, domStart := 5, domEnd := 8, textStart := 4, textEnd := 7 }
      ] := by
  decide

end ChromiumLayout.TestsInline
