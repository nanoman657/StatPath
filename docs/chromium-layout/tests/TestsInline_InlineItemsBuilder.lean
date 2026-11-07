/-
  docs/chromium-layout/tests/TestsInline_InlineItemsBuilder.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/inline_items_builder_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineItemBuilder

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from inline_items_builder_test.cc -/

/-- Test 1: CollapseSpaces (inline_items_builder_test.cc:206) -/
theorem inlineItemsBuilder_collapseSpaces :
    let input := "text text  text   text".toList
    String.ofList (collapseText .normal input) = "text text text text" ∧
    String.ofList (collapseText .pre input) = "text text  text   text" := by
  decide

/-- Test 2: CollapseTabs (inline_items_builder_test.cc:216) -/
theorem inlineItemsBuilder_collapseTabs :
    let input := "text\ttext\t\ttext".toList
    String.ofList (collapseText .normal input) = "text text text" := by
  decide

/-- Test 3: CollapseNewLines (inline_items_builder_test.cc:226) -/
theorem inlineItemsBuilder_collapseNewlines :
    let input := "text\ntext\n\ntext".toList
    String.ofList (collapseText .normal input) = "text text text" ∧
    String.ofList (collapseText .pre input) = "text\ntext\n\ntext" := by
  decide

/-- Test 4: CollapseNewlinesAsSpaces (inline_items_builder_test.cc:236) -/
theorem inlineItemsBuilder_collapseNewlinesAsSpaces :
    String.ofList (collapseText .normal "text\ntext".toList) = "text text" ∧
    String.ofList (collapseText .normal "text \n\n text".toList) = "text text" := by
  decide

/-- Test 5: CollapseAcrossElements (inline_items_builder_test.cc:243) -/
theorem inlineItemsBuilder_collapseAcrossElements :
    String.ofList (collapseText .normal "text  text".toList) = "text text" := by
  decide

/-- Test 6: CollapseLeadingSpaces (inline_items_builder_test.cc:248) -/
theorem inlineItemsBuilder_collapseLeadingSpaces :
    String.ofList (collapseText .normal "  text".toList) = "text" := by
  decide

/-- Test 7: CollapseTrailingSpaces (inline_items_builder_test.cc:254) -/
theorem inlineItemsBuilder_collapseTrailingSpaces :
    String.ofList (collapseText .normal "text  ".toList) = "text" := by
  decide

/-- Test 8: CollapseAllSpaces (inline_items_builder_test.cc:260) -/
theorem inlineItemsBuilder_collapseAllSpaces :
    String.ofList (collapseText .normal "  ".toList) = "" ∧
    String.ofList (collapseText .normal "  \n  ".toList) = "" := by
  decide

/-- Test 9: CollapseLeadingNewlines (inline_items_builder_test.cc:267) -/
theorem inlineItemsBuilder_collapseLeadingNewlines :
    String.ofList (collapseText .normal "\n\ntext".toList) = "text" := by
  decide

/-- Test 10: CollapseTrailingNewlines (inline_items_builder_test.cc:281) -/
theorem inlineItemsBuilder_collapseTrailingNewlines :
    String.ofList (collapseText .normal "text\n\n".toList) = "text" := by
  decide

/-- Test 11: CollapseNewlineAcrossElements (inline_items_builder_test.cc:289) -/
theorem inlineItemsBuilder_collapseNewlineAcrossElements :
    String.ofList (collapseText .normal "text \ntext".toList) = "text text" := by
  decide

end ChromiumLayout.TestsInline
