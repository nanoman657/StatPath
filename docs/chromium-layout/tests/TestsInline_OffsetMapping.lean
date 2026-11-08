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

/-- Test: CollapseAcrossElements (offset_mapping_test.cc:253) -/
theorem test_OffsetMapping_CollapseAcrossElements :
    testCollapsing [DomNode.text 0 "text ", DomNode.text 1 " text"] = "{}{0}" := by
  decide

/-- Test: CollapseTrailingSpaces (offset_mapping_test.cc:266) -/
theorem test_OffsetMapping_CollapseTrailingSpaces :
    testCollapsing [DomNode.text 0 "text  "] = "{4, 5}" ∧
    testCollapsing [DomNode.text 0 "text", DomNode.text 1 " "] = "{}{0}" := by
  decide

/-- Test: CollapseLeadingNewlines (offset_mapping_test.cc:283) -/
theorem test_OffsetMapping_CollapseLeadingNewlines :
    testCollapsing [DomNode.text 0 "\ntext"] = "{0}" ∧
    testCollapsing [DomNode.text 0 "\n\ntext"] = "{0, 1}" := by
  decide

/-- Test: CollapseTrailingNewlines (offset_mapping_test.cc:299) -/
theorem test_OffsetMapping_CollapseTrailingNewlines :
    testCollapsing [DomNode.text 0 "text\n"] = "{4}" ∧
    testCollapsing [DomNode.text 0 "text", DomNode.text 1 "\n"] = "{}{0}" := by
  decide

/-- Test: CollapseNewlineAcrossElements (offset_mapping_test.cc:309) -/
theorem test_OffsetMapping_CollapseNewlineAcrossElements :
    testCollapsing [DomNode.text 0 "text ", DomNode.text 1 "\ntext"] = "{}{0}" ∧
    testCollapsing [DomNode.text 0 "text ", DomNode.text 1 "\n text"] = "{}{0, 1}" ∧
    testCollapsing [DomNode.text 0 "text", DomNode.text 1 " ", DomNode.text 2 "\ntext"] = "{}{}{0}" := by
  decide

/-- Test: CollapseBeforeAndAfterNewline (offset_mapping_test.cc:315) -/
theorem test_OffsetMapping_CollapseBeforeAndAfterNewline :
    testCollapsing [DomNode.text 0 "text  \n  text" .preLine] = "{4, 5, 7, 8}" := by
  decide

/-- Test: CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements (offset_mapping_test.cc:321) -/
theorem test_OffsetMapping_CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements :
    testCollapsing [DomNode.text 0 "text " .preWrap, DomNode.text 1 " text" .normal] = "{}{}" := by
  decide

/-- Test: TwoTextNodes (offset_mapping_test.cc:492) -/
theorem test_OffsetMapping_TwoTextNodes :
    let nodes := [DomNode.text 0 "foo", DomNode.text 1 "bar"]
    let units := buildDomOffsetMapping nodes
    (renderedTextContent nodes = "foobar") ∧
    (units.length = 2) ∧
    (units[0]! = { nodeId := 0, unitType := .identity, domStart := 0, domEnd := 3, textStart := 0, textEnd := 3 }) ∧
    (units[1]! = { nodeId := 1, unitType := .identity, domStart := 0, domEnd := 3, textStart := 3, textEnd := 6 }) ∧
    (domToTextContentOffset units 0 0 = 0) ∧
    (domToTextContentOffset units 0 1 = 1) ∧
    (domToTextContentOffset units 0 2 = 2) ∧
    (domToTextContentOffset units 0 3 = 3) ∧
    (domToTextContentOffset units 1 0 = 3) ∧
    (domToTextContentOffset units 1 1 = 4) ∧
    (domToTextContentOffset units 1 2 = 5) ∧
    (domToTextContentOffset units 1 3 = 6) ∧
    (isBeforeNonCollapsed (unitsForNode units 0) 0 = true) ∧
    (isBeforeNonCollapsed (unitsForNode units 0) 1 = true) ∧
    (isBeforeNonCollapsed (unitsForNode units 0) 2 = true) ∧
    (isBeforeNonCollapsed (unitsForNode units 0) 3 = false) ∧
    (isBeforeNonCollapsed (unitsForNode units 1) 0 = true) ∧
    (isBeforeNonCollapsed (unitsForNode units 1) 1 = true) ∧
    (isBeforeNonCollapsed (unitsForNode units 1) 2 = true) ∧
    (isBeforeNonCollapsed (unitsForNode units 1) 3 = false) ∧
    (isAfterNonCollapsed (unitsForNode units 0) 0 = false) ∧
    (isAfterNonCollapsed (unitsForNode units 0) 1 = true) ∧
    (isAfterNonCollapsed (unitsForNode units 0) 2 = true) ∧
    (isAfterNonCollapsed (unitsForNode units 0) 3 = true) ∧
    (isAfterNonCollapsed (unitsForNode units 1) 0 = false) ∧
    (isAfterNonCollapsed (unitsForNode units 1) 1 = true) ∧
    (isAfterNonCollapsed (unitsForNode units 1) 2 = true) ∧
    (isAfterNonCollapsed (unitsForNode units 1) 3 = true) := by
  decide

/-- Test: BRBetweenTextNodes (offset_mapping_test.cc:558) -/
theorem test_OffsetMapping_BRBetweenTextNodes :
    let nodes := [DomNode.text 0 "foo", DomNode.br 1, DomNode.text 2 "bar"]
    let units := buildDomOffsetMapping nodes
    (renderedTextContent nodes = "foo\nbar") ∧
    (units.length = 3) ∧
    (units[0]! = { nodeId := 0, unitType := .identity, domStart := 0, domEnd := 3, textStart := 0, textEnd := 3 }) ∧
    (units[1]! = { nodeId := 1, unitType := .identity, domStart := 0, domEnd := 1, textStart := 3, textEnd := 4 }) ∧
    (units[2]! = { nodeId := 2, unitType := .identity, domStart := 0, domEnd := 3, textStart := 4, textEnd := 7 }) := by
  decide

/-- Test: PreLine (offset_mapping_test.cc:1128) -/
theorem test_OffsetMapping_PreLine :
    let nodes := [DomNode.text 0 "ab \n cd" .preLine]
    let units := buildDomOffsetMapping nodes
    (renderedTextContent nodes = "ab\ncd") ∧
    (units = [
      { nodeId := 0, unitType := .identity, domStart := 0, domEnd := 2, textStart := 0, textEnd := 2 },
      { nodeId := 0, unitType := .collapsed, domStart := 2, domEnd := 3, textStart := 2, textEnd := 2 },
      { nodeId := 0, unitType := .identity, domStart := 3, domEnd := 4, textStart := 2, textEnd := 3 },
      { nodeId := 0, unitType := .collapsed, domStart := 4, domEnd := 5, textStart := 3, textEnd := 3 },
      { nodeId := 0, unitType := .identity, domStart := 5, domEnd := 7, textStart := 3, textEnd := 5 }
    ]) := by
  decide

end ChromiumLayout.TestsInline
