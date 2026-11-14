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

/-- Test: FullyCollapsedWhiteSpaceNode (offset_mapping_test.cc:686)
    CSS Text 3 §4.1.2: Completely collapsed whitespace node generates collapsed unit. -/
theorem test_OffsetMapping_FullyCollapsedWhiteSpaceNode :
    let nodes := [DomNode.text 1 "foo ", DomNode.text 2 " ", DomNode.text 3 "bar"]
    let units := buildDomOffsetMapping nodes
    (renderedTextContent nodes = "foo bar") ∧
    (units = [
      { nodeId := 1, unitType := .identity, domStart := 0, domEnd := 4, textStart := 0, textEnd := 4 },
      { nodeId := 2, unitType := .collapsed, domStart := 0, domEnd := 1, textStart := 4, textEnd := 4 },
      { nodeId := 3, unitType := .identity, domStart := 0, domEnd := 3, textStart := 4, textEnd := 7 }
    ]) := by
  decide

/-- Test: ReplacedElement (offset_mapping_test.cc:748)
    CSS 2.1 §9.4.2: Atomic inline / replaced element forms identity unit of length 1;
    positions at boundaries resolve to BeforeNode and AfterNode. -/
theorem test_OffsetMapping_ReplacedElement :
    let fooNode := 1
    let imgNode := 2
    let barNode := 3
    let nodes := [DomNode.text fooNode "foo ", DomNode.replaced imgNode, DomNode.text barNode " bar"]
    let units := buildDomOffsetMapping nodes
    (units.length = 3) ∧
    (units[0]! = { nodeId := fooNode, unitType := .identity, domStart := 0, domEnd := 4, textStart := 0, textEnd := 4 }) ∧
    (units[1]! = { nodeId := imgNode, unitType := .identity, domStart := 0, domEnd := 1, textStart := 4, textEnd := 5 }) ∧
    (units[2]! = { nodeId := barNode, unitType := .identity, domStart := 0, domEnd := 4, textStart := 5, textEnd := 9 }) ∧
    (getUnitForPosition units (.offset fooNode 0) = some units[0]!) ∧
    (getUnitForPosition units (.offset fooNode 4) = some units[0]!) ∧
    (getUnitForPosition units (.beforeNode imgNode) = some units[1]!) ∧
    (getUnitForPosition units (.afterNode imgNode) = some units[1]!) ∧
    (getUnitForPosition units (.offset barNode 0) = some units[2]!) ∧
    (getTextContentOffset units (.offset fooNode 4) = some 4) ∧
    (getTextContentOffset units (.beforeNode imgNode) = some 4) ∧
    (getTextContentOffset units (.afterNode imgNode) = some 5) ∧
    (getTextContentOffset units (.offset barNode 0) = some 5) ∧
    (getFirstPosition units 4 = some (.offset fooNode 4)) ∧
    (getLastPosition units 4 = some (.beforeNode imgNode)) ∧
    (getFirstPosition units 5 = some (.afterNode imgNode)) ∧
    (getLastPosition units 5 = some (.offset barNode 0)) := by
  decide

/-- Test: FirstLetter (offset_mapping_test.cc:805)
    CSS Pseudo 4 §7: First-letter and remaining text are partitioned into separate mapping units. -/
theorem test_OffsetMapping_FirstLetter :
    let fooNode := 1
    let nodes := [DomNode.text fooNode "foo" .normal true]
    let units := buildDomOffsetMapping nodes
    (units.length = 2) ∧
    (units[0]! = { nodeId := fooNode, unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }) ∧
    (units[1]! = { nodeId := fooNode, unitType := .identity, domStart := 1, domEnd := 3, textStart := 1, textEnd := 3 }) ∧
    (getTextContentOffset units (.offset fooNode 0) = some 0) ∧
    (getTextContentOffset units (.offset fooNode 1) = some 1) ∧
    (getTextContentOffset units (.offset fooNode 2) = some 2) := by
  decide

/-- Test: FirstLetterWithLeadingSpace (offset_mapping_test.cc:835)
    CSS Pseudo 4 §7 & CSS Text 3 §4.1: Leading whitespace collapses before first-letter identity unit. -/
theorem test_OffsetMapping_FirstLetterWithLeadingSpace :
    let fooNode := 1
    let nodes := [DomNode.text fooNode "  foo" .normal true]
    let units := buildDomOffsetMapping nodes
    (units.length = 3) ∧
    (units[0]! = { nodeId := fooNode, unitType := .collapsed, domStart := 0, domEnd := 2, textStart := 0, textEnd := 0 }) ∧
    (units[1]! = { nodeId := fooNode, unitType := .identity, domStart := 2, domEnd := 3, textStart := 0, textEnd := 1 }) ∧
    (units[2]! = { nodeId := fooNode, unitType := .identity, domStart := 3, domEnd := 5, textStart := 1, textEnd := 3 }) ∧
    (getTextContentOffset units (.offset fooNode 0) = some 0) ∧
    (getTextContentOffset units (.offset fooNode 2) = some 0) ∧
    (getTextContentOffset units (.offset fooNode 3) = some 1) ∧
    (getTextContentOffset units (.offset fooNode 4) = some 2) := by
  decide

/-- Test: FirstLetterWithoutRemainingText (offset_mapping_test.cc:871)
    CSS Pseudo 4 §7: First-letter without remaining text produces collapsed unit and single identity unit. -/
theorem test_OffsetMapping_FirstLetterWithoutRemainingText :
    let textNode := 1
    let nodes := [DomNode.text textNode "  f" .normal true]
    let units := buildDomOffsetMapping nodes
    (units.length = 2) ∧
    (units[0]! = { nodeId := textNode, unitType := .collapsed, domStart := 0, domEnd := 2, textStart := 0, textEnd := 0 }) ∧
    (units[1]! = { nodeId := textNode, unitType := .identity, domStart := 2, domEnd := 3, textStart := 0, textEnd := 1 }) ∧
    (getTextContentOffset units (.offset textNode 0) = some 0) ∧
    (getTextContentOffset units (.offset textNode 2) = some 0) ∧
    (getTextContentOffset units (.offset textNode 3) = some 1) := by
  decide

/-- Test: FirstLetterInDifferentBlock (offset_mapping_test.cc:902)
    CSS Pseudo 4 §7: Floating or block first-letter is mapped in its own block formatting context. -/
theorem test_OffsetMapping_FirstLetterInDifferentBlock :
    let textNode := 1
    let (firstUnits, remUnits) := firstLetterBlockOffsetMapping textNode "foo"
    (firstUnits.length = 1) ∧
    (firstUnits[0]! = { nodeId := textNode, unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }) ∧
    (remUnits.length = 1) ∧
    (remUnits[0]! = { nodeId := textNode, unitType := .identity, domStart := 1, domEnd := 3, textStart := 0, textEnd := 2 }) := by
  decide

/-- Test: WhiteSpaceTextNodeWithoutLayoutText (offset_mapping_test.cc:967)
    CSS Text 3 §4.1.2: Completely collapsed leading whitespace node contains no non-collapsed content. -/
theorem test_OffsetMapping_WhiteSpaceTextNodeWithoutLayoutText :
    let textNode := 1
    let spanNode := 2
    let nodes := [DomNode.text textNode " ", DomNode.text spanNode "foo"]
    let units := buildDomOffsetMapping nodes
    (endOfLastNonCollapsedContent units textNode 1 = none) ∧
    (startOfNextNonCollapsedContent units textNode 0 = none) := by
  decide

/-- Test: ContainerWithGeneratedContent (offset_mapping_test.cc:976)
    CSS 2.1 §12.1: Generated content ::before and ::after pseudo-elements receive dedicated
    OffsetMappingUnits and queryable mapping units. -/
theorem test_OffsetMapping_ContainerWithGeneratedContent :
    let beforeNode := 1
    let textNode := 2
    let afterNode := 3
    let nodes := [DomNode.text beforeNode "bar" .normal false,
                  DomNode.text textNode "foo" .normal false,
                  DomNode.text afterNode "baz" .normal false]
    let units := buildDomOffsetMapping nodes
    (units.length = 3) ∧
    (units[0]! = { nodeId := beforeNode, unitType := .identity, domStart := 0, domEnd := 3, textStart := 0, textEnd := 3 }) ∧
    (units[1]! = { nodeId := textNode, unitType := .identity, domStart := 0, domEnd := 3, textStart := 3, textEnd := 6 }) ∧
    (units[2]! = { nodeId := afterNode, unitType := .identity, domStart := 0, domEnd := 3, textStart := 6, textEnd := 9 }) ∧
    (getMappingUnitsForNode units beforeNode = [units[0]!]) ∧
    (getMappingUnitsForNode units afterNode = [units[2]!]) := by
  decide

/-- Test: NoWrapSpaceAndCollapsibleSpace (offset_mapping_test.cc:1098)
    CSS Text 3 §5.2: Boundary between nowrap whitespace and collapsible space
    preserves nowrap space and collapses subsequent normal space. -/
theorem test_OffsetMapping_NoWrapSpaceAndCollapsibleSpace :
    let spanNode := 1
    let barNode := 2
    let units := buildNoWrapBoundaryMapping spanNode barNode "foo " " bar"
    (units.length = 3) ∧
    (units[0]! = { nodeId := spanNode, unitType := .identity, domStart := 0, domEnd := 4, textStart := 0, textEnd := 4 }) ∧
    (units[1]! = { nodeId := barNode, unitType := .collapsed, domStart := 0, domEnd := 1, textStart := 5, textEnd := 5 }) ∧
    (units[2]! = { nodeId := barNode, unitType := .identity, domStart := 1, domEnd := 4, textStart := 5, textEnd := 8 }) := by
  decide

/-- Test: RestoreTrailingCollapsibleSpaceReplace (offset_mapping_test.cc:1266)
    CSS Text 3 §4.1: Collapsible space followed only by whitespace and block-end remains collapsed. -/
theorem test_OffsetMapping_RestoreTrailingCollapsibleSpaceReplace :
    let bNode := 2
    let bUnits := resolveTrailingCollapsibleSpace false 1 2 bNode
    (bUnits.length = 1) ∧
    (bUnits[0]! = { nodeId := bNode, unitType := .collapsed, domStart := 0, domEnd := 1, textStart := 2, textEnd := 2 }) := by
  decide

/-- Test: RestoreTrailingCollapsibleSpaceReplaceKeep (offset_mapping_test.cc:1295)
    CSS Text 3 §4.1: Collapsible space followed by visible text is restored to identity unit. -/
theorem test_OffsetMapping_RestoreTrailingCollapsibleSpaceReplaceKeep :
    let bNode := 2
    let bUnits := resolveTrailingCollapsibleSpace true 1 2 bNode
    (bUnits.length = 1) ∧
    (bUnits[0]! = { nodeId := bNode, unitType := .identity, domStart := 0, domEnd := 1, textStart := 2, textEnd := 3 }) := by
  decide

/-- Test: RestoreTrailingCollapsibleSpaceNone (offset_mapping_test.cc:1324)
    CSS Text 3 §4.1: First collapsible space followed by visible text is restored; remainder collapses. -/
theorem test_OffsetMapping_RestoreTrailingCollapsibleSpaceNone :
    let bNode := 2
    let bUnits := resolveTrailingCollapsibleSpace true 3 1 bNode
    (bUnits.length = 2) ∧
    (bUnits[0]! = { nodeId := bNode, unitType := .identity, domStart := 0, domEnd := 1, textStart := 1, textEnd := 2 }) ∧
    (bUnits[1]! = { nodeId := bNode, unitType := .collapsed, domStart := 1, domEnd := 3, textStart := 2, textEnd := 2 }) := by
  decide

/-- Test: RestoreTrailingCollapsibleSpaceSplit (offset_mapping_test.cc:1349)
    CSS Text 3 §4.1: Multiple collapsible spaces not followed by text remain fully collapsed. -/
theorem test_OffsetMapping_RestoreTrailingCollapsibleSpaceSplit :
    let bNode := 2
    let bUnits := resolveTrailingCollapsibleSpace false 3 2 bNode
    (bUnits.length = 1) ∧
    (bUnits[0]! = { nodeId := bNode, unitType := .collapsed, domStart := 0, domEnd := 3, textStart := 2, textEnd := 2 }) := by
  decide

end ChromiumLayout.TestsInline
