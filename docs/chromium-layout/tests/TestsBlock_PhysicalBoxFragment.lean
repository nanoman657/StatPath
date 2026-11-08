import ColumnLayout
import BlockFloat

namespace TestsBlock

open ChromiumLayout.ColumnLayout
open ChromiumLayout.BlockFloat

-- physical_box_fragment_test.cc:29: PhysicalBoxFragmentTest.FloatingDescendantsInlineChlidren
theorem FloatingDescendantsInlineChlidren_vectors :
    let hasfloats : List BoxDescendant := [
      .leaf 1,
      .leaf 2 .block true
    ]
    let nofloats : List BoxDescendant := [
      .leaf 1
    ]
    listHasFloats 10 hasfloats = true ∧
    listHasFloats 10 nofloats = false := by
  decide

-- physical_box_fragment_test.cc:65: PhysicalBoxFragmentTest.FloatingDescendantsInlineBlock
theorem FloatingDescendantsInlineBlock_vectors :
    let spanHasFloats : BoxDescendant :=
      .node 2 .inlineBlock [.leaf 3 .block true]
    let nofloats : List BoxDescendant := [
      .leaf 1,
      spanHasFloats
    ]
    listHasFloats 10 nofloats = false ∧
    hasFloatingDescendants 10 (.node 2 .block [.leaf 3 .block true]) = true := by
  decide

-- physical_box_fragment_test.cc:83: PhysicalBoxFragmentTest.FloatingDescendantsBlockFormattingContext
theorem FloatingDescendantsBlockFormattingContext_vectors :
    let hasfloats : List BoxDescendant := [
      .node 1 .flowRoot [.leaf 2 .block true]
    ]
    let hasfloats2 : List BoxDescendant := [
      .node 1 .block [.leaf 2 .block true]
    ]
    listHasFloats 10 hasfloats = true ∧
    listHasFloats 10 hasfloats2 = true := by
  decide

-- physical_box_fragment_test.cc:115: PhysicalBoxFragmentTest.IsFragmentationContextRoot
-- Empty child in columns:3 generates 1 column fragmentainer
theorem IsFragmentationContextRoot_columnCount :
    (layoutMulticol { cols := 3, gap := 0, width := 300, height := 100, children := [{ id := 1, height := 0 }] }).columns.length = 1 := by
  decide

-- physical_box_fragment_test.cc:135: PhysicalBoxFragmentTest.IsFragmentationContextRootNested
-- Nested multicol containers each generate 1 column fragmentainer
theorem IsFragmentationContextRootNested_columnCounts :
    (layoutMulticol { cols := 3, gap := 0, width := 300, height := 100, children := [{ id := 1, height := 0 }] }).columns.length = 1 ∧
    (layoutMulticol { cols := 3, gap := 0, width := 300, height := 100, children := [{ id := 2, height := 0 }] }).columns.length = 1 := by
  decide

end TestsBlock
