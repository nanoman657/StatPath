import ColumnLayout

namespace TestsBlock

open ChromiumLayout.ColumnLayout

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
