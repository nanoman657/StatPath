import GridLayout

namespace ChromiumLayout
namespace TestsBlock

open GridLayout

-- grid_track_collection_test.cc:85: TestRangeIndexFromGridLine
theorem TestRangeIndexFromGridLine_vectors :
    -- Small case {3, 10, 5}
    rangeIndexFromGridLine [3, 10, 5] 0 = 0 ∧
    rangeIndexFromGridLine [3, 10, 5] 4 = 1 ∧
    rangeIndexFromGridLine [3, 10, 5] 15 = 2 ∧
    -- Large repeat case {3000000, 7, 10}
    rangeIndexFromGridLine [3000000, 7, 10] 600 = 0 ∧
    rangeIndexFromGridLine [3000000, 7, 10] 3000000 = 1 ∧
    rangeIndexFromGridLine [3000000, 7, 10] 3000004 = 1 ∧
    -- Larger case {10, 10, 10, 10, 20, 20, 20, 100}
    rangeIndexFromGridLine [10, 10, 10, 10, 20, 20, 20, 100] 0 = 0 ∧
    rangeIndexFromGridLine [10, 10, 10, 10, 20, 20, 20, 100] 35 = 3 ∧
    rangeIndexFromGridLine [10, 10, 10, 10, 20, 20, 20, 100] 40 = 4 ∧
    rangeIndexFromGridLine [10, 10, 10, 10, 20, 20, 20, 100] 79 = 5 ∧
    rangeIndexFromGridLine [10, 10, 10, 10, 20, 20, 20, 100] 105 = 7 := by
  decide

-- grid_track_collection_test.cc:171: TestGridRangeBuilder
theorem TestGridRangeBuilder_vectors :
    let ranges := buildGridRanges [(2, 4), (3, 3)]
    ranges.length = 2 ∧
    (ranges[0]!).startLine = 0 ∧ (ranges[0]!).trackCount = 8 ∧
    (ranges[1]!).startLine = 8 ∧ (ranges[1]!).trackCount = 9 := by
  decide

end TestsBlock
end ChromiumLayout
