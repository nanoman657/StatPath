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

-- grid_track_collection_test.cc:188: TestGridRangeBuilderCollapsed (auto-fit repeater, no items)
theorem TestGridRangeBuilderCollapsed_vectors :
    let ranges := buildGridRangesAuto 3
      [{ tracks := 2, reps := 4 }, { tracks := 3, autoFit := true }, { tracks := 3, reps := 7 }]
    ranges.length = 3 ∧
    (ranges[0]!).1.startLine = 0 ∧ (ranges[0]!).1.trackCount = 8 ∧ (ranges[0]!).2 = false ∧
    (ranges[1]!).1.startLine = 8 ∧ (ranges[1]!).1.trackCount = 9 ∧ (ranges[1]!).2 = true ∧
    (ranges[2]!).1.startLine = 17 ∧ (ranges[2]!).1.trackCount = 21 ∧ (ranges[2]!).2 = false := by
  decide

-- grid_track_collection_test.cc:248: TestGridSetTrackSizeNormalization (definite and indefinite)
theorem TestGridSetTrackSizeNormalization_vectors :
    normalizeTrack true (.single .auto) = (.auto, .auto) ∧
    normalizeTrack false (.single .auto) = (.auto, .auto) ∧
    normalizeTrack true (.single (.pct 10)) = (.pct 10, .pct 10) ∧
    normalizeTrack false (.single (.pct 10)) = (.auto, .auto) ∧
    normalizeTrack true (.minmax (.fixed 50) (.pct 20)) = (.fixed 50, .pct 20) ∧
    normalizeTrack false (.minmax (.fixed 50) (.pct 20)) = (.fixed 50, .auto) ∧
    normalizeTrack true (.single .minContent) = (.minContent, .minContent) ∧
    normalizeTrack false (.single .minContent) = (.minContent, .minContent) ∧
    normalizeTrack true (.single .maxContent) = (.maxContent, .maxContent) ∧
    normalizeTrack false (.single .maxContent) = (.maxContent, .maxContent) ∧
    normalizeTrack true (.minmax (.fr 1) (.fr 3)) = (.auto, .fr 3) ∧
    normalizeTrack false (.minmax (.fr 1) (.fr 3)) = (.auto, .fr 3) ∧
    normalizeTrack true (.single (.fitContent 40)) = (.pct 40, .fitContent 40) ∧
    normalizeTrack false (.single (.fitContent 40)) = (.auto, .maxContent) := by
  decide

end TestsBlock
end ChromiumLayout
