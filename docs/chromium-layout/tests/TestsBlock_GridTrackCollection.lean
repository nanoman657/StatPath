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

-- grid_track_collection_test.cc:188: TestGridRangeBuilderCollapsed
-- Repeaters with auto-fit collapse empty repeated tracks.
-- CSS Grid Layout Level 1 §7.2.3.
theorem TestGridRangeBuilderCollapsed_vectors :
    let repeaters : List GridRepeater := [
      ⟨2, 4, false⟩,
      ⟨3, 3, true⟩,
      ⟨3, 7, false⟩
    ]
    let ranges := buildGridRanges repeaters
    ranges.length = 3 ∧
    (ranges[0]!).startLine = 0 ∧ (ranges[0]!).trackCount = 8 ∧ (ranges[0]!).isCollapsed = false ∧
    (ranges[1]!).startLine = 8 ∧ (ranges[1]!).trackCount = 9 ∧ (ranges[1]!).isCollapsed = true ∧
    (ranges[2]!).startLine = 17 ∧ (ranges[2]!).trackCount = 21 ∧ (ranges[2]!).isCollapsed = false := by
  decide

-- grid_track_collection_test.cc:248: TestGridSetTrackSizeNormalization
-- Track sizing normalization for definite vs indefinite container.
-- CSS Grid Layout Level 1 §7.2.5.
theorem TestGridSetTrackSizeNormalization_vectors :
    -- auto -> (auto, auto) / (auto, auto)
    normalizeTrackSize .auto .auto false = ⟨.auto, .auto⟩ ∧
    normalizeTrackSize .auto .auto true = ⟨.auto, .auto⟩ ∧
    -- 10% -> (10%, 10%) / (auto, auto)
    normalizeTrackSize (.percent 10) (.percent 10) false = ⟨.percent 10, .percent 10⟩ ∧
    normalizeTrackSize (.percent 10) (.percent 10) true = ⟨.auto, .auto⟩ ∧
    -- minmax(50px, 20%) -> (50px, 20%) / (50px, auto)
    normalizeTrackSize (.fixed 50) (.percent 20) false = ⟨.fixed 50, .percent 20⟩ ∧
    normalizeTrackSize (.fixed 50) (.percent 20) true = ⟨.fixed 50, .auto⟩ ∧
    -- min-content -> (min-content, min-content) / (min-content, min-content)
    normalizeTrackSize .minContent .minContent false = ⟨.minContent, .minContent⟩ ∧
    normalizeTrackSize .minContent .minContent true = ⟨.minContent, .minContent⟩ ∧
    -- max-content -> (max-content, max-content) / (max-content, max-content)
    normalizeTrackSize .maxContent .maxContent false = ⟨.maxContent, .maxContent⟩ ∧
    normalizeTrackSize .maxContent .maxContent true = ⟨.maxContent, .maxContent⟩ ∧
    -- minmax(1fr, 3fr) -> (auto, 3fr) / (auto, 3fr)
    normalizeTrackSize (.flex 1) (.flex 3) false = ⟨.auto, .flex 3⟩ ∧
    normalizeTrackSize (.flex 1) (.flex 3) true = ⟨.auto, .flex 3⟩ ∧
    -- fit-content(40%) -> (40%, fit-content 40) / (auto, max-content)
    normalizeTrackSize (.percent 40) (.fitContent 40) false = ⟨.percent 40, .fitContent 40⟩ ∧
    normalizeTrackSize (.percent 40) (.fitContent 40) true = ⟨.auto, .maxContent⟩ := by
  decide

end TestsBlock
end ChromiumLayout
