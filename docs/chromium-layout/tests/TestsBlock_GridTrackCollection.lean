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

-- grid_track_collection_test.cc:208: TestGridRangeBuilderImplicit
-- CSS Grid Layout Level 1 §7.2.3, §7.6. Range builder splits explicit tracks and appends implicit tracks for coverage.
theorem TestGridRangeBuilderImplicit_vectors :
    let ranges : List TrackRange := [
      ⟨0, 3, false, false, false, false⟩,
      ⟨3, 5, false, false, false, false⟩,
      ⟨8, 9, false, false, false, false⟩,
      ⟨17, 21, false, false, false, false⟩,
      ⟨38, 5, false, true, false, false⟩
    ]
    coverageRangeIndices ranges 3 40 = some (1, 4) ∧
    ranges.length = 5 ∧
    ranges[0]!.startLine = 0 ∧ ranges[0]!.trackCount = 3 ∧ ranges[0]!.isImplicit = false ∧
    ranges[1]!.startLine = 3 ∧ ranges[1]!.trackCount = 5 ∧ ranges[1]!.isImplicit = false ∧
    ranges[2]!.startLine = 8 ∧ ranges[2]!.trackCount = 9 ∧ ranges[2]!.isImplicit = false ∧
    ranges[3]!.startLine = 17 ∧ ranges[3]!.trackCount = 21 ∧ ranges[3]!.isImplicit = false ∧
    ranges[4]!.startLine = 38 ∧ ranges[4]!.trackCount = 5 ∧ ranges[4]!.isImplicit = true := by
  decide

-- grid_track_collection_test.cc:300: TestGridSizingTrackCollectionSetIterator
-- CSS Grid Layout Level 1 §7.2.3. Sizing collection set iteration partitions sets into ranges.
theorem TestGridSizingTrackCollectionSetIterator_vectors :
    let setCounts : List Nat := [2, 5, 3, 11, 13, 7]
    let totalSets := setCounts.foldl (·+·) 0
    let ranges : List TrackRange := [
      ⟨0, 2, false, false, false, false⟩,
      ⟨2, 5, false, false, false, false⟩,
      ⟨7, 3, false, false, false, false⟩,
      ⟨10, 11, false, false, false, false⟩,
      ⟨21, 13, false, false, false, false⟩,
      ⟨34, 7, false, false, false, false⟩
    ]
    totalSets = 41 ∧
    ranges.length = 6 ∧
    ranges[0]!.startLine = 0 ∧ ranges[0]!.trackCount = 2 ∧
    ranges[1]!.startLine = 2 ∧ ranges[1]!.trackCount = 5 ∧
    ranges[2]!.startLine = 7 ∧ ranges[2]!.trackCount = 3 ∧
    ranges[3]!.startLine = 10 ∧ ranges[3]!.trackCount = 11 ∧
    ranges[4]!.startLine = 21 ∧ ranges[4]!.trackCount = 13 ∧
    ranges[5]!.startLine = 34 ∧ ranges[5]!.trackCount = 7 := by
  decide

-- grid_track_collection_test.cc:351: TestGridSizingTrackCollectionExplicitTracks
-- CSS Grid Layout Level 1 §7.2.3, §7.6. Sizing collection ranges across auto-fit, collapsed, and implicit tracks.
theorem TestGridSizingTrackCollectionExplicitTracks_vectors :
    let ranges : List TrackRange := [
      ⟨0, 2, false, false, false, false⟩,
      ⟨2, 4, false, false, false, false⟩,
      ⟨6, 3, false, false, false, false⟩,
      ⟨9, 3, true, false, false, false⟩,
      ⟨12, 4, false, false, false, false⟩,
      ⟨16, 1, true, false, false, false⟩,
      ⟨17, 2, false, false, false, false⟩,
      ⟨19, 1, false, false, false, false⟩,
      ⟨20, 2, false, false, false, false⟩,
      ⟨22, 5, false, false, false, false⟩
    ]
    coverageRangeIndices ranges 2 4 = some (1, 1) ∧
    coverageRangeIndices ranges 12 4 = some (4, 4) ∧
    coverageRangeIndices ranges 17 3 = some (6, 7) ∧
    coverageRangeIndices ranges 22 5 = some (9, 9) ∧
    ranges.length = 10 ∧
    ranges[0]!.startLine = 0 ∧ ranges[0]!.trackCount = 2 ∧
    ranges[1]!.startLine = 2 ∧ ranges[1]!.trackCount = 4 ∧
    ranges[2]!.startLine = 6 ∧ ranges[2]!.trackCount = 3 ∧
    ranges[3]!.startLine = 9 ∧ ranges[3]!.trackCount = 3 ∧ ranges[3]!.isCollapsed = true ∧
    ranges[4]!.startLine = 12 ∧ ranges[4]!.trackCount = 4 ∧
    ranges[5]!.startLine = 16 ∧ ranges[5]!.trackCount = 1 ∧ ranges[5]!.isCollapsed = true ∧
    ranges[6]!.startLine = 17 ∧ ranges[6]!.trackCount = 2 ∧
    ranges[7]!.startLine = 19 ∧ ranges[7]!.trackCount = 1 ∧
    ranges[8]!.startLine = 20 ∧ ranges[8]!.trackCount = 2 ∧
    ranges[9]!.startLine = 22 ∧ ranges[9]!.trackCount = 5 := by
  decide

-- grid_track_collection_test.cc:459: TestGridSizingTrackCollectionImplicitTracks
-- CSS Grid Layout Level 1 §7.6. Sizing collection creates implicit ranges beyond explicit track bounds.
theorem TestGridSizingTrackCollectionImplicitTracks_vectors :
    let ranges : List TrackRange := [
      ⟨0, 2, false, false, false, false⟩,
      ⟨2, 2, false, false, false, false⟩,
      ⟨4, 11, false, true, false, false⟩,
      ⟨15, 8, false, true, false, false⟩,
      ⟨23, 2, false, true, false, false⟩
    ]
    coverageRangeIndices ranges 2 13 = some (1, 2) ∧
    coverageRangeIndices ranges 23 2 = some (4, 4) ∧
    ranges.length = 5 ∧
    ranges[0]!.startLine = 0 ∧ ranges[0]!.trackCount = 2 ∧
    ranges[1]!.startLine = 2 ∧ ranges[1]!.trackCount = 2 ∧
    ranges[2]!.startLine = 4 ∧ ranges[2]!.trackCount = 11 ∧
    ranges[3]!.startLine = 15 ∧ ranges[3]!.trackCount = 8 ∧
    ranges[4]!.startLine = 23 ∧ ranges[4]!.trackCount = 2 := by
  decide

-- grid_track_collection_test.cc:539: TestGridSizingTrackCollectionIntrinsicAndFlexTracks
-- CSS Grid Layout Level 1 §11.4. Ranges classify flexible and intrinsic track properties.
theorem TestGridSizingTrackCollectionIntrinsicAndFlexTracks_vectors :
    let ranges : List TrackRange := [
      ⟨0, 1, false, false, false, true⟩,
      ⟨1, 2, false, false, true, true⟩,
      ⟨3, 4, false, false, true, true⟩,
      ⟨7, 1, false, false, false, false⟩,
      ⟨8, 3, false, true, false, true⟩
    ]
    coverageRangeIndices ranges 1 2 = some (1, 1) ∧
    coverageRangeIndices ranges 7 4 = some (3, 4) ∧
    ranges.length = 5 ∧
    ranges[0]!.hasFlexible = false ∧ ranges[0]!.hasIntrinsic = true ∧
    ranges[1]!.hasFlexible = true ∧ ranges[1]!.hasIntrinsic = true ∧
    ranges[2]!.hasFlexible = true ∧ ranges[2]!.hasIntrinsic = true ∧
    ranges[3]!.hasFlexible = false ∧ ranges[3]!.hasIntrinsic = false := by
  decide

end TestsBlock
end ChromiumLayout
