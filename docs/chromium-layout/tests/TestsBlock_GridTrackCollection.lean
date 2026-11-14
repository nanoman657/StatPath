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
    let repeaters : List TrackRepeater := [
      ⟨8, false, false, false⟩,
      ⟨9, false, false, false⟩,
      ⟨21, false, false, false⟩
    ]
    let baseRanges := buildTrackRanges repeaters
    let (ranges, rStart, rEnd) := ensureTrackCoverage baseRanges 3 40
    rStart = 1 ∧ rEnd = 4 ∧
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
    let ranges := buildTrackRangesFromSetCounts setCounts
    let totalSets := (ranges.map (·.trackCount)).foldl (·+·) 0
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
    let repeaters : List TrackRepeater := [
      ⟨9, false, false, false⟩,
      ⟨10, true, false, false⟩
    ]
    let r0 := buildTrackRanges repeaters
    let (r1, s1, e1) := ensureTrackCoverage r0 2 4
    let (r2, s2, e2) := ensureTrackCoverage r1 12 4
    let (r3, s3, e3) := ensureTrackCoverage r2 17 3
    let (r4, s4, e4) := ensureTrackCoverage r3 22 5
    s1 = 1 ∧ e1 = 1 ∧
    s2 = 4 ∧ e2 = 4 ∧
    s3 = 6 ∧ e3 = 7 ∧
    s4 = 9 ∧ e4 = 9 ∧
    r4.length = 10 ∧
    r4[0]!.startLine = 0 ∧ r4[0]!.trackCount = 2 ∧
    r4[1]!.startLine = 2 ∧ r4[1]!.trackCount = 4 ∧
    r4[2]!.startLine = 6 ∧ r4[2]!.trackCount = 3 ∧
    r4[3]!.startLine = 9 ∧ r4[3]!.trackCount = 3 ∧ r4[3]!.isCollapsed = true ∧
    r4[4]!.startLine = 12 ∧ r4[4]!.trackCount = 4 ∧
    r4[5]!.startLine = 16 ∧ r4[5]!.trackCount = 1 ∧ r4[5]!.isCollapsed = true ∧
    r4[6]!.startLine = 17 ∧ r4[6]!.trackCount = 2 ∧
    r4[7]!.startLine = 19 ∧ r4[7]!.trackCount = 1 ∧
    r4[8]!.startLine = 20 ∧ r4[8]!.trackCount = 2 ∧
    r4[9]!.startLine = 22 ∧ r4[9]!.trackCount = 5 := by
  decide

-- grid_track_collection_test.cc:459: TestGridSizingTrackCollectionImplicitTracks
-- CSS Grid Layout Level 1 §7.6. Sizing collection creates implicit ranges beyond explicit track bounds.
theorem TestGridSizingTrackCollectionImplicitTracks_vectors :
    let repeaters : List TrackRepeater := [
      ⟨2, false, false, false⟩,
      ⟨2, false, false, false⟩
    ]
    let r0 := buildTrackRanges repeaters
    let (r1, s1, e1) := ensureTrackCoverage r0 2 13
    let (r2, s2, e2) := ensureTrackCoverage r1 23 2
    s1 = 1 ∧ e1 = 2 ∧
    s2 = 4 ∧ e2 = 4 ∧
    r2.length = 5 ∧
    r2[0]!.startLine = 0 ∧ r2[0]!.trackCount = 2 ∧
    r2[1]!.startLine = 2 ∧ r2[1]!.trackCount = 2 ∧
    r2[2]!.startLine = 4 ∧ r2[2]!.trackCount = 11 ∧
    r2[3]!.startLine = 15 ∧ r2[3]!.trackCount = 8 ∧
    r2[4]!.startLine = 23 ∧ r2[4]!.trackCount = 2 := by
  decide

-- grid_track_collection_test.cc:539: TestGridSizingTrackCollectionIntrinsicAndFlexTracks
-- CSS Grid Layout Level 1 §11.4. Ranges classify flexible and intrinsic track properties.
theorem TestGridSizingTrackCollectionIntrinsicAndFlexTracks_vectors :
    let repeaters : List TrackRepeater := [
      ⟨1, false, false, true⟩,
      ⟨2, false, true, true⟩,
      ⟨4, false, true, true⟩,
      ⟨1, false, false, false⟩
    ]
    let r0 := buildTrackRanges repeaters
    let (r1, s1, e1) := ensureTrackCoverage r0 1 2 false true
    let (r2, s2, e2) := ensureTrackCoverage r1 7 4 false true
    s1 = 1 ∧ e1 = 1 ∧
    s2 = 3 ∧ e2 = 4 ∧
    r2.length = 5 ∧
    r2[0]!.hasFlexible = false ∧ r2[0]!.hasIntrinsic = true ∧
    r2[1]!.hasFlexible = true ∧ r2[1]!.hasIntrinsic = true ∧
    r2[2]!.hasFlexible = true ∧ r2[2]!.hasIntrinsic = true ∧
    r2[3]!.hasFlexible = false ∧ r2[3]!.hasIntrinsic = false ∧
    r2[4]!.hasFlexible = false ∧ r2[4]!.hasIntrinsic = true := by
  decide

end TestsBlock
end ChromiumLayout
