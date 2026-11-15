import GridLanesGap

namespace TestsBlock

open ChromiumLayout.GridLanesGap

-- All tests: border 5px, box-sizing border-box, gap rule 2px (except RequiresGapRule).

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2925 GapGeometryColumn (80px 120px 90px, gap 14,
-- height 400; container 1000 x 400)
theorem GapGeometryColumn_vectors :
    gridAxisGaps 5 14 true [80, 120, 90] = some ([92, 226], 5, 323) ∧ stackContent 5 400 = (5, 395) := by decide

-- :2979 GapGeometryRow (rows 90px 130px 110px, gap 12, width 500)
theorem GapGeometryRow_vectors :
    gridAxisGaps 5 12 true [90, 130, 110] = some ([101, 243], 5, 359) ∧ stackContent 5 500 = (5, 495) := by decide

-- :3031 GapGeometryEmptyExplicitTracks (repeat(3, 50px), gap 10, no items)
theorem GapGeometryEmptyExplicitTracks_vectors :
    (gridAxisGaps 5 10 true [50, 50, 50]).map (·.1) = some [60, 120] := by decide

-- :3066 GapGeometrySingleTrack and :3096 GapGeometryRequiresGapRule
theorem GapGeometrySingleTrack_vectors : gridAxisGaps 5 10 true [100] = none := gridAxisGaps_single 5 10 true 100
theorem GapGeometryRequiresGapRule_vectors : gridAxisGaps 5 20 false [100, 100] = none := gridAxisGaps_no_rule 5 20 [100, 100]

end TestsBlock
