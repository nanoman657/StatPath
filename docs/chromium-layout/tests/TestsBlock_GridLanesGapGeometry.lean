import GridLanes
import GridLanesGap

namespace TestsBlock

open ChromiumLayout.GridLayout ChromiumLayout.GridLanes ChromiumLayout.GridLanesGap

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

-- :3125 GapGeometryCollapsedAutoFitTracks (repeat(auto-fit, 100px), gap 10, 5 auto-placed items -> 4 main gaps)
theorem GapGeometryCollapsedAutoFitTracks_vectors :
    (gridAxisGaps 5 10 true (laneSizes 1000 [.autoFit 100] (List.replicate 5 none))).map (·.1.length) = some 4 := by
  decide +kernel

-- :3171 GapGeometryGridAxisAlignment (100px 100px, gap 20, justify-content: center, 300x100, border 5)
theorem GapGeometryGridAxisAlignment_vectors :
    gridAxisGaps (centerStart 5 300 20 [100, 100]) 20 true [100, 100] = some ([150], 40, 260) ∧
    stackContent 5 100 = (5, 95) := by decide

-- :3265 GapGeometryRowStackingAxisOverflow (rows 80px 80px, row-gap 10, column-gap 6, width 60, two 40px items in row 1)
theorem GapGeometryRowStackingAxisOverflow_vectors :
    (gridAxisGaps 5 10 true [80, 80]).map (·.1.length) = some 1 ∧
    stackContent 5 60 (gridTotalSpan 6 [40, 40]) = (5, 91) := by decide

end TestsBlock
