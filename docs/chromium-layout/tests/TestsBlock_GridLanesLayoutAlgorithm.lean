import GridLayout

namespace ChromiumLayout
namespace TestsBlock

open GridLayout

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3066: GapGeometrySingleTrack
-- One 100px lane with a column rule: there is no gap, so no gap geometry object.
theorem GridLanesGapGeometrySingleTrack_vectors :
    gapGeometryPresent true [100] = false := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3096: GapGeometryRequiresGapRule
-- Two 100px lanes with a 20px column gap but no rule: no gap geometry object.
theorem GridLanesGapGeometryRequiresGapRule_vectors :
    gapGeometryPresent false [100, 100] = false := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2925: GapGeometryColumn
-- Columns 80, 120 and 90px with a 14px column-gap inside a 5px border. Each gap offset is the
-- gap midpoint measured from the border edge (5px). The inline content end is the border plus
-- the grid content size, and the block content end is the 400px border-box minus the border.
-- The object's container type, main direction and cross-gap count are not modelled.
theorem GridLanesGapGeometryColumn_vectors :
    gapGeometryPresent true [80, 120, 90] = true ∧
    ([80, 120, 90] : List Nat).length - 1 = 2 ∧
    5 + gapMidpoint 14 [80, 120, 90] 0 = 92 ∧
    5 + gapMidpoint 14 [80, 120, 90] 1 = 226 ∧
    5 + gridContentSize 14 [80, 120, 90] = 323 ∧
    400 - 5 = 395 := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2979: GapGeometryRow
-- Rows 90, 130 and 110px with a 12px row-gap inside a 5px border, in a 500px-wide box. The
-- block content end is the border plus the grid content size. The object's container type,
-- main direction and cross-gap count are not modelled.
theorem GridLanesGapGeometryRow_vectors :
    gapGeometryPresent true [90, 130, 110] = true ∧
    ([90, 130, 110] : List Nat).length - 1 = 2 ∧
    5 + gapMidpoint 12 [90, 130, 110] 0 = 101 ∧
    5 + gapMidpoint 12 [90, 130, 110] 1 = 243 ∧
    500 - 5 = 495 ∧
    5 + gridContentSize 12 [90, 130, 110] = 359 := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3031: GapGeometryEmptyExplicitTracks
-- Three 50px columns with a 10px column-gap and no items, inside a 5px border. The main gap
-- count is the number of tracks minus one. The cross-gap count is not modelled.
theorem GridLanesGapGeometryEmptyExplicitTracks_vectors :
    gapGeometryPresent true [50, 50, 50] = true ∧
    ([50, 50, 50] : List Nat).length - 1 = 2 ∧
    5 + gapMidpoint 10 [50, 50, 50] 0 = 60 ∧
    5 + gapMidpoint 10 [50, 50, 50] 1 = 120 := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3265: GapGeometryRowStackingAxisOverflow
-- Two 80px rows with a 10px row-gap inside a 5px border, in a 60px-wide box. The two 40px items
-- in row 1 sit on the inline (stacking) axis with a 6px gap between them, so the inline content
-- end is the border (5px) plus the stacking extent 40 + 6 + 40 = 86 (gridContentSize 6 [40, 40]).
theorem GridLanesGapGeometryRowStackingAxisOverflow_vectors :
    gapGeometryPresent true [80, 80] = true ∧
    ([80, 80] : List Nat).length - 1 = 1 ∧
    5 + gridContentSize 6 [40, 40] = 91 := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:662: BuildIntrinsicTrackSizes
-- Columns min-content and max-content in a 100px container. Item text widths (10px glyphs): "XX XX"
-- has min-content 20 and max-content 50; "XXX XXXXXX XXXXXXXXX" has min-content 90 and
-- max-content 200. The steps give column 1 base 30 and column 2 base 170.
theorem GridLanesBuildIntrinsicTrackSizes_vectors :
    intrinsicTrackSizes 100 [.single .minContent, .single .maxContent]
      [⟨0, 1, 20, 50⟩, ⟨1, 1, 20, 50⟩, ⟨0, 2, 90, 200⟩] = some [30, 170] := by
  decide

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:697: MaximizeAndStretchAutoTracks
-- Columns minmax(15px, min-content), max-content and auto in a 100px container. Item text widths
-- (10px glyphs): "XXX XXX" has min-content 30 and max-content 70; "X XX X" has min-content 20 and
-- max-content 60. The maximize step leaves column 1 at base 30 and the auto column is stretched to 25.
theorem GridLanesMaximizeAndStretchAutoTracks_vectors :
    intrinsicTrackSizes 100
      [.minmax (.fixed 15) .minContent, .single .maxContent, .single .auto]
      [⟨0, 1, 30, 70⟩, ⟨0, 2, 20, 60⟩] = some [30, 45, 25] := by
  decide

end TestsBlock
end ChromiumLayout
