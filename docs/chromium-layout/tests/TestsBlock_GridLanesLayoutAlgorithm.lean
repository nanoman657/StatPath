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

end TestsBlock
end ChromiumLayout
