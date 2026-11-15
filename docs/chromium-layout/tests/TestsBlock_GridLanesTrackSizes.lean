import GridTrackSizing

namespace TestsBlock

open ChromiumLayout.GridTrackSizing

private def fix (z : Sz) (n : Nat := 1) : TS := ⟨z, z, n⟩

-- All five tests lay a grid-lanes container out in a 100x100 constraint space.
-- Ahem 10px (test helper `LoadAhem`): every glyph, including the space, is 10px wide.

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:425 BuildFixedTrackSizes
-- (5% repeat(3, 10px 15%) repeat(1, 15px 5px 20px), one entry per track set)
theorem GridLanesBuildFixedTrackSizes_vectors :
    sizes 100 [fix (.pct 5), fix (.px 10) 3, fix (.pct 15) 3, fix (.px 15), fix (.px 5), fix (.px 20)] =
      [5, 30, 45, 15, 5, 20] := by decide

-- :662 BuildIntrinsicTrackSizes (min-content max-content; items "XX XX", "XX XX", and a
-- 20-glyph item with longest word 9 spanning both)
theorem GridLanesBuildIntrinsicTrackSizes_vectors :
    sizes 100 [fix .minC, fix .maxC]
      [⟨0, 1, 0, 20, 50⟩, ⟨1, 2, 0, 20, 50⟩, ⟨0, 2, 0, 90, 200⟩] = [30, 170] := by decide

-- :697 MaximizeAndStretchAutoTracks (minmax(15px, min-content) max-content auto; items
-- "XXX XXX" in track 1 and "X XX X" spanning tracks 1-2)
theorem GridLanesMaximizeAndStretchAutoTracks_vectors :
    sizes 100 [⟨.px 15, .minC, 1⟩, fix .maxC, fix .auto]
      [⟨0, 1, 0, 30, 70⟩, ⟨0, 2, 0, 20, 60⟩] = [30, 45, 25] := by decide

-- :766 BuildRowSizes (grid-lanes-direction: row; height 100px; 20px 1fr 30%)
theorem GridLanesBuildRowSizes_vectors :
    sizes 100 [fix (.px 20), ⟨.auto, .fr 1, 1⟩, fix (.pct 30)] = [20, 50, 30] := by decide

end TestsBlock
