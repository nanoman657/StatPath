import GridLanesItems
import GridLanesPlacement
/-
  TestsBlock_GridLanesItems.lean: Formalized item span resolution, item group collection,
  track range splitting, fit-tolerance auto-placement, and fill-reverse/track-reverse
  test vectors from
  third_party/blink/renderer/core/layout/grid_lanes/grid_lanes_layout_algorithm_test.cc.
-/

namespace ChromiumLayout
namespace TestsBlock_GridLanesItems

open GridLanesItems
open GridLanesPlacement

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:259
-- GridLanesLayoutAlgorithmTest.ConstructGridLanesItems
theorem constructGridLanesItems :
    ([.auto 1, .startSpan 3 2, .auto 2, .auto 3,
      .startEnd 2 5, .startEnd 3 5, .startEnd 1 3, .startEnd 3 5].map
        (fun s => ((resolveSpan s).1, (resolveSpan s).2.1))) =
      [(none, 1), (some (2, 4), 2), (none, 2), (none, 3),
       (some (1, 4), 3), (some (2, 4), 2), (some (0, 2), 2), (some (2, 4), 2)] :=
  rfl
#print axioms constructGridLanesItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:310
-- GridLanesLayoutAlgorithmTest.GridLanesAutoPlacedItems
theorem gridLanesAutoPlacedItems :
    ([.startEnd 1 3, .auto 2, .startEnd 2 4, .auto 1].map
        (fun s => (resolveSpan s).2.2)) =
      [false, true, false, true] :=
  rfl
#print axioms gridLanesAutoPlacedItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:378
-- GridLanesLayoutAlgorithmTest.BuildRanges
theorem buildRanges :
    buildTrackRanges 2 [1, 6, 3] 10 15 =
      [(0, 2), (2, 1), (3, 6), (9, 1), (10, 2), (12, 3)] :=
  rfl
#print axioms buildRanges

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:455
-- GridLanesLayoutAlgorithmTest.CollectGridLanesItemGroups
theorem collectGridLanesItemGroups :
    collectItemGroups
      [(.auto 1, none), (.startSpan 1 1, none), (.startEnd 1 4, none),
       (.auto 3, none), (.endSpan 4 3, none), (.auto 1, none)] =
      [(none, 1, none, 2), (some (0, 1), 1, none, 1),
       (some (0, 3), 3, none, 2), (none, 3, none, 1)] :=
  rfl
#print axioms collectGridLanesItemGroups

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:499
-- GridLanesLayoutAlgorithmTest.CollectGridLanesItemGroupsWithBaseline
theorem collectGridLanesItemGroupsWithBaseline :
    collectItemGroups
      [(.auto 1, some true), (.auto 1, some true), (.auto 1, some false),
       (.auto 2, none), (.auto 2, some true), (.auto 2, some true),
       (.auto 2, some false), (.auto 2, some false), (.auto 2, some false)] =
      [(none, 1, some true, 2), (none, 1, some false, 1),
       (none, 2, none, 1), (none, 2, some true, 2), (none, 2, some false, 3)] :=
  rfl
#print axioms collectGridLanesItemGroupsWithBaseline

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1492
-- GridLanesLayoutAlgorithmTest.GetFirstEligibleLine
theorem getFirstEligibleLine :
    firstEligibleLine [4, 6, 7, 5] 1 2 1 = ((1, 3), 7) ∧
    firstEligibleLine [4, 6, 7, 5] 1 1 3 = ((3, 4), 5) ∧
    firstEligibleLine [4, 6, 7, 5] 1 4 4 = ((0, 4), 7) ∧
    firstEligibleLine [4, 6, 7, 5] 1 2 2 = ((2, 4), 7) ∧
    firstEligibleLine [4, 6, 7, 5] 1 2 3 = ((0, 2), 6) ∧
    firstEligibleLine [4, 6, 7, 5] 1 2 4 = ((0, 2), 6) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms getFirstEligibleLine

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4191
-- GridLanesLayoutAlgorithmTest.PopulateColumnFillAndTrackReverseBreakTokenData
theorem populateColumnFillAndTrackReverseBreakTokenData :
    directLaneCounts 3
      [(2, 1, [false]), (1, 2, [false, false]), (1, 1, [true]), (1, 1, [true])] = [0, 1, 2] ∧
    orderForFillReverse false
      [placeFillReverse false 100 200 2 1 20 true 0 20 0 true,
       placeFillReverse false 100 200 1 2 200 false 20 20 160 false] =
      [(100, 0), (280, 180)] ∧
    orderForFillReverse false
      [placeFillReverse false 100 200 1 1 20 true 0 10 0 true,
       placeFillReverse false 100 200 1 1 100 false 10 5 5 false] =
      [(100, 180), (180, 190)] :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateColumnFillAndTrackReverseBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4236
-- GridLanesLayoutAlgorithmTest.PopulateRowFillAndTrackReverseBreakTokenData
theorem populateRowFillAndTrackReverseBreakTokenData :
    directLaneCounts 3
      [(2, 1, [false]), (1, 2, [false, false]), (1, 1, [true]), (1, 1, [true])] = [0, 1, 2] ∧
    orderForFillReverse true
      [placeFillReverse true 50 200 2 1 20 true 0 20 0 true,
       placeFillReverse true 50 200 1 2 100 false 20 20 160 false] =
      [(180, 130), (0, 50)] ∧
    orderForFillReverse true
      [placeFillReverse true 50 200 1 1 20 true 0 10 0 true,
       placeFillReverse true 50 200 1 1 50 false 10 5 5 false] =
      [(190, 80), (180, 50)] :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateRowFillAndTrackReverseBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4281
-- GridLanesLayoutAlgorithmTest.PopulateIndefiniteFillReverseBreakTokenData
theorem populateIndefiniteFillReverseBreakTokenData :
    directLaneCounts 3
      [(1, 1, [false]), (0, 2, [false, false]), (0, 1, [true]), (0, 1, [true])] = [1, 2, 0] ∧
    orderForFillReverse false
      [placeFillReverse false 100 40 1 1 100 false 0 20 0 false,
       placeFillReverse false 100 40 0 2 200 false 20 20 0 false] =
      [(0, 0), (100, 20)] ∧
    orderForFillReverse false
      [placeFillReverse false 100 40 0 1 100 false 0 10 0 true,
       placeFillReverse false 100 40 0 1 100 false 10 5 5 false] =
      [(0, 20), (0, 30)] :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateIndefiniteFillReverseBreakTokenData

end TestsBlock_GridLanesItems
end ChromiumLayout
