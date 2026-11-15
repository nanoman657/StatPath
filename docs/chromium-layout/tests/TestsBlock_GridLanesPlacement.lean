import GridLanesPlacement
/-
  TestsBlock_GridLanesPlacement.lean: Formalized break-token placement, alignment, stretch opening,
  dense packing, and fragmentation sharing test vectors from
  third_party/blink/renderer/core/layout/grid_lanes/grid_lanes_layout_algorithm_test.cc
  (:3310 through :4163).
-/

namespace ChromiumLayout
namespace TestsBlock_GridLanesPlacement

open GridLanesPlacement

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3310
-- GridLanesLayoutAlgorithmTest.PopulateGridLanesBreakTokenData
theorem populateGridLanesBreakTokenData :
    directLaneCounts 3 [(0, 1, [false]), (1, 1, [false]), (0, 1, [false])] = [2, 1, 0] ∧
    (placeAligned false 100 0 1 0 .start 0 20 20 .start).1 = (0, 0) ∧
    (placeAligned false 100 1 1 0 .start 0 30 30 .start).1 = (100, 0) ∧
    (placeAligned false 100 0 1 0 .start 20 20 20 .start).1 = (0, 20) ∧
    isItemStart 0 0 = true ∧ isItemStart 1 1 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms populateGridLanesBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3346
-- GridLanesLayoutAlgorithmTest.SharePlacementDataAcrossFragments
theorem sharePlacementDataAcrossFragments :
    directLaneCounts 3 [(0, 2, [false, false]), (0, 1, [false]), (1, 1, [false])] = [2, 2, 0] ∧
    sharePlacementAcrossFragments 30 20 5 10 = (20, 5, true, false) :=
  ⟨rfl, rfl⟩
#print axioms sharePlacementDataAcrossFragments

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3385
-- GridLanesLayoutAlgorithmTest.ShareExpansionDataAcrossFragments
theorem shareExpansionDataAcrossFragments :
    directLaneCounts 2 [(0, 2, [false, false]), (0, 1, [false]), (1, 1, [false])] = [2, 2] ∧
    shareExpansionAcrossFragments 30 20 20 = (40, 0, 10) :=
  ⟨rfl, rfl⟩
#print axioms shareExpansionDataAcrossFragments

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3419
-- GridLanesLayoutAlgorithmTest.PopulateRowGridLanesBreakTokenData
theorem populateRowGridLanesBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 1, [false])] = [2, 1] ∧
    (placeAligned true 50 0 1 0 .start 0 20 20 .start).1 = (0, 0) ∧
    (placeAligned true 50 1 1 0 .start 0 30 30 .start).1 = (0, 50) ∧
    (placeAligned true 50 0 1 0 .start 20 20 20 .start).1 = (20, 0) :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms populateRowGridLanesBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3501
-- GridLanesLayoutAlgorithmTest.PopulateDensePackedBreakTokenData
theorem populateDensePackedBreakTokenData :
    directLaneCounts 3 [(1, 1, [false]), (0, 2, [false, false]), (0, 1, [true])] = [1, 2, 0] ∧
    (placeAligned false 100 0 2 0 .start 20 20 20 .start).1 = (0, 20) ∧
    placeDenseInOpening 100 0 0 20 10 .end = ((0, 10), true, false) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateDensePackedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3535
-- GridLanesLayoutAlgorithmTest.PopulateDensePackedSpannerBreakTokenData
theorem populateDensePackedSpannerBreakTokenData :
    directLaneCounts 3
      [(0, 1, [false]), (0, 2, [false, false]), (1, 2, [true, false])] = [2, 1, 1] ∧
    placeDenseInOpening 100 1 0 20 10 .start = ((100, 0), true, false) :=
  ⟨rfl, rfl⟩
#print axioms populateDensePackedSpannerBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3572
-- GridLanesLayoutAlgorithmTest.PopulateDenseSpannerWithDifferentParentsPerLane
theorem populateDenseSpannerWithDifferentParentsPerLane :
    directLaneCounts 4
      [(0, 1, [false]), (3, 1, [false]), (0, 2, [false, false]), (2, 2, [false, false]),
       (1, 2, [true, true]), (1, 2, [true, true])] = [2, 1, 1, 2] ∧
    placeDenseInOpening 100 1 0 30 10 .start = ((100, 0), true, false) ∧
    placeDenseInOpening 100 1 10 30 5 .start = ((100, 10), true, false) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateDenseSpannerWithDifferentParentsPerLane

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3637
-- GridLanesLayoutAlgorithmTest.PopulateDenseItemAboveDenseSpannerUsesParentSpanner
theorem populateDenseItemAboveDenseSpannerUsesParentSpanner :
    directLaneCounts 4
      [(0, 1, [false]), (2, 1, [false]), (3, 1, [false]),
       (0, 2, [false, false]), (2, 2, [false, false]),
       (1, 2, [true, true]), (1, 1, [true])] = [2, 1, 2, 2] ∧
    (placeDenseInOpening 100 1 10 30 10 .start).1 = (100, 10) ∧
    (placeDenseInOpening 100 1 0 10 5 .start).1 = (100, 0) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateDenseItemAboveDenseSpannerUsesParentSpanner

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3718
-- GridLanesLayoutAlgorithmTest.PopulateGridAxisAlignedBreakTokenData
theorem populateGridAxisAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    (placeAligned false 100 0 1 50 .center 0 20 20 .start).1 = (25, 0) ∧
    (placeAligned false 100 1 1 60 .end 0 30 30 .start).1 = (140, 0) ∧
    (placeAligned false 100 0 2 100 .center 30 20 20 .start).1 = (50, 30) :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms populateGridAxisAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3752
-- GridLanesLayoutAlgorithmTest.PopulateRowGridAxisAlignedBreakTokenData
theorem populateRowGridAxisAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    (placeAligned true 50 0 1 20 .center 0 20 20 .start).1 = (0, 15) ∧
    (placeAligned true 50 1 1 30 .end 0 30 30 .start).1 = (0, 70) ∧
    (placeAligned true 50 0 2 40 .center 30 20 20 .start).1 = (30, 30) :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms populateRowGridAxisAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3785
-- GridLanesLayoutAlgorithmTest.PopulateStackingAxisAlignedBreakTokenData
theorem populateStackingAxisAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    placeAligned false 100 0 1 0 .start 0 40 20 .end true = ((0, 20), none) :=
  ⟨rfl, rfl⟩
#print axioms populateStackingAxisAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3810
-- GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisAlignedBreakTokenData
theorem populateRowStackingAxisAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    placeAligned true 50 0 1 0 .start 0 40 20 .end true = ((20, 0), none) :=
  ⟨rfl, rfl⟩
#print axioms populateRowStackingAxisAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3835
-- GridLanesLayoutAlgorithmTest.PopulateExplicitStackingAxisStretchBreakTokenData
theorem populateExplicitStackingAxisStretchBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    placeAligned false 100 0 1 0 .start 0 40 20 .stretch true = ((0, 0), none) :=
  ⟨rfl, rfl⟩
#print axioms populateExplicitStackingAxisStretchBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3862
-- GridLanesLayoutAlgorithmTest.PopulateRowExplicitStackingAxisStretchBreakTokenData
theorem populateRowExplicitStackingAxisStretchBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    placeAligned true 50 0 1 0 .start 0 40 20 .stretch true = ((0, 0), none) :=
  ⟨rfl, rfl⟩
#print axioms populateRowExplicitStackingAxisStretchBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3914
-- GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisStretchSpaceBreakTokenData
theorem populateRowStackingAxisStretchSpaceBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false]), (0, 2, [false, false])] = [2, 2] ∧
    placeAligned true 50 0 1 0 .start 0 40 20 .stretch false = ((0, 0), some 40) :=
  ⟨rfl, rfl⟩
#print axioms populateRowStackingAxisStretchSpaceBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3940
-- GridLanesLayoutAlgorithmTest.PopulateStackingAxisStretchSpannerSpaceBreakTokenData
theorem populateStackingAxisStretchSpannerSpaceBreakTokenData :
    directLaneCounts 3
      [(0, 2, [false, false]), (2, 1, [false]), (0, 3, [false, false, false])] = [2, 2, 2] ∧
    placeAligned false 100 0 2 0 .start 0 40 20 .stretch false = ((0, 0), some 40) :=
  ⟨rfl, rfl⟩
#print axioms populateStackingAxisStretchSpannerSpaceBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:3976
-- GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisStretchSpannerSpaceBreakTokenData
theorem populateRowStackingAxisStretchSpannerSpaceBreakTokenData :
    directLaneCounts 3
      [(0, 2, [false, false]), (2, 1, [false]), (0, 3, [false, false, false])] = [2, 2, 2] ∧
    placeAligned true 50 0 2 0 .start 0 40 20 .stretch false = ((0, 0), some 40) :=
  ⟨rfl, rfl⟩
#print axioms populateRowStackingAxisStretchSpannerSpaceBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4012
-- GridLanesLayoutAlgorithmTest.PopulateLastStackingAxisAlignedBreakTokenData
theorem populateLastStackingAxisAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false])] = [1, 1] ∧
    placeAligned false 100 0 1 0 .start 0 200 20 .end true = ((0, 180), none) ∧
    placeAligned false 100 1 1 0 .start 0 200 20 .stretch false = ((100, 0), some 200) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateLastStackingAxisAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4042
-- GridLanesLayoutAlgorithmTest.PopulateRowLastStackingAxisAlignedBreakTokenData
theorem populateRowLastStackingAxisAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (1, 1, [false])] = [1, 1] ∧
    placeAligned true 50 0 1 0 .start 0 200 20 .end true = ((180, 0), none) ∧
    placeAligned true 50 1 1 0 .start 0 200 20 .stretch false = ((0, 50), some 200) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateRowLastStackingAxisAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4073
-- GridLanesLayoutAlgorithmTest.PopulateStackingAxisAlignedSpannerBreakTokenData
theorem populateStackingAxisAlignedSpannerBreakTokenData :
    directLaneCounts 3
      [(0, 2, [false, false]), (2, 1, [false]), (0, 3, [false, false, false])] = [2, 2, 2] ∧
    (placeAligned false 100 0 2 0 .start 0 40 20 .end true).1 = (0, 20) :=
  ⟨rfl, rfl⟩
#print axioms populateStackingAxisAlignedSpannerBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4104
-- GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisAlignedSpannerBreakTokenData
theorem populateRowStackingAxisAlignedSpannerBreakTokenData :
    directLaneCounts 3
      [(0, 2, [false, false]), (2, 1, [false]), (0, 3, [false, false, false])] = [2, 2, 2] ∧
    (placeAligned true 50 0 2 0 .start 0 40 20 .end true).1 = (20, 0) :=
  ⟨rfl, rfl⟩
#print axioms populateRowStackingAxisAlignedSpannerBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4135
-- GridLanesLayoutAlgorithmTest.PopulateContentAlignedBreakTokenData
theorem populateContentAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (0, 2, [false, false])] = [2, 1] ∧
    (placeAligned false 100 0 1 0 .start 0 20 20 .start true (contentShift .center 200 40)).1 = (0, 80) ∧
    (placeAligned false 100 0 2 0 .start 20 20 20 .start true (contentShift .center 200 40)).1 = (0, 100) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateContentAlignedBreakTokenData

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:4163
-- GridLanesLayoutAlgorithmTest.PopulateRowContentAlignedBreakTokenData
theorem populateRowContentAlignedBreakTokenData :
    directLaneCounts 2 [(0, 1, [false]), (0, 2, [false, false])] = [2, 1] ∧
    (placeAligned true 50 0 1 0 .start 0 20 20 .start true (contentShift .center 200 40)).1 = (80, 0) ∧
    (placeAligned true 50 0 2 0 .start 20 20 20 .start true (contentShift .center 200 40)).1 = (100, 0) :=
  ⟨rfl, rfl, rfl⟩
#print axioms populateRowContentAlignedBreakTokenData

end TestsBlock_GridLanesPlacement
end ChromiumLayout
