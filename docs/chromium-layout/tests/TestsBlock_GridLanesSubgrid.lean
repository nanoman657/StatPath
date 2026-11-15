import GridLanesSubgrid
/-
  TestsBlock_GridLanesSubgrid.lean: Formalized subgrid and placement invalidation test vectors from
  third_party/blink/renderer/core/layout/grid_lanes/grid_lanes_layout_algorithm_test.cc
  (:1549 through :2899).
-/

namespace ChromiumLayout
namespace TestsBlock_GridLanesSubgrid

open GridLanesSubgrid

/-- Shared nested subgrid fixture from `SetNestedSubgridTestBody()`
    (`grid_lanes/grid_lanes_layout_algorithm_test.cc:159-195`). -/
def innerNode : Node := .mk 7 true false [.mk 9 false false []]
def middleNode : Node := .mk 4 true true [.mk 6 false false [], innerNode, .mk 8 false false []]
def outerNode : Node := .mk 1 true false [.mk 3 false false [], middleNode, .mk 5 false false []]
def rootNode : Node := .mk 0 false false [.mk 0 false false [], outerNode, .mk 2 false false []]

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1549
-- GridLanesLayoutAlgorithmTest.IncludeSubgriddedItemsIncludesNestedDescendants
theorem includeSubgriddedItemsIncludesNestedDescendants :
    (nodeItemLists true false rootNode).1 = [0, 1, 2] ∧
    (nodeItemLists true false rootNode).2.1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] ∧
    (nodeItemLists false true outerNode).1 = [3, 4, 5] ∧
    (nodeItemLists false true outerNode).2.1 = [3, 4, 5, 6, 7, 8] ∧
    (nodeItemLists false false middleNode).1 = [6, 7, 8] ∧
    (nodeItemLists false false middleNode).2.1 = [6, 7, 8] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms includeSubgriddedItemsIncludesNestedDescendants

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1580
-- GridLanesLayoutAlgorithmTest.ItemsSubgriddedToParentExcludesDirectItems
theorem itemsSubgriddedToParentExcludesDirectItems :
    (nodeItemLists true false rootNode).2.2 = [3, 4, 5, 6, 7, 8, 9] ∧
    (nodeItemLists false true outerNode).2.2 = [6, 7, 8] ∧
    (nodeItemLists false false middleNode).2.2 = [] ∧
    (nodeItemLists false true innerNode).2.2 = [] :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms itemsSubgriddedToParentExcludesDirectItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1609
-- GridLanesLayoutAlgorithmTest.AppendSubgriddedItemsColumns
theorem appendSubgriddedItemsColumns :
    subgridFlags .cols true false true = (true, false, true) ∧
    singleSubgridCounts .cols 2 2 true false true = (4, 2) :=
  ⟨rfl, rfl⟩
#print axioms appendSubgriddedItemsColumns

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1659
-- GridLanesLayoutAlgorithmTest.AppendSubgriddedItemsRows
theorem appendSubgriddedItemsRows :
    subgridFlags .rows false true true = (false, true, true) ∧
    singleSubgridCounts .rows 2 2 false true true = (4, 2) :=
  ⟨rfl, rfl⟩
#print axioms appendSubgriddedItemsRows

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1710
-- GridLanesLayoutAlgorithmTest.SubgridRowsIgnoredInColumnGridLanes
theorem subgridRowsIgnoredInColumnGridLanes :
    subgridFlags .cols false true true = (false, false, false) ∧
    singleSubgridCounts .cols 2 1 false true true = (2, 0) :=
  ⟨rfl, rfl⟩
#print axioms subgridRowsIgnoredInColumnGridLanes

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1758
-- GridLanesLayoutAlgorithmTest.SubgridColumnsIgnoredInRowGridLanes
theorem subgridColumnsIgnoredInRowGridLanes :
    subgridFlags .rows true false true = (false, false, false) ∧
    singleSubgridCounts .rows 2 1 true false true = (2, 0) :=
  ⟨rfl, rfl⟩
#print axioms subgridColumnsIgnoredInRowGridLanes

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1807
-- GridLanesLayoutAlgorithmTest.OrthogonalAppendSubgriddedItemsColumns
theorem orthogonalAppendSubgriddedItemsColumns :
    subgridFlags .cols false true false = (true, false, true) ∧
    singleSubgridCounts .cols 2 2 false true false = (4, 2) :=
  ⟨rfl, rfl⟩
#print axioms orthogonalAppendSubgriddedItemsColumns

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1859
-- GridLanesLayoutAlgorithmTest.OrthogonalAppendSubgriddedItemsRows
theorem orthogonalAppendSubgriddedItemsRows :
    subgridFlags .rows true false false = (false, true, true) ∧
    singleSubgridCounts .rows 2 2 true false false = (4, 2) :=
  ⟨rfl, rfl⟩
#print axioms orthogonalAppendSubgriddedItemsRows

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1914
-- GridLanesLayoutAlgorithmTest.AutoPlacedSubgriddedItemsAreAutoPlaced
theorem autoPlacedSubgriddedItemsAreAutoPlaced :
    subgridFlags .cols true false true = (true, false, true) ∧
    childAutoPlaced true false = true ∧
    childAutoPlaced true true = true ∧
    (singleSubgridCounts .cols 2 2 true false true).2 = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms autoPlacedSubgriddedItemsAreAutoPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:1973
-- GridLanesLayoutAlgorithmTest.DefiniteSubgridChildrenAreExplicitlyPlaced
theorem definiteSubgridChildrenAreExplicitlyPlaced :
    subgridFlags .cols true false true = (true, false, true) ∧
    childAutoPlaced false true = false ∧
    translateSpan 1 3 0 1 false = (1, 2) ∧
    translateSpan 1 3 1 2 false = (2, 3) ∧
    (singleSubgridCounts .cols 2 2 true false true).2 = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
#print axioms definiteSubgridChildrenAreExplicitlyPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2036
-- GridLanesLayoutAlgorithmTest.OppositeDirectionSubgridReversesChildSpans
theorem oppositeDirectionSubgridReversesChildSpans :
    subgridFlags .cols true false true = (true, false, true) ∧
    translateSpan 0 3 0 1 true = (2, 3) :=
  ⟨rfl, rfl⟩
#print axioms oppositeDirectionSubgridReversesChildSpans

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2093
-- GridLanesLayoutAlgorithmTest.OrthogonalSubgridColumnsIgnoredInColumnGridLanes
theorem orthogonalSubgridColumnsIgnoredInColumnGridLanes :
    subgridFlags .cols true false false = (false, false, false) ∧
    singleSubgridCounts .cols 2 1 true false false = (2, 0) :=
  ⟨rfl, rfl⟩
#print axioms orthogonalSubgridColumnsIgnoredInColumnGridLanes

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2145
-- GridLanesLayoutAlgorithmTest.OrthogonalSubgridRowsIgnoredInRowGridLanes
theorem orthogonalSubgridRowsIgnoredInRowGridLanes :
    subgridFlags .rows false true false = (false, false, false) ∧
    singleSubgridCounts .rows 2 1 false true false = (2, 0) :=
  ⟨rfl, rfl⟩
#print axioms orthogonalSubgridRowsIgnoredInRowGridLanes

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2201
-- GridLanesLayoutAlgorithmTest.DefiniteSubgridsAtDifferentPositionsProduceSeparateVirtualItems
theorem definiteSubgridsAtDifferentPositionsProduceSeparateVirtualItems :
    expandVirtualItems 4
      [(some 0, 2, 0), (some (translateSpan 0 2 0 1 false).1, 1, 40),
       (some 2, 2, 0), (some (translateSpan 2 4 0 1 false).1, 1, 80)] =
      [(0, 2, 0), (0, 1, 40), (2, 4, 0), (2, 3, 80)] :=
  rfl
#print axioms definiteSubgridsAtDifferentPositionsProduceSeparateVirtualItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2261
-- GridLanesLayoutAlgorithmTest.AutoPlacedSubgridChildrenAreAutoPlacedForVirtualItems
theorem autoPlacedSubgridChildrenAreAutoPlacedForVirtualItems :
    (expandVirtualItems 3 [(none, 1, 40), (none, 2, 0), (none, 1, 20)]).map
      (fun (s, e, _) => (s, e)) =
      [(0, 1), (1, 2), (2, 3), (0, 2), (1, 3)] :=
  rfl
#print axioms autoPlacedSubgridChildrenAreAutoPlacedForVirtualItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2327
-- GridLanesLayoutAlgorithmTest.DefiniteSubgridAutoPlacedChildProducesDefiniteVirtualItem
theorem definiteSubgridAutoPlacedChildProducesDefiniteVirtualItem :
    expandVirtualItems 4
      [(some 1, 2, 0),
       (some (translateSpan 1 3 0 1 false).1, 1, 40),
       (some (translateSpan 1 3 1 2 false).1, 1, 80)] =
      [(1, 3, 0), (1, 2, 40), (2, 3, 80)] :=
  rfl
#print axioms definiteSubgridAutoPlacedChildProducesDefiniteVirtualItem

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2386
-- GridLanesLayoutAlgorithmTest.NestedSubgridInAutoPlacedSubgridIsAutoPlaced
theorem nestedSubgridInAutoPlacedSubgridIsAutoPlaced :
    childAutoPlaced true false = true ∧
    chainAutoPlaced true 2 = [true, true] :=
  ⟨rfl, rfl⟩
#print axioms nestedSubgridInAutoPlacedSubgridIsAutoPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2448
-- GridLanesLayoutAlgorithmTest.ExplicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced
theorem explicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced :
    childAutoPlaced true true = true ∧
    chainAutoPlaced true 2 = [true, true] :=
  ⟨rfl, rfl⟩
#print axioms explicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2503
-- GridLanesLayoutAlgorithmTest.NestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced
theorem nestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced :
    childAutoPlaced false true = false ∧
    chainAutoPlaced false 2 = [false, false] :=
  ⟨rfl, rfl⟩
#print axioms nestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2558
-- GridLanesLayoutAlgorithmTest.DeepNestedAutoPlacedSubgridsAreAllAutoPlaced
theorem deepNestedAutoPlacedSubgridsAreAllAutoPlaced :
    chainAutoPlaced true 3 = [true, true, true] :=
  rfl
#print axioms deepNestedAutoPlacedSubgridsAreAllAutoPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2621
-- GridLanesLayoutAlgorithmTest.AllChildrenOfAutoPlacedSubgridAreAutoPlaced
theorem allChildrenOfAutoPlacedSubgridAreAutoPlaced :
    [childAutoPlaced true false, childAutoPlaced true true] = [true, true] :=
  rfl
#print axioms allChildrenOfAutoPlacedSubgridAreAutoPlaced

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2668
-- GridLanesLayoutAlgorithmTest.AppendColumnSubgriddedGridLanesItems
theorem appendColumnSubgriddedGridLanesItems :
    sizingTreeSize .cols [(true, false, true, some .cols)] = 2 ∧
    hasSubCols true false true (some .cols) = true ∧
    hasSubRows true false true (some .cols) = false ∧
    singleSubgridCounts .cols 1 2 true false true (some .cols) = (3, 2) :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms appendColumnSubgriddedGridLanesItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2709
-- GridLanesLayoutAlgorithmTest.AppendRowSubgriddedGridLanesItems
theorem appendRowSubgriddedGridLanesItems :
    sizingTreeSize .rows [(false, true, true, some .rows)] = 2 ∧
    hasSubCols false true true (some .rows) = false ∧
    hasSubRows false true true (some .rows) = true ∧
    singleSubgridCounts .rows 1 2 false true true (some .rows) = (3, 2) :=
  ⟨rfl, rfl, rfl, rfl⟩
#print axioms appendRowSubgriddedGridLanesItems

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2744
-- GridLanesLayoutAlgorithmTest.GridLanesSubgridIgnoresNonGridAxis
theorem gridLanesSubgridIgnoresNonGridAxis :
    sizingTreeSize .cols [(false, true, true, some .cols)] = 1 ∧
    subgridFlags .cols false true true (some .cols) = (false, false, false) ∧
    (singleSubgridCounts .cols 1 1 false true true (some .cols)).2 = 0 :=
  ⟨rfl, rfl, rfl⟩
#print axioms gridLanesSubgridIgnoresNonGridAxis

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2778
-- GridLanesLayoutAlgorithmTest.OrthogonalGridLanesSubgridMapsGridAxis
theorem orthogonalGridLanesSubgridMapsGridAxis :
    sizingTreeSize .cols [(false, true, false, some .rows)] = 2 ∧
    hasSubCols false true false (some .rows) = true ∧
    hasSubRows false true false (some .rows) = false :=
  ⟨rfl, rfl, rfl⟩
#print axioms orthogonalGridLanesSubgridMapsGridAxis

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2807
-- GridLanesLayoutAlgorithmTest.BuildsNestedGridLanesSubgrids
theorem buildsNestedGridLanesSubgrids :
    sizingTreeSize .cols
      [(true, false, true, some .cols), (true, false, true, some .cols)] = 3 ∧
    hasSubCols true false true (some .cols) = true :=
  ⟨rfl, rfl⟩
#print axioms buildsNestedGridLanesSubgrids

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2842
-- GridLanesLayoutAlgorithmTest.GridLanesDirectionChangeMarksPlacementDirty
theorem gridLanesDirectionChangeMarksPlacementDirty :
    placementDirty .col .col true false true false false false = false ∧
    placementDirty .col .row true false true false false false = true :=
  ⟨rfl, rfl⟩
#print axioms gridLanesDirectionChangeMarksPlacementDirty

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2870
-- GridLanesLayoutAlgorithmTest.GridLanesPackChangeMarksPlacementDirty
theorem gridLanesPackChangeMarksPlacementDirty :
    placementDirty .normal .normal true false true false false false = false ∧
    placementDirty .normal .normal true false true false false true = true :=
  ⟨rfl, rfl⟩
#print axioms gridLanesPackChangeMarksPlacementDirty

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:2899
-- GridLanesLayoutAlgorithmTest.ResolvedGridAxisFlipMarksPlacementDirty
theorem resolvedGridAxisFlipMarksPlacementDirty :
    resolveAxis .normal false true = .rows ∧
    resolveAxis .normal false false = .cols ∧
    placementDirty .normal .normal false true false false false false = true :=
  ⟨rfl, rfl, rfl⟩
#print axioms resolvedGridAxisFlipMarksPlacementDirty

end TestsBlock_GridLanesSubgrid
end ChromiumLayout
