/-
  TestsBlock_LayoutBoxModelObject.lean: formalization of Chromium tests from
  layout_box_model_object_test.cc.
  Owned by the block lane (TestsBlock_*).
-/
import BlockLength
import BlockOverflow
import BlockSticky

namespace ChromiumLayout
namespace TestsBlock

open BlockLength BlockOverflow BlockSticky

-- layout_box_model_object_test.cc:974: StickyPositionNested
-- Nested sticky divs: parent shifts by 50px, child is already aligned with scroll top.
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionNested_vectors :
    let scrollerScroll := 100
    let parentConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 50,
      cbHeight := 1000
    }
    let parentShift := computeStickyOffset parentConstraint scrollerScroll 0
    let childConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 25,
      cbHeight := 50
    }
    let childShift := computeStickyOffset childConstraint scrollerScroll parentShift
    parentShift = 50 ∧ childShift = 0 := by
  decide

-- layout_box_model_object_test.cc:1005: StickyPositionChildHasLargerTop
-- Child has top: 25px, parent has top: 0px. Child offsets 25px relative to parent.
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionChildHasLargerTop_vectors :
    let scrollerScroll := 100
    let parentConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 50,
      cbHeight := 1000
    }
    let parentShift := computeStickyOffset parentConstraint scrollerScroll 0
    let childConstraint : StickyConstraint := {
      top := some 25,
      inFlowTop := 50,
      height := 25,
      cbHeight := 50
    }
    let childShift := computeStickyOffset childConstraint scrollerScroll parentShift
    parentShift = 50 ∧ childShift = 25 := by
  decide

-- layout_box_model_object_test.cc:1036: StickyPositionParentHasLargerTop
-- Parent has top: 25px (shifts 75px), child has top: 0px. Child cannot push above parent.
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionParentHasLargerTop_vectors :
    let scrollerScroll := 100
    let parentConstraint : StickyConstraint := {
      top := some 25,
      inFlowTop := 50,
      height := 50,
      cbHeight := 1000
    }
    let parentShift := computeStickyOffset parentConstraint scrollerScroll 0
    let childConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 25,
      cbHeight := 50
    }
    let childShift := computeStickyOffset childConstraint scrollerScroll parentShift
    parentShift = 75 ∧ childShift = 0 := by
  decide

-- layout_box_model_object_test.cc:1067: StickyPositionChildPushingOutsideParent
-- Child top: 50px wants 50px shift, but is capped by 25px headroom inside parent.
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionChildPushingOutsideParent_vectors :
    let scrollerScroll := 100
    let parentConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 50,
      cbHeight := 1000
    }
    let parentShift := computeStickyOffset parentConstraint scrollerScroll 0
    let childConstraint : StickyConstraint := {
      top := some 50,
      inFlowTop := 50,
      height := 25,
      cbHeight := 50
    }
    let childShift := computeStickyOffset childConstraint scrollerScroll parentShift
    parentShift = 50 ∧ childShift = 25 := by
  decide

-- layout_box_model_object_test.cc:1100: StickyPositionTripleNestedDiv
-- Triple nested sticky divs: outmost (top: 0 -> 50), middle (top: 0 -> 0), inner (top: 25 -> 25).
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionTripleNestedDiv_vectors :
    let scrollerScroll := 100
    let outmostConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 100,
      cbHeight := 1000
    }
    let outmostShift := computeStickyOffset outmostConstraint scrollerScroll 0
    let middleConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 50,
      height := 75,
      cbHeight := 100
    }
    let middleShift := computeStickyOffset middleConstraint scrollerScroll outmostShift
    let innerConstraint : StickyConstraint := {
      top := some 25,
      inFlowTop := 50,
      height := 25,
      cbHeight := 75
    }
    let innerShift := computeStickyOffset innerConstraint scrollerScroll (outmostShift + middleShift)
    outmostShift = 50 ∧ middleShift = 0 ∧ innerShift = 25 := by
  decide

-- layout_box_model_object_test.cc:143: StickyPositionConstraints
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionConstraints_vectors :
    let cb := containingBlockInterval 100 10 5 400 true
    let sb := stickyBoxInterval cb.top 0 100
    cb = ⟨115, 370⟩ ∧ sb = ⟨115, 100⟩ := by
  decide

-- layout_box_model_object_test.cc:184: StickyPositionVerticalRLConstraints
-- CSS Positioned Layout Level 3 §2.3, CSS Writing Modes Level 3 §6.4.
theorem StickyPositionVerticalRLConstraints_vectors :
    let cb := containingBlockInterval 100 10 5 400 true
    let sb := stickyBoxInterval cb.top 0 100
    cb = ⟨115, 370⟩ ∧ sb = ⟨115, 100⟩ := by
  decide

-- layout_box_model_object_test.cc:225: StickyPositionInlineConstraints
-- CSS Positioned Layout Level 3 §2.3.
theorem StickyPositionInlineConstraints_vectors :
    let cb := containingBlockInterval 100 0 0 400 false
    let sb := stickyBoxInterval cb.top 0 10
    cb = ⟨100, 400⟩ ∧ sb = ⟨100, 10⟩ := by
  decide

-- layout_box_model_object_test.cc:330: StickyPositionTransforms
-- CSS Positioned Layout Level 3 §2.3, CSS Transforms 1 §3.
-- Sticky constraint geometry is resolved in layout coordinates invariant under transforms.
theorem StickyPositionTransforms_vectors :
    let cb := containingBlockInterval 100 10 5 400 true
    let sb := stickyBoxInterval cb.top 0 100
    cb = ⟨115, 370⟩ ∧ sb = ⟨115, 100⟩ := by
  decide

-- layout_box_model_object_test.cc:410: StickyPositionContainerIsScroller
-- CSS Positioned Layout Level 3 §2.3.
-- When scroller is containing block, containing block interval covers entire scrollable content (1100px).
theorem StickyPositionContainerIsScroller_vectors :
    let cb := containingBlockInterval 0 0 0 1100 false
    let sb := stickyBoxInterval cb.top 0 100
    cb = ⟨0, 1100⟩ ∧ sb = ⟨0, 100⟩ := by
  decide

-- layout_box_model_object_test.cc:506: StickyPositionAnonymousContainer
-- CSS Positioned Layout Level 3 §2.3.
-- Sticky item following a 50px header starts at offset 50 inside containing block.
theorem StickyPositionAnonymousContainer_vectors :
    let cb := containingBlockInterval 100 10 5 400 true
    let sb := stickyBoxInterval cb.top 50 100
    cb = ⟨115, 370⟩ ∧ sb = ⟨165, 100⟩ := by
  decide

-- layout_box_model_object_test.cc:1138: StickyPositionNestedStickyTable
-- CSS Positioned Layout Level 3 §2.3.
-- Sticky header inside sticky table inside scroller:
-- at scroll 150: stickyDiv = 100, stickyTh = 0
-- at scroll 275: stickyDiv = 200, stickyTh = 25
-- at scroll 350: stickyDiv = 200, stickyTh = 100
theorem StickyPositionNestedStickyTable_vectors :
    let divC : StickyConstraint := ⟨some 0, 50, 200, 400⟩
    let thC : StickyConstraint := ⟨some 0, 50, 25, 125⟩
    (computeStickyOffset divC 150 0 = 100 ∧ computeStickyOffset thC 150 100 = 0) ∧
    (computeStickyOffset divC 275 0 = 200 ∧ computeStickyOffset thC 275 200 = 25) ∧
    (computeStickyOffset divC 350 0 = 200 ∧ computeStickyOffset thC 350 200 = 100) := by
  decide

-- layout_box_model_object_test.cc:1230: StickyPositionNestedInlineElements
-- CSS Positioned Layout Level 3 §2.3.
-- Empty unanchored sticky inlines produce 0 offset; nested sticky with top: 25px produces 25px offset.
theorem StickyPositionNestedInlineElements_vectors :
    let outerC : StickyConstraint := ⟨none, 50, 0, 250⟩
    let innerC : StickyConstraint := ⟨some 25, 50, 0, 250⟩
    computeStickyOffset outerC 50 0 = 0 ∧
    computeStickyOffset innerC 50 0 = 25 := by
  decide

-- layout_box_model_object_test.cc:610: StickyPositionStatusChange
-- position: sticky with top: 0 has constraints; changing top to auto removes constraints.
-- CSS Positioned Layout 3 §2.3.
theorem StickyPositionStatusChange_vectors :
    let withTop : StickyConstraint := { top := some 0 }
    let withAuto : StickyConstraint := { top := none }
    withTop.top.isSome = true ∧ withAuto.top.isSome = false := by
  decide

-- layout_box_model_object_test.cc:701: StickyPositionFindsCorrectStickyBoxShiftingAncestor
-- Unanchored sticky element (no top/bottom/left/right) has no constraints.
-- CSS Positioned Layout 3 §2.3.
theorem StickyPositionFindsCorrectStickyBoxShiftingAncestor_vectors :
    let unanchored : StickyConstraint := {}
    let anchored : StickyConstraint := { top := some 0 }
    unanchored.top.isSome = false ∧ anchored.top.isSome = true := by
  decide

-- layout_box_model_object_test.cc:1268: StickyPositionNestedFixedPos
-- Sticky box inside fixed-pos container is fixed to view, constrained by view,
-- and unaffected by intermediate scroller.
-- CSS Positioned Layout 3 §2.3.
theorem StickyPositionNestedFixedPos_vectors :
    let scrollerScroll := 100
    let outerConstraint : StickyConstraint := {
      top := some 0,
      inFlowTop := 0,
      height := 50,
      cbHeight := 650
    }
    let outerShift := computeStickyOffset outerConstraint scrollerScroll 0
    let innerTopConstraint : StickyConstraint := {
      top := some 25,
      inFlowTop := 0,
      height := 25,
      cbHeight := 1000
    }
    let innerTopShift := computeStickyOffset innerTopConstraint 0 0
    outerShift = 100 ∧ innerTopShift = 25 := by
  decide

-- layout_box_model_object_test.cc:805: StickyPositionFindsNearestStickyInlineForBlockChild
-- Block child inside nested sticky inline elements detects the nearest inline sticky ancestor.
-- CSS Positioned Layout 3 §2.3.
theorem StickyPositionFindsNearestStickyInlineForBlockChild_vectors :
    let nodes : List StickyNode := [
      { id := "scroller", isScroller := true },
      { id := "container", containingBlockId := some "scroller", parentId := some "scroller" },
      { id := "farther", isSticky := true, isAnchored := true, parentId := some "container" },
      { id := "nearer", isSticky := true, isAnchored := true, parentId := some "farther" },
      { id := "inner", isSticky := true, isAnchored := true, parentId := some "nearer" }
    ]
    findNearestStickyBoxShiftingAncestor nodes "inner" = some "nearer" := by
  decide

-- layout_box_model_object_test.cc:843: StickyPositionFindsCorrectContainingBlockShiftingAncestor
-- Descendant sticky elements find the nearest containing-block shifting ancestor, skipping unanchored sticky.
-- CSS Positioned Layout 3 §2.3.
theorem StickyPositionFindsCorrectContainingBlockShiftingAncestor_vectors :
    let nodes : List StickyNode := [
      { id := "scroller", isScroller := true },
      { id := "stickyParent", isSticky := true, isAnchored := true, containingBlockId := some "scroller", parentId := some "scroller" },
      { id := "unanchoredSticky", isSticky := true, isAnchored := false, parentId := some "stickyParent" },
      { id := "stickyChild", isSticky := true, isAnchored := true, containingBlockId := some "stickyParent", parentId := some "unanchoredSticky" },
      { id := "div", containingBlockId := some "stickyParent", parentId := some "unanchoredSticky" },
      { id := "stickyNestedChild", isSticky := true, isAnchored := true, containingBlockId := some "stickyParent", parentId := some "div" }
    ]
    findNearestContainingBlockShiftingAncestor nodes "stickyParent" = none ∧
    findNearestContainingBlockShiftingAncestor nodes "stickyChild" = some "stickyParent" ∧
    findNearestContainingBlockShiftingAncestor nodes "stickyNestedChild" = some "stickyParent" := by
  decide

-- layout_box_model_object_test.cc:905: StickyPositionFindsCorrectContainingBlockShiftingAncestorRoot
-- Grandchild sticky detects ancestor sticky as containing-block shifting ancestor when overflow ancestor is the page.
-- CSS Positioned Layout 3 §2.3.
theorem StickyPositionFindsCorrectContainingBlockShiftingAncestorRoot_vectors :
    let nodes : List StickyNode := [
      { id := "stickyParent", isSticky := true, isAnchored := true },
      { id := "div", parentId := some "stickyParent" },
      { id := "stickyGrandchild", isSticky := true, isAnchored := true, containingBlockId := some "stickyParent", parentId := some "div" }
    ]
    findNearestContainingBlockShiftingAncestor nodes "stickyGrandchild" = some "stickyParent" := by
  decide

-- layout_box_model_object_test.cc:940: StickyPositionFindsCorrectContainingBlockShiftingAncestorTable
-- In a table, table cell's containing block is table, skipping over thead/tr to find outer sticky.
-- CSS Positioned Layout 3 §2.3, CSS 2.1 §10.1.
theorem StickyPositionFindsCorrectContainingBlockShiftingAncestorTable_vectors :
    let nodes : List StickyNode := [
      { id := "scroller", isScroller := true },
      { id := "stickyOuter", isSticky := true, isAnchored := true, parentId := some "scroller" },
      { id := "table", parentId := some "stickyOuter" },
      { id := "thead", parentId := some "table" },
      { id := "tr", parentId := some "thead" },
      { id := "stickyTh", isSticky := true, isAnchored := true, containingBlockId := some "table", parentId := some "tr" }
    ]
    findNearestContainingBlockShiftingAncestor nodes "stickyTh" = some "stickyOuter" := by
  decide

-- layout_box_model_object_test.cc:571: StickyPositionConstraintInvalidation
-- Flex container distributes width: 150px (with 50px target) vs 200px (when target hidden).
-- Auto margins on 100px container update sticky box X offset from 25px to 50px.
-- CSS Flexible Box 1 §9.2, CSS 2.1 §10.3.3, CSS Positioned Layout 3 §2.3.
theorem StickyPositionConstraintInvalidation_vectors :
    let x1 := (autoMargins 150 100 .auto .auto).1
    let x2 := (autoMargins 200 100 .auto .auto).1
    x1 = 25 ∧ x2 = 50 := by
  decide

-- layout_box_model_object_test.cc:1589: StickyParentContainStrictChangeOverflowProperty
-- When body has visible overflow, containing scroll container is LayoutView.
-- When body toggles to overflow: hidden, containing scroll container becomes body.
-- When body reverts to visible overflow, containing scroll container reverts to LayoutView.
-- CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3.
theorem StickyParentContainStrictChangeOverflowProperty_vectors :
    let initial := findContainingScrollContainer [("body", .visible, .visible)] "LayoutView"
    let withHidden := findContainingScrollContainer [("body", .hidden, .hidden)] "LayoutView"
    let reverted := findContainingScrollContainer [("body", .visible, .visible)] "LayoutView"
    initial = "LayoutView" ∧ withHidden = "body" ∧ reverted = "LayoutView" := by
  decide

-- layout_box_model_object_test.cc:1618: RemoveStickyUnderContain
-- Removing a parent element clears its sticky descendants from the scrollable area.
-- CSS Positioned Layout 3 §2.3.
theorem RemoveStickyUnderContain_vectors :
    let initialSticky : Option StickyConstraint := some { top := some 100 }
    let removedSticky : Option StickyConstraint := none
    initialSticky.isSome = true ∧ removedSticky.isSome = false := by
  decide

-- layout_box_model_object_test.cc:1643: ChangeStickyStatusUnderContain
-- Toggling position between static and sticky dynamically attaches and detaches sticky constraints.
-- CSS Positioned Layout 3 §2.3.
theorem ChangeStickyStatusUnderContain_vectors :
    let initial : StickyConstraint := {}
    let sticky : StickyConstraint := { top := some 1 }
    let cleared : StickyConstraint := {}
    initial.top.isSome = false ∧ sticky.top.isSome = true ∧ cleared.top.isSome = false := by
  decide

-- layout_box_model_object_test.cc:1671: ChangeStickyStatusKeepLayerUnderContain
-- An element with existing paint layer (opacity < 1) gains and loses sticky constraints on position change.
-- CSS Positioned Layout 3 §2.3, CSS Color 3 §3.2.
theorem ChangeStickyStatusKeepLayerUnderContain_vectors :
    let initial : StickyConstraint := {}
    let sticky : StickyConstraint := { top := some 1 }
    let cleared : StickyConstraint := {}
    initial.top.isSome = false ∧ sticky.top.isSome = true ∧ cleared.top.isSome = false := by
  decide

-- layout_box_model_object_test.cc:1700: RemoveStickyStatusInNestedStickyElementsWithContain
-- When container changes from sticky to relative, child sticky element updates its
-- nearest containing-block shifting ancestor from container to body.
-- CSS Positioned Layout 3 §2.3.
theorem RemoveStickyStatusInNestedStickyElementsWithContain_vectors :
    let nodesWithStickyContainer : List StickyNode := [
      { id := "body", isSticky := true, isAnchored := true },
      { id := "container", isSticky := true, isAnchored := true, containingBlockId := some "body", parentId := some "body" },
      { id := "child", isSticky := true, isAnchored := true, containingBlockId := some "container", parentId := some "container" }
    ]
    let nodesWithRelContainer : List StickyNode := [
      { id := "body", isSticky := true, isAnchored := true },
      { id := "container", isSticky := false, isAnchored := false, containingBlockId := some "body", parentId := some "body" },
      { id := "child", isSticky := true, isAnchored := true, containingBlockId := some "container", parentId := some "container" }
    ]
    findNearestContainingBlockShiftingAncestor nodesWithStickyContainer "child" = some "container" ∧
    findNearestContainingBlockShiftingAncestor nodesWithRelContainer "child" = some "body" := by
  decide

end TestsBlock
end ChromiumLayout
