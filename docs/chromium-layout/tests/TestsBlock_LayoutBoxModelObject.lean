/-
  TestsBlock_LayoutBoxModelObject.lean: formalization of Chromium tests from
  layout_box_model_object_test.cc.
  Owned by the block lane (TestsBlock_*).
-/
import BlockSticky

namespace ChromiumLayout
namespace TestsBlock

open BlockSticky

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

end TestsBlock
end ChromiumLayout
