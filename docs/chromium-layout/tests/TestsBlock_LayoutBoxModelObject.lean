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

end TestsBlock
end ChromiumLayout
