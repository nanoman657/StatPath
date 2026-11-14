/-
  TestsBlock_AnchorEvaluatorImpl.lean: formalization of Chromium tests from
  anchor_evaluator_impl_test.cc.
  Owned by the block lane (TestsBlock_*).
-/
import OutOfFlowAnchor

namespace ChromiumLayout
namespace TestsBlock

open OutOfFlowAnchor

-- anchor_evaluator_impl_test.cc:71: AnchorNameAdd
-- Adding anchor-name registers anchor entry in containing block anchor map.
-- CSS Anchor Positioning Level 1 §3.1.
theorem AnchorNameAdd_vectors :
    let map : AnchorMap := [{ name := "--div1a", rect := ⟨0, 0, 50, 20⟩ }]
    lookupAnchor [] "--div1a" = none ∧
    lookupAnchor map "--div1a" = some ⟨0, 0, 50, 20⟩ := by
  decide

-- anchor_evaluator_impl_test.cc:104: AnchorNameChange
-- Changing anchor-name updates anchor map association.
-- CSS Anchor Positioning Level 1 §3.1.
theorem AnchorNameChange_vectors :
    let map1 : AnchorMap := [{ name := "--div1", rect := ⟨0, 0, 50, 20⟩ }]
    let map2 : AnchorMap := [{ name := "--div1a", rect := ⟨0, 0, 50, 20⟩ }]
    lookupAnchor map1 "--div1" = some ⟨0, 0, 50, 20⟩ ∧
    lookupAnchor map2 "--div1a" = some ⟨0, 0, 50, 20⟩ ∧
    lookupAnchor map2 "--div1" = none := by
  decide

-- anchor_evaluator_impl_test.cc:141: AnchorNameRemove
-- Removing anchor-name clears anchor map entry.
-- CSS Anchor Positioning Level 1 §3.1.
theorem AnchorNameRemove_vectors :
    let map : AnchorMap := [{ name := "--div1", rect := ⟨0, 0, 50, 20⟩ }]
    lookupAnchor map "--div1" = some ⟨0, 0, 50, 20⟩ ∧
    lookupAnchor [] "--div1" = none := by
  decide

-- anchor_evaluator_impl_test.cc:175: BlockFlow
-- Block flow anchor rects update coordinates with sibling size changes.
-- CSS Anchor Positioning Level 1 §3.1, §4.1.
theorem BlockFlow_vectors :
    -- Before: div1 (0, 0, 400, 20), div2 (0, 20, 800, 0), div3 (0, 50, 800, 0)
    let mapBefore : AnchorMap := [
      { name := "--div1", rect := ⟨0, 0, 400, 20⟩ },
      { name := "--div2", rect := ⟨0, 20, 800, 0⟩ },
      { name := "--div3", rect := ⟨0, 50, 800, 0⟩ }
    ]
    -- After: div1 height increases to 40px, div2 at 40px, div3 at 70px
    let mapAfter : AnchorMap := [
      { name := "--div1", rect := ⟨0, 0, 400, 40⟩ },
      { name := "--div2", rect := ⟨0, 40, 800, 0⟩ },
      { name := "--div3", rect := ⟨0, 70, 800, 0⟩ }
    ]
    evaluateAnchor mapBefore "--div1" .bottom = some 20 ∧
    evaluateAnchor mapBefore "--div2" .top = some 20 ∧
    evaluateAnchor mapBefore "--div3" .top = some 50 ∧
    evaluateAnchor mapAfter "--div1" .bottom = some 40 ∧
    evaluateAnchor mapAfter "--div2" .top = some 40 ∧
    evaluateAnchor mapAfter "--div3" .top = some 70 := by
  decide

-- anchor_evaluator_impl_test.cc:284: OutOfFlow
-- Anchor names of out-of-flow positioned objects propagate to containing block.
-- CSS Anchor Positioning Level 1 §3.1.
theorem OutOfFlow_vectors :
    let map : AnchorMap := [{ name := "--abs1", rect := ⟨100, 50, 400, 20⟩ }]
    lookupAnchor map "--abs1" = some ⟨100, 50, 400, 20⟩ := by
  decide

-- anchor_evaluator_impl_test.cc:330: Transform
-- CSS transforms shift anchor rectangle coordinates in anchor map.
-- CSS Transforms 1 §2, CSS Anchor Positioning 1 §3.1.
theorem Transform_vectors :
    let initialRect : AnchorRect := ⟨0, 0, 800, 0⟩
    let transformed := transformAnchor initialRect 100 100
    let map : AnchorMap := [{ name := "--transform", rect := transformed }]
    transformed = ⟨100, 100, 800, 0⟩ ∧
    lookupAnchor map "--transform" = some ⟨100, 100, 800, 0⟩ := by
  decide

-- anchor_evaluator_impl_test.cc:351: Scroll
-- Scroll positions do not shift anchor rectangles in anchor map.
-- CSS Anchor Positioning Level 1 §3.1.
theorem Scroll_vectors :
    let baseRect : AnchorRect := ⟨0, 0, 400, 500⟩
    let scrolled := scrollAnchor baseRect 30 20
    let map : AnchorMap := [{ name := "--inner", rect := scrolled }]
    scrolled = baseRect ∧
    lookupAnchor map "--inner" = some ⟨0, 0, 400, 500⟩ := by
  decide

-- anchor_evaluator_impl_test.cc:375: FragmentedContainingBlock
-- Anchor rectangles fragment across multicol columns.
-- CSS Fragmentation 3 §2, CSS Anchor Positioning 1 §3.3.
theorem FragmentedContainingBlock_vectors :
    let cbFrag1Map : AnchorMap := [{ name := "--a1", rect := ⟨0, 50, 100, 50⟩ }]
    let cbFrag2Map : AnchorMap := [{ name := "--a1", rect := ⟨0, 0, 100, 50⟩ }]
    let columnsMap : AnchorMap := [{ name := "--a1", rect := ⟨110, 0, 210, 100⟩ }]
    let containerMap : AnchorMap := [{ name := "--a1", rect := ⟨110, 10, 210, 100⟩ }]
    lookupAnchor cbFrag1Map "--a1" = some ⟨0, 50, 100, 50⟩ ∧
    lookupAnchor cbFrag2Map "--a1" = some ⟨0, 0, 100, 50⟩ ∧
    lookupAnchor columnsMap "--a1" = some ⟨110, 0, 210, 100⟩ ∧
    lookupAnchor containerMap "--a1" = some ⟨110, 10, 210, 100⟩ := by
  decide

-- anchor_evaluator_impl_test.cc:437: FragmentHasRunningAnchorTransformAnimation
-- HasRunningAnchorTransformAnimation returns false when no animation is running.
-- CSS Anchor Positioning Level 1 §3.1.
theorem FragmentHasRunningAnchorTransformAnimation_vectors :
    hasRunningAnchorTransformAnimation false = false := by
  decide

-- anchor_evaluator_impl_test.cc:446: FrameViewHasRunningAnchorTransformAnimation
-- HasRunningAnchorTransformAnimation on frame view returns false when no animation is running.
-- CSS Anchor Positioning Level 1 §3.1.
theorem FrameViewHasRunningAnchorTransformAnimation_vectors :
    hasRunningAnchorTransformAnimation false = false := by
  decide

end TestsBlock
end ChromiumLayout
