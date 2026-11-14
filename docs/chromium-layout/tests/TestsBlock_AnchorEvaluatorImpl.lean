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

end TestsBlock
end ChromiumLayout
