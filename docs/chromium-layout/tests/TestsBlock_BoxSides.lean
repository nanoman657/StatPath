import BlockBoxSides

namespace TestsBlock

open ChromiumLayout.BlockWritingModeConverter ChromiumLayout.BlockBoxSides

-- geometry/box_sides_test.cc:13: GeometryUnitsTest.LogicalBoxSidesToLineLogical
-- (inline-start and block-start absent, others present)
theorem LogicalBoxSidesToLineLogical_vectors :
    lineSides .rtl false true = (true, false) ∧ lineSides .ltr false true = (false, true) := by
  decide

-- geometry/box_sides_test.cc:35: GeometryUnitsTest.PhysicalBoxSidesToLogical
-- (bottom and left absent, top and right present); result = (is, ie, bs, be)
theorem PhysicalBoxSidesToLogical_vectors :
    let f := fun wm d => toLogical wm d true true false false
    f .verticalRl .rtl = (false, true, true, false) ∧ f .verticalRl .ltr = (true, false, true, false) ∧
    f .verticalLr .rtl = (false, true, false, true) ∧ f .verticalLr .ltr = (true, false, false, true) ∧
    f .sidewaysRl .rtl = (false, true, true, false) ∧ f .sidewaysRl .ltr = (true, false, true, false) ∧
    f .sidewaysLr .rtl = (true, false, false, true) ∧ f .sidewaysLr .ltr = (false, true, false, true) ∧
    f .horizontalTb .rtl = (true, false, true, false) ∧ f .horizontalTb .ltr = (false, true, true, false) := by
  decide

end TestsBlock
