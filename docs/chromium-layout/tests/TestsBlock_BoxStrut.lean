import BlockWritingMode

namespace TestsBlock

open ChromiumLayout.BlockWritingMode

-- geometry/box_strut_test.cc:16: GeometryUnitsTest.ConvertPhysicalStrutToLogical
theorem ConvertPhysicalStrutToLogical_vectors :
    let p : Phys := ⟨15, 10, 20, 5⟩
    (toLogical .horizontalTb p).inlineStart = 5 ∧
    (toLogical .horizontalTb p).blockStart = 15 ∧
    (toLogical .verticalLr p).inlineStart = 15 ∧
    (toLogical .verticalLr p).blockStart = 5 ∧
    (toLogical .verticalRl p).inlineStart = 15 ∧
    (toLogical .verticalRl p).blockStart = 10 := by
  decide

-- geometry/box_strut_test.cc:52: GeometryUnitsTest.ConvertLogicalStrutToPhysical
-- General roundtrip identity proved for all writing modes
theorem ConvertLogicalStrutToPhysical_roundtrip (wm : WritingMode) (l : Logical) :
    toLogical wm (toPhysical wm l) = l :=
  toLogical_toPhysical wm l

end TestsBlock
