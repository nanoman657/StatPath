import BlockWritingModeConverter

namespace TestsBlock

open ChromiumLayout.BlockWritingModeConverter

private def outer : Int × Int := (300, 400)
private def inner : Int × Int := (5, 65)

-- geometry/writing_mode_converter_test.cc:15: WritingModeConverterTest.ConvertLogicalOffsetToPhysicalOffset
theorem ConvertLogicalOffsetToPhysicalOffset_vectors :
    let f := fun wm d => toPhysical wm d outer inner (20, 30)
    f .horizontalTb .ltr = (20, 30) ∧ f .horizontalTb .rtl = (275, 30) ∧
    f .verticalRl .ltr = (265, 20) ∧ f .verticalRl .rtl = (265, 315) ∧
    f .sidewaysRl .ltr = (265, 20) ∧ f .sidewaysRl .rtl = (265, 315) ∧
    f .verticalLr .ltr = (30, 20) ∧ f .verticalLr .rtl = (30, 315) ∧
    f .sidewaysLr .ltr = (30, 315) ∧ f .sidewaysLr .rtl = (30, 20) := by
  decide

-- geometry/writing_mode_converter_test.cc:73: WritingModeConverterTest.ConvertPhysicalOffsetToLogicalOffset
theorem ConvertPhysicalOffsetToLogicalOffset_vectors :
    let f := fun wm d => toLogical wm d outer inner (20, 30)
    f .horizontalTb .ltr = (20, 30) ∧ f .horizontalTb .rtl = (275, 30) ∧
    f .verticalRl .ltr = (30, 275) ∧ f .verticalRl .rtl = (305, 275) ∧
    f .sidewaysRl .ltr = (30, 275) ∧ f .sidewaysRl .rtl = (305, 275) ∧
    f .verticalLr .ltr = (30, 20) ∧ f .verticalLr .rtl = (305, 20) ∧
    f .sidewaysLr .ltr = (305, 20) ∧ f .sidewaysLr .rtl = (30, 20) := by
  decide

end TestsBlock
