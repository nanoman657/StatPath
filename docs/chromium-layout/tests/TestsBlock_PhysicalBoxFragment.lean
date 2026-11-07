import BlockPhysicalFragment

namespace TestsBlock

open ChromiumLayout.BlockPhysicalFragment

-- physical_box_fragment_test.cc:29: FloatingDescendantsInlineChlidren
theorem FloatingDescendantsInlineChlidren_vectors :
    propagatesFloats .block = true := rfl

-- physical_box_fragment_test.cc:46: FloatingDescendantsBlockChlidren
theorem FloatingDescendantsBlockChlidren_vectors :
    propagatesFloats .block = true := rfl

-- physical_box_fragment_test.cc:65: FloatingDescendantsInlineBlock
theorem FloatingDescendantsInlineBlock_vectors :
    propagatesFloats .inlineBlock = false := rfl

-- physical_box_fragment_test.cc:83: FloatingDescendantsBlockFormattingContext
theorem FloatingDescendantsBlockFormattingContext_vectors :
    propagatesFloats .flowRoot = true ∧
    propagatesFloats .positioned = true := ⟨rfl, rfl⟩

-- physical_box_fragment_test.cc:115: IsFragmentationContextRoot
theorem IsFragmentationContextRoot_vectors :
    isFragmentationContextRoot .multicol = true ∧
    isFragmentationContextRoot .column = false ∧
    isFragmentationContextRoot .normal = false := by
  decide

-- physical_box_fragment_test.cc:135: IsFragmentationContextRootNested
theorem IsFragmentationContextRootNested_vectors :
    isFragmentationContextRoot .multicol = true ∧
    isFragmentationContextRoot .column = false ∧
    isFragmentationContextRoot .normal = false := by
  decide

-- physical_box_fragment_test.cc:169: IsFragmentationContextRootFieldset
theorem IsFragmentationContextRootFieldset_vectors :
    isFragmentationContextRoot .normal = false ∧
    isFragmentationContextRoot .fieldsetWrapper = true ∧
    isFragmentationContextRoot .column = false := by
  decide

-- physical_box_fragment_test.cc:201: MayHaveDescendantAboveBlockStart
-- margin-top: -200px gives child top < 0
theorem MayHaveDescendantAboveBlockStart_vectors :
    mayHaveDescendantAboveBlockStart (-100) = true ∧
    mayHaveDescendantAboveBlockStart 0 = false := by
  decide

-- physical_box_fragment_test.cc:216: MayHaveDescendantAboveBlockStartBlockInInline
theorem MayHaveDescendantAboveBlockStartBlockInInline_vectors :
    mayHaveDescendantAboveBlockStart (-100) = true := by
  decide

-- physical_box_fragment_test.cc:233: OverflowClipMarginVisualBox
theorem OverflowClipMarginVisualBox_vectors :
    clipMarginWidth .contentBox = 75 ∧
    clipMarginHeightFrag1 .contentBox = 40 ∧
    clipMarginWidth .paddingBox = 80 ∧
    clipMarginHeightFrag1 .paddingBox = 45 ∧
    clipMarginWidth .borderBox = 85 ∧
    clipMarginHeightFrag1 .borderBox = 50 := by
  decide

end TestsBlock
