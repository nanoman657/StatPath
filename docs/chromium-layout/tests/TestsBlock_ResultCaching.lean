import LayoutTypes
import LayoutBlock
import BlockResultCache

namespace TestsBlock_ResultCaching

open BlockResultCache

#print axioms BlockResultCache.checkBfcCache_aboveStart_floats
#print axioms BlockResultCache.checkShrinkToFitCache_same_avail
#print axioms BlockResultCache.checkSizeAndQuirksCache_dirty
#print axioms BlockResultCache.checkFragmentationCache_overflow

-- block_layout_algorithm_test.cc:106 Caching
theorem blockCaching :
    checkSizeAndQuirksCache 30 0 0 40 0 0 false true false false false false false 100 100 100 100 = true ∧
    checkSizeAndQuirksCache 30 0 0 40 0 0 false true false false false false false 100 100 200 100 = true ∧
    checkSizeAndQuirksCache 30 0 0 40 0 0 false true false false false false false 100 100 200 200 = false ∧
    checkSizeAndQuirksCache 30 0 0 40 0 0 false true false false false false true 200 200 200 200 = false := by decide

-- block_layout_algorithm_test.cc:166 MinInlineSizeCaching
theorem minInlineSizeCaching :
    checkSizeAndQuirksCache 10 30 40 0 0 40 false false false false false false false 100 100 100 100 = true ∧
    checkSizeAndQuirksCache 10 30 40 0 0 40 false false false false false false false 100 100 100 200 = true ∧
    checkSizeAndQuirksCache 10 30 40 0 0 40 false false false false false false false 100 100 200 100 = false := by decide

-- block_layout_algorithm_test.cc:216 PercentageBlockSizeQuirkDescendantsCaching
theorem percentageBlockSizeQuirkDescendantsCaching :
    ([false, false, true, false, true, false, false, true].map fun q =>
      checkSizeAndQuirksCache 100 0 0 0 0 0 q q false false true true false 100 100 100 200) =
      [true, true, false, true, false, true, true, false] := by decide

-- block_layout_algorithm_test.cc:310 LineOffsetCaching
theorem lineOffsetCaching :
    checkBfcCache 0 0 false false 0 0 0 0 0 0 0 0 = some 0 := by decide

-- layout_result_caching_test.cc:51 HitDifferentExclusionSpace
theorem hitDifferentExclusionSpace :
    checkBfcCache 20 0 false false 50 0 20 0 50 0 30 0 = some 50 := by decide

-- layout_result_caching_test.cc:84 HitDifferentBFCOffset
theorem hitDifferentBFCOffset :
    checkBfcCache 25 0 false false 50 0 20 0 40 0 20 0 = some 40 ∧
    shiftedExclusionOpportunities 50 20 40 5 20 100 =
      [(50, 0, 100), (0, 20, 45), (0, 65, 100)] := by decide

-- layout_result_caching_test.cc:144 HitDifferentBFCOffsetSameMarginStrut
theorem hitDifferentBFCOffsetSameMarginStrut :
    checkBfcCache 20 0 false false 50 20 0 0 40 20 0 0 = some 60 := by decide

-- layout_result_caching_test.cc:170 MissDescendantAboveBlockStart1
theorem missDescendantAboveBlockStart1 :
    checkBfcCache 25 0 false true 50 0 20 0 50 0 30 0 = none := by decide

-- layout_result_caching_test.cc:204 MissDescendantAboveBlockStart2
theorem missDescendantAboveBlockStart2 :
    checkBfcCache 25 0 false true 50 0 20 0 40 0 20 0 = none := by decide

-- layout_result_caching_test.cc:238 HitOOFDescendantAboveBlockStart
theorem hitOOFDescendantAboveBlockStart :
    checkBfcCache 25 0 false false 50 0 20 0 40 0 20 0 = some 40 := by decide

-- layout_result_caching_test.cc:311 MissFloatInitiallyIntruding1
theorem missFloatInitiallyIntruding1 :
    checkBfcCache 20 0 false false 50 0 60 0 50 0 30 0 = none := by decide

-- layout_result_caching_test.cc:343 MissFloatInitiallyIntruding2
theorem missFloatInitiallyIntruding2 :
    checkBfcCache 60 0 false false 50 0 60 0 70 0 60 0 = none := by decide

-- layout_result_caching_test.cc:375 MissFloatWillIntrude1
theorem missFloatWillIntrude1 :
    checkBfcCache 20 0 false false 50 0 40 0 50 0 60 0 = none := by decide

-- layout_result_caching_test.cc:406 MissFloatWillIntrude2
theorem missFloatWillIntrude2 :
    checkBfcCache 60 0 false false 50 0 40 0 30 0 40 0 = none := by decide

-- layout_result_caching_test.cc:437 HitPushedByFloats1
theorem hitPushedByFloats1 :
    checkBfcCache 20 1 false false 50 0 60 0 50 0 70 0 = some 70 := by decide

-- layout_result_caching_test.cc:468 HitPushedByFloats2
theorem hitPushedByFloats2 :
    checkBfcCache 20 1 false false 50 0 60 0 30 0 60 0 = some 60 := by decide

-- layout_result_caching_test.cc:499 MissPushedByFloats1
theorem missPushedByFloats1 :
    checkBfcCache 20 1 false false 50 0 70 0 50 0 60 0 = none := by decide

-- layout_result_caching_test.cc:531 MissPushedByFloats2
theorem missPushedByFloats2 :
    checkBfcCache 20 1 false false 30 0 60 0 50 0 60 0 = none := by decide

-- layout_result_caching_test.cc:563 HitDifferentRareData
theorem hitDifferentRareData :
    checkSizeAndQuirksCache 100 0 100 0 0 100 false false false false false false false 100 100 200 200 = true := by decide

-- layout_result_caching_test.cc:638 HitShrinkToFit
theorem hitShrinkToFit :
    checkShrinkToFitCache 150 200 0 0 300 400 = true ∧
    checkShrinkToFitCache 350 600 0 0 300 200 = true := by decide

-- layout_result_caching_test.cc:685 MissShrinkToFit
theorem missShrinkToFit :
    checkShrinkToFitCache 150 200 0 0 300 100 = false ∧
    checkShrinkToFitCache 350 600 0 0 300 400 = false ∧
    checkShrinkToFitCache 250 400 0 80 300 400 = false ∧
    checkShrinkToFitCache 150 200 75 0 300 250 = false := by decide

-- layout_result_caching_test.cc:765 HitShrinkToFitSameIntrinsicSizes
theorem hitShrinkToFitSameIntrinsicSizes :
    checkShrinkToFitCache 250 250 0 0 300 200 = true := by decide

-- layout_result_caching_test.cc:796 HitShrinkToFitDifferentParent
theorem hitShrinkToFitDifferentParent :
    checkShrinkToFitCache 250 250 0 0 250 250 = true := by decide

-- layout_result_caching_test.cc:826 MissQuirksModePercentageBasedChild
theorem missQuirksModePercentageBasedChild :
    checkSizeAndQuirksCache 300 0 0 0 0 0 true true false false true true false 300 300 300 200 = false := by decide

-- layout_result_caching_test.cc:856 HitQuirksModePercentageBasedParentAndChild
theorem hitQuirksModePercentageBasedParentAndChild :
    checkSizeAndQuirksCache 300 0 0 50 200 100 true true false false false false false 300 300 300 200 = true := by decide

-- layout_result_caching_test.cc:891 HitStandardsModePercentageBasedChild
theorem hitStandardsModePercentageBasedChild :
    checkSizeAndQuirksCache 300 0 0 0 0 0 false true false false true true false 300 300 300 200 = true := by decide

-- layout_result_caching_test.cc:920 ChangeTableCellBlockSizeConstrainedness
theorem changeTableCellBlockSizeConstrainedness :
    checkSizeAndQuirksCache 300 0 100 0 0 100 false false false false true false false 300 0 300 300 = true ∧
    checkSizeAndQuirksCache 300 0 0 10 0 30 false false false false true false false 300 0 300 300 = true ∧
    checkSizeAndQuirksCache 300 0 0 10 0 0 false false false false true false false 300 0 300 300 = false := by decide

-- layout_result_caching_test.cc:979 OptimisticFloatPlacementNoRelayout
theorem optimisticFloatPlacementNoRelayout :
    forcedBfcForSelfCollapsing 0 0 = none := by decide

-- layout_result_caching_test.cc:1078 ClearancePastAdjoiningFloatsMovement
theorem clearancePastAdjoiningFloatsMovement :
    checkBfcCache 20 3 false false 0 0 10 20 0 0 20 20 = some 20 ∧
    checkBfcCache 20 1 false false 0 0 10 20 0 0 20 20 = none := by decide

-- layout_result_caching_test.cc:1199 MarginStrutMovementInFlow
theorem marginStrutMovementInFlow :
    checkBfcCache 20 0 false false 0 10 0 0 0 5 0 0 = some 5 ∧
    checkBfcCache 20 0 true false 0 10 0 0 0 5 0 0 = none ∧
    checkBfcCache 20 0 true false 0 10 0 0 0 5 0 0 = none := by decide

-- layout_result_caching_test.cc:1286 MarginStrutMovementPercentage
theorem marginStrutMovementPercentage :
    checkBfcCache 20 0 true false 0 10 0 0 0 5 0 0 = none := by decide

-- layout_result_caching_test.cc:1321 HitIsFixedBlockSizeIndefinite
theorem hitIsFixedBlockSizeIndefinite :
    checkSizeAndQuirksCache 100 0 100 0 100 50 false false false false true false false 100 100 100 100 = true := by decide

-- layout_result_caching_test.cc:1350 MissIsFixedBlockSizeIndefinite
theorem missIsFixedBlockSizeIndefinite :
    checkSizeAndQuirksCache 100 0 100 0 100 50 false true false false false true false 100 100 100 100 = false := by decide

-- layout_result_caching_test.cc:1380 HitColumnFlexBoxMeasureAndLayout
theorem hitColumnFlexBoxMeasureAndLayout :
    checkMeasureLayoutSlot false false = (0, true) ∧
    checkMeasureLayoutSlot true false = (1, false) := by decide

-- layout_result_caching_test.cc:1433 HitRowFlexBoxMeasureAndLayout
theorem hitRowFlexBoxMeasureAndLayout :
    checkMeasureLayoutSlot false false = (0, true) ∧
    checkMeasureLayoutSlot true false = (1, false) := by decide

-- layout_result_caching_test.cc:1488 MissFlexReplaced
theorem missFlexReplaced :
    checkSizeAndQuirksCache 300 0 200 0 0 200 false false true false true false false 300 200 300 200 = false := by decide

-- layout_result_caching_test.cc:1516 HitFlexDefiniteChange
theorem hitFlexDefiniteChange :
    checkMeasureLayoutSlot false false = (0, true) := by decide

-- layout_result_caching_test.cc:1539 HitOrthogonalRoot
theorem hitOrthogonalRoot :
    checkSizeAndQuirksCache 20 0 250 0 0 250 false false true false false false false 20 250 20 250 = true := by decide

-- layout_result_caching_test.cc:1562 SimpleTable
theorem simpleTable :
    checkMeasureLayoutSlot false false = (0, true) := by decide

-- layout_result_caching_test.cc:1592 MissTableCellMiddleAlignment
theorem missTableCellMiddleAlignment :
    checkMeasureLayoutSlot true false = (1, false) := by decide

-- layout_result_caching_test.cc:1615 MissTableCellBottomAlignment
theorem missTableCellBottomAlignment :
    checkMeasureLayoutSlot true false = (1, false) := by decide

-- layout_result_caching_test.cc:1638 HitTableCellBaselineAlignment
theorem hitTableCellBaselineAlignment :
    checkMeasureLayoutSlot false false = (0, true) := by decide

-- layout_result_caching_test.cc:1661 MissTableCellBaselineAlignment
theorem missTableCellBaselineAlignment :
    checkMeasureLayoutSlot false true = (1, false) := by decide

-- layout_result_caching_test.cc:1687 MissTablePercent
theorem missTablePercent :
    checkSizeAndQuirksCache 100 0 0 100 0 50 false false false true false false false 100 50 100 100 = false := by decide

-- layout_result_caching_test.cc:1718 HitTableRowAdd
theorem hitTableRowAdd :
    checkTableRowSectionCache [30, 60] [30, 60] = true := by decide

-- layout_result_caching_test.cc:1739 MissTableRowAdd
theorem missTableRowAdd :
    checkTableRowSectionCache [90, 60] [30, 60] = false := by decide

-- layout_result_caching_test.cc:1760 HitTableRowRemove
theorem hitTableRowRemove :
    checkTableRowSectionCache [30, 60] [30, 60] = true := by decide

-- layout_result_caching_test.cc:1781 MissTableRowRemove
theorem missTableRowRemove :
    checkTableRowSectionCache [30, 60] [90, 60] = false := by decide

-- layout_result_caching_test.cc:1802 HitTableSectionAdd
theorem hitTableSectionAdd :
    checkTableRowSectionCache [30, 60] [30, 60] = true := by decide

-- layout_result_caching_test.cc:1823 HitTableSectionRemove
theorem hitTableSectionRemove :
    checkTableRowSectionCache [30, 60] [30, 60] = true := by decide

-- layout_result_caching_test.cc:1844 FragmentainerSizeChange
theorem fragmentainerSizeChange :
    ([0, 51, 102].map fun off => checkFragmentationCache true false 120 51 51 off off) =
      [true, true, true] ∧
    ([0, 51, 102].map fun off => checkFragmentationCache true false 120 51 50 off off) =
      [false, false, false] := by decide

-- layout_result_caching_test.cc:1921 BlockOffsetChangeInFragmentainer
theorem blockOffsetChangeInFragmentainer :
    ([19, 20, 21].map fun off => checkFragmentationCache false false 80 100 100 10 off) =
      [true, true, false] := by decide

-- layout_result_caching_test.cc:1963 BfcRootBlockOffsetChangeInFragmentainer
theorem bfcRootBlockOffsetChangeInFragmentainer :
    ([19, 20, 21].map fun off => checkFragmentationCache false false 80 100 100 10 off) =
      [true, true, false] := by decide

-- layout_result_caching_test.cc:2005 HitBlockOffsetUnchangedInFragmentainer
theorem hitBlockOffsetUnchangedInFragmentainer :
    checkFragmentationCache false false 50 100 100 30 30 = true := by decide

-- layout_result_caching_test.cc:2035 HitNewFormattingContextInFragmentainer
theorem hitNewFormattingContextInFragmentainer :
    checkFragmentationCache false true 50 0 0 0 0 = true := by decide

-- layout_result_caching_test.cc:2092 MissGridIncorrectIntrinsicSize
theorem missGridIncorrectIntrinsicSize :
    checkSizeAndQuirksCache 100 0 200 0 100 100 false false true false false true false 100 200 100 200 = false := by decide

end TestsBlock_ResultCaching
