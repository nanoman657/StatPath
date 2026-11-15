import LayoutTypes
import LayoutBlock
import BlockFragmentation
import ColumnFloatBreak

namespace TestsBlock_ColumnFloatBreak

open ColumnFloatBreak

#print axioms ColumnFloatBreak.editableMulticol_height
#print axioms ColumnFloatBreak.floatIndentAt_nil
#print axioms ColumnFloatBreak.linesInFirstColumn_lt_orphans
#print axioms ColumnFloatBreak.balancedNegativeMargin_le_childH
#print axioms ColumnFloatBreak.oofFragmentainerBreakTokens_length

-- column_layout_algorithm_test.cc:41 EmptyEditable
theorem emptyEditable :
    layoutEditableMulticol 200 3 10 20 0 0 =
      ((200, 20), [(0, 0, 60, 20, [])]) := by rfl

-- column_layout_algorithm_test.cc:56 EmptyEditableWithFloat
theorem emptyEditableWithFloat :
    layoutEditableMulticol 200 3 10 20 10 60 =
      ((200, 20),
       [(0, 0, 60, 20, [(0, 0, 10, 20)]),
        (70, 0, 60, 20, [(0, 0, 10, 20)]),
        (140, 0, 60, 20, [(0, 0, 10, 20)])]) := by rfl

-- column_layout_algorithm_test.cc:1725 LinesAndFloatsMulticol
theorem linesAndFloatsMulticol :
    layoutLinesAndFloats 70 0
      [.line 20, .leftFloat 10 120, .line 20, .leftFloat 11 120,
       .line 20, .line 20, .line 20] =
      ([(0, 0, 0), (0, 10, 20), (0, 21, 40), (1, 21, 0), (1, 21, 20)],
       [(0, 0, 20, 10, 50), (1, 0, 0, 10, 70),
        (0, 10, 40, 11, 30), (1, 10, 0, 11, 70), (2, 0, 0, 11, 20)]) := by decide

-- column_layout_algorithm_test.cc:2278 FloatInBlockMovedByOrphans
theorem floatInBlockMovedByOrphans :
    layoutBlockWithMovedFloat 50 30 2 20 2 1 1 10 50 =
      (0, ([(1, 0, 0), (1, 10, 20)], [(1, 0, 20, 10, 30), (2, 0, 0, 10, 20)])) := by decide

-- column_layout_algorithm_test.cc:2318 FloatMovedWithWidows
theorem floatMovedWithWidows :
    layoutBlockWithMovedFloat 70 0 4 20 1 2 2 10 50 =
      (2, ([(1, 10, 0), (1, 10, 20)], [(1, 0, 0, 10, 50)])) := by decide

-- column_layout_algorithm_test.cc:2427 ForcedBreaks
theorem forcedBreaks :
    layoutWrapperForcedBreak 60 10 100
      [(some (10, 10), 20), (some (10, 10), 20), (none, 20)] =
      [(0, 0, 60, 20, [(0, 0, 10, 10), (0, 0, 60, 20)]),
       (70, 0, 60, 20, [(0, 0, 10, 10), (0, 0, 60, 20)]),
       (140, 0, 60, 20, [(0, 0, 60, 20)])] := by rfl

-- column_layout_algorithm_test.cc:3597 ColumnBalancingUnderflow
theorem columnBalancingUnderflow :
    layoutBalancedNegativeMargin 120 2 10 55 110 100 =
      ((120, 10), (0, 0, 55, 10), (0, -100, 55, 110)) := by decide

-- column_layout_algorithm_test.cc:4388 AbsposFitsInOneColumn
theorem absposFitsInOneColumn :
    layoutRelWithSingleColAbspos 100 10 100 100 250 111 50 =
      [(0, 0, 100, 100, [(0, 0, 100, 100), (0, 0, 111, 50)]),
       (110, 0, 100, 100, [(0, 0, 100, 100)]),
       (220, 0, 100, 50, [(0, 0, 100, 50)])] := by rfl

-- fragmentation_test.cc:235 InkOverflowInline
theorem inkOverflowInline :
    multicolInkOverflow 100 10 15 [(100, 10), (150, 10)] =
      (0, 0, 260, 15) := by decide

-- fragmentation_test.cc:303 OffsetFromOwnerLayoutBoxNested
theorem offsetFromOwnerLayoutBoxNested :
    nestedOffsetFromOwnerLayoutBox 100 10 500 700 45 10 800 400 1000 =
      [(0, 0), (55, -300), (110, -300)] := by decide

-- fragmentation_test.cc:373 ConsumedBlockSizeOverflowOutOfFlow
theorem consumedBlockSizeOverflowOutOfFlow :
    (List.range 3).map (fun i => ChromiumLayout.BlockFlow.consumedBlockSize 100 i) =
      [100, 200, 300] ∧
    (ChromiumLayout.ColumnNested.sliceOne 100 334 (max 150 333) 0).1.map (·.2) =
      [100, 100, 100, 33] := by decide

-- out_of_flow_layout_part_test.cc:694 PositionedFragmentationAndColumnSpanners
theorem positionedFragmentationAndColumnSpanners :
    layoutOofAfterSpanner 1000 16 40 30 60 5 20 =
      ([(0, 0, 492, 0), (0, 0, 1000, 0), (0, 0, 492, 30), (508, 0, 492, 30), (0, 30, 1000, 0)],
       [(0, 30, 492, 10, [(0, 0, 30, 0), (0, 0, 5, 10)]),
        (508, 30, 492, 10, [(0, 0, 5, 10)])]) := by rfl

-- out_of_flow_layout_part_test.cc:745 PositionedFragmentationWithNestedSpanner
theorem positionedFragmentationWithNestedSpanner :
    layoutOofAfterSpanner 1000 16 40 30 0 5 50 =
      ([(0, 0, 492, 0), (0, 0, 1000, 0)],
       [(0, 0, 492, 40, [(0, 0, 30, 0), (0, 0, 5, 40)]),
        (508, 0, 492, 40, [(0, 0, 5, 10)])]) := by rfl

-- out_of_flow_layout_part_test.cc:842 AbsposInSpanner
theorem absposInSpanner :
    layoutAbsposInSpanner 50 16 40 30 0 0 5 50 (some 5) =
      ([(0, 0, 17, 15), (33, 0, 17, 15), (0, 15, 50, 0), (0, 15, 17, 25)],
       (0, 5, 5, 50)) := by decide

-- out_of_flow_layout_part_test.cc:895 AbsposInSpannerStaticPos
theorem absposInSpannerStaticPos :
    layoutAbsposInSpanner 50 16 40 30 5 5 5 50 none =
      ([(0, 0, 17, 15), (33, 0, 17, 15), (0, 20, 50, 5), (0, 25, 17, 15)],
       (0, 25, 5, 50)) := by decide

-- out_of_flow_layout_part_test.cc:987 PositionedFragmentationWithNewColumnsAndSpanners
theorem positionedFragmentationWithNewColumnsAndSpanners :
    layoutOofBeforeSpanners 1000 16 40 20 0 5 120 3 =
      ([(0, 0, 492, 40, [(0, 0, 5, 40)]),
        (508, 0, 492, 40, [(0, 0, 5, 40)]),
        (1016, 0, 492, 40, [(0, 0, 5, 40)])],
       [(0, 40, 1000, 0), (0, 40, 1000, 0), (0, 40, 1000, 0)]) := by rfl

-- out_of_flow_layout_part_test.cc:1038 PositionedFragmentationWithNewColumnsAfterSpanner
-- (block sizes scaled by 2 for exact half-pixel 37.5px = 75/2, 12.5px = 25/2)
theorem positionedFragmentationWithNewColumnsAfterSpanner :
    layoutOofBeforeSpanners 1000 16 80 40 50 5 100 1 =
      ([(0, 0, 492, 75, [(0, 50, 5, 25)]),
        (508, 0, 492, 75, [(0, 0, 5, 75)])],
       [(0, 75, 1000, 0)]) := by rfl

-- out_of_flow_layout_part_test.cc:1128 AbsposFragWithSpannerAndNewEmptyColumns
theorem absposFragWithSpannerAndNewEmptyColumns :
    layoutOofBeforeSpanners 1000 16 40 0 80 5 120 3 =
      ([(0, 0, 492, 40, []),
        (508, 0, 492, 40, []),
        (1016, 0, 492, 40, [(0, 0, 5, 40)]),
        (1524, 0, 492, 40, [(0, 0, 5, 40)]),
        (2032, 0, 492, 40, [(0, 0, 5, 40)])],
       [(0, 40, 1000, 0), (0, 40, 1000, 0), (0, 40, 1000, 0)]) := by rfl

-- out_of_flow_layout_part_test.cc:1431 PositionedFragmentationWithBottomPropertyAndHeightAuto
theorem positionedFragmentationWithBottomPropertyAndHeightAuto :
    layoutAutoHeightBottomOof 492 16 40 32 60 5 [(2, 10), (3, 20), (4, 10)] =
      [(0, 0, 492, 40, [(0, 0, 32, 40), (0, 20, 5, 20)]),
       (508, 0, 492, 40, [(0, 0, 32, 20), (0, 0, 5, 20)])] := by rfl

-- out_of_flow_layout_part_test.cc:1479 AbsposFragWithInlineCBAndSpanner
theorem absposFragWithInlineCBAndSpanner :
    layoutOofBeforeSpanners 1000 16 40 0 80 5 120 3 =
      ([(0, 0, 492, 40, []),
        (508, 0, 492, 40, []),
        (1016, 0, 492, 40, [(0, 0, 5, 40)]),
        (1524, 0, 492, 40, [(0, 0, 5, 40)]),
        (2032, 0, 492, 40, [(0, 0, 5, 40)])],
       [(0, 40, 1000, 0), (0, 40, 1000, 0), (0, 40, 1000, 0)]) := by rfl

-- out_of_flow_layout_part_test.cc:1596 FragmentainerBreakTokens
theorem fragmentainerBreakTokens :
    fragmentainerBreakTokensWithSpanner 100 200 200 100 =
      ([(0, 100, 1, false), (1, 200, 1, true)], true, [(2, 250, 1, false)], false) := by rfl

-- out_of_flow_layout_part_test.cc:1657 FragmentainerBreakTokenBeforeSpanner
theorem fragmentainerBreakTokenBeforeSpanner :
    fragmentainerBreakTokensWithSpanner 100 100 200 100 =
      ([(0, 100, 1, true), (1, 200, 1, true)], true, [(2, 250, 1, false)], false) := by rfl

-- out_of_flow_layout_part_test.cc:1716 RelayoutNestedMulticolWithOOF
theorem relayoutNestedMulticolWithOOF :
    ([333, 334, 335].map fun w =>
      (layoutRelWithSingleColAbspos w 0 50 50 10 1 1).head?.map (fun (_, _, _, _, kids) => kids.length)) =
      [some 2, some 2, some 2] := by decide

-- out_of_flow_layout_part_test.cc:1764 EmptyFragmentainersBeforeOOF
theorem emptyFragmentainersBeforeOOF :
    oofFragmentainerBreakTokens 6 100 [(300, 300)] =
      [some 0, some 0, some 0, some 1, some 1, none] := by decide

-- out_of_flow_layout_part_test.cc:1810 MultipleUnfragmentedOOFs
theorem multipleUnfragmentedOOFs :
    oofFragmentainerBreakTokens 3 100 [(0, 10), (100, 10), (200, 10)] =
      [some 0, some 0, none] := by decide

end TestsBlock_ColumnFloatBreak
