# Block lane test manifest

Branch `chromium-layout-tests-block`, pin `36c121be58126ddbb0686965897b8c8ff9b246fb`,
folder `third_party/blink/renderer/core/layout/`. The tests are the specification: rows record
what each test says layout must do. Implementation `.cc/.h` files were opened only where a row
says so.

Classes: `geometry` (sizes/offsets/fragments), `behaviour` (another observable layout rule),
`internal` (C++ plumbing only). Status: `formalized`, `partly formalized`, `blocked` (reason
given), `internal`.

Model modules added by this lane: `BlockFlow.lean` (signed-margin block flow, auto margins,
percent/shrink-to-fit widths, laws), `BlockFragmentation.lean` (fragmentainer slicing), `BlockNode.lean` (child nodes, child iterator, multicol), `BlockScroll.lean` (scrollbar gutter), `OutOfFlowCB.lean` (fixed containing block), `BlockWritingMode.lean` (physical/logical mapping, orthogonal fallback), `BlockLength.lean` (CSS length resolution, contributions, aspect ratio), `ColumnWidth.lean` (multicol column width and count).
Vectors live in `tests/TestsBlock_<File>.lean`. `tests/check_tests.sh` (called from `check.sh`)
checks every row against the pinned sources and the Lean modules.

| file:line | test | class | status | evidence / reason |
|---|---|---|---|---|
| block_layout_algorithm_test.cc:90 | BlockLayoutAlgorithmTest.FixedSize | geometry | formalized | `TestsBlock.FixedSize_size` |
| block_layout_algorithm_test.cc:106 | BlockLayoutAlgorithmTest.Caching | behaviour | blocked | layout-result cache hit/miss on ConstraintSpace comparison not modelled (cache is outside BlockFlow) |
| block_layout_algorithm_test.cc:166 | BlockLayoutAlgorithmTest.MinInlineSizeCaching | behaviour | blocked | layout-result cache not modelled |
| block_layout_algorithm_test.cc:216 | BlockLayoutAlgorithmTest.PercentageBlockSizeQuirkDescendantsCaching | behaviour | blocked | quirks-mode %-descendant tracking and result cache not modelled |
| block_layout_algorithm_test.cc:310 | BlockLayoutAlgorithmTest.LineOffsetCaching | behaviour | blocked | layout-result cache not modelled |
| block_layout_algorithm_test.cc:341 | BlockLayoutAlgorithmTest.LayoutBlockChildren | geometry | formalized | `TestsBlock.LayoutBlockChildren_container`, `TestsBlock.LayoutBlockChildren_children` |
| block_layout_algorithm_test.cc:380 | BlockLayoutAlgorithmTest.LayoutBlockChildrenWithWritingMode | geometry | blocked | needs vertical writing-mode child (orthogonal flow); BlockFlow is horizontal-tb only |
| block_layout_algorithm_test.cc:418 | BlockLayoutAlgorithmTest.CollapsingMarginsCase1WithFloats | geometry | blocked | needs floats (exclusion space); not modelled |
| block_layout_algorithm_test.cc:487 | BlockLayoutAlgorithmTest.CollapsingMarginsCase2WithFloats | geometry | blocked | needs floats between empty blocks; margin arithmetic itself is covered by `collapse_pair` and `ZeroBlockSizeAboveEdge`, but the test's floats are not modelled |
| block_layout_algorithm_test.cc:568 | BlockLayoutAlgorithmTest.CollapsingMarginsCase3 | geometry | formalized | `TestsBlock.CollapsingMarginsCase3_auto`, `TestsBlock.CollapsingMarginsCase3_fixed` |
| block_layout_algorithm_test.cc:618 | BlockLayoutAlgorithmTest.CollapsingMarginsCase4 | geometry | formalized | `TestsBlock.CollapsingMarginsCase4_with_padding`, `TestsBlock.CollapsingMarginsCase4_without_padding`, `BlockFlow.start_edge_top` |
| block_layout_algorithm_test.cc:680 | BlockLayoutAlgorithmTest.CollapsingMarginsCase5 | geometry | blocked | needs vertical-lr container with horizontal-tb child (writing modes) |
| block_layout_algorithm_test.cc:744 | BlockLayoutAlgorithmTest.CollapsingMarginsWithText | geometry | blocked | needs text line layout in `<p>`; expected offsets depend on the text's line box, not modelled by BlockFlow |
| block_layout_algorithm_test.cc:772 | BlockLayoutAlgorithmTest.CollapsingMarginsCase6 | geometry | blocked | needs vertical-rl child (writing modes) |
| block_layout_algorithm_test.cc:815 | BlockLayoutAlgorithmTest.CollapsingMarginsCase7 | geometry | blocked | needs float and `clear` |
| block_layout_algorithm_test.cc:869 | BlockLayoutAlgorithmTest.CollapsingMarginsEmptyBlockWithClearance | geometry | blocked | needs float, `clear`, abspos |
| block_layout_algorithm_test.cc:1029 | BlockLayoutAlgorithmTest.NewFormattingContextAutoMargins | geometry | blocked | needs float and rtl layout opportunity |
| block_layout_algorithm_test.cc:1062 | BlockLayoutAlgorithmTest.BorderAndPadding | geometry | formalized | `TestsBlock.BorderAndPadding_div1`, `TestsBlock.BorderAndPadding_div2_offset` |
| block_layout_algorithm_test.cc:1118 | BlockLayoutAlgorithmTest.PercentageResolutionSize | geometry | formalized | `TestsBlock.PercentageResolutionSize_widths` |
| block_layout_algorithm_test.cc:1145 | BlockLayoutAlgorithmTest.AutoMargin | geometry | formalized | `TestsBlock.AutoMargin_offsets`, `BlockFlow.auto_width_fills` |
| block_layout_algorithm_test.cc:1180 | BlockLayoutAlgorithmTest.PositionFloatInsideEmptyBlocks | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:1275 | BlockLayoutAlgorithmTest.PositionFloatFragments | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:1390 | BlockLayoutAlgorithmTest.PositionFragmentsWithClear | geometry | blocked | needs floats and `clear` |
| block_layout_algorithm_test.cc:1516 | BlockLayoutAlgorithmTest.ComputeMinMaxContent | geometry | formalized | `TestsBlock.ComputeMinMaxContent_sizes` |
| block_layout_algorithm_test.cc:1533 | BlockLayoutAlgorithmTest.ComputeMinMaxContentFloats | geometry | blocked | needs floats in min/max-content |
| block_layout_algorithm_test.cc:1554 | BlockLayoutAlgorithmTest.ComputeMinMaxContentFloatsClearance | geometry | blocked | needs floats and `clear` in min/max-content |
| block_layout_algorithm_test.cc:1575 | BlockLayoutAlgorithmTest.ComputeMinMaxContentNewFormattingContext | geometry | blocked | needs floats beside a flex new-FC child |
| block_layout_algorithm_test.cc:1596 | BlockLayoutAlgorithmTest.ComputeMinMaxContentNewFormattingContextNegativeMargins | geometry | blocked | needs floats beside a flex new-FC child |
| block_layout_algorithm_test.cc:1618 | BlockLayoutAlgorithmTest.ComputeMinMaxContentSingleNewFormattingContextNegativeMargins | geometry | blocked | needs a flex new-FC child (flex lane module); BlockFlow has no negative-margin max-content clamp vector for a flex child |
| block_layout_algorithm_test.cc:1637 | BlockLayoutAlgorithmTest.ShrinkToFit | geometry | formalized | `TestsBlock.ShrinkToFit_width` |
| block_layout_algorithm_test.cc:1660 | BlockLayoutAlgorithmTest.PositionEmptyBlocksInNewBfc | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:1705 | BlockLayoutAlgorithmTest.PositionBlocksWithClearanceAndIntrudingFloats | geometry | blocked | needs floats and `clear` |
| block_layout_algorithm_test.cc:1778 | BlockLayoutAlgorithmTest.NoFragmentation | geometry | formalized | `TestsBlock.NoFragmentation_vectors` |
| block_layout_algorithm_test.cc:1806 | BlockLayoutAlgorithmTest.SimpleFragmentation | geometry | formalized | `TestsBlock.SimpleFragmentation_vectors`, `BlockFlow.fragmentation_conserves_size` |
| block_layout_algorithm_test.cc:1838 | BlockLayoutAlgorithmTest.InnerChildrenFragmentation | geometry | formalized | `TestsBlock.InnerChildrenFragmentation_vectors` |
| block_layout_algorithm_test.cc:1900 | BlockLayoutAlgorithmTest.InnerFormattingContextChildrenFragmentation | geometry | formalized | `TestsBlock.InnerFormattingContextChildrenFragmentation_vectors` |
| block_layout_algorithm_test.cc:1964 | BlockLayoutAlgorithmTest.InnerChildrenFragmentationSmallHeight | geometry | formalized | `TestsBlock.InnerChildrenFragmentationSmallHeight_vectors` |
| block_layout_algorithm_test.cc:2026 | BlockLayoutAlgorithmTest.DISABLED_FloatFragmentationParallelFlows | geometry | blocked | DISABLED_ in the test source; needs floats and fragmentation |
| block_layout_algorithm_test.cc:2104 | BlockLayoutAlgorithmTest.FloatFragmentationOrthogonalFlows | geometry | blocked | needs floats and a vertical-rl float |
| block_layout_algorithm_test.cc:2155 | BlockLayoutAlgorithmTest.DISABLED_FloatFragmentationZeroHeight | geometry | blocked | DISABLED_ in the test source; needs floats and fragmentation |
| block_layout_algorithm_test.cc:2226 | BlockLayoutAlgorithmTest.NewFcBlockWithAdjoiningFloatCollapsesMargins | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:2281 | BlockLayoutAlgorithmTest.NewFcAvoidsFloats | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:2321 | BlockLayoutAlgorithmTest.ZeroBlockSizeAboveEdge | geometry | formalized | `TestsBlock.ZeroBlockSizeAboveEdge_vectors`, `BlockFlow.empty_box_keeps_pos` |
| block_layout_algorithm_test.cc:2357 | BlockLayoutAlgorithmTest.NewFcFirstChildIsZeroBlockSize | geometry | formalized | `TestsBlock.NewFcFirstChildIsZeroBlockSize_vectors`, `BlockFlow.collapse_pair` |
| block_layout_algorithm_test.cc:2400 | BlockLayoutAlgorithmTest.RootFragmentOffsetInsideLegacy | internal | internal | assertion is commented out (TODO crbug.com/781241); only checks a fragment exists |
| block_layout_algorithm_test.cc:2420 | BlockLayoutAlgorithmTest.LayoutRubyTextCrash | internal | internal | crash regression, no expectation |
| block_layout_algorithm_test.cc:2428 | BlockLayoutAlgorithmTest.HandleTextControlPlaceholderCrash | internal | internal | crash regression, no expectation |
| block_layout_algorithm_test.cc:2447 | BlockLayoutAlgorithmTest.ComputeInitialBlockStartAnnotationSpace | geometry | blocked | needs ruby annotation space (inline/ruby, Ahem font); not modelled |
| block_layout_algorithm_test.cc:2599 | BlockLayoutAlgorithmTest.PreviousSiblingBlockEndAnnotationSpace | geometry | blocked | needs ruby annotation space (inline/ruby, Ahem font); not modelled |
| block_child_iterator_test.cc:43 | BlockChildIteratorTest.NullFirstChild | behaviour | formalized | `TestsBlock.NullFirstChild_vectors` |
| block_child_iterator_test.cc:48 | BlockChildIteratorTest.NoBreakToken | behaviour | formalized | `TestsBlock.NoBreakToken_vectors` |
| block_child_iterator_test.cc:66 | BlockChildIteratorTest.BreakTokens | behaviour | formalized | `TestsBlock.BreakTokens_vectors`, `BlockNode.iterate_mem` |
| block_child_iterator_test.cc:140 | BlockChildIteratorTest.SeenAllChildren | behaviour | formalized | `TestsBlock.SeenAllChildren_vectors` |
| block_child_iterator_test.cc:177 | BlockChildIteratorTest.DeleteNodeWhileIteration | behaviour | formalized | `TestsBlock.DeleteNodeWhileIteration_vectors` |
| block_node_test.cc:16 | BlockNodeForTest.IsFloatingForOutOfFlowFloating | behaviour | formalized | `TestsBlock.IsFloatingForOutOfFlowFloating_vectors` |
| block_node_test.cc:31 | BlockNodeForTest.ChildInlineAndBlock | behaviour | formalized | `TestsBlock.ChildInlineAndBlock_vectors` |
| block_node_test.cc:45 | BlockNodeForTest.ChildBlockAndInline | behaviour | formalized | `TestsBlock.ChildBlockAndInline_vectors` |
| block_node_test.cc:59 | BlockNodeForTest.ChildFloatBeforeBlock | behaviour | formalized | `TestsBlock.ChildFloatBeforeBlock_vectors` |
| block_node_test.cc:76 | BlockNodeForTest.ChildFloatBeforeInline | behaviour | formalized | `TestsBlock.ChildFloatBeforeInline_vectors` |
| block_node_test.cc:91 | BlockNodeForTest.ChildFloatAfterInline | behaviour | formalized | `TestsBlock.ChildFloatAfterInline_vectors` |
| block_node_test.cc:106 | BlockNodeForTest.ChildFloatOnly | behaviour | formalized | `TestsBlock.ChildFloatOnly_vectors` |
| block_node_test.cc:121 | BlockNodeForTest.ChildFloatWithSpaces | behaviour | formalized | `TestsBlock.ChildFloatWithSpaces_vectors` |
| block_node_test.cc:138 | BlockNodeForTest.ChildOofBeforeInline | behaviour | formalized | `TestsBlock.ChildOofBeforeInline_vectors` |
| block_node_test.cc:153 | BlockNodeForTest.ChildOofAfterInline | behaviour | formalized | `TestsBlock.ChildOofAfterInline_vectors` |
| block_node_test.cc:169 | BlockNodeForTest.MinContentForControls | geometry | blocked | needs form-control intrinsic sizes (select, file input, marquee) as flex items; not modelled |
| layout_block_flow_test.cc:16 | LayoutBlockFlowTest.RecalcInlineChildrenScrollableOverflow | internal | internal | crash/DCHECK regression (passes if no DCHECK failure in ink_overflow.cc) |
| layout_block_flow_test.cc:38 | LayoutBlockFlowTest.IsInsideMulticol | behaviour | formalized | `TestsBlock.IsInsideMulticol_vectors` |
| layout_block_flow_test.cc:109 | LayoutBlockFlowTest.AnonymousContainer | behaviour | formalized | `TestsBlock.AnonymousContainer_vectors` |
| layout_block_flow_test.cc:165 | LayoutBlockFlowTest.NoAnonymousContainer | behaviour | formalized | `TestsBlock.NoAnonymousContainer_vectors` |
| layout_block_test.cc:20 | LayoutBlockTest.LayoutNameCalledWithNullStyle | internal | internal | checks DecoratedName() string on an unstyled object |
| layout_block_test.cc:28 | LayoutBlockTest.WidthAvailableToChildrenChanged | geometry | formalized | `TestsBlock.WidthAvailableToChildrenChanged_vectors`, `TestsBlock.scroller_content_height` (scrollbar width kept symbolic: test compares against ComputeScrollbars) |
| layout_block_test.cc:61 | LayoutBlockTest.OverflowWithTransformAndPerspective | geometry | blocked | expects scrollable overflow 187.625 under rotateY(-45deg) with perspective; 3D transforms are not modelled |
| layout_block_test.cc:73 | LayoutBlockTest.NestedInlineVisualOverflow | geometry | blocked | expects visual overflow rect of an img with negative margin in a zero-size box (inline replaced layout); not modelled |
| layout_block_test.cc:86 | LayoutBlockTest.NestedInlineVisualOverflowVerticalRL | geometry | blocked | same as NestedInlineVisualOverflow in vertical-rl; writing modes not modelled |
| layout_block_test.cc:101 | LayoutBlockTest.ContainmentStyleChange | behaviour | formalized | `TestsBlock.ContainmentStyleChange_vectors` |
| constraint_space_builder_test.cc:17 | ConstraintSpaceBuilderTest.AvailableSizeFromHorizontalICB | geometry | formalized | `TestsBlock.AvailableSizeFromHorizontalICB_vectors`, `BlockWritingMode.indefinite_inline_falls_back` |
| constraint_space_builder_test.cc:49 | ConstraintSpaceBuilderTest.AvailableSizeFromVerticalICB | geometry | formalized | `TestsBlock.AvailableSizeFromVerticalICB_vectors`, `BlockWritingMode.indefinite_inline_falls_back` |
| length_utils_test.cc:120 | LengthUtilsTest.TestResolveInlineLength | geometry | formalized | `TestsBlock.TestResolveInlineLength_vectors` |
| length_utils_test.cc:144 | LengthUtilsTest.TestIndefiniteResolveInlineLength | geometry | formalized | `TestsBlock.TestIndefiniteResolveInlineLength_vectors` |
| length_utils_test.cc:155 | LengthUtilsTest.TestResolveBlockLength | geometry | formalized | `TestsBlock.TestResolveBlockLength_vectors` |
| length_utils_test.cc:161 | LengthUtilsTestWithNode.TestComputeContentContribution | geometry | formalized | `TestsBlock.TestComputeContentContribution_vectors`, `BlockLength.clampSize_ge_min` |
| length_utils_test.cc:270 | LengthUtilsTestWithNode.TestComputeInlineSizeForFragment | geometry | formalized | `TestsBlock.TestComputeInlineSizeForFragment_vectors` |
| length_utils_test.cc:355 | LengthUtilsTestWithNode.TestComputeBlockSizeForFragment | geometry | formalized | `TestsBlock.TestComputeBlockSizeForFragment_vectors` |
| length_utils_test.cc:443 | LengthUtilsTestWithNode.TestIndefinitePercentages | geometry | formalized | `TestsBlock.TestIndefinitePercentages_vectors` |
| length_utils_test.cc:460 | LengthUtilsTestWithNode.ComputeReplacedSizeSvgNoScaling | internal | internal | crash/DCHECK regression in BlockNode::FinishLayout with huge margin-left on svg |
| length_utils_test.cc:475 | LengthUtilsTest.TestMargins | geometry | formalized | `TestsBlock.TestMargins_vectors` |
| length_utils_test.cc:493 | LengthUtilsTest.TestBorders | geometry | formalized | `TestsBlock.TestBorders_vectors`, `BlockWritingMode.toPhysical_toLogical` |
| length_utils_test.cc:514 | LengthUtilsTest.TestPadding | geometry | formalized | `TestsBlock.TestPadding_vectors` |
| length_utils_test.cc:534 | LengthUtilsTest.TestAutoMargins | geometry | formalized | `TestsBlock.TestAutoMargins_vectors` |
| length_utils_test.cc:612 | LengthUtilsTest.TestColumnWidthAndCount | geometry | formalized | `TestsBlock.TestColumnWidthAndCount_vectors`, `ColumnWidth.columns_fit` |
| length_utils_test.cc:657 | LengthUtilsTest.AspectRatio | geometry | formalized | `TestsBlock.AspectRatio_vectors`, `BlockLength.inlineFromAspectRatio_le_max`, `BlockLength.inlineFromAspectRatio_one` |

## Laws proved

- `BlockFlow.collapse_pair`: two adjoining margins collapse to max-positive plus min-negative (CSS 2.1 8.3.1).
- `BlockFlow.empty_box_keeps_pos`: an empty box does not advance the flow position.
- `BlockFlow.start_edge_top`: a non-empty box with a start edge sits at its collapsed top margin.
- `BlockFlow.auto_width_fills`: auto-width box with definite margins fills the containing block.
- `BlockFlow.fragmentation_conserves_size`: fragment sizes sum to the box's block size.
- `BlockNode.iterate_mem`: the child iterator only returns real children.
- `BlockWritingMode.indefinite_inline_falls_back`: indefinite available inline size falls back to orthogonal fallback size.
- `BlockWritingMode.toPhysical_toLogical`: physical to logical edge mapping is an isomorphism.
- `BlockLength.clampSize_ge_min`: clamping by min/max never returns less than the minimum.
- `BlockLength.inlineFromAspectRatio_le_max`: aspect ratio inline size saturates at LayoutUnit::Max().
- `BlockLength.inlineFromAspectRatio_one`: 1:1 aspect ratio preserves block size below saturation.
- `ColumnWidth.columns_fit`: multicol columns plus gaps fit the available inline size.

## Merge notes

- `BlockFlow.lean` extends `MarginStrut` from `LayoutTypes.lean` with `MarginStrut.ofInt` /
  `MarginStrut.signedSum` (namespace `ChromiumLayout.MarginStrut`) instead of editing the shared file.
- `check.sh` gained one block (call to `tests/check_tests.sh`) before the final line; the other lane
  may add its own call next to it.
