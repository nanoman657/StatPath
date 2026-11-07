# Block lane test manifest

Branch `chromium-layout-tests-block`, pin `36c121be58126ddbb0686965897b8c8ff9b246fb`,
folder `third_party/blink/renderer/core/layout/`. The tests are the specification: rows record
what each test says layout must do. Implementation `.cc/.h` files were opened only where a row
says so.

## Formalization rule

A row is marked `formalized` only if ALL of the following hold:
- **(a)** The test's input (its HTML/CSS, viewport and constraints) is written as a value of a model input type, e.g. a box tree (`BF`) or item list (`List Item`).
- **(b)** A **GENERAL** model function, one that works on any input of that type and does not mention any test, computes the output from that input.
- **(c)** The theorem compares that computed output with the test's `EXPECT_*` values written as literals on the right-hand side.

No model function may branch on test names, test ids, or an enum invented to stand for one test's case. A function whose body is a table of a test's expected numbers is a lookup, not a model.

Classes: `geometry` (sizes/offsets/fragments), `behaviour` (another observable layout rule),
`internal` (C++ plumbing only). Status: `formalized`, `partly formalized`, `blocked` (reason
given), `internal`.

Model modules added by this lane: `BlockFlow.lean` (signed-margin block flow, auto margins,
percent/shrink-to-fit widths, laws), `BlockFragmentation.lean` (fragmentainer slicing), `BlockNode.lean` (child nodes, child iterator), `BlockScroll.lean` (scrollbar gutter), `BlockWritingMode.lean` (physical/logical mapping), `BlockLength.lean` (CSS length resolution, contributions, aspect ratio), `ColumnWidth.lean` (multicol column width and count), `BlockRelative.lean` (relative positioning insets), `BlockAbsolute.lean` (out-of-flow positioning constraints).
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
| layout_block_flow_test.cc:38 | LayoutBlockFlowTest.IsInsideMulticol | internal | internal | checks C++ LayoutObject::IsInsideMulticol query |
| layout_block_flow_test.cc:109 | LayoutBlockFlowTest.AnonymousContainer | internal | internal | checks C++ anonymous LayoutBlockFlow wrapper insertion for inline children in multicol |
| layout_block_flow_test.cc:165 | LayoutBlockFlowTest.NoAnonymousContainer | internal | internal | checks C++ anonymous LayoutBlockFlow wrapper insertion for inline children in multicol |
| layout_block_test.cc:20 | LayoutBlockTest.LayoutNameCalledWithNullStyle | internal | internal | checks DecoratedName() string on an unstyled object |
| layout_block_test.cc:28 | LayoutBlockTest.WidthAvailableToChildrenChanged | geometry | formalized | `TestsBlock.WidthAvailableToChildrenChanged_vectors`, `TestsBlock.scroller_content_height` (scrollbar width kept symbolic: test compares against ComputeScrollbars) |
| layout_block_test.cc:61 | LayoutBlockTest.OverflowWithTransformAndPerspective | geometry | blocked | expects scrollable overflow 187.625 under rotateY(-45deg) with perspective; 3D transforms are not modelled |
| layout_block_test.cc:73 | LayoutBlockTest.NestedInlineVisualOverflow | geometry | blocked | expects visual overflow rect of an img with negative margin in a zero-size box (inline replaced layout); not modelled |
| layout_block_test.cc:86 | LayoutBlockTest.NestedInlineVisualOverflowVerticalRL | geometry | blocked | same as NestedInlineVisualOverflow in vertical-rl; writing modes not modelled |
| layout_block_test.cc:101 | LayoutBlockTest.ContainmentStyleChange | behaviour | blocked | model lacks layout containment containing block resolution on box trees |
| constraint_space_builder_test.cc:17 | ConstraintSpaceBuilderTest.AvailableSizeFromHorizontalICB | internal | internal | checks C++ ConstraintSpaceBuilder orthogonal fallback plumbing |
| constraint_space_builder_test.cc:49 | ConstraintSpaceBuilderTest.AvailableSizeFromVerticalICB | internal | internal | checks C++ ConstraintSpaceBuilder orthogonal fallback plumbing |
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
| min_max_size_test.cc:13 | MinMaxSizesTest.ShrinkToFit | geometry | formalized | `TestsBlock.ShrinkToFit_vectors`, `BlockFlow.shrinkToFit_bounds` |
| min_max_sizes_cache_test.cc:14 | MinMaxSizesCacheTest.Eviction | internal | internal | checks C++ MinMaxSizesCache LRU eviction plumbing |
| physical_fragment_test.cc:84 | StickyFragmentPropagationTest.StickyAxisEnabled | behaviour | blocked | model lacks single-axis sticky scroll container fragment propagation |
| physical_fragment_test.cc:113 | StickyFragmentPropagationTest.StickyAxisDisabled | behaviour | blocked | model lacks single-axis sticky scroll container fragment propagation |
| physical_fragment_test.cc:134 | PhysicalFragmentTest.DumpFragmentTreeBasic | geometry | formalized | `TestsBlock.DumpFragmentTreeBasic_vectors` |
| physical_fragment_test.cc:149 | PhysicalFragmentTest.DumpFragmentTreeWithAbspos | geometry | blocked | model lacks out-of-flow fragment positioning in layoutRoot |
| physical_fragment_test.cc:165 | PhysicalFragmentTest.DumpFragmentTreeWithAbsposInRelpos | geometry | blocked | model lacks out-of-flow fragment positioning inside relative container |
| physical_fragment_test.cc:184 | PhysicalFragmentTest.DumpFragmentTreeWithGrid | geometry | blocked | needs grid layout algorithm (display: grid); not modelled |
| physical_fragment_test.cc:213 | PhysicalFragmentTest.DumpFragmentTreeWithTargetInsideColumn | geometry | blocked | model lacks multicolumn target fragment tree dump |
| physical_fragment_test.cc:243 | PhysicalFragmentTest.DumpFragmentTreeWithRepeatedContent | geometry | blocked | needs table layout with repeated header group across multicol columns; not modelled |
| physical_fragment_test.cc:295 | PhysicalFragmentTest.CrashInScrollableOverflowCalculator | internal | internal | crash regression in ScrollableOverflowCalculator under fullscreen menulist keyframes |
| physical_box_fragment_test.cc:29 | PhysicalBoxFragmentTest.FloatingDescendantsInlineChlidren | behaviour | blocked | model lacks floating descendants propagation on physical fragments |
| physical_box_fragment_test.cc:46 | PhysicalBoxFragmentTest.FloatingDescendantsBlockChlidren | behaviour | blocked | model lacks floating descendants propagation on physical fragments |
| physical_box_fragment_test.cc:65 | PhysicalBoxFragmentTest.FloatingDescendantsInlineBlock | behaviour | blocked | model lacks floating descendants propagation on physical fragments |
| physical_box_fragment_test.cc:83 | PhysicalBoxFragmentTest.FloatingDescendantsBlockFormattingContext | behaviour | blocked | model lacks floating descendants propagation on physical fragments |
| physical_box_fragment_test.cc:104 | PhysicalBoxFragmentTest.ReplacedBlock | internal | internal | checks C++ Type(), IsAtomicInline() and GetBoxType() flags on replaced block fragment |
| physical_box_fragment_test.cc:115 | PhysicalBoxFragmentTest.IsFragmentationContextRoot | behaviour | blocked | model lacks fragmentation context root query on physical fragments |
| physical_box_fragment_test.cc:135 | PhysicalBoxFragmentTest.IsFragmentationContextRootNested | behaviour | blocked | model lacks fragmentation context root query on physical fragments |
| physical_box_fragment_test.cc:169 | PhysicalBoxFragmentTest.IsFragmentationContextRootFieldset | behaviour | blocked | model lacks fragmentation context root query on physical fragments |
| physical_box_fragment_test.cc:201 | PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStart | behaviour | blocked | model lacks descendant overflow above block-start query on physical fragments |
| physical_box_fragment_test.cc:216 | PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStartBlockInInline | behaviour | blocked | model lacks descendant overflow above block-start query on physical fragments |
| physical_box_fragment_test.cc:233 | PhysicalBoxFragmentTest.OverflowClipMarginVisualBox | geometry | blocked | model lacks visual box overflow-clip-margin calculation |
| physical_box_fragment_test.cc:294 | PhysicalBoxFragmentTest.CloneWithPostLayoutFragments | internal | internal | checks CloneWithPostLayoutFragments preserves C++ frame set layout data pointer |
| relative_utils_test.cc:49 | RelativeUtilsTest.HorizontalTB | geometry | formalized | `TestsBlock.HorizontalTB_vectors`, `BlockRelative.opposing_sum_zero` |
| absolute_utils_test.cc:150 | AbsoluteUtilsTest.Horizontal | geometry | formalized | `TestsBlock.Horizontal_vectors` |
| absolute_utils_test.cc:315 | AbsoluteUtilsTest.Vertical | geometry | formalized | `TestsBlock.Vertical_vectors` |
| absolute_utils_test.cc:436 | AbsoluteUtilsTest.CenterStaticPosition | geometry | blocked | model lacks static position alignment for out-of-flow |
| absolute_utils_test.cc:474 | AbsoluteUtilsTest.MinMax | geometry | blocked | model lacks min/max size clamping in out-of-flow dimension solver |
| out_of_flow_layout_part_test.cc:46 | OutOfFlowLayoutPartTest.FixedInsideAbs | geometry | blocked | model lacks out-of-flow fragment positioning inside positioned ancestor |
| out_of_flow_layout_part_test.cc:103 | OutOfFlowLayoutPartTest.PositionedInMulticol | geometry | blocked | needs out-of-flow fragmentation in multicolumn with column spanners; not modelled |
| out_of_flow_layout_part_test.cc:149 | OutOfFlowLayoutPartTest.SimplePositionedFragmentation | geometry | blocked | needs out-of-flow fragmentation in multicolumn with column spanners; not modelled |
| out_of_flow_layout_part_test.cc:191 | OutOfFlowLayoutPartTest.PositionedFragmentationWithOverflow | geometry | blocked | needs out-of-flow fragmentation in multicolumn with column spanners; not modelled |
| out_of_flow_layout_part_test.cc:238 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumns | geometry | blocked | needs out-of-flow fragmentation in multicolumn with column spanners; not modelled |
| out_of_flow_layout_part_test.cc:279 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewEmptyColumns | geometry | blocked | needs out-of-flow fragmentation in multicolumn with column spanners; not modelled |
| out_of_flow_layout_part_test.cc:320 | OutOfFlowLayoutPartTest.BreakInsideAvoid | behaviour | blocked | needs break-inside: avoid on out-of-flow node in multicol; not modelled |
| out_of_flow_layout_part_test.cc:359 | OutOfFlowLayoutPartTest.BreakBeforeColumn | behaviour | blocked | needs break-before: column on out-of-flow node in multicol; not modelled |
| out_of_flow_layout_part_test.cc:398 | OutOfFlowLayoutPartTest.BreakAfterColumn | behaviour | blocked | needs break-after: column on out-of-flow node in multicol; not modelled |
| out_of_flow_layout_part_test.cc:437 | OutOfFlowLayoutPartTest.ChildBreakInsideAvoid | behaviour | blocked | needs break-inside: avoid on descendant in multicol; not modelled |
| out_of_flow_layout_part_test.cc:479 | OutOfFlowLayoutPartTest.ChildBreakBeforeAvoid | behaviour | blocked | needs break-before: avoid on descendant in multicol; not modelled |
| out_of_flow_layout_part_test.cc:523 | OutOfFlowLayoutPartTest.ChildBreakAfterAvoid | behaviour | blocked | needs break-after: avoid on descendant in multicol; not modelled |
| out_of_flow_layout_part_test.cc:568 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNegativeTopPropertyAndNewEmptyColumn | geometry | blocked | needs out-of-flow fragmentation in multicolumn with negative top; not modelled |
| out_of_flow_layout_part_test.cc:610 | OutOfFlowLayoutPartTest.PositionedFragmentationWithBottomProperty | geometry | blocked | needs out-of-flow fragmentation in multicolumn with bottom property; not modelled |
| out_of_flow_layout_part_test.cc:649 | OutOfFlowLayoutPartTest.PositionedFragmentationInFlowWithAddedColumns | geometry | blocked | needs out-of-flow fragmentation in multicolumn with added columns; not modelled |
| out_of_flow_layout_part_test.cc:694 | OutOfFlowLayoutPartTest.PositionedFragmentationAndColumnSpanners | geometry | blocked | needs column spanners (column-span: all) with out-of-flow fragmentation; not modelled |
| out_of_flow_layout_part_test.cc:745 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNestedSpanner | geometry | blocked | needs nested column spanners with out-of-flow fragmentation; not modelled |
| out_of_flow_layout_part_test.cc:787 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNestedSpanners | geometry | blocked | needs nested column spanners with out-of-flow fragmentation; not modelled |
| out_of_flow_layout_part_test.cc:842 | OutOfFlowLayoutPartTest.AbsposInSpanner | geometry | blocked | needs abspos inside column spanner; not modelled |
| out_of_flow_layout_part_test.cc:895 | OutOfFlowLayoutPartTest.AbsposInSpannerStaticPos | geometry | blocked | needs abspos inside column spanner static position; not modelled |
| out_of_flow_layout_part_test.cc:945 | OutOfFlowLayoutPartTest.SpannerInAbspos | geometry | blocked | needs column spanner inside abspos container; not modelled |
| out_of_flow_layout_part_test.cc:987 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumnsAndSpanners | geometry | blocked | needs column spanner with abspos fragmentation and new columns; not modelled |
| out_of_flow_layout_part_test.cc:1038 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumnsAfterSpanner | geometry | blocked | needs column spanner with abspos fragmentation and fixed bottom; not modelled |
| out_of_flow_layout_part_test.cc:1083 | OutOfFlowLayoutPartTest.AbsposFragWithSpannerAndNewColumnsAutoHeight | geometry | blocked | needs column spanner with abspos fragmentation and auto height; not modelled |
| out_of_flow_layout_part_test.cc:1128 | OutOfFlowLayoutPartTest.AbsposFragWithSpannerAndNewEmptyColumns | geometry | blocked | needs column spanner with abspos fragmentation and new empty columns; not modelled |
| out_of_flow_layout_part_test.cc:1175 | OutOfFlowLayoutPartTest.AbsposFragmentationPctResolution | geometry | blocked | needs percentage resolution in multicol out-of-flow fragmentation; not modelled |
| out_of_flow_layout_part_test.cc:1218 | OutOfFlowLayoutPartTest.AbsposFragmentationPctResolutionWithOverflow | geometry | blocked | needs percentage resolution with overflow in multicol out-of-flow; not modelled |
| out_of_flow_layout_part_test.cc:1278 | OutOfFlowLayoutPartTest.SimpleAbsposNestedFragmentation | geometry | blocked | needs nested multicol out-of-flow fragmentation; not modelled |
| out_of_flow_layout_part_test.cc:1322 | OutOfFlowLayoutPartTest.AbsposNestedFragmentationNewColumns | geometry | blocked | needs nested multicol out-of-flow fragmentation with new columns; not modelled |
| out_of_flow_layout_part_test.cc:1375 | OutOfFlowLayoutPartTest.AbsposNestedFragmentationNewEmptyColumns | geometry | blocked | needs nested multicol out-of-flow fragmentation with new empty columns; not modelled |
| out_of_flow_layout_part_test.cc:1431 | OutOfFlowLayoutPartTest.PositionedFragmentationWithBottomPropertyAndHeightAuto | geometry | blocked | needs out-of-flow fragmentation with bottom property and height auto; not modelled |
| out_of_flow_layout_part_test.cc:1479 | OutOfFlowLayoutPartTest.AbsposFragWithInlineCBAndSpanner | geometry | blocked | needs inline containing block and column spanner in multicol; not modelled |
| out_of_flow_layout_part_test.cc:1549 | OutOfFlowLayoutPartTest.PositionedObjectsInMulticol | behaviour | blocked | needs multicolumn positioned objects tracking; not modelled |
| out_of_flow_layout_part_test.cc:1572 | OutOfFlowLayoutPartTest.PositionedObjectsInMulticolWithInline | behaviour | blocked | needs multicolumn positioned objects with inline; not modelled |
| out_of_flow_layout_part_test.cc:1596 | OutOfFlowLayoutPartTest.FragmentainerBreakTokens | behaviour | blocked | needs fragmentainer break token sequence tracking with column spanner; not modelled |
| out_of_flow_layout_part_test.cc:1657 | OutOfFlowLayoutPartTest.FragmentainerBreakTokenBeforeSpanner | behaviour | blocked | needs fragmentainer break token before spanner; not modelled |
| out_of_flow_layout_part_test.cc:1716 | OutOfFlowLayoutPartTest.RelayoutNestedMulticolWithOOF | behaviour | blocked | needs nested multicol relayout cache with out-of-flow; not modelled |
| out_of_flow_layout_part_test.cc:1764 | OutOfFlowLayoutPartTest.EmptyFragmentainersBeforeOOF | behaviour | blocked | needs empty fragmentainers break token tracking before out-of-flow; not modelled |
| out_of_flow_layout_part_test.cc:1810 | OutOfFlowLayoutPartTest.MultipleUnfragmentedOOFs | behaviour | blocked | needs unfragmented out-of-flow break token propagation in multicol; not modelled |

| column_layout_algorithm_test.cc:41 | ColumnLayoutAlgorithmTest.EmptyEditable | geometry | blocked | needs contenteditable minimum height / line-height model in multicolumn |
| column_layout_algorithm_test.cc:56 | ColumnLayoutAlgorithmTest.EmptyEditableWithFloat | geometry | blocked | needs contenteditable minimum height / line-height model in multicolumn |
| column_layout_algorithm_test.cc:73 | ColumnLayoutAlgorithmTest.EmptyMulticol | geometry | formalized | `TestsBlock.EmptyMulticol_vectors`, `ColumnLayout.actualColumnCount_at_least_one` |
| column_layout_algorithm_test.cc:111 | ColumnLayoutAlgorithmTest.EmptyBlock | geometry | formalized | `TestsBlock.EmptyBlock_vectors` |
| column_layout_algorithm_test.cc:160 | ColumnLayoutAlgorithmTest.BlockInOneColumn | geometry | formalized | `TestsBlock.BlockInOneColumn_vectors` |
| column_layout_algorithm_test.cc:210 | ColumnLayoutAlgorithmTest.ZeroHeightBlockAtFragmentainerBoundary | geometry | formalized | `TestsBlock.ZeroHeightBlockAtFragmentainerBoundary_vectors` |
| column_layout_algorithm_test.cc:242 | ColumnLayoutAlgorithmTest.BlockInTwoColumns | geometry | formalized | `TestsBlock.BlockInTwoColumns_vectors` |
| column_layout_algorithm_test.cc:272 | ColumnLayoutAlgorithmTest.BlockInThreeColumns | geometry | formalized | `TestsBlock.BlockInThreeColumns_vectors`, `ColumnLayout.columns_non_overlapping` |
| column_layout_algorithm_test.cc:304 | ColumnLayoutAlgorithmTest.ActualColumnCountGreaterThanSpecified | geometry | formalized | `TestsBlock.ActualColumnCountGreaterThanSpecified_vectors` |
| column_layout_algorithm_test.cc:336 | ColumnLayoutAlgorithmTest.TwoBlocksInTwoColumns | geometry | formalized | `TestsBlock.TwoBlocksInTwoColumns_vectors` |
| column_layout_algorithm_test.cc:368 | ColumnLayoutAlgorithmTest.ZeroHeight | geometry | formalized | `TestsBlock.ZeroHeight_vectors` |
| column_layout_algorithm_test.cc:393 | ColumnLayoutAlgorithmTest.ZeroHeightWithContent | geometry | formalized | `TestsBlock.ZeroHeightWithContent_vectors` |
| column_layout_algorithm_test.cc:429 | ColumnLayoutAlgorithmTest.OverflowedBlock | geometry | blocked | needs nested block overflow fragmentation in multicolumn |
| column_layout_algorithm_test.cc:467 | ColumnLayoutAlgorithmTest.OverflowedBlock2 | geometry | blocked | needs nested block overflow fragmentation in multicolumn |
| column_layout_algorithm_test.cc:515 | ColumnLayoutAlgorithmTest.OverflowedBlock3 | geometry | blocked | needs nested block overflow fragmentation in multicolumn |
| column_layout_algorithm_test.cc:554 | ColumnLayoutAlgorithmTest.UnusedSpaceInBlock | geometry | blocked | needs nested block with grandchild fragmentation in multicolumn |
| column_layout_algorithm_test.cc:589 | ColumnLayoutAlgorithmTest.FloatInOneColumn | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:617 | ColumnLayoutAlgorithmTest.TwoFloatsInOneColumn | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:647 | ColumnLayoutAlgorithmTest.TwoFloatsInTwoColumns | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:680 | ColumnLayoutAlgorithmTest.FloatWithForcedBreak | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:717 | ColumnLayoutAlgorithmTest.FloatWithMargin | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:747 | ColumnLayoutAlgorithmTest.FloatWithMarginBelowFloat | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:779 | ColumnLayoutAlgorithmTest.FloatWithLastResortBreak | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:818 | ColumnLayoutAlgorithmTest.FloatWithAvoidBreak | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:855 | ColumnLayoutAlgorithmTest.FloatWithMarginAndAvoidBreak | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:893 | ColumnLayoutAlgorithmTest.UnbreakableFloatBeforeBreakable | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:939 | ColumnLayoutAlgorithmTest.BlockWithTopMarginInThreeColumns | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:973 | ColumnLayoutAlgorithmTest.BlockStartAtColumnBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:1004 | ColumnLayoutAlgorithmTest.NestedBlockAfterBlock | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:1042 | ColumnLayoutAlgorithmTest.BreakInsideAvoid | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1073 | ColumnLayoutAlgorithmTest.BreakInsideAvoidColumn | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1104 | ColumnLayoutAlgorithmTest.BreakInsideAvoidPage | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1137 | ColumnLayoutAlgorithmTest.BreakInsideAvoidTallBlock | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1174 | ColumnLayoutAlgorithmTest.NestedBreakInsideAvoid | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1215 | ColumnLayoutAlgorithmTest.NestedBreakInsideAvoidTall | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1258 | ColumnLayoutAlgorithmTest.BreakInsideAvoidAtColumnBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:1292 | ColumnLayoutAlgorithmTest.MarginTopPastEndOfFragmentainer | geometry | blocked | needs margin truncation at fragmentainer boundary in multicolumn |
| column_layout_algorithm_test.cc:1327 | ColumnLayoutAlgorithmTest.MarginBottomPastEndOfFragmentainer | geometry | blocked | needs margin truncation at fragmentainer boundary in multicolumn |
| column_layout_algorithm_test.cc:1362 | ColumnLayoutAlgorithmTest.MarginTopAtEndOfFragmentainer | geometry | blocked | needs margin truncation at fragmentainer boundary in multicolumn |
| column_layout_algorithm_test.cc:1396 | ColumnLayoutAlgorithmTest.MarginBottomAtEndOfFragmentainer | geometry | blocked | needs margin truncation at fragmentainer boundary in multicolumn |
| column_layout_algorithm_test.cc:1430 | ColumnLayoutAlgorithmTest.LinesInMulticolExtraSpace | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1470 | ColumnLayoutAlgorithmTest.LinesInMulticolExactFit | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1510 | ColumnLayoutAlgorithmTest.LinesInMulticolChildExtraSpace | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1552 | ColumnLayoutAlgorithmTest.LinesInMulticolChildExactFit | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1594 | ColumnLayoutAlgorithmTest.LinesInMulticolChildNoSpaceForFirst | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1637 | ColumnLayoutAlgorithmTest.LinesInMulticolChildInsufficientSpaceForFirst | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1681 | ColumnLayoutAlgorithmTest.LineAtColumnBoundaryInFirstBlock | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:1725 | ColumnLayoutAlgorithmTest.LinesAndFloatsMulticol | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1774 | ColumnLayoutAlgorithmTest.FloatBelowLastLineInColumn | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1820 | ColumnLayoutAlgorithmTest.Orphans | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:1861 | ColumnLayoutAlgorithmTest.OrphansUnsatisfiable | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:1905 | ColumnLayoutAlgorithmTest.Widows | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:1951 | ColumnLayoutAlgorithmTest.WidowsUnsatisfiable | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:2017 | ColumnLayoutAlgorithmTest.OrphansAndUnsatisfiableWidows | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:2057 | ColumnLayoutAlgorithmTest.UnsatisfiableOrphansAndWidows | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:2097 | ColumnLayoutAlgorithmTest.WidowsAndAbspos | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:2147 | ColumnLayoutAlgorithmTest.BreakBetweenLinesNotBefore | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2194 | ColumnLayoutAlgorithmTest.BreakBetweenLinesNotBefore2 | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2236 | ColumnLayoutAlgorithmTest.BreakBetweenLinesNotBefore3 | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2278 | ColumnLayoutAlgorithmTest.FloatInBlockMovedByOrphans | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2318 | ColumnLayoutAlgorithmTest.FloatMovedWithWidows | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2361 | ColumnLayoutAlgorithmTest.BorderAndPadding | geometry | blocked | needs container border and padding fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2391 | ColumnLayoutAlgorithmTest.BreakInsideWithBorder | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:2427 | ColumnLayoutAlgorithmTest.ForcedBreaks | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:2480 | ColumnLayoutAlgorithmTest.ForcedBreakInSecondChild | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:2517 | ColumnLayoutAlgorithmTest.ForcedAndUnforcedBreaksAtSameBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:2568 | ColumnLayoutAlgorithmTest.ResumeInsideFormattingContextRoot | geometry | blocked | needs new formatting context root fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2602 | ColumnLayoutAlgorithmTest.NewFcAtColumnBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:2633 | ColumnLayoutAlgorithmTest.NewFcWithMargin | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:2665 | ColumnLayoutAlgorithmTest.NewFcBelowFloat | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:2697 | ColumnLayoutAlgorithmTest.NewFcWithMarginPastColumnBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:2728 | ColumnLayoutAlgorithmTest.MinMax | geometry | blocked | needs multicolumn min/max-content intrinsic size resolution |
| column_layout_algorithm_test.cc:2799 | ColumnLayoutAlgorithmTest.ColumnBalancing | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:2829 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightExactMatch | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:2860 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightLessContent | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:2891 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightOverflowingContent | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:2927 | ColumnLayoutAlgorithmTest.ColumnBalancingMinHeight | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:2960 | ColumnLayoutAlgorithmTest.ColumnBalancingMaxHeight | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:2993 | ColumnLayoutAlgorithmTest.ColumnBalancingMinHeightLargerThanMaxHeight | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3027 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightMinHeight | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3063 | ColumnLayoutAlgorithmTest.ColumnBalancing100By3 | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3086 | ColumnLayoutAlgorithmTest.ColumnBalancingEmpty | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3109 | ColumnLayoutAlgorithmTest.ColumnBalancingEmptyBlock | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3135 | ColumnLayoutAlgorithmTest.ColumnBalancingSingleLine | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3163 | ColumnLayoutAlgorithmTest.ColumnBalancingSingleLineInNested | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3195 | ColumnLayoutAlgorithmTest.ColumnBalancingSingleLineInNestedSpanner | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3229 | ColumnLayoutAlgorithmTest.ColumnBalancingOverflow | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3264 | ColumnLayoutAlgorithmTest.ColumnBalancingLines | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3302 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesOrphans | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3348 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesForcedBreak | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3394 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesForcedBreak2 | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3447 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesForcedBreak3 | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3506 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesAvoidBreakInside | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:3552 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesAvoidBreakInside2 | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:3597 | ColumnLayoutAlgorithmTest.ColumnBalancingUnderflow | geometry | blocked | needs column balancing binary search algorithm in multicolumn |
| column_layout_algorithm_test.cc:3623 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBfc | geometry | blocked | needs class C break point resolution in multicolumn |
| column_layout_algorithm_test.cc:3660 | ColumnLayoutAlgorithmTest.NoClassCBreakPointBeforeBfc | geometry | blocked | needs class C break point resolution in multicolumn |
| column_layout_algorithm_test.cc:3696 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBfcWithClearance | geometry | blocked | needs class C break point resolution in multicolumn |
| column_layout_algorithm_test.cc:3733 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBfcWithMargin | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:3770 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBlockMarginCollapsing | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:3813 | ColumnLayoutAlgorithmTest.NoClassCBreakPointBeforeBlockMarginCollapsing | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:3856 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeLine | geometry | blocked | needs inline line box fragmentation in multicolumn |
| column_layout_algorithm_test.cc:3894 | ColumnLayoutAlgorithmTest.ForcedBreakAtClassCBreakPoint | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:3931 | ColumnLayoutAlgorithmTest.Nested | geometry | blocked | needs nested multicolumn layout |
| column_layout_algorithm_test.cc:3982 | ColumnLayoutAlgorithmTest.NestedWithEdibleMargin | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4019 | ColumnLayoutAlgorithmTest.NestedNoInnerContent | geometry | blocked | needs nested multicolumn layout |
| column_layout_algorithm_test.cc:4051 | ColumnLayoutAlgorithmTest.NestedSomeInnerContent | geometry | blocked | needs nested multicolumn layout |
| column_layout_algorithm_test.cc:4086 | ColumnLayoutAlgorithmTest.NestedLimitedHeight | geometry | blocked | needs nested multicolumn layout |
| column_layout_algorithm_test.cc:4143 | ColumnLayoutAlgorithmTest.NestedLimitedHeightWithPadding | geometry | blocked | needs container border and padding fragmentation in multicolumn |
| column_layout_algorithm_test.cc:4179 | ColumnLayoutAlgorithmTest.NestedUnbalancedInnerAutoHeight | geometry | blocked | needs nested multicolumn layout |
| column_layout_algorithm_test.cc:4225 | ColumnLayoutAlgorithmTest.NestedAtOuterBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4258 | ColumnLayoutAlgorithmTest.NestedZeroHeightAtOuterBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4288 | ColumnLayoutAlgorithmTest.NestedWithMarginAtOuterBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4321 | ColumnLayoutAlgorithmTest.NestedWithTallBorder | geometry | blocked | needs container border and padding fragmentation in multicolumn |
| column_layout_algorithm_test.cc:4353 | ColumnLayoutAlgorithmTest.NestedWithTallSpanner | geometry | blocked | needs nested multicolumn layout |
| column_layout_algorithm_test.cc:4388 | ColumnLayoutAlgorithmTest.AbsposFitsInOneColumn | geometry | blocked | needs out-of-flow abspos layout in multicolumn |
| column_layout_algorithm_test.cc:4415 | ColumnLayoutAlgorithmTest.Spanner | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4468 | ColumnLayoutAlgorithmTest.SpannerWithContent | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4528 | ColumnLayoutAlgorithmTest.TwoSpannersPercentWidth | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4583 | ColumnLayoutAlgorithmTest.SpannerNoBalancing | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4638 | ColumnLayoutAlgorithmTest.SpannerAtStart | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4679 | ColumnLayoutAlgorithmTest.SpannerAtEnd | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4719 | ColumnLayoutAlgorithmTest.SpannerAlone | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4746 | ColumnLayoutAlgorithmTest.SpannerInBlock | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4781 | ColumnLayoutAlgorithmTest.SpannerWithSiblingsInBlock | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4824 | ColumnLayoutAlgorithmTest.SpannerInBlockWithSiblings | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4866 | ColumnLayoutAlgorithmTest.SpannerMargins | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4902 | ColumnLayoutAlgorithmTest.SpannerMarginsRtl | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4939 | ColumnLayoutAlgorithmTest.FixedSizeMulticolWithSpanner | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4980 | ColumnLayoutAlgorithmTest.MarginAndBorderTopWithSpanner | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:5018 | ColumnLayoutAlgorithmTest.BreakInsideSpannerWithMargins | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:5054 | ColumnLayoutAlgorithmTest.InvalidSpanners | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:5101 | ColumnLayoutAlgorithmTest.BreakInsideSpanner | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5148 | ColumnLayoutAlgorithmTest.BreakInsideSpannerTwice | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5198 | ColumnLayoutAlgorithmTest.BreakInsideSpannerWithContent | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5246 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:5279 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners2 | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:5312 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners3 | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:5351 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners4 | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:5390 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners5 | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:5424 | ColumnLayoutAlgorithmTest.SoftBreakBetweenSpanners | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:5458 | ColumnLayoutAlgorithmTest.SoftBreakBetweenSpanners2 | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:5493 | ColumnLayoutAlgorithmTest.AvoidSoftBreakBetweenSpanners | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5530 | ColumnLayoutAlgorithmTest.AvoidSoftBreakBetweenSpanners2 | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5574 | ColumnLayoutAlgorithmTest.AvoidSoftBreakBetweenSpanners3 | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5624 | ColumnLayoutAlgorithmTest.SoftBreakBetweenRowAndSpanner | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:5671 | ColumnLayoutAlgorithmTest.SpannerAsMulticol | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:5723 | ColumnLayoutAlgorithmTest.AvoidBreakBetween | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5762 | ColumnLayoutAlgorithmTest.AvoidAndForceBreakBetween | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5800 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenInFloat | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:5845 | ColumnLayoutAlgorithmTest.IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5892 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenAndInsideIgnoreInside | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5938 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenAndInside | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5984 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenInsideBreakableParent | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6037 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenAfterBreakableSibling | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6092 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenBreakInsidePreviousSibling | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6136 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenHonorOrphansWidows | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6182 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenHonorOrphansWidows2 | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6225 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenHonorOrphansWidows3 | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6281 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenIgnoreOrphansWidows | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6326 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenLinesInsideBreakAvoid | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6375 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenBreakAtEarlyClassC | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6416 | ColumnLayoutAlgorithmTest.AvoidBreakBeforeBlockReplacedContent | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:6451 | ColumnLayoutAlgorithmTest.TallReplacedContent | geometry | blocked | needs replaced element fragmentation in multicolumn |
| column_layout_algorithm_test.cc:6480 | ColumnLayoutAlgorithmTest.GapDecorationBasic | geometry | blocked | needs column gap decorations layout |
| column_layout_algorithm_test.cc:6553 | ColumnLayoutAlgorithmTest.GapDecorationContentEndPastContainer | geometry | blocked | needs column gap decorations layout |
| column_layout_algorithm_test.cc:6619 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapOneColumn | geometry | blocked | needs column gap decorations layout |
| column_layout_algorithm_test.cc:6711 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapBasic | geometry | blocked | needs column gap decorations layout |
| column_layout_algorithm_test.cc:6798 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapAndSpanner | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:6893 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapLastRowNotFilled | geometry | blocked | needs column gap decorations layout |
| column_layout_algorithm_test.cc:6951 | ColumnLayoutAlgorithmTest.GapDecorationTwoSpanners | geometry | blocked | needs column spanners (column-span: all) in multicolumn |

| fragmentation_test.cc:25 | FragmentationTest.MultipleFragments | geometry | formalized | `TestsBlock.MultipleFragments_vectors` |
| fragmentation_test.cc:68 | FragmentationTest.MultipleFragmentsAndColumnSpanner | geometry | blocked | needs column spanners (column-span: all) and line fragmentation |
| fragmentation_test.cc:132 | FragmentationTest.MultipleFragmentsNestedMulticol | geometry | blocked | needs nested multicolumn fragmentation |
| fragmentation_test.cc:187 | FragmentationTest.HasSeenAllChildrenIfc | behaviour | blocked | needs inline formatting context break tokens HasSeenAllChildren tracking |
| fragmentation_test.cc:235 | FragmentationTest.InkOverflowInline | geometry | blocked | needs inline-block visual ink overflow calculation across columns |
| fragmentation_test.cc:271 | FragmentationTest.OffsetFromOwnerLayoutBoxFloat | geometry | blocked | needs float fragmentation OffsetFromOwnerLayoutBox calculation |
| fragmentation_test.cc:303 | FragmentationTest.OffsetFromOwnerLayoutBoxNested | geometry | blocked | needs nested multicol OffsetFromOwnerLayoutBox calculation |
| fragmentation_test.cc:345 | FragmentationTest.ConsumedBlockSizeOverflowInflow | geometry | formalized | `TestsBlock.ConsumedBlockSizeOverflowInflow_vectors`, `BlockFlow.consumedBlockSize_step` |
| fragmentation_test.cc:373 | FragmentationTest.ConsumedBlockSizeOverflowOutOfFlow | geometry | blocked | needs out-of-flow fragmentation in containing block with break tokens |

| flex/flex_layout_algorithm_test.cc:42 | FlexLayoutAlgorithmTest.DetailsFlexDoesntCrash | internal | internal | crash regression with details element styled as display:flex |
| flex/flex_layout_algorithm_test.cc:50 | FlexLayoutAlgorithmTest.ReplacedAspectRatioPrecision | geometry | blocked | needs SVG replaced aspect-ratio sizing in flex column |
| flex/flex_layout_algorithm_test.cc:72 | FlexLayoutAlgorithmTest.GapDecorationsOneLine | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:144 | FlexLayoutAlgorithmTest.GapDecorationsBasic | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:219 | FlexLayoutAlgorithmTest.GapDecorationsContentEndPastContainer | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:285 | FlexLayoutAlgorithmTest.GapDecorationsNonAlignedColumn | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:370 | FlexLayoutAlgorithmTest.GapDecorationsNonAlignedColumn2 | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:453 | FlexLayoutAlgorithmTest.GapDecorationsVerticalFlexAlignedCenter | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:538 | FlexLayoutAlgorithmTest.GapDecorationsVerticalFlexAlignedStart | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:623 | FlexLayoutAlgorithmTest.GapDecorationsVerticalFlexAlignedStretch | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:708 | FlexLayoutAlgorithmTest.GapDecorationsColumnFlexDirection | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:790 | FlexLayoutAlgorithmTest.GapDecorationsContentDistributionGaps | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:878 | FlexLayoutAlgorithmTest.GapDecorationsContentDistributionGapsBetweenLines | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:939 | FlexLayoutAlgorithmTest.DevtoolsBasic | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:953 | FlexLayoutAlgorithmTest.DevtoolsWrap | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:968 | FlexLayoutAlgorithmTest.DevtoolsCoordinates | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:983 | FlexLayoutAlgorithmTest.DevtoolsOverflow | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:993 | FlexLayoutAlgorithmTest.DevtoolsWithRelPosItem | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1012 | FlexLayoutAlgorithmTest.DevtoolsBaseline | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1032 | FlexLayoutAlgorithmTest.DevtoolsOneImageItemCrash | internal | internal | crash regression with devtools flex layout on lone image item |
| flex/flex_layout_algorithm_test.cc:1040 | FlexLayoutAlgorithmTest.DevtoolsColumnWrap | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1052 | FlexLayoutAlgorithmTest.DevtoolsColumnWrapOrtho | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1064 | FlexLayoutAlgorithmTest.DevtoolsRowWrapOrtho | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1077 | FlexLayoutAlgorithmTest.DevtoolsLegacyItem | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1091 | FlexLayoutAlgorithmTest.DevtoolsFragmentedItemDoesntCrash | internal | internal | crash regression with fragmented flex item in devtools |
| flex/flex_layout_algorithm_test.cc:1103 | FlexLayoutAlgorithmTest.DevtoolsAutoScrollbar | behaviour | blocked | needs devtools flex data layout inspector model |
| flex/flex_layout_algorithm_test.cc:1127 | FlexLayoutAlgorithmTest.SingleAxisScrollerAutoMinSizeUseCount | internal | internal | checks UseCounter for SingleAxisScrollerAutoMinSize feature |
| layout_flexible_box_test.cc:96 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowHTB | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:123 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowVLR | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:151 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowVRL | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:160 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowReverseHTB | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:200 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowReverseVLR | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:229 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowReverseVRL | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:238 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnHTB | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:247 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnVLR | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:256 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnVRL | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:269 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnReverseHTB | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:292 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnReverseVLR | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:315 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnReverseVRL | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:357 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowHTB | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:366 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowVLR | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:375 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowVRL | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:384 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowReverseHTB | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:409 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowReverseVLR | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:418 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowReverseVRL | geometry | blocked | needs flexible box scrollable overflow and scroll offsets with scrollbars across writing modes |
| layout_flexible_box_test.cc:427 | LayoutFlexibleBoxTest.ResizedFlexChildRequiresVisualOverflowRecalc | behaviour | blocked | needs flexbox visual overflow invalidation tracking on child resize |
## Laws proved

- `BlockFlow.consumedBlockSize_step`: consumed block size increases by fragmentainer size with each fragment.
- `ColumnLayout.colStride_pos`: column stride is strictly positive when column width is positive.
- `ColumnLayout.columnInlineOffset_step`: column offset advances by stride for each subsequent column.
- `ColumnLayout.columns_non_overlapping`: columns do not overlap when gap is non-negative and column width is positive.
- `ColumnLayout.actualColumnCount_at_least_one`: multicolumn container always generates at least one column fragmentainer.


- `BlockFlow.collapse_pair`: two adjoining margins collapse to max-positive plus min-negative (CSS 2.1 8.3.1).
- `BlockFlow.empty_box_keeps_pos`: an empty box does not advance the flow position.
- `BlockFlow.start_edge_top`: a non-empty box with a start edge sits at its collapsed top margin.
- `BlockFlow.auto_width_fills`: auto-width box with definite margins fills the containing block.
- `BlockFlow.shrinkToFit_bounds`: shrink-to-fit always lies within [min-content, max-content].
- `BlockFlow.fragmentation_conserves_size`: fragment sizes sum to the box's block size.
- `BlockNode.iterate_mem`: the child iterator only returns real children.
- `BlockWritingMode.toPhysical_toLogical`: physical to logical edge mapping is an isomorphism.
- `BlockLength.clampSize_ge_min`: clamping by min/max never returns less than the minimum.
- `BlockLength.inlineFromAspectRatio_le_max`: aspect ratio inline size saturates at LayoutUnit::Max().
- `BlockLength.inlineFromAspectRatio_one`: 1:1 aspect ratio preserves block size below saturation.
- `ColumnWidth.columns_fit`: multicol columns plus gaps fit the available inline size.
- `BlockRelative.opposing_sum_zero`: when only one opposing relative inset is specified, the resolved insets sum to zero.
- `BlockAbsolute.clamp_bounds`: clamping always stays within [minVal, maxVal] when minVal ≤ maxVal.

## Merge notes

- `BlockFlow.lean` extends `MarginStrut` from `LayoutTypes.lean` with `MarginStrut.ofInt` /
  `MarginStrut.signedSum` (namespace `ChromiumLayout.MarginStrut`) instead of editing the shared file.
- `check.sh` gained one block (call to `tests/check_tests.sh`) before the final line; the other lane
  may add its own call next to it.
