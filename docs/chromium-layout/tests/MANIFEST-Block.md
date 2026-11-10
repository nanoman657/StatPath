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
percent/shrink-to-fit widths, laws), `BlockFloat.lean` (floats and clearance), `BlockFragmentation.lean` (fragmentainer slicing), `BlockNode.lean` (child nodes, child iterator), `BlockScroll.lean` (scrollbar gutter), `BlockWritingMode.lean` (physical/logical mapping), `BlockLength.lean` (CSS length resolution, contributions, aspect ratio), `ColumnWidth.lean` (multicol column width and count), `BlockRelative.lean` (relative positioning insets), `BlockAbsolute.lean` (out-of-flow positioning constraints), `GridLayout.lean` (CSS Grid track sizing, gaps, placement, and ranges), `TableLayout.lean` (CSS table section ordering, colspan/rowspan distribution, and block sizing).
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
| block_layout_algorithm_test.cc:380 | BlockLayoutAlgorithmTest.LayoutBlockChildrenWithWritingMode | geometry | formalized | `TestsBlock.LayoutBlockChildrenWithWritingMode_vectors` |
| block_layout_algorithm_test.cc:418 | BlockLayoutAlgorithmTest.CollapsingMarginsCase1WithFloats | geometry | formalized | `TestsBlock.CollapsingMarginsCase1WithFloats_vectors` |
| block_layout_algorithm_test.cc:487 | BlockLayoutAlgorithmTest.CollapsingMarginsCase2WithFloats | geometry | formalized | `TestsBlock.CollapsingMarginsCase2WithFloats_vectors`: body at -7 and body children at 0, 70, 40, 90 via `layoutFloat` (floats are leaves that never collapse margins; `isEmpty`, `firstResolve`, `allMargins` skip them) |
| block_layout_algorithm_test.cc:568 | BlockLayoutAlgorithmTest.CollapsingMarginsCase3 | geometry | formalized | `TestsBlock.CollapsingMarginsCase3_auto`, `TestsBlock.CollapsingMarginsCase3_fixed` |
| block_layout_algorithm_test.cc:618 | BlockLayoutAlgorithmTest.CollapsingMarginsCase4 | geometry | formalized | `TestsBlock.CollapsingMarginsCase4_with_padding`, `TestsBlock.CollapsingMarginsCase4_without_padding`, `BlockFlow.start_edge_top` |
| block_layout_algorithm_test.cc:680 | BlockLayoutAlgorithmTest.CollapsingMarginsCase5 | geometry | formalized | `TestsBlock.CollapsingMarginsCase5_vectors` |
| block_layout_algorithm_test.cc:744 | BlockLayoutAlgorithmTest.CollapsingMarginsWithText | geometry | blocked | needs text line layout in `<p>`; expected offsets depend on the text's line box, not modelled by BlockFlow |
| block_layout_algorithm_test.cc:772 | BlockLayoutAlgorithmTest.CollapsingMarginsCase6 | geometry | formalized | `TestsBlock.CollapsingMarginsCase6_vectors` |
| block_layout_algorithm_test.cc:815 | BlockLayoutAlgorithmTest.CollapsingMarginsCase7 | geometry | blocked | needs float and `clear` |
| block_layout_algorithm_test.cc:869 | BlockLayoutAlgorithmTest.CollapsingMarginsEmptyBlockWithClearance | geometry | blocked | needs float, `clear`, abspos |
| block_layout_algorithm_test.cc:1029 | BlockLayoutAlgorithmTest.NewFormattingContextAutoMargins | geometry | blocked | needs float and rtl layout opportunity |
| block_layout_algorithm_test.cc:1062 | BlockLayoutAlgorithmTest.BorderAndPadding | geometry | formalized | `TestsBlock.BorderAndPadding_div1`, `TestsBlock.BorderAndPadding_div2_offset` |
| block_layout_algorithm_test.cc:1118 | BlockLayoutAlgorithmTest.PercentageResolutionSize | geometry | formalized | `TestsBlock.PercentageResolutionSize_widths` |
| block_layout_algorithm_test.cc:1145 | BlockLayoutAlgorithmTest.AutoMargin | geometry | formalized | `TestsBlock.AutoMargin_offsets`, `BlockFlow.auto_width_fills` |
| block_layout_algorithm_test.cc:1180 | BlockLayoutAlgorithmTest.PositionFloatInsideEmptyBlocks | geometry | formalized | `TestsBlock.PositionFloatInsideEmptyBlocks_vectors`: body top 20; empty1 at (20, 0); empty2 at (35, 0); left float at (25, 10) and right float at (150, 15) in empty2, via `layoutFloat` (a right float ends at the content right edge); the floats do not overlap, so the model's no-shift placement is exact here |
| block_layout_algorithm_test.cc:1275 | BlockLayoutAlgorithmTest.PositionFloatFragments | geometry | formalized | `TestsBlock.PositionFloatFragments_vectors` |
| block_layout_algorithm_test.cc:1390 | BlockLayoutAlgorithmTest.PositionFragmentsWithClear | geometry | formalized | `TestsBlock.PositionFragmentsWithClear_none_vectors`, `TestsBlock.PositionFragmentsWithClear_left_vectors`, `TestsBlock.PositionFragmentsWithClear_right_vectors`, `TestsBlock.PositionFragmentsWithClear_both_vectors`, `BlockFloat.clearance_respects_left_floats`, `BlockFloat.clearance_respects_right_floats`, `BlockFloat.clearance_respects_both_floats` |
| block_layout_algorithm_test.cc:1516 | BlockLayoutAlgorithmTest.ComputeMinMaxContent | geometry | formalized | `TestsBlock.ComputeMinMaxContent_sizes` |
| block_layout_algorithm_test.cc:1533 | BlockLayoutAlgorithmTest.ComputeMinMaxContentFloats | geometry | blocked | needs floats in min/max-content |
| block_layout_algorithm_test.cc:1554 | BlockLayoutAlgorithmTest.ComputeMinMaxContentFloatsClearance | geometry | blocked | needs floats and `clear` in min/max-content |
| block_layout_algorithm_test.cc:1575 | BlockLayoutAlgorithmTest.ComputeMinMaxContentNewFormattingContext | geometry | blocked | needs floats beside a flex new-FC child |
| block_layout_algorithm_test.cc:1596 | BlockLayoutAlgorithmTest.ComputeMinMaxContentNewFormattingContextNegativeMargins | geometry | blocked | needs floats beside a flex new-FC child |
| block_layout_algorithm_test.cc:1618 | BlockLayoutAlgorithmTest.ComputeMinMaxContentSingleNewFormattingContextNegativeMargins | geometry | blocked | needs a flex new-FC child (flex lane module); BlockFlow has no negative-margin max-content clamp vector for a flex child |
| block_layout_algorithm_test.cc:1637 | BlockLayoutAlgorithmTest.ShrinkToFit | geometry | formalized | `TestsBlock.ShrinkToFit_width` |
| block_layout_algorithm_test.cc:1660 | BlockLayoutAlgorithmTest.PositionEmptyBlocksInNewBfc | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:1705 | BlockLayoutAlgorithmTest.PositionBlocksWithClearanceAndIntrudingFloats | geometry | partly formalized | `TestsBlock.PositionBlocksWithClearanceAndIntrudingFloats_vectors` with `BlockFloat.layoutBlockWithFloats`; the container block with clear: left is flattened into the flow as an item carrying its first child's collapsed margin, and the body/html margin collapse is taken as given (not derived) |
| block_layout_algorithm_test.cc:1778 | BlockLayoutAlgorithmTest.NoFragmentation | geometry | formalized | `TestsBlock.NoFragmentation_vectors` |
| block_layout_algorithm_test.cc:1806 | BlockLayoutAlgorithmTest.SimpleFragmentation | geometry | formalized | `TestsBlock.SimpleFragmentation_vectors`, `BlockFlow.fragmentation_conserves_size` |
| block_layout_algorithm_test.cc:1838 | BlockLayoutAlgorithmTest.InnerChildrenFragmentation | geometry | formalized | `TestsBlock.InnerChildrenFragmentation_vectors` |
| block_layout_algorithm_test.cc:1900 | BlockLayoutAlgorithmTest.InnerFormattingContextChildrenFragmentation | geometry | formalized | `TestsBlock.InnerFormattingContextChildrenFragmentation_vectors` |
| block_layout_algorithm_test.cc:1964 | BlockLayoutAlgorithmTest.InnerChildrenFragmentationSmallHeight | geometry | formalized | `TestsBlock.InnerChildrenFragmentationSmallHeight_vectors` |
| block_layout_algorithm_test.cc:2026 | BlockLayoutAlgorithmTest.DISABLED_FloatFragmentationParallelFlows | geometry | blocked | DISABLED_ in the test source; needs floats and fragmentation |
| block_layout_algorithm_test.cc:2104 | BlockLayoutAlgorithmTest.FloatFragmentationOrthogonalFlows | geometry | blocked | needs floats and a vertical-rl float |
| block_layout_algorithm_test.cc:2155 | BlockLayoutAlgorithmTest.DISABLED_FloatFragmentationZeroHeight | geometry | blocked | DISABLED_ in the test source; needs floats and fragmentation |
| block_layout_algorithm_test.cc:2226 | BlockLayoutAlgorithmTest.NewFcBlockWithAdjoiningFloatCollapsesMargins | geometry | formalized | `TestsBlock.NewFcBlockWithAdjoiningFloatCollapsesMargins_vectors` |
| block_layout_algorithm_test.cc:2281 | BlockLayoutAlgorithmTest.NewFcAvoidsFloats | geometry | formalized | `TestsBlock.NewFcAvoidsFloats_vectors` |
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
| physical_box_fragment_test.cc:115 | PhysicalBoxFragmentTest.IsFragmentationContextRoot | geometry | formalized | `TestsBlock.IsFragmentationContextRoot_columnCount`, `ColumnLayout.actualColumnCount_at_least_one` |
| physical_box_fragment_test.cc:135 | PhysicalBoxFragmentTest.IsFragmentationContextRootNested | geometry | formalized | `TestsBlock.IsFragmentationContextRootNested_columnCounts`, `ColumnLayout.actualColumnCount_at_least_one` |
| physical_box_fragment_test.cc:169 | PhysicalBoxFragmentTest.IsFragmentationContextRootFieldset | behaviour | blocked | model lacks fragmentation context root query on physical fragments |
| physical_box_fragment_test.cc:201 | PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStart | behaviour | blocked | model lacks descendant overflow above block-start query on physical fragments |
| physical_box_fragment_test.cc:216 | PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStartBlockInInline | behaviour | blocked | model lacks descendant overflow above block-start query on physical fragments |
| physical_box_fragment_test.cc:233 | PhysicalBoxFragmentTest.OverflowClipMarginVisualBox | geometry | blocked | model lacks visual box overflow-clip-margin calculation |
| physical_box_fragment_test.cc:294 | PhysicalBoxFragmentTest.CloneWithPostLayoutFragments | internal | internal | checks CloneWithPostLayoutFragments preserves C++ frame set layout data pointer |
| relative_utils_test.cc:49 | RelativeUtilsTest.HorizontalTB | geometry | formalized | `TestsBlock.HorizontalTB_vectors`, `BlockRelative.opposing_sum_zero` |
| absolute_utils_test.cc:150 | AbsoluteUtilsTest.Horizontal | geometry | formalized | `TestsBlock.Horizontal_vectors` |
| absolute_utils_test.cc:315 | AbsoluteUtilsTest.Vertical | geometry | formalized | `TestsBlock.Vertical_vectors` |
| absolute_utils_test.cc:436 | AbsoluteUtilsTest.CenterStaticPosition | geometry | formalized | `TestsBlock.CenterStaticPosition_vectors` |
| absolute_utils_test.cc:474 | AbsoluteUtilsTest.MinMax | geometry | formalized | `TestsBlock.MinMax_vectors`, `BlockAbsolute.clamp_bounds` |
| out_of_flow_layout_part_test.cc:46 | OutOfFlowLayoutPartTest.FixedInsideAbs | geometry | formalized | `TestsBlock.FixedInsideAbs_offsets`, `BlockAbsolute.explicit_inset_overrides_static`, `BlockAbsolute.auto_inset_uses_static` |
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
| column_layout_algorithm_test.cc:4415 | ColumnLayoutAlgorithmTest.Spanner | geometry | formalized | `TestsBlock.Spanner_vectors`, `ColumnLayout.spanner_width_auto`, `ColumnLayout.spanner_offset_advances` |
| column_layout_algorithm_test.cc:4468 | ColumnLayoutAlgorithmTest.SpannerWithContent | geometry | formalized | `TestsBlock.SpannerWithContent_vectors` |
| column_layout_algorithm_test.cc:4528 | ColumnLayoutAlgorithmTest.TwoSpannersPercentWidth | geometry | formalized | `TestsBlock.TwoSpannersPercentWidth_vectors` |
| column_layout_algorithm_test.cc:4583 | ColumnLayoutAlgorithmTest.SpannerNoBalancing | geometry | formalized | `TestsBlock.SpannerNoBalancing_vectors` |
| column_layout_algorithm_test.cc:4638 | ColumnLayoutAlgorithmTest.SpannerAtStart | geometry | formalized | `TestsBlock.SpannerAtStart_vectors` |
| column_layout_algorithm_test.cc:4679 | ColumnLayoutAlgorithmTest.SpannerAtEnd | geometry | formalized | `TestsBlock.SpannerAtEnd_vectors` |
| column_layout_algorithm_test.cc:4719 | ColumnLayoutAlgorithmTest.SpannerAlone | geometry | formalized | `TestsBlock.SpannerAlone_vectors` |
| column_layout_algorithm_test.cc:4746 | ColumnLayoutAlgorithmTest.SpannerInBlock | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4781 | ColumnLayoutAlgorithmTest.SpannerWithSiblingsInBlock | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4824 | ColumnLayoutAlgorithmTest.SpannerInBlockWithSiblings | geometry | blocked | needs column spanners (column-span: all) in multicolumn |
| column_layout_algorithm_test.cc:4866 | ColumnLayoutAlgorithmTest.SpannerMargins | geometry | formalized | `TestsBlock.SpannerMargins_vectors`, `ColumnLayout.spanner_margin_collapsing` |
| column_layout_algorithm_test.cc:4902 | ColumnLayoutAlgorithmTest.SpannerMarginsRtl | geometry | formalized | `TestsBlock.SpannerMarginsRtl_vectors` |
| column_layout_algorithm_test.cc:4939 | ColumnLayoutAlgorithmTest.FixedSizeMulticolWithSpanner | geometry | formalized | `TestsBlock.FixedSizeMulticolWithSpanner_vectors` |
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
| table/layout_table_section_test.cc:18 | LayoutTableSectionTest.BackgroundIsKnownToBeOpaqueWithLayerAndCollapsedBorder | behaviour | blocked | needs table section BackgroundIsKnownToBeOpaque paint model |
| table/layout_table_section_test.cc:35 | LayoutTableSectionTest.BackgroundIsKnownToBeOpaqueWithBorderSpacing | behaviour | blocked | needs table section BackgroundIsKnownToBeOpaque paint model |
| table/layout_table_section_test.cc:50 | LayoutTableSectionTest.BackgroundIsKnownToBeOpaqueWithEmptyCell | behaviour | blocked | needs table section BackgroundIsKnownToBeOpaque paint model |
| table/layout_table_section_test.cc:66 | LayoutTableSectionTest.VisualOverflowWithCollapsedBorders | geometry | blocked | needs table section visual overflow with collapsed borders |
| table/layout_table_section_test.cc:99 | LayoutTableSectionTest.RowCollapseNegativeHeightCrash | internal | internal | crash regression in row collapse with negative height |
| table/layout_table_test.cc:21 | LayoutTableTest.OverflowViaOutline | geometry | blocked | needs table visual overflow rect calculation |
| table/layout_table_test.cc:47 | LayoutTableTest.OverflowWithCollapsedBorders | geometry | blocked | needs table visual overflow rect calculation |
| table/layout_table_test.cc:88 | LayoutTableTest.CollapsedBorders | geometry | blocked | needs table collapsed borders layout model |
| table/layout_table_test.cc:143 | LayoutTableTest.CollapsedBordersWithCol | geometry | blocked | needs table collapsed borders layout model |
| table/layout_table_test.cc:207 | LayoutTableTest.WidthPercentagesExceedHundred | geometry | blocked | needs table column percentage and max width resolution |
| table/layout_table_test.cc:230 | LayoutTableTest.CloseToMaxWidth | geometry | formalized | `TestsBlock.CloseToMaxWidth_vectors` |
| table/layout_table_test.cc:250 | LayoutTableTest.PaddingWithCollapsedBorder | geometry | formalized | `TestsBlock.PaddingWithCollapsedBorder_vectors`, `TableLayout.collapsed_border_padding_zero` |
| table/layout_table_test.cc:260 | LayoutTableTest.OutOfOrderHeadAndBody | geometry | formalized | `TestsBlock.OutOfOrderHeadAndBody_vectors` |
| table/layout_table_test.cc:279 | LayoutTableTest.OutOfOrderFootAndBody | geometry | formalized | `TestsBlock.OutOfOrderFootAndBody_vectors` |
| table/layout_table_test.cc:298 | LayoutTableTest.OutOfOrderHeadFootAndBody | geometry | formalized | `TestsBlock.OutOfOrderHeadFootAndBody_vectors` |
| table/layout_table_test.cc:330 | LayoutTableTest.VisualOverflowCleared | geometry | blocked | needs table visual overflow rect calculation |
| table/table_layout_utils_test.cc:55 | TableLayoutUtilsTest.DistributeColspanAutoPercent | geometry | formalized | `TestsBlock.DistributeColspanAutoPercent_vectors` |
| table/table_layout_utils_test.cc:93 | TableLayoutUtilsTest.DistributeColspanAutoSizeUnconstrained | geometry | formalized | `TestsBlock.DistributeColspanAutoSizeUnconstrained_vectors` |
| table/table_layout_utils_test.cc:121 | TableLayoutUtilsTest.DistributeColspanAutoSizeConstrained | geometry | formalized | `TestsBlock.DistributeColspanAutoSizeConstrained_vectors` |
| table/table_layout_utils_test.cc:149 | TableLayoutUtilsTest.DistributeColspanAutoExactMaxSize | geometry | blocked | needs table colspan column width distribution algorithm |
| table/table_layout_utils_test.cc:187 | TableLayoutUtilsTest.ComputeGridInlineMinMax | geometry | blocked | needs table grid inline min/max sizes algorithm |
| table/table_layout_utils_test.cc:246 | TableLayoutUtilsTest.DistributeRowspanCellToRows | geometry | blocked | needs table rowspan row height distribution algorithm |
| table/table_layout_utils_test.cc:280 | TableLayoutUtilsTest.DistributeSectionFixedBlockSizeToRows | geometry | formalized | `TestsBlock.DistributeSectionFixedBlockSizeToRows_vectors` |
| table/table_layout_utils_test.cc:294 | TableLayoutUtilsTest.DistributeTableBlockSizeToSections | geometry | formalized | `TestsBlock.DistributeTableBlockSizeToSections_vectors` |
| grid/grid_layout_algorithm_test.cc:171 | GridLayoutAlgorithmTest.GridLayoutAlgorithmAvailableRowSizes | geometry | blocked | needs CSS grid layout algorithm |
| grid/grid_layout_algorithm_test.cc:209 | GridLayoutAlgorithmTest.GridLayoutAlgorithmGapGeometry | geometry | blocked | needs CSS grid gap geometry calculation |
| grid/grid_layout_algorithm_test.cc:290 | GridLayoutAlgorithmTest.GapGeomoetryWithSpanningItems | geometry | blocked | needs CSS grid gap geometry calculation |
| grid/grid_layout_algorithm_test.cc:421 | GridLayoutAlgorithmTest.GapGeometryWithEmptyCellsAndSpanningItems | geometry | blocked | needs CSS grid gap geometry calculation |
| grid/grid_layout_algorithm_test.cc:603 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRanges | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:650 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesWithAutoRepeater | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:701 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicit | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:764 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitAutoColumns | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:822 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitAutoRows | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:881 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitMixed | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:929 | GridLayoutAlgorithmTest.GridLayoutAlgorithmAutoGridPositions | geometry | blocked | needs CSS grid item placement and auto-placement algorithm |
| grid/grid_layout_algorithm_test.cc:1003 | GridLayoutAlgorithmTest.GridLayoutAlgorithmAutoDense | geometry | blocked | needs CSS grid item placement and auto-placement algorithm |
| grid/grid_layout_algorithm_test.cc:1159 | GridLayoutAlgorithmTest.GridLayoutAlgorithmGridPositions | geometry | blocked | needs CSS grid item placement and auto-placement algorithm |
| grid/grid_layout_algorithm_test.cc:1216 | GridLayoutAlgorithmTest.GridLayoutAlgorithmResolveFixedTrackSizes | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:1273 | GridLayoutAlgorithmTest.GridLayoutAlgorithmDetermineGridItemsSpanningIntrinsicOrFlexTracks | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:1356 | GridLayoutAlgorithmTest.FixedSizePositioning | geometry | formalized | `TestsBlock.FixedSizePositioning_vectors`, `GridLayout.track_offset_zero` |
| grid/grid_layout_algorithm_test.cc:1405 | GridLayoutAlgorithmTest.FixedSizePositioningAutoRows | geometry | formalized | `TestsBlock.FixedSizePositioningAutoRows_vectors` |
| grid/grid_layout_algorithm_test.cc:1462 | GridLayoutAlgorithmTest.SpecifiedPositionsOutOfOrder | geometry | formalized | `TestsBlock.SpecifiedPositionsOutOfOrder_vectors` |
| grid/grid_layout_algorithm_test.cc:1536 | GridLayoutAlgorithmTest.GridWithGap | geometry | formalized | `TestsBlock.GridWithGap_vectors`, `GridLayout.grid_gap_positive` |
| grid/grid_layout_algorithm_test.cc:1586 | GridLayoutAlgorithmTest.GridWithPercentGap | geometry | blocked | needs CSS grid gap geometry calculation |
| grid/grid_layout_algorithm_test.cc:1640 | GridLayoutAlgorithmTest.AutoSizedGridWithGap | geometry | formalized | `TestsBlock.AutoSizedGridWithGap_vectors` |
| grid/grid_layout_algorithm_test.cc:1694 | GridLayoutAlgorithmTest.AutoSizedGridWithPercentageGap | geometry | blocked | needs CSS grid gap geometry calculation |
| grid/grid_layout_algorithm_test.cc:1739 | GridLayoutAlgorithmTest.ItemsSizeWithGap | geometry | formalized | `TestsBlock.ItemsSizeWithGap_vectors` |
| grid/grid_layout_algorithm_test.cc:1800 | GridLayoutAlgorithmTest.PositionedOutOfFlowItems | geometry | blocked | needs CSS grid item placement and auto-placement algorithm |
| grid/grid_layout_algorithm_test.cc:1940 | GridLayoutAlgorithmTest.NGGridAxisType | geometry | blocked | needs CSS grid layout algorithm |
| grid/grid_layout_algorithm_test.cc:1973 | GridLayoutAlgorithmTest.SubgridLineNameList | geometry | blocked | needs CSS subgrid line names and track alignment |
| grid/grid_layout_algorithm_test.cc:2019 | GridLayoutAlgorithmTest.SubgridLineNameListWithRepeaters | geometry | blocked | needs CSS subgrid line names and track alignment |
| grid/grid_layout_algorithm_test.cc:2090 | GridLayoutAlgorithmTest.SingleAxisScrollerAutoMinSizeUseCount | internal | internal | checks UseCounter for SingleAxisScrollerAutoMinSize feature |
| grid/grid_layout_algorithm_test.cc:2136 | GridLayoutAlgorithmTest.FragmentedOofInGridPlaceItemsTwice | geometry | blocked | needs fragmented out-of-flow grid items placement |
| grid/grid_track_collection_test.cc:85 | GridTrackCollectionTest.TestRangeIndexFromGridLine | geometry | formalized | `TestsBlock.TestRangeIndexFromGridLine_vectors`, `GridLayout.range_index_first_track` |
| grid/grid_track_collection_test.cc:119 | GridTrackCollectionTest.TestGridTrackList | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:171 | GridTrackCollectionTest.TestGridRangeBuilder | geometry | formalized | `TestsBlock.TestGridRangeBuilder_vectors` |
| grid/grid_track_collection_test.cc:188 | GridTrackCollectionTest.TestGridRangeBuilderCollapsed | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:208 | GridTrackCollectionTest.TestGridRangeBuilderImplicit | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:248 | GridTrackCollectionTest.TestGridSetTrackSizeNormalization | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:300 | GridTrackCollectionTest.TestGridSizingTrackCollectionSetIterator | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:351 | GridTrackCollectionTest.TestGridSizingTrackCollectionExplicitTracks | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:459 | GridTrackCollectionTest.TestGridSizingTrackCollectionImplicitTracks | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:539 | GridTrackCollectionTest.TestGridSizingTrackCollectionIntrinsicAndFlexTracks | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:259 | GridLanesLayoutAlgorithmTest.ConstructGridLanesItems | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:310 | GridLanesLayoutAlgorithmTest.GridLanesAutoPlacedItems | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:346 | GridLanesLayoutAlgorithmTest.ConstructGridLanesItemsParentAutoPlacedMarksAll | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:378 | GridLanesLayoutAlgorithmTest.BuildRanges | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:425 | GridLanesLayoutAlgorithmTest.BuildFixedTrackSizes | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:455 | GridLanesLayoutAlgorithmTest.CollectGridLanesItemGroups | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:499 | GridLanesLayoutAlgorithmTest.CollectGridLanesItemGroupsWithBaseline | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:559 | GridLanesLayoutAlgorithmTest.ExplicitlyPlacedVirtualItems | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:608 | GridLanesLayoutAlgorithmTest.AutoPlacedVirtualItems | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:662 | GridLanesLayoutAlgorithmTest.BuildIntrinsicTrackSizes | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:697 | GridLanesLayoutAlgorithmTest.MaximizeAndStretchAutoTracks | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:737 | GridLanesLayoutAlgorithmTest.ExpandFlexibleTracks | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:766 | GridLanesLayoutAlgorithmTest.BuildRowSizes | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:797 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:837 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoAndExplicitPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:877 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:919 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitNoCollapse | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:962 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoSizeAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1005 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoSizeAndAutoAndExplicitPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1050 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitAutoAndAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1095 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitAutoNoCollapse | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1138 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1180 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoAndExplicitPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1222 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1266 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitNoCollapse | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1311 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoSizeAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1356 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoSizeAndAutoAndExplicitPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1401 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitAutoAndAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1447 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitAutoNoCollapse | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1492 | GridLanesLayoutAlgorithmTest.GetFirstEligibleLine | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1533 | GridLanesLayoutAlgorithmTest.GetMaxPositionsForAllTracks | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1549 | GridLanesLayoutAlgorithmTest.IncludeSubgriddedItemsIncludesNestedDescendants | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1580 | GridLanesLayoutAlgorithmTest.ItemsSubgriddedToParentExcludesDirectItems | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1609 | GridLanesLayoutAlgorithmTest.AppendSubgriddedItemsColumns | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1659 | GridLanesLayoutAlgorithmTest.AppendSubgriddedItemsRows | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1710 | GridLanesLayoutAlgorithmTest.SubgridRowsIgnoredInColumnGridLanes | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1758 | GridLanesLayoutAlgorithmTest.SubgridColumnsIgnoredInRowGridLanes | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1807 | GridLanesLayoutAlgorithmTest.OrthogonalAppendSubgriddedItemsColumns | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1859 | GridLanesLayoutAlgorithmTest.OrthogonalAppendSubgriddedItemsRows | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1914 | GridLanesLayoutAlgorithmTest.AutoPlacedSubgriddedItemsAreAutoPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1973 | GridLanesLayoutAlgorithmTest.DefiniteSubgridChildrenAreExplicitlyPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2036 | GridLanesLayoutAlgorithmTest.OppositeDirectionSubgridReversesChildSpans | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2093 | GridLanesLayoutAlgorithmTest.OrthogonalSubgridColumnsIgnoredInColumnGridLanes | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2145 | GridLanesLayoutAlgorithmTest.OrthogonalSubgridRowsIgnoredInRowGridLanes | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2201 | GridLanesLayoutAlgorithmTest.DefiniteSubgridsAtDifferentPositionsProduceSeparateVirtualItems | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2261 | GridLanesLayoutAlgorithmTest.AutoPlacedSubgridChildrenAreAutoPlacedForVirtualItems | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2327 | GridLanesLayoutAlgorithmTest.DefiniteSubgridAutoPlacedChildProducesDefiniteVirtualItem | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2386 | GridLanesLayoutAlgorithmTest.NestedSubgridInAutoPlacedSubgridIsAutoPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2448 | GridLanesLayoutAlgorithmTest.ExplicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2503 | GridLanesLayoutAlgorithmTest.NestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2558 | GridLanesLayoutAlgorithmTest.DeepNestedAutoPlacedSubgridsAreAllAutoPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2621 | GridLanesLayoutAlgorithmTest.AllChildrenOfAutoPlacedSubgridAreAutoPlaced | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2668 | GridLanesLayoutAlgorithmTest.AppendColumnSubgriddedGridLanesItems | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2709 | GridLanesLayoutAlgorithmTest.AppendRowSubgriddedGridLanesItems | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2744 | GridLanesLayoutAlgorithmTest.GridLanesSubgridIgnoresNonGridAxis | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2778 | GridLanesLayoutAlgorithmTest.OrthogonalGridLanesSubgridMapsGridAxis | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2807 | GridLanesLayoutAlgorithmTest.BuildsNestedGridLanesSubgrids | geometry | blocked | needs grid lanes subgridded item layout and mapping |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2842 | GridLanesLayoutAlgorithmTest.GridLanesDirectionChangeMarksPlacementDirty | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2870 | GridLanesLayoutAlgorithmTest.GridLanesPackChangeMarksPlacementDirty | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2899 | GridLanesLayoutAlgorithmTest.ResolvedGridAxisFlipMarksPlacementDirty | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2925 | GridLanesLayoutAlgorithmTest.GapGeometryColumn | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2979 | GridLanesLayoutAlgorithmTest.GapGeometryRow | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3031 | GridLanesLayoutAlgorithmTest.GapGeometryEmptyExplicitTracks | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3066 | GridLanesLayoutAlgorithmTest.GapGeometrySingleTrack | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3096 | GridLanesLayoutAlgorithmTest.GapGeometryRequiresGapRule | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3125 | GridLanesLayoutAlgorithmTest.GapGeometryCollapsedAutoFitTracks | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3171 | GridLanesLayoutAlgorithmTest.GapGeometryGridAxisAlignment | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3219 | GridLanesLayoutAlgorithmTest.GapGeometryColumnStackingAxisOverflow | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3265 | GridLanesLayoutAlgorithmTest.GapGeometryRowStackingAxisOverflow | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3310 | GridLanesLayoutAlgorithmTest.PopulateGridLanesBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3346 | GridLanesLayoutAlgorithmTest.SharePlacementDataAcrossFragments | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3385 | GridLanesLayoutAlgorithmTest.ShareExpansionDataAcrossFragments | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3419 | GridLanesLayoutAlgorithmTest.PopulateRowGridLanesBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3446 | GridLanesLayoutAlgorithmTest.PopulateSpannerBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3501 | GridLanesLayoutAlgorithmTest.PopulateDensePackedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3535 | GridLanesLayoutAlgorithmTest.PopulateDensePackedSpannerBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3572 | GridLanesLayoutAlgorithmTest.PopulateDenseSpannerWithDifferentParentsPerLane | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3637 | GridLanesLayoutAlgorithmTest.PopulateDenseItemAboveDenseSpannerUsesParentSpanner | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3674 | GridLanesLayoutAlgorithmTest.PopulateDenseItemsUseCorrectSpannerForMultipleOpenings | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3718 | GridLanesLayoutAlgorithmTest.PopulateGridAxisAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3752 | GridLanesLayoutAlgorithmTest.PopulateRowGridAxisAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3785 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3810 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3835 | GridLanesLayoutAlgorithmTest.PopulateExplicitStackingAxisStretchBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3862 | GridLanesLayoutAlgorithmTest.PopulateRowExplicitStackingAxisStretchBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3889 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisStretchSpaceBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3914 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisStretchSpaceBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3940 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisStretchSpannerSpaceBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3976 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisStretchSpannerSpaceBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4012 | GridLanesLayoutAlgorithmTest.PopulateLastStackingAxisAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4042 | GridLanesLayoutAlgorithmTest.PopulateRowLastStackingAxisAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4073 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisAlignedSpannerBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4104 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisAlignedSpannerBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4135 | GridLanesLayoutAlgorithmTest.PopulateContentAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4163 | GridLanesLayoutAlgorithmTest.PopulateRowContentAlignedBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4191 | GridLanesLayoutAlgorithmTest.PopulateColumnFillAndTrackReverseBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4236 | GridLanesLayoutAlgorithmTest.PopulateRowFillAndTrackReverseBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4281 | GridLanesLayoutAlgorithmTest.PopulateIndefiniteFillReverseBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| layout_box_test.cc:45 | LayoutBoxTest.BackgroundIsKnownToBeObscured | behaviour | blocked | needs LayoutBox background/foreground obscuration paint model |
| layout_box_test.cc:59 | LayoutBoxTest.BackgroundNotObscuredWithCssClippedChild | behaviour | blocked | needs LayoutBox background/foreground obscuration paint model |
| layout_box_test.cc:88 | LayoutBoxTest.BackgroundNotObscuredWithCssClippedGrandChild | behaviour | blocked | needs LayoutBox background/foreground obscuration paint model |
| layout_box_test.cc:127 | LayoutBoxTest.ForegroundIsKnownToBeOpaqueInRect | behaviour | blocked | needs LayoutBox background/foreground obscuration paint model |
| layout_box_test.cc:161 | LayoutBoxTest.ForegroundIsKnownToBeOpaqueInRectVerticalRL | behaviour | blocked | needs LayoutBox background/foreground obscuration paint model |
| layout_box_test.cc:197 | LayoutBoxTest.BackgroundRect | behaviour | blocked | needs LayoutBox background/foreground obscuration paint model |
| layout_box_test.cc:356 | LayoutBoxTest.LocationContainer | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:386 | LayoutBoxTest.TopLeftLocationFlipped | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:401 | LayoutBoxTest.TableRowCellTopLeftLocationFlipped | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:435 | LayoutBoxTest.LocationContainerOfSVG | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:465 | LayoutBoxTest.ControlClip | geometry | blocked | needs LayoutBox geometry model |
| layout_box_test.cc:482 | LayoutBoxTest.VisualOverflowRectWithBlockChild | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:494 | LayoutBoxTest.VisualOverflowRectWithLegacyChild | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:506 | LayoutBoxTest.VisualOverflowRectWithMask | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:522 | LayoutBoxTest.VisualOverflowRectWithMaskAndOverflowHidden | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:538 | LayoutBoxTest.VisualOverflowRectWithMaskWithOutset | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:555 | LayoutBoxTest.VisualOverflowRectWithMaskWithOutsetAndOverflowHidden | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:572 | LayoutBoxTest.VisualOverflowRectOverflowHidden | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:587 | LayoutBoxTest.VisualOverflowRectOverflowClip | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:623 | LayoutBoxTest.VisualOverflowRectWithOverflowClipMargin | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:670 | LayoutBoxTest.ContentsVisualOverflowPropagation | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:717 | LayoutBoxTest.HitTestOverflowClipMargin | behaviour | blocked | needs LayoutBox hit-testing model |
| layout_box_test.cc:737 | LayoutBoxTest.HitTestContainPaint | behaviour | blocked | needs LayoutBox hit-testing model |
| layout_box_test.cc:751 | LayoutBoxTest.OverflowRectsContainPaint | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:769 | LayoutBoxTest.OverflowRectsOverflowHidden | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:787 | LayoutBoxTest.SetTextFieldIntrinsicInlineSize | geometry | blocked | needs LayoutBox geometry model |
| layout_box_test.cc:816 | LayoutBoxTest.DelayedInvalidation | behaviour | blocked | needs LayoutBox layout/overflow invalidation tracking |
| layout_box_test.cc:849 | LayoutBoxTest.DelayedInvalidationLayoutViewScrolled | behaviour | blocked | needs LayoutBox layout/overflow invalidation tracking |
| layout_box_test.cc:891 | LayoutBoxTest.MarkerContainerScrollableOverflowRect | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:934 | LayoutBoxTest.LocationOfAbsoluteChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:990 | LayoutBoxTest.LocationOfAbsoluteChildWithContainerScrollbarsDifferentWritingModes | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1039 | LayoutBoxTest.LocationOfAbsoluteAutoTopLeftChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1103 | LayoutBoxTest.LocationOfAbsoluteAutoTopLeftGrandChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1165 | LayoutBoxTest.LocationOfInFlowChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1234 | LayoutBoxTest.LocationOfRelativeChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1289 | LayoutBoxTest.LocationOfFloatLeftChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1345 | LayoutBoxTest.LocationOfFloatRightChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1405 | LayoutBoxTest.GeometriesWithScrollbarsNonScrollable | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1500 | LayoutBoxTest.GeometriesWithScrollbarsScrollable | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1624 | LayoutBoxTest.ThickScrollbarSubpixelSizeMarginNoDirtyLayoutAfterLayout | internal | internal | checks LayoutBox internal flag/crash regression |
| layout_box_test.cc:1652 | LayoutBoxTest.MenuListIntrinsicBlockSize | geometry | blocked | needs LayoutBox geometry model |
| layout_box_test.cc:1664 | LayoutBoxTest.HasReflection | geometry | blocked | needs LayoutBox geometry model |
| layout_box_test.cc:1693 | LayoutBoxTest.VisualOverflowRectIncludingFilters | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:1709 | LayoutBoxTest.SetNeedsOverflowRecalcLayoutBox | behaviour | blocked | needs LayoutBox layout/overflow invalidation tracking |
| layout_box_test.cc:1732 | LayoutBoxTest.SetNeedsOverflowRecalcFlexBox | behaviour | blocked | needs LayoutBox layout/overflow invalidation tracking |
| layout_box_test.cc:1755 | LayoutBoxTest.ScrollsWithViewportRelativePosition | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1760 | LayoutBoxTest.ScrollsWithViewportFixedPosition | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1765 | LayoutBoxTest.ScrollsWithViewportFixedPositionInsideTransform | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1775 | LayoutBoxTest.HitTestResizerWithTextAreaChild | behaviour | blocked | needs LayoutBox hit-testing model |
| layout_box_test.cc:1790 | LayoutBoxTest.HitTestResizerStackedWithTextAreaChild | behaviour | blocked | needs LayoutBox hit-testing model |
| layout_box_test.cc:1805 | LayoutBoxTest.AnchorInFragmentedContainingBlock | geometry | blocked | needs CSS anchor positioning in fragmented/inline containing block |
| layout_box_test.cc:1849 | LayoutBoxTest.AnchorInInlineContainingBlock | geometry | blocked | needs CSS anchor positioning in fragmented/inline containing block |
| layout_box_test.cc:1869 | LayoutBoxTest.AnchorInInlineContainingBlockWithNameConflicts | geometry | blocked | needs CSS anchor positioning in fragmented/inline containing block |
| layout_box_test.cc:1906 | LayoutBoxTest.IsUserScrollable | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1935 | LayoutBoxTest.IsUserScrollableLayoutView | behaviour | blocked | needs LayoutBox scrollable area and scrollbar geometry model |
| layout_box_test.cc:1957 | LayoutBoxTest.LogicalRectInContainer | geometry | blocked | needs LayoutBox geometry model |
| layout_box_test.cc:2006 | LayoutBoxTest.VisualOverflowRectWithEmptyInlineChildAndReflectAndOutline | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:2033 | LayoutBoxTest.ContentBoxFragmentedHtb | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2045 | LayoutBoxTest.ContentBoxFragmentedVlr | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2057 | LayoutBoxTest.ContentBoxFragmentedVrl | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2069 | LayoutBoxTest.StitchedBlockSize | geometry | formalized | `TestsBlock.StitchedBlockSize_vectors`, `BlockFlow.fragmentation_conserves_size` |
| layout_box_test.cc:2087 | LayoutBoxTest.StitchedBlockSizeVrl | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2105 | LayoutBoxTest.StitchedSizeWithOverflow | geometry | formalized | `TestsBlock.StitchedSizeWithOverflow_vectors` |
| layout_box_test.cc:2124 | LayoutBoxTest.StitchedSizeWithOverflowVrl | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2143 | LayoutBoxTest.StitchedSizeAfterRelayout | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2166 | LayoutBoxTest.StitchedSizeRepeatedWhenPrinting | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2232 | LayoutBoxBackgroundPaintLocationTest.ContentBoxClipZeroPadding | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2245 | LayoutBoxBackgroundPaintLocationTest.AttachmentLocalContentBoxClipNonZeroPadding | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2259 | LayoutBoxBackgroundPaintLocationTest.NonLocalImage | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2274 | LayoutBoxBackgroundPaintLocationTest.LocalImageAndColor | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2288 | LayoutBoxBackgroundPaintLocationTest.LocalImageAndNonLocalClipPaddingColor | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2306 | LayoutBoxBackgroundPaintLocationTest.LocalImageAndNonLocalClipContentColorNonZeroPadding | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2323 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorNoBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2335 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorSolidBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2349 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorSolidBorderWithBorderShape | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2365 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorTranslucentBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2381 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorDashedBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2395 | LayoutBoxBackgroundPaintLocationTest.ContentClipColorZeroPadding | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2407 | LayoutBoxBackgroundPaintLocationTest.ContentClipColorNonZeroPadding | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2420 | LayoutBoxBackgroundPaintLocationTest.CustomScrollbar | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2438 | LayoutBoxBackgroundPaintLocationTest.TranslucentColorAndTranslucentBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2454 | LayoutBoxBackgroundPaintLocationTest.LocalImageTranslucentColorAndTransparentBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2471 | LayoutBoxBackgroundPaintLocationTest.InsetBoxShadow | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2485 | LayoutBoxBackgroundPaintLocationTest.OutsetBoxShadow | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2496 | LayoutBoxBackgroundPaintLocationTest.BorderImage | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2509 | LayoutBoxBackgroundPaintLocationTest.ElasticOverscrollEnabledForSubscroll | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2560 | LayoutBoxBackgroundPaintLocationTest.ElasticOverscrollSupportedForLayoutView | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_model_object_test.cc:48 | LayoutBoxModelObjectTest.LocalCaretRectForEmptyElementVertical | behaviour | blocked | model lacks caret rect geometry for vertical writing modes |
| layout_box_model_object_test.cc:143 | LayoutBoxModelObjectTest.StickyPositionConstraints | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:184 | LayoutBoxModelObjectTest.StickyPositionVerticalRLConstraints | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:225 | LayoutBoxModelObjectTest.StickyPositionInlineConstraints | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:275 | LayoutBoxModelObjectTest.StickyPositionVerticalRLInlineConstraints | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:330 | LayoutBoxModelObjectTest.StickyPositionTransforms | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:368 | LayoutBoxModelObjectTest.StickyPositionPercentageStyles | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:410 | LayoutBoxModelObjectTest.StickyPositionContainerIsScroller | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:440 | LayoutBoxModelObjectTest.SingleAxisScrollerPositionStickyUseCount | internal | internal | Blink use counter check |
| layout_box_model_object_test.cc:490 | LayoutBoxModelObjectTest.NoSingleAxisScrollerPositionStickyUseCountWhenDisabled | internal | internal | Blink use counter check |
| layout_box_model_object_test.cc:506 | LayoutBoxModelObjectTest.StickyPositionAnonymousContainer | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:540 | LayoutBoxModelObjectTest.StickyPositionTableContainers | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:571 | LayoutBoxModelObjectTest.StickyPositionConstraintInvalidation | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:610 | LayoutBoxModelObjectTest.StickyPositionStatusChange | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:701 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectStickyBoxShiftingAncestor | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:764 | LayoutBoxModelObjectTest.StickyPositionInlineBlockUnderStickyInline | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:805 | LayoutBoxModelObjectTest.StickyPositionFindsNearestStickyInlineForBlockChild | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:843 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectContainingBlockShiftingAncestor | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:905 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectContainingBlockShiftingAncestorRoot | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:940 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectContainingBlockShiftingAncestorTable | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:974 | LayoutBoxModelObjectTest.StickyPositionNested | geometry | blocked | model lacks nested sticky position offsets |
| layout_box_model_object_test.cc:1005 | LayoutBoxModelObjectTest.StickyPositionChildHasLargerTop | geometry | blocked | model lacks nested sticky position offsets |
| layout_box_model_object_test.cc:1036 | LayoutBoxModelObjectTest.StickyPositionParentHasLargerTop | geometry | blocked | model lacks nested sticky position offsets |
| layout_box_model_object_test.cc:1067 | LayoutBoxModelObjectTest.StickyPositionChildPushingOutsideParent | geometry | blocked | model lacks nested sticky position offsets |
| layout_box_model_object_test.cc:1100 | LayoutBoxModelObjectTest.StickyPositionTripleNestedDiv | geometry | blocked | model lacks nested sticky position offsets |
| layout_box_model_object_test.cc:1138 | LayoutBoxModelObjectTest.StickyPositionNestedStickyTable | geometry | blocked | model lacks nested sticky table offsets |
| layout_box_model_object_test.cc:1197 | LayoutBoxModelObjectTest.StickyPositionComplexTableNesting | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:1230 | LayoutBoxModelObjectTest.StickyPositionNestedInlineElements | geometry | blocked | model lacks nested sticky inline offsets |
| layout_box_model_object_test.cc:1268 | LayoutBoxModelObjectTest.StickyPositionNestedFixedPos | geometry | blocked | model lacks nested sticky fixed position offsets |
| layout_box_model_object_test.cc:1364 | LayoutBoxModelObjectTest.InvalidatePaintLayerOnStackedChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1406 | LayoutBoxModelObjectTest.BackfaceVisibilityChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1434 | LayoutBoxModelObjectTest.ChangingFilterWithWillChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1465 | LayoutBoxModelObjectTest.ChangingWillChangeFilter | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1500 | LayoutBoxModelObjectTest.ChangingBackdropFilterWithWillChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1531 | LayoutBoxModelObjectTest.ChangingWillChangeBackdropFilter | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1566 | LayoutBoxModelObjectTest.UpdateStackingContextForOption | internal | internal | Blink option element stacking context check |
| layout_box_model_object_test.cc:1589 | LayoutBoxModelObjectTest.StickyParentContainStrictChangeOverflowProperty | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:1618 | LayoutBoxModelObjectTest.RemoveStickyUnderContain | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:1643 | LayoutBoxModelObjectTest.ChangeStickyStatusUnderContain | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:1671 | LayoutBoxModelObjectTest.ChangeStickyStatusKeepLayerUnderContain | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:1700 | LayoutBoxModelObjectTest.RemoveStickyStatusInNestedStickyElementsWithContain | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_object_test.cc:77 | LayoutObjectTest.CommonAncestor | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:131 | LayoutObjectTest.OwnerNodeId | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:160 | LayoutObjectTest.LayoutDecoratedNameCalledWithPositionedObject | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:172 | LayoutObjectTest.DisplayNoneCreateObject | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:177 | LayoutObjectTest.DisplayBlockCreateObject | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:186 | LayoutObjectTest.DisplayInlineBlockCreateObject | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:195 | LayoutObjectTest.BackdropFilterAsGroupingProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:217 | LayoutObjectTest.BlendModeAsGroupingProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:234 | LayoutObjectTest.CSSClipAsGroupingProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:257 | LayoutObjectTest.ClipPathAsGroupingProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:274 | LayoutObjectTest.IsolationAsGroupingProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:291 | LayoutObjectTest.MaskAsGroupingProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:309 | LayoutObjectTest.UseCountGridLanesLayout | internal | internal | Blink use counter check |
| layout_object_test.cc:335 | LayoutObjectTest.UseCountContainWithoutContentVisibility | internal | internal | Blink use counter check |
| layout_object_test.cc:383 | LayoutObjectTest.ContainingBoxLayoutViewShouldBeNull | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:387 | LayoutObjectTest.ContainingBoxBodyShouldBeDocumentElement | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:392 | LayoutObjectTest.ContainingBoxDocumentElementShouldBeLayoutView | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:397 | LayoutObjectTest.ContainingBoxStaticLayoutObjectShouldBeParent | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:404 | LayoutObjectTest.ContainingBoxAbsoluteLayoutObjectShouldBeLayoutView | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:411 | LayoutObjectTest.ContainingBoxAbsoluteLayoutObjectShouldBeNonStaticallyPositionedBlockAncestor | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:438 | LayoutObjectTest.ContainingBoxFixedPosUnderFlattened3D | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:450 | LayoutObjectTest.ContainingBoxFixedLayoutObjectInTransformedDiv | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:473 | LayoutObjectTest.ContainingBoxFixedLayoutObjectInBody | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:487 | LayoutObjectTest.ContainingBoxAbsoluteLayoutObjectInBody | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:501 | LayoutObjectTest.ContainingBoxAbsoluteLayoutObjectShouldNotBeNonStaticallyPositionedInlineAncestor | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:533 | LayoutObjectTest.PaintingLayerOfOverflowClipLayerUnderColumnSpanAll | behaviour | blocked | model lacks paint layer hierarchy under column span |
| layout_object_test.cc:549 | LayoutObjectTest.FloatUnderBlock | behaviour | blocked | model lacks floats |
| layout_object_test.cc:570 | LayoutObjectTest.InlineFloatMismatch | behaviour | blocked | model lacks floats |
| layout_object_test.cc:584 | LayoutObjectTest.FloatUnderInline | behaviour | blocked | model lacks floats |
| layout_object_test.cc:616 | LayoutObjectTest.MutableForPaintingClearPaintFlags | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:650 | LayoutObjectTest.DelayFullPaintInvalidation | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:673 | LayoutObjectTest.SubtreeAndDelayFullPaintInvalidation | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:693 | LayoutObjectTest.NoPaintInvalidationWhileStayingInvisible | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:725 | LayoutObjectTest.VisibleDescendantOfInvisibleObjectStillInvalidates | internal | internal | Blink LayoutObject internal check |
| layout_object_test.cc:748 | LayoutObjectTest.PaintInvalidationWhileStayingInvisibleKillSwitch | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:765 | LayoutObjectTest.SubtreePaintPropertyUpdateReasons | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:781 | LayoutObjectTest.ShouldCheckLayoutForPaintInvalidation | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:850 | LayoutObjectTest.AssociatedLayoutObjectOfFirstLetterPunctuations | behaviour | blocked | model lacks first-letter layout object split |
| layout_object_test.cc:877 | LayoutObjectTest.AssociatedLayoutObjectOfFirstLetterSplit | behaviour | blocked | model lacks first-letter layout object split |
| layout_object_test.cc:899 | LayoutObjectTest.AssociatedLayoutObjectOfFirstLetterWithTrailingWhitespace | behaviour | blocked | model lacks first-letter layout object split |
| layout_object_test.cc:929 | LayoutObjectTest.DisplayContentsInlineWrapper | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:938 | LayoutObjectTest.DisplayContentsNoInlineWrapper | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:947 | LayoutObjectTest.DisplayContentsAddInlineWrapper | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:960 | LayoutObjectTest.DisplayContentsRemoveInlineWrapper | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:973 | LayoutObjectTest.DisplayContentsWrapperPerTextNode | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:995 | LayoutObjectTest.DisplayContentsWrapperInTable | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1021 | LayoutObjectTest.DisplayContentsWrapperInTableSection | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1047 | LayoutObjectTest.DisplayContentsWrapperInTableRow | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1073 | LayoutObjectTest.DisplayContentsWrapperInTableCell | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1094 | LayoutObjectTest.DumpLayoutObject | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1125 | LayoutObjectTest.DumpDestroyedLayoutObject | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1146 | LayoutObjectTest.DisplayContentsSVGGElementInHTML | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1164 | LayoutObjectTest.HasDistortingVisualEffects | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1204 | LayoutObjectTest.DistortingVisualEffectsUnaliases | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1221 | LayoutObjectTest.UpdateVisualRectAfterAncestorLayout | behaviour | blocked | model lacks visual rect ancestor layout update |
| layout_object_test.cc:1259 | LayoutObjectSimTest.TouchActionUpdatesSubframeEventHandler | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1318 | LayoutObjectSimTest.HitTestForOcclusionInIframe | behaviour | blocked | model lacks hit testing |
| layout_object_test.cc:1347 | LayoutObjectSimTest.FirstLineBackgroundImage | internal | internal | Blink LayoutObject internal check |
| layout_object_test.cc:1403 | LayoutObjectTest.FirstLineBackgroundImageNestedCrash | internal | internal | Blink crash regression test |
| layout_object_test.cc:1418 | LayoutObjectTest.FirstLineBackgroundImageAddBlockBackgroundImageCrash | internal | internal | Blink crash regression test |
| layout_object_test.cc:1435 | LayoutObjectTest.FirstLineBackgroundImageChangeStyleCrash | internal | internal | Blink crash regression test |
| layout_object_test.cc:1459 | LayoutObjectSimTest.FirstLineBackgroundImageDirtyStyleCrash | internal | internal | Blink crash regression test |
| layout_object_test.cc:1505 | LayoutObjectTest.NeedsScrollableOverflowRecalc | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1534 | LayoutObjectTest.ContainValueIsRelayoutBoundary | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1551 | LayoutObjectTest.PerspectiveIsNotParent | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1573 | LayoutObjectTest.PerspectiveWithAnonymousTable | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1593 | LayoutObjectTest.LocalToAncestoRectIgnoreAncestorScroll | behaviour | blocked | model lacks coordinate mapping across scroll containers |
| layout_object_test.cc:1619 | LayoutObjectTest.LocalToAncestoRectViewIgnoreAncestorScroll | behaviour | blocked | model lacks coordinate mapping across scroll containers |
| layout_object_test.cc:1642 | LayoutObjectTest.LocalToAncestoRectIgnoreAncestorScrollIntermediateScroller | behaviour | blocked | model lacks coordinate mapping across scroll containers |
| layout_object_test.cc:1676 | LayoutObjectTest.LocalToAncestoRectViewIgnoreAncestorScrollIntermediateScroller | behaviour | blocked | model lacks coordinate mapping across scroll containers |
| layout_object_test.cc:1708 | LayoutObjectTest.SetNeedsCollectInlinesForSvgText | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1724 | LayoutObjectTest.SetNeedsCollectInlinesForSvgInline | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1737 | LayoutObjectTest.RemovePendingTransformUpdatesCorrectly | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1764 | LayoutObjectTestWithCompositing.UseCountDifferentPerspectiveCBOrParent | internal | internal | Blink use counter check |
| layout_object_test.cc:1841 | LayoutObjectTest.HasTransformRelatedProperty | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1887 | LayoutObjectTest.ContainingScrollContainer | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1927 | LayoutObjectTest.ContainingScrollContainerSingleAxis | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:1946 | LayoutObjectTest.ScrollOffsetMapping | behaviour | blocked | model lacks scroll offset coordinate mapping |
| layout_object_test.cc:1983 | LayoutObjectTest.QuadsInAncestor_Block | behaviour | blocked | model lacks nested multicolumn coordinate mapping |
| layout_object_test.cc:2044 | LayoutObjectTest.QuadsInAncestor_Inline | behaviour | blocked | inline lane (model lacks inline text line quad mapping) |
| layout_object_test.cc:2099 | LayoutObjectTest.GeneratingNode | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:2166 | LayoutObjectTest.NoEllipsisForAnonymousBlockWithNonBlockParent | behaviour | blocked | model lacks text-overflow ellipsis |
| layout_object_test.cc:2205 | LayoutObjectTest.InCanvasSubtree | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_object_test.cc:2280 | LayoutObjectTest.MAYBE_Depth | internal | internal | Blink LayoutObject tree/property plumbing check |
| layout_view_test.cc:25 | LayoutViewTest.UpdateCountersLayout | behaviour | blocked | model lacks CSS counters layout |
| layout_view_test.cc:48 | LayoutViewTest.DisplayNoneFrame | internal | internal | Blink display:none iframe LayoutView creation check |
| layout_view_test.cc:72 | LayoutViewTest.NamedPages | geometry | blocked | model lacks @page named page pagination |
| layout_view_test.cc:122 | LayoutViewTest.NamedPagesAbsPos | geometry | blocked | model lacks @page named page pagination |
| layout_view_test.cc:197 | LayoutViewHitTestTest.BlockInInlineBelowBottom | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:242 | LayoutViewHitTestTest.BlockInInlineWithListItem | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:287 | LayoutViewHitTestTest.EmptySpan | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:316 | LayoutViewHitTestTest.FlexBlockChildren | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:345 | LayoutViewHitTestTest.FlexBlockEditableChildren | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:370 | LayoutViewHitTestTest.FloatLeftLeft | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:405 | LayoutViewHitTestTest.FloatLeftMiddle | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:440 | LayoutViewHitTestTest.FloatLeftRight | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:475 | LayoutViewHitTestTest.FloatRightLeft | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:521 | LayoutViewHitTestTest.FloatRightMiddle | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:559 | LayoutViewHitTestTest.FloatRightRight | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:593 | LayoutViewHitTestTest.PositionAbsolute | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:632 | LayoutViewHitTestTest.HitTestHorizontal | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:747 | LayoutViewHitTestTest.HitTestVerticalLR | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:857 | LayoutViewHitTestTest.HitTestVerticalRL | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:980 | LayoutViewHitTestTest.HitTestVerticalRLRoot | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1070 | LayoutViewHitTestTest.PseudoElementAfterBlock | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1095 | LayoutViewHitTestTest.PseudoElementAfterInline | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1124 | LayoutViewHitTestTest.PseudoElementAfterBlockWithMargin | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1151 | LayoutViewHitTestTest.ScrolledBlockChildren | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1190 | LayoutViewHitTestTest.ScrolledInlineChildren | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1263 | LayoutViewHitTestTest.TextAndInputsWithRtlDirection | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1353 | LayoutViewHitTestTest.TextCombineOneTextNode | behaviour | blocked | model lacks hit testing engine |
| layout_view_test.cc:1399 | LayoutViewHitTestTest.TextCombineTwoTextNodes | behaviour | blocked | model lacks hit testing engine |
| layout_result_caching_test.cc:51 | LayoutResultCachingTest.HitDifferentExclusionSpace | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:84 | LayoutResultCachingTest.HitDifferentBFCOffset | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:144 | LayoutResultCachingTest.HitDifferentBFCOffsetSameMarginStrut | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:170 | LayoutResultCachingTest.MissDescendantAboveBlockStart1 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:204 | LayoutResultCachingTest.MissDescendantAboveBlockStart2 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:238 | LayoutResultCachingTest.HitOOFDescendantAboveBlockStart | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:272 | LayoutResultCachingTest.HitLineBoxDescendantAboveBlockStart | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:311 | LayoutResultCachingTest.MissFloatInitiallyIntruding1 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:343 | LayoutResultCachingTest.MissFloatInitiallyIntruding2 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:375 | LayoutResultCachingTest.MissFloatWillIntrude1 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:406 | LayoutResultCachingTest.MissFloatWillIntrude2 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:437 | LayoutResultCachingTest.HitPushedByFloats1 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:468 | LayoutResultCachingTest.HitPushedByFloats2 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:499 | LayoutResultCachingTest.MissPushedByFloats1 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:531 | LayoutResultCachingTest.MissPushedByFloats2 | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:563 | LayoutResultCachingTest.HitDifferentRareData | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:588 | LayoutResultCachingTest.HitPercentageMinWidth | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:613 | LayoutResultCachingTest.HitFixedMinWidth | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:638 | LayoutResultCachingTest.HitShrinkToFit | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:685 | LayoutResultCachingTest.MissShrinkToFit | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:765 | LayoutResultCachingTest.HitShrinkToFitSameIntrinsicSizes | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:796 | LayoutResultCachingTest.HitShrinkToFitDifferentParent | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:826 | LayoutResultCachingTest.MissQuirksModePercentageBasedChild | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:856 | LayoutResultCachingTest.HitQuirksModePercentageBasedParentAndChild | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:891 | LayoutResultCachingTest.HitStandardsModePercentageBasedChild | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:920 | LayoutResultCachingTest.ChangeTableCellBlockSizeConstrainedness | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:979 | LayoutResultCachingTest.OptimisticFloatPlacementNoRelayout | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1003 | LayoutResultCachingTest.SelfCollapsingShifting | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1078 | LayoutResultCachingTest.ClearancePastAdjoiningFloatsMovement | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1136 | LayoutResultCachingTest.MarginStrutMovementSelfCollapsing | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1199 | LayoutResultCachingTest.MarginStrutMovementInFlow | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1286 | LayoutResultCachingTest.MarginStrutMovementPercentage | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1321 | LayoutResultCachingTest.HitIsFixedBlockSizeIndefinite | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1350 | LayoutResultCachingTest.MissIsFixedBlockSizeIndefinite | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1380 | LayoutResultCachingTest.HitColumnFlexBoxMeasureAndLayout | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1433 | LayoutResultCachingTest.HitRowFlexBoxMeasureAndLayout | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1488 | LayoutResultCachingTest.MissFlexReplaced | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1516 | LayoutResultCachingTest.HitFlexDefiniteChange | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1539 | LayoutResultCachingTest.HitOrthogonalRoot | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1562 | LayoutResultCachingTest.SimpleTable | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1592 | LayoutResultCachingTest.MissTableCellMiddleAlignment | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1615 | LayoutResultCachingTest.MissTableCellBottomAlignment | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1638 | LayoutResultCachingTest.HitTableCellBaselineAlignment | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1661 | LayoutResultCachingTest.MissTableCellBaselineAlignment | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1687 | LayoutResultCachingTest.MissTablePercent | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1718 | LayoutResultCachingTest.HitTableRowAdd | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1739 | LayoutResultCachingTest.MissTableRowAdd | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1760 | LayoutResultCachingTest.HitTableRowRemove | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1781 | LayoutResultCachingTest.MissTableRowRemove | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1802 | LayoutResultCachingTest.HitTableSectionAdd | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1823 | LayoutResultCachingTest.HitTableSectionRemove | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1844 | LayoutResultCachingTest.FragmentainerSizeChange | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1921 | LayoutResultCachingTest.BlockOffsetChangeInFragmentainer | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1963 | LayoutResultCachingTest.BfcRootBlockOffsetChangeInFragmentainer | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:2005 | LayoutResultCachingTest.HitBlockOffsetUnchangedInFragmentainer | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:2035 | LayoutResultCachingTest.HitNewFormattingContextInFragmentainer | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:2066 | LayoutResultCachingTest.MissMonolithicChangeInFragmentainer | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:2092 | LayoutResultCachingTest.MissGridIncorrectIntrinsicSize | behaviour | blocked | model lacks incremental layout result caching |
| ink_overflow_test.cc:30 | InkOverflowTest.Empty | internal | internal | Blink InkOverflow union struct compaction check |
| ink_overflow_test.cc:118 | RectDataTest.Self | internal | internal | Blink InkOverflow union struct compaction check |
| ink_overflow_test.cc:129 | RectDataTest.Contents | internal | internal | Blink InkOverflow union struct compaction check |
| ink_overflow_test.cc:140 | RectDataTest.Copy | internal | internal | Blink InkOverflow union struct compaction check |
| ink_overflow_test.cc:172 | SelfAndContentsDataTest.SelfAndContents | internal | internal | Blink InkOverflow union struct compaction check |
| outline_rect_collector_test.cc:14 | OutlineRectCollectorTest.Empty | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:23 | OutlineRectCollectorTest.AddRect | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:57 | OutlineRectCollectorTest.CombineWithOffset | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:85 | OutlineRectCollectorTest.AddEmptyRect | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:107 | OutlineRectCollectorTest.UnionCombineWithEmptyRects | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:122 | OutlineRectCollectorTest.VectorCombineWithEmptyRects | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:164 | OutlineRectCollectorRenderingTest.CombineWithAncestor | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:205 | OutlineRectCollectorRenderingTest.UnionCombineWithEmptyRects | internal | internal | Blink outline rect collector accumulator check |
| outline_rect_collector_test.cc:220 | OutlineRectCollectorRenderingTest.VectorCombineWithEmptyRects | internal | internal | Blink outline rect collector accumulator check |
| scrollbars_test.cc:361 | ScrollbarsTest.DocumentStyleRecalcPreservesScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:386 | ScrollbarsTest.ScrollbarsUpdatedOnOverlaySettingsChange | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:405 | ScrollbarsTestWithOwnWebViewHelper.ScrollbarSizeF | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:467 | ScrollbarsTest.CustomScrollbarsCauseLayoutOnExistenceChange | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:518 | ScrollbarsTest.TransparentBackgroundUsesLightOverlayColorScheme | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:543 | ScrollbarsTest.BodyBackgroundChangesOverlayColorTheme | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:573 | ScrollbarsTest.OverlayScrollbarChangeToDisplayNoneDynamically | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:643 | ScrollbarsTest.OverlayScrolblarNotCreatedInUnscrollableAxis | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:680 | ScrollbarsTest.HidingScrollbarsOnScrollableAreaDisablesScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:751 | ScrollbarsTest.MouseOverScrollbarInCustomCursorElement | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:799 | ScrollbarsTest.MouseOverCustomScrollbarInCustomCursorElement | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:855 | ScrollbarsTest.MouseOverCustomScrollbarWithCustomCursor | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:908 | ScrollbarsTest.MouseOverCustomScrollbarThumbWithCustomCursor | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:969 | ScrollbarsTest.MouseOverCustomScrollbarTrackPieceWithCustomCursor | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1052 | ScrollbarsTest.MouseOverCustomScrollbarTrackPieceWithoutStyle | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1121 | ScrollbarsTest.MouseOverCustomScrollbarTrackPieceBothTrackAndTrackPieceWithoutStyle | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1183 | ScrollbarsTest.MouseOverCustomScrollbarButtonTrackWithCustomCursor | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1252 | ScrollbarsTest.MouseOverCustomScrollbarCornerTrackWithCustomCursor | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1316 | ScrollbarsTest.MouseOverCustomScrollbarCornerFrame | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1365 | ScrollbarsTest.MouseOverLinkAndOverlayScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1456 | ScrollbarsTest.MouseOverCustomScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1523 | ScrollbarsTest.MouseOverScrollbarAndIFrame | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1613 | ScrollbarsTest.MouseOverScrollbarAndParentElement | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1700 | ScrollbarsTest.MouseOverRootScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1736 | ScrollbarsTest.MouseReleaseUpdatesScrollbarHoveredPart | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1800 | ScrollbarsTest.ContextMenuUpdatesScrollbarPressedPart | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1851 | ScrollbarsTest.CustomScrollbarInOverlayScrollbarThemeWillNotCauseDCHECKFails | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1880 | ScrollbarsTest.CustomScrollbarChangeToMobileByEmulator | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:1962 | ScrollbarsTest.CustomScrollbarWhenStyleOwnerChange | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2018 | ScrollbarsTestWithVirtualTimer.DISABLED_TestNonCompositedOverlayScrollbarsFade | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2021 | ScrollbarsTestWithVirtualTimer.TestNonCompositedOverlayScrollbarsFade | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2133 | ScrollbarAppearanceTest.DISABLED_NativeScrollbarChangeToMobileByEmulator | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2136 | ScrollbarAppearanceTest.NativeScrollbarChangeToMobileByEmulator | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2229 | ScrollbarAppearanceTest.ThemeEngineDefinesMinimumThumbLength | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2256 | ScrollbarAppearanceTest.HugeScrollingThumbPosition | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2295 | ScrollbarAppearanceTest.CustomScrollbarUseThemeEngineMinimumThumbLength | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2343 | ScrollbarsTest.WideBodyShouldNotHaveScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2367 | ScrollbarsTest.TallBodyShouldNotHaveScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2392 | ScrollbarsTest.TallAndWideBodyShouldNotHaveScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2417 | ScrollbarsTest.BodySizeEqualWindowSizeShouldNotHaveScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2442 | ScrollbarsTest.WidePercentageBodyShouldHaveScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2468 | ScrollbarsTest.WidePercentageAndTallBodyShouldHaveScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2494 | ScrollbarsTest.TallPercentageBodyShouldHaveScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2520 | ScrollbarsTest.TallPercentageAndWideBodyShouldHaveScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2546 | ScrollbarsTest.TallAndWidePercentageBodyShouldHaveScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2570 | ScrollbarsTest.MouseOverIFrameScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2622 | ScrollbarsTest.AutosizeTest | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2690 | ScrollbarsTest.AutosizeHeightOverflowWithOverlayScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2730 | ScrollbarsTest.AutosizeAlmostRemovableScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2770 | ScrollbarsTest.AutosizeExpandingContentScrollable | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2801 | ScrollbarsTest.HideTheOverlayScrollbarNotCrashAfterPLSADisposedPaintLayer | internal | internal | Blink crash regression test |
| scrollbars_test.cc:2846 | ScrollbarsTest.PLSADisposeShouldClearPointerInLayers | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2881 | ScrollbarsTest.OverlayScrollbarHitTest | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2941 | ScrollbarsTest.RecorderedOverlayScrollbarHitTest | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:2972 | ScrollbarsTest.AllowMiddleButtonPressOnScrollbarWhenDisableMiddleClickAutoScroll | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3007 | ScrollbarsTest.NotAllowMiddleButtonPressOnScrollbarWhenEnableMiddleClickAutoScroll | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3042 | ScrollbarsTest.NotAllowNonLeftButtonPressOnScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3077 | ScrollbarsTest.MiddleDownShouldNotAffectScrollbarPress | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3131 | ScrollbarsTest.UseCounterNegativeWhenThumbIsNotScrolledWithMouse | internal | internal | Blink use counter check |
| scrollbars_test.cc:3218 | ScrollbarsTest.UseCounterPositiveWhenThumbIsScrolledWithMouse | internal | internal | Blink use counter check |
| scrollbars_test.cc:3260 | ScrollbarsTest.UseCounterNegativeWhenThumbIsNotScrolledWithTouch | internal | internal | Blink use counter check |
| scrollbars_test.cc:3326 | ScrollbarsTest.UseCounterPositiveWhenThumbIsScrolledWithTouch | internal | internal | Blink use counter check |
| scrollbars_test.cc:3372 | ScrollbarsTest.UseCounterCustomScrollbarPercentSize | internal | internal | Blink use counter check |
| scrollbars_test.cc:3416 | ScrollbarsTest.CheckScrollCornerIfThereIsNoScrollbar | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3467 | ScrollbarsTest.NoNeedsBeginFrameForCustomScrollbarAfterBeginFrame | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3508 | ScrollbarsTest.CustomScrollbarHypotheticalThickness | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3550 | ScrollbarsTestWithVirtualTimer.DISABLED_PressScrollbarButtonOnInfiniteScrolling | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3553 | ScrollbarsTestWithVirtualTimer.PressScrollbarButtonOnInfiniteScrolling | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3746 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInOverlayScrollbarWhenMouseWheelEventMayBeginPhase | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3924 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInOverlayScrollbarWhenMouseWheelEventMayBeginPhaseOnSlottedText | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:3986 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInAllPossiblyChainedOverlayScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4168 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInAllPossiblyChainedOverlayScrollbarsWithWritingMode | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4354 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInAllPossiblyChainedOverlayScrollbarsWithMacScrollbarAnimatorImpl | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4468 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInAllPossiblyChainedOverlayScrollbarsCrossingDocumentBoundaries | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4683 | ScrollbarsTestWithMacScrollbarAnimatorProxy.FadeInOutOverlayScrollbarWhenMouseWheelEventWithScrollbarAnimatorImpl | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4740 | ScrollbarsTest.ScrollableAreaTraversal | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4811 | ScrollbarsTest.ScrollableAreaTraversalCrossingDocumentBoundary | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4939 | ScrollbarTrackMarginsTest.CustomScrollbarFractionalMarginsWillNotCauseDCHECKFailure | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4955 | ScrollbarTrackMarginsTest.CustomScrollbarScaledMarginsWillNotCauseDCHECKFailure | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:4979 | ScrollbarColorSchemeTest.ThemeEnginePaint | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5026 | ScrollbarsTest.ScrollbarGutterWithHorizontalTextAndClassicScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5090 | ScrollbarsTest.ScrollbarGutterWithVerticalTextAndClassicScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5154 | ScrollbarsTest.ScrollbarGutterWithHorizontalTextAndOverlayScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5219 | ScrollbarsTest.ScrollbarGutterWithVerticalTextAndOverlayScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5285 | ScrollbarsTest.ScrollbarGutterBothEdgesKeywordWithClassicScrollbars | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5366 | ScrollbarsTest.ScrollbarsRestoredAfterCapturePaintPreview | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5426 | ScrollbarsTest.OverlayScrollbarsRestoredAfterCapturePaintPreview | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5476 | ScrollbarsTest.CapturePaintPreviewWithScrollbarsEnabled | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5518 | ScrollbarsTest.CapturePaintPreviewWithOverlayScrollbarsEnabled | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scrollbars_test.cc:5563 | ScrollbarsTest.ScrollbarsUsedColorSchemeFollowsOverlayTheme | behaviour | blocked | model lacks scrollbar theme and overlay controller |
| scroll_anchor_test.cc:154 | ScrollAnchorTest.VisualViewportAnchors | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:193 | ScrollAnchorTest.ClearScrollAnchorsOnAncestors | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:219 | ScrollAnchorTest.AncestorClearingWithSiblingReference | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:261 | ScrollAnchorTest.FractionalOffsetsAreRoundedBeforeComparing | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:278 | ScrollAnchorTest.AvoidStickyAnchorWhichMovesWithScroll | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:296 | ScrollAnchorTest.AnchorWithLayerInScrollingDiv | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:329 | ScrollAnchorTest.AnchorWhileDraggingScrollbar | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:385 | ScrollAnchorTest.RemoveScrollerWithLayerInScrollingDiv | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:425 | ScrollAnchorTest.FlexboxDelayedClampingAlsoDelaysAdjustment | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:456 | ScrollAnchorTest.FlexboxDelayedAdjustmentRespectsSANACLAP | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:490 | ScrollAnchorTest.AnchoringDisabledForPrinting | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:507 | ScrollAnchorTest.SerializeAnchorSimple | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:520 | ScrollAnchorTest.SerializeAnchorWithVariousLineHeights | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:628 | ScrollAnchorTest.SerializeAnchorForSvgText | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:668 | ScrollAnchorTest.SerializeAnchorUsesTagname | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:683 | ScrollAnchorTest.SerializeAnchorSetsIsAnchorBit | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:711 | ScrollAnchorTest.SerializeAnchorSetsSavedRelativeOffset | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:728 | ScrollAnchorTest.SerializeAnchorUsesClassname | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:743 | ScrollAnchorTest.SerializeAnchorUsesNthChild | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:758 | ScrollAnchorTest.SerializeAnchorUsesLeastSpecificSelector | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:780 | ScrollAnchorTest.SerializeAnchorWithNoIdAttribute | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:802 | ScrollAnchorTest.SerializeAnchorChangesWithScroll | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:826 | ScrollAnchorTest.SerializeAnchorVerticalWritingMode | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:851 | ScrollAnchorTest.RestoreAnchorVerticalRlWritingMode | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:875 | ScrollAnchorTest.SerializeAnchorQualifiedTagName | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:889 | ScrollAnchorTest.SerializeAnchorLimitsSelectorLength | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:906 | ScrollAnchorTest.SerializeAnchorIgnoresDuplicatedId | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:924 | ScrollAnchorTest.SerializeAnchorFailsForPseudoElement | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:938 | ScrollAnchorTest.SerializeAnchorFailsForShadowDOMElement | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:967 | ScrollAnchorTest.RestoreAnchorSimple | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:989 | ScrollAnchorTest.RestoreAnchorNonTrivialSelector | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1019 | ScrollAnchorTest.RestoreAnchorFailsForInvalidSelectors | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1047 | ScrollAnchorTest.RestoreAnchorSucceedsForNonBoxNonTextElement | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1070 | ScrollAnchorTest.RestoreAnchorSucceedsWhenScriptForbidden | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1087 | ScrollAnchorTest.RestoreAnchorSucceedsWithExistingAnchorObject | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1109 | ScrollAnchorTest.DeleteAnonymousBlockCrash | internal | internal | Blink crash regression test |
| scroll_anchor_test.cc:1126 | ScrollAnchorTest.ClampAdjustsAnchorAnimation | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1166 | ScrollAnchorTest.DynamicMultiColumnCrash | internal | internal | Blink crash regression test |
| scroll_anchor_test.cc:1267 | ScrollAnchorFindInPageTest.FindInPageResultPrioritized | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1315 | ScrollAnchorFindInPageTest.FocusPrioritizedOverFindInPage | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1374 | ScrollAnchorFindInPageTest.FocusedUnderStickyIsSkipped | behaviour | blocked | model lacks scroll anchoring engine |
| scroll_anchor_test.cc:1428 | ScrollAnchorPageTest.SvgRelativeBoundsCrashAfterClearLayoutResults | internal | internal | Blink crash regression test |
| scroll_anchor_test.cc:1460 | ScrollAnchorTest.SuppressScrollAnchorScopeWithNullScroller | behaviour | blocked | model lacks scroll anchoring engine |
| anchor_scope_test.cc:33 | AnchorScopedNameTest.HashInsertDuplicate | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_scope_test.cc:44 | AnchorScopedNameTest.HashDifferentNames | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_scope_test.cc:56 | AnchorScopedNameTest.HashEqualNames | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_scope_test.cc:72 | AnchorScopedNameTest.LookupEmpty | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_scope_test.cc:80 | AnchorScopedNameTest.LookupDeleted | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_scope_test.cc:93 | AnchorScopedNameTest.ElementEquality | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_scope_test.cc:115 | AnchorScopedNameTest.TreeScopeEquality | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:71 | AnchorEvaluatorImplTest.AnchorNameAdd | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:104 | AnchorEvaluatorImplTest.AnchorNameChange | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:141 | AnchorEvaluatorImplTest.AnchorNameRemove | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:175 | AnchorEvaluatorImplTest.BlockFlow | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:221 | AnchorEvaluatorImplTest.Inline | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:284 | AnchorEvaluatorImplTest.OutOfFlow | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:310 | AnchorEvaluatorImplTest.Relative | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:330 | AnchorEvaluatorImplTest.Transform | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:351 | AnchorEvaluatorImplTest.Scroll | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:375 | AnchorEvaluatorImplTest.FragmentedContainingBlock | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:437 | AnchorEvaluatorImplTest.FragmentHasRunningAnchorTransformAnimation | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:446 | AnchorEvaluatorImplTest.FrameViewHasRunningAnchorTransformAnimation | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:45 | AnchorPositionScrollDataTest.HasDataAndScrollAdjustment | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:94 | AnchorPositionScrollDataTest.Detach | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:142 | AnchorPositionScrollDataTest.ScrollerSizeChange | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:205 | AnchorPositionScrollDataTest.ScrollContentSizeChange | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:266 | AnchorPositionScrollDataTest.RelayoutOnScrollEnd | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:327 | AnchorPositionScrollDataTest.RelayoutOnScrollEndSimpleTranslation | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_position_scroll_data_test.cc:392 | AnchorPositionScrollDataTest.ScrollableOverflowDuringAndAfterScroll | behaviour | blocked | model lacks CSS anchor positioning engine |
| layout_shift_tracker_test.cc:44 | LayoutShiftTrackerTest.IgnoreAfterInput | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:63 | LayoutShiftTrackerTest.CompositedShiftBeforeFirstPaint | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:90 | LayoutShiftTrackerTest.IgnoreSVG | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:103 | LayoutShiftTrackerTest.IgnoreAfterChangeEvent | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:133 | LayoutShiftTrackerSimTest.SubframeWeighting | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:186 | LayoutShiftTrackerSimTest.ViewportSizeChange | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:220 | LayoutShiftTrackerSimTest.ZoomLevelChange | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:351 | LayoutShiftTrackerNavigationTest.BrowserInitiatedSameDocumentHistoryNavigation | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:356 | LayoutShiftTrackerNavigationTest.RendererInitiatedSameDocumentHistoryNavigation | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:437 | LayoutShiftTrackerPointerdownTest.PointerdownBecomesTap | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:441 | LayoutShiftTrackerPointerdownTest.PointerdownCancelled | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:445 | LayoutShiftTrackerPointerdownTest.PointerdownBecomesScroll | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:450 | LayoutShiftTrackerSimTest.MouseMoveDraggingAction | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:543 | LayoutShiftTrackerSimTest.TouchDraggingAction | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:626 | LayoutShiftTrackerSimTest.TouchScrollingAction | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:730 | LayoutShiftTrackerSimTest.MultiplePointerDownUps | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:823 | LayoutShiftTrackerTest.StableCompositingChanges | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:875 | LayoutShiftTrackerTest.CompositedOverflowExpansion | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:938 | LayoutShiftTrackerTest.ContentVisibilityAutoFirstPaint | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:960 | LayoutShiftTrackerTest.ContentVisibilityAutoOffscreenAfterScrollFirstPaint | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:996 | LayoutShiftTrackerTest.ContentVisibilityHiddenFirstPaint | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1016 | LayoutShiftTrackerTest.ContentVisibilityAutoResize | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1040 | LayoutShiftTrackerTest.ContentVisibilityAutoOnscreenAndOffscreenAfterScrollFirstPaint | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1115 | LayoutShiftTrackerTest.NestedFixedPos | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1135 | LayoutShiftTrackerTest.ClipByVisualViewport | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1175 | LayoutShiftTrackerTest.ScrollThenCauseScrollAnchoring | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1217 | LayoutShiftTrackerTest.NeedsToTrack | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_tracker_test.cc:1319 | LayoutShiftTrackerTest.AnimatingTransformCreatesLayoutShiftRoot | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_region_test.cc:14 | LayoutShiftRegionTest.Basic | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_region_test.cc:46 | LayoutShiftRegionTest.LargeRandom | behaviour | blocked | model lacks layout shift (CLS) tracking |
| layout_shift_region_test.cc:122 | LayoutShiftRegionTest.Waffle | behaviour | blocked | model lacks layout shift (CLS) tracking |
| custom/layout_worklet_test.cc:82 | LayoutWorkletTest.ParseProperties | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:121 | LayoutWorkletTest.RegisterLayout | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:144 | LayoutWorkletTest.RegisterLayout_EmptyName | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:155 | LayoutWorkletTest.RegisterLayout_Duplicate | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:172 | LayoutWorkletTest.RegisterLayout_NoIntrinsicSizes | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:183 | LayoutWorkletTest.RegisterLayout_ThrowingPropertyGetter | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:195 | LayoutWorkletTest.RegisterLayout_BadPropertyGetter | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:207 | LayoutWorkletTest.RegisterLayout_NoPrototype | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:219 | LayoutWorkletTest.RegisterLayout_BadPrototype | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:231 | LayoutWorkletTest.RegisterLayout_BadIntrinsicSizes | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:243 | LayoutWorkletTest.RegisterLayout_NoLayout | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| custom/layout_worklet_test.cc:255 | LayoutWorkletTest.RegisterLayout_BadLayout | behaviour | blocked | model lacks CSS layout worklet (Houdini custom layout) |
| paint_containment_test.cc:34 | PaintContainmentTest.BlockPaintContainment | behaviour | blocked | model lacks paint containment stacking and BFC creation |
| paint_containment_test.cc:47 | PaintContainmentTest.InlinePaintContainment | internal | internal | Blink object type check on non-atomic inline |
| paint_containment_test.cc:58 | PaintContainmentTest.SvgWithContainmentShouldNotCrash | internal | internal | Blink crash regression test |
| selection_state_test.cc:14 | SelectionStateTest.StreamOutput | internal | internal | Blink C++ string serialization operator check |
| layout_progress_test.cc:22 | LayoutProgressTest.AnimationScheduling | internal | internal | Blink animation scheduling timer check |
| layout_frame_set_test.cc:13 | LayoutFrameSetTest.GetCursor | behaviour | blocked | model lacks frameset resize cursor resolution |
| layout_frame_set_test.cc:33 | LayoutFrameSetTest.HitTestingCrash | internal | internal | Blink crash regression test |
| layout_image_resource_test.cc:19 | LayoutImageResourceTest.BrokenImageHighRes | internal | internal | Blink image resource cache plumbing check |
| layout_image_resource_test.cc:24 | LayoutImageResourceTest.InvalidatePaintRequiresCachedImage | internal | internal | Blink image resource cache plumbing check |
| layout_image_test.cc:15 | LayoutImageTest.HitTestUnderTransform | behaviour | blocked | model lacks hit testing under transform |
| layout_image_test.cc:33 | LayoutImageTest.NeedsVisualOverflowRecalc | internal | internal | Blink image layout object flag/lifecycle check |
| layout_image_test.cc:50 | LayoutImageTest.IsUnsizedImage | internal | internal | Blink image layout object flag/lifecycle check |
| layout_replaced_test.cc:14 | LayoutReplacedTest.InvalidateAfterAddingBorderRadius | behaviour | blocked | model lacks paint property update invalidation on border radius mutation |
| layout_media_test.cc:13 | LayoutMediaTest.DisallowInlineChild | internal | internal | Blink media controls pseudo child layout object creation rules |
| layout_media_test.cc:24 | LayoutMediaTest.DisallowBlockChild | internal | internal | Blink media controls pseudo child layout object creation rules |
| layout_media_test.cc:35 | LayoutMediaTest.DisallowOutOfFlowPositionedChild | internal | internal | Blink media controls pseudo child layout object creation rules |
| layout_media_test.cc:46 | LayoutMediaTest.DisallowFloatingChild | internal | internal | Blink media controls pseudo child layout object creation rules |
| layout_media_test.cc:58 | LayoutMediaTest.BlockifyInlineFlex | internal | internal | Blink media controls pseudo child layout object creation rules |
| layout_media_test.cc:71 | LayoutMediaTest.DisallowContainerBeyondMedia | internal | internal | Blink media controls pseudo child layout object creation rules |
| layout_video_test.cc:38 | LayoutVideoTest.PosterSizeWithNormal | behaviour | blocked | model lacks HTMLVideoElement poster sizing with zoom |
| layout_video_test.cc:55 | LayoutVideoTest.PosterSizeWithZoom | behaviour | blocked | model lacks HTMLVideoElement poster sizing with zoom |
| layout_video_test.cc:72 | LayoutVideoTest.PosterSizeAfterPlay | behaviour | blocked | model lacks HTMLVideoElement poster sizing with zoom |
| layout_video_test.cc:98 | LayoutVideoTest.DefaultPosterImageSize | behaviour | blocked | model lacks HTMLVideoElement poster sizing with zoom |
| layout_theme_test.cc:47 | LayoutThemeTest.ChangeFocusRingColor | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:79 | LayoutThemeTest.AppearanceDoesNotAdjustDisplayOfNonWidgets | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:99 | LayoutThemeTest.AppearanceAdjustsDisplayOfWidgets | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:120 | LayoutThemeTest.FocusRingColorWithColorScheme | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:135 | LayoutThemeTest.SystemColorWithColorScheme | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:166 | LayoutThemeTest.SetSelectionColors | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:192 | LayoutThemeTest.SetSelectionColorsNoInvalidation | behaviour | blocked | model lacks platform theme color resolution |
| layout_theme_test.cc:213 | LayoutThemeTest.AndroidSelectionColor | behaviour | blocked | model lacks platform theme color resolution |
| layout_input_node_test.cc:29 | LayoutInputNodeTest.DumpBasic | internal | internal | Blink debug string dumper check |
| layout_input_node_test.cc:47 | LayoutInputNodeTest.DumpBlockInInline | internal | internal | Blink debug string dumper check |
| layout_input_node_test.cc:79 | LayoutInputNodeTest.DumpInlineBlockInInline | internal | internal | Blink debug string dumper check |
| layout_input_node_test.cc:111 | LayoutInputNodeTest.DumpFloatInInline | internal | internal | Blink debug string dumper check |
| layout_input_node_test.cc:142 | LayoutInputNodeTest.DumpAbsposInInline | internal | internal | Blink debug string dumper check |
| layout_input_node_test.cc:173 | LayoutInputNodeTest.DumpRelposInline | internal | internal | Blink debug string dumper check |
| inline_layout_test.cc:32 | InlineLayoutTest.BlockWithSingleTextNode | behaviour | blocked | inline lane (model lacks inline formatting context / inline layout algorithm) |
| inline_layout_test.cc:59 | InlineLayoutTest.BlockWithTextAndAtomicInline | behaviour | blocked | inline lane (model lacks inline formatting context / inline layout algorithm) |






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
