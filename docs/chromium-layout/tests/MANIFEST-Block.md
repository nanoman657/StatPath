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
percent/shrink-to-fit widths, laws), `BlockFloat.lean` (floats and clearance), `BlockFragmentation.lean` (fragmentainer slicing), `BlockNode.lean` (child nodes, child iterator), `BlockScroll.lean` (scrollbar gutter), `BlockWritingMode.lean` (physical/logical mapping), `BlockLength.lean` (CSS length resolution, contributions, aspect ratio), `ColumnWidth.lean` (multicol column width and count), `ColumnLayout.lean` (multicol column layout, column balancing), `FlexLayout.lean` (CSS flex container and line layout, item sizing, line wrapping), `BlockRelative.lean` (relative positioning insets), `BlockAbsolute.lean` (out-of-flow positioning constraints), `BlockSticky.lean` (sticky positioning constraints and scroll offsets), `OutOfFlowAnchor.lean` (CSS anchor positioning declarations, queries, and side evaluation), `GridLayout.lean` (CSS Grid track sizing, gaps, placement, and ranges), `TableLayout.lean` (CSS table section ordering, colspan/rowspan distribution, and block sizing), `BlockOverflow.lean` (CSS overflow clipping, scroll containers, overflow-clip-margin, and paint containment), `BlockReplaced.lean` (replaced element intrinsic dimensions and zoom).
Vectors live in `tests/TestsBlock_<File>.lean`. `tests/check_tests.sh` (called from `check.sh`)
checks every row against the pinned sources and the Lean modules.

| file:line | test | class | status | evidence / reason |
|---|---|---|---|---|
| block_layout_algorithm_test.cc:90 | BlockLayoutAlgorithmTest.FixedSize | geometry | formalized | `TestsBlock.FixedSize_size` |
| block_layout_algorithm_test.cc:106 | BlockLayoutAlgorithmTest.Caching | behaviour | formalized | `TestsBlock_ResultCaching.blockCaching`, `BlockResultCache.checkSizeAndQuirksCache`, `BlockResultCache.checkSizeAndQuirksCache_dirty` (opened layout_utils.cc to resolve CalculateSizeBasedLayoutCacheStatus) |
| block_layout_algorithm_test.cc:166 | BlockLayoutAlgorithmTest.MinInlineSizeCaching | behaviour | formalized | `TestsBlock_ResultCaching.minInlineSizeCaching`, `BlockResultCache.checkSizeAndQuirksCache` |
| block_layout_algorithm_test.cc:216 | BlockLayoutAlgorithmTest.PercentageBlockSizeQuirkDescendantsCaching | behaviour | formalized | `TestsBlock_ResultCaching.percentageBlockSizeQuirkDescendantsCaching`, `BlockResultCache.checkSizeAndQuirksCache` |
| block_layout_algorithm_test.cc:310 | BlockLayoutAlgorithmTest.LineOffsetCaching | behaviour | formalized | `TestsBlock_ResultCaching.lineOffsetCaching`, `BlockResultCache.checkBfcCache` |
| block_layout_algorithm_test.cc:341 | BlockLayoutAlgorithmTest.LayoutBlockChildren | geometry | formalized | `TestsBlock.LayoutBlockChildren_container`, `TestsBlock.LayoutBlockChildren_children` |
| block_layout_algorithm_test.cc:380 | BlockLayoutAlgorithmTest.LayoutBlockChildrenWithWritingMode | geometry | formalized | `TestsBlock.LayoutBlockChildrenWithWritingMode_vectors` |
| block_layout_algorithm_test.cc:418 | BlockLayoutAlgorithmTest.CollapsingMarginsCase1WithFloats | geometry | formalized | `TestsBlock.CollapsingMarginsCase1WithFloats_vectors` |
| block_layout_algorithm_test.cc:487 | BlockLayoutAlgorithmTest.CollapsingMarginsCase2WithFloats | geometry | formalized | `TestsBlock.CollapsingMarginsCase2WithFloats_vectors` |
| block_layout_algorithm_test.cc:568 | BlockLayoutAlgorithmTest.CollapsingMarginsCase3 | geometry | formalized | `TestsBlock.CollapsingMarginsCase3_auto`, `TestsBlock.CollapsingMarginsCase3_fixed` |
| block_layout_algorithm_test.cc:618 | BlockLayoutAlgorithmTest.CollapsingMarginsCase4 | geometry | formalized | `TestsBlock.CollapsingMarginsCase4_with_padding`, `TestsBlock.CollapsingMarginsCase4_without_padding`, `BlockFlow.start_edge_top` |
| block_layout_algorithm_test.cc:680 | BlockLayoutAlgorithmTest.CollapsingMarginsCase5 | geometry | formalized | `TestsBlock.CollapsingMarginsCase5_vectors` |
| block_layout_algorithm_test.cc:744 | BlockLayoutAlgorithmTest.CollapsingMarginsWithText | geometry | blocked | needs text line layout in `<p>`; expected offsets depend on the text's line box, not modelled by BlockFlow |
| block_layout_algorithm_test.cc:772 | BlockLayoutAlgorithmTest.CollapsingMarginsCase6 | geometry | formalized | `TestsBlock.CollapsingMarginsCase6_vectors` |
| block_layout_algorithm_test.cc:815 | BlockLayoutAlgorithmTest.CollapsingMarginsCase7 | geometry | formalized | `TestsBlock.CollapsingMarginsCase7_vectors`, `BlockFloat.clear_left_no_left` |
| block_layout_algorithm_test.cc:869 | BlockLayoutAlgorithmTest.CollapsingMarginsEmptyBlockWithClearance | geometry | blocked | needs float, `clear`, abspos |
| block_layout_algorithm_test.cc:1029 | BlockLayoutAlgorithmTest.NewFormattingContextAutoMargins | geometry | formalized | `TestsBlock.NewFormattingContextAutoMargins_vectors`, `BlockFloat.new_fc_auto_margin` |
| block_layout_algorithm_test.cc:1062 | BlockLayoutAlgorithmTest.BorderAndPadding | geometry | formalized | `TestsBlock.BorderAndPadding_div1`, `TestsBlock.BorderAndPadding_div2_offset` |
| block_layout_algorithm_test.cc:1118 | BlockLayoutAlgorithmTest.PercentageResolutionSize | geometry | formalized | `TestsBlock.PercentageResolutionSize_widths` |
| block_layout_algorithm_test.cc:1145 | BlockLayoutAlgorithmTest.AutoMargin | geometry | formalized | `TestsBlock.AutoMargin_offsets`, `BlockFlow.auto_width_fills` |
| block_layout_algorithm_test.cc:1180 | BlockLayoutAlgorithmTest.PositionFloatInsideEmptyBlocks | geometry | formalized | `TestsBlock.PositionFloatInsideEmptyBlocks_vectors`, `BlockFloat.float_no_overlap` |
| block_layout_algorithm_test.cc:1275 | BlockLayoutAlgorithmTest.PositionFloatFragments | geometry | formalized | `TestsBlock.PositionFloatFragments_vectors` |
| block_layout_algorithm_test.cc:1390 | BlockLayoutAlgorithmTest.PositionFragmentsWithClear | geometry | formalized | `TestsBlock.PositionFragmentsWithClear_none_vectors`, `TestsBlock.PositionFragmentsWithClear_left_vectors`, `TestsBlock.PositionFragmentsWithClear_right_vectors`, `TestsBlock.PositionFragmentsWithClear_both_vectors`, `BlockFloat.clearance_respects_left_floats`, `BlockFloat.clearance_respects_right_floats`, `BlockFloat.clearance_respects_both_floats` |
| block_layout_algorithm_test.cc:1516 | BlockLayoutAlgorithmTest.ComputeMinMaxContent | geometry | formalized | `TestsBlock.ComputeMinMaxContent_sizes` |
| block_layout_algorithm_test.cc:1533 | BlockLayoutAlgorithmTest.ComputeMinMaxContentFloats | geometry | formalized | `TestsBlock.ComputeMinMaxContentFloats_vectors`, `BlockFloat.floats_max_content` |
| block_layout_algorithm_test.cc:1554 | BlockLayoutAlgorithmTest.ComputeMinMaxContentFloatsClearance | geometry | formalized | `TestsBlock.ComputeMinMaxContentFloatsClearance_vectors`, `BlockFloat.clear_breaks_line` |
| block_layout_algorithm_test.cc:1575 | BlockLayoutAlgorithmTest.ComputeMinMaxContentNewFormattingContext | geometry | formalized | `TestsBlock.ComputeMinMaxContentNewFormattingContext_vectors`, `BlockFloat.floats_max_content` |
| block_layout_algorithm_test.cc:1596 | BlockLayoutAlgorithmTest.ComputeMinMaxContentNewFormattingContextNegativeMargins | geometry | formalized | `TestsBlock.ComputeMinMaxContentNewFormattingContextNegativeMargins_vectors`, `BlockFloat.floats_max_content` |
| block_layout_algorithm_test.cc:1618 | BlockLayoutAlgorithmTest.ComputeMinMaxContentSingleNewFormattingContextNegativeMargins | geometry | formalized | `TestsBlock.ComputeMinMaxContentSingleNewFormattingContextNegativeMargins_vectors`, `BlockFloat.single_float_min_max` |
| block_layout_algorithm_test.cc:1637 | BlockLayoutAlgorithmTest.ShrinkToFit | geometry | formalized | `TestsBlock.ShrinkToFit_width` |
| block_layout_algorithm_test.cc:1660 | BlockLayoutAlgorithmTest.PositionEmptyBlocksInNewBfc | geometry | blocked | needs floats |
| block_layout_algorithm_test.cc:1705 | BlockLayoutAlgorithmTest.PositionBlocksWithClearanceAndIntrudingFloats | geometry | formalized | `TestsBlock.PositionBlocksWithClearanceAndIntrudingFloats_vectors`, `BlockFloat.clear_intrude_pos` |
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
| block_node_test.cc:169 | BlockNodeForTest.MinContentForControls | geometry | formalized | `TestsBlock.MinContentForControls_vectors`, `BlockOverflow.control_min_size_eq` |
| layout_block_flow_test.cc:16 | LayoutBlockFlowTest.RecalcInlineChildrenScrollableOverflow | internal | internal | crash/DCHECK regression (passes if no DCHECK failure in ink_overflow.cc) |
| layout_block_flow_test.cc:38 | LayoutBlockFlowTest.IsInsideMulticol | internal | internal | checks C++ LayoutObject::IsInsideMulticol query |
| layout_block_flow_test.cc:109 | LayoutBlockFlowTest.AnonymousContainer | internal | internal | checks C++ anonymous LayoutBlockFlow wrapper insertion for inline children in multicol |
| layout_block_flow_test.cc:165 | LayoutBlockFlowTest.NoAnonymousContainer | internal | internal | checks C++ anonymous LayoutBlockFlow wrapper insertion for inline children in multicol |
| layout_block_test.cc:20 | LayoutBlockTest.LayoutNameCalledWithNullStyle | internal | internal | checks DecoratedName() string on an unstyled object |
| layout_block_test.cc:28 | LayoutBlockTest.WidthAvailableToChildrenChanged | geometry | formalized | `TestsBlock.WidthAvailableToChildrenChanged_vectors`, `TestsBlock.scroller_content_height` (scrollbar width kept symbolic: test compares against ComputeScrollbars) |
| layout_block_test.cc:61 | LayoutBlockTest.OverflowWithTransformAndPerspective | geometry | blocked | expects scrollable overflow 187.625 under rotateY(-45deg) with perspective; 3D transforms are not modelled |
| layout_block_test.cc:73 | LayoutBlockTest.NestedInlineVisualOverflow | geometry | formalized | `TestsBlock.NestedInlineVisualOverflow_vectors`, `BlockOverflow.child_visual_overflow_origin` |
| layout_block_test.cc:86 | LayoutBlockTest.NestedInlineVisualOverflowVerticalRL | geometry | formalized | `TestsBlock.NestedInlineVisualOverflowVerticalRL_vectors`, `BlockOverflow.child_visual_overflow_origin` |
| layout_block_test.cc:101 | LayoutBlockTest.ContainmentStyleChange | behaviour | formalized | `TestsBlock.ContainmentStyleChange_vectors`, `BlockOverflow.contain_strict_fixed_pos`, `BlockOverflow.contain_style_not_fixed_pos` |
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
| physical_fragment_test.cc:84 | StickyFragmentPropagationTest.StickyAxisEnabled | behaviour | formalized | `TestsBlock.StickyAxisEnabled_vectors`, `BlockSticky.diff_axes_self` |
| physical_fragment_test.cc:113 | StickyFragmentPropagationTest.StickyAxisDisabled | behaviour | blocked | model lacks single-axis sticky scroll container fragment propagation |
| physical_fragment_test.cc:134 | PhysicalFragmentTest.DumpFragmentTreeBasic | geometry | formalized | `TestsBlock.DumpFragmentTreeBasic_vectors` |
| physical_fragment_test.cc:149 | PhysicalFragmentTest.DumpFragmentTreeWithAbspos | geometry | formalized | `TestsBlock.DumpFragmentTreeWithAbspos_vectors`, `BlockAbsolute.layout_document_kids_len` |
| physical_fragment_test.cc:165 | PhysicalFragmentTest.DumpFragmentTreeWithAbsposInRelpos | geometry | formalized | `TestsBlock.DumpFragmentTreeWithAbsposInRelpos_vectors`, `BlockAbsolute.resolve_oof_container_relative` |
| physical_fragment_test.cc:184 | PhysicalFragmentTest.DumpFragmentTreeWithGrid | geometry | formalized | `TestsBlock.DumpFragmentTreeWithGrid_vectors`, `GridLayout.grid_container_is_fc_root` |
| physical_fragment_test.cc:213 | PhysicalFragmentTest.DumpFragmentTreeWithTargetInsideColumn | geometry | formalized | `TestsBlock.DumpFragmentTreeWithTargetInsideColumn_vectors`, `ColumnLayout.multicol_bp_size` |
| physical_fragment_test.cc:243 | PhysicalFragmentTest.DumpFragmentTreeWithRepeatedContent | geometry | blocked | needs table layout with repeated header group across multicol columns; not modelled |
| physical_fragment_test.cc:295 | PhysicalFragmentTest.CrashInScrollableOverflowCalculator | internal | internal | crash regression in ScrollableOverflowCalculator under fullscreen menulist keyframes |
| physical_box_fragment_test.cc:29 | PhysicalBoxFragmentTest.FloatingDescendantsInlineChlidren | behaviour | formalized | `TestsBlock.FloatingDescendantsInlineChlidren_vectors`, `BlockFloat.direct_float_has` |
| physical_box_fragment_test.cc:46 | PhysicalBoxFragmentTest.FloatingDescendantsBlockChlidren | behaviour | blocked | model lacks floating descendants propagation on physical fragments |
| physical_box_fragment_test.cc:65 | PhysicalBoxFragmentTest.FloatingDescendantsInlineBlock | behaviour | formalized | `TestsBlock.FloatingDescendantsInlineBlock_vectors`, `BlockFloat.ib_no_float_prop` |
| physical_box_fragment_test.cc:83 | PhysicalBoxFragmentTest.FloatingDescendantsBlockFormattingContext | behaviour | formalized | `TestsBlock.FloatingDescendantsBlockFormattingContext_vectors`, `BlockFloat.flow_root_propagates` |
| physical_box_fragment_test.cc:104 | PhysicalBoxFragmentTest.ReplacedBlock | internal | internal | checks C++ Type(), IsAtomicInline() and GetBoxType() flags on replaced block fragment |
| physical_box_fragment_test.cc:115 | PhysicalBoxFragmentTest.IsFragmentationContextRoot | geometry | formalized | `TestsBlock.IsFragmentationContextRoot_columnCount`, `ColumnLayout.actualColumnCount_at_least_one` |
| physical_box_fragment_test.cc:135 | PhysicalBoxFragmentTest.IsFragmentationContextRootNested | geometry | formalized | `TestsBlock.IsFragmentationContextRootNested_columnCounts`, `ColumnLayout.actualColumnCount_at_least_one` |
| physical_box_fragment_test.cc:169 | PhysicalBoxFragmentTest.IsFragmentationContextRootFieldset | behaviour | formalized | `TestsBlock.IsFragmentationContextRootFieldset_vectors`, `ColumnLayout.fieldset_never_frag_context_root` |
| physical_box_fragment_test.cc:201 | PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStart | behaviour | formalized | `TestsBlock.MayHaveDescendantAboveBlockStart_vectors`, `BlockOverflow.compute_may_have_descendant_above_propagation` |
| physical_box_fragment_test.cc:216 | PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStartBlockInInline | behaviour | formalized | `TestsBlock.MayHaveDescendantAboveBlockStartBlockInInline_vectors`, `BlockOverflow.compute_may_have_descendant_above_propagation` |
| physical_box_fragment_test.cc:233 | PhysicalBoxFragmentTest.OverflowClipMarginVisualBox | geometry | formalized | `TestsBlock.OverflowClipMarginVisualBox_vectors`, `BlockOverflow.visual_box_clip_size_monotonic` |
| physical_box_fragment_test.cc:294 | PhysicalBoxFragmentTest.CloneWithPostLayoutFragments | internal | internal | checks CloneWithPostLayoutFragments preserves C++ frame set layout data pointer |
| relative_utils_test.cc:49 | RelativeUtilsTest.HorizontalTB | geometry | formalized | `TestsBlock.HorizontalTB_vectors`, `BlockRelative.opposing_sum_zero` |
| absolute_utils_test.cc:150 | AbsoluteUtilsTest.Horizontal | geometry | formalized | `TestsBlock.Horizontal_vectors` |
| absolute_utils_test.cc:315 | AbsoluteUtilsTest.Vertical | geometry | formalized | `TestsBlock.Vertical_vectors` |
| absolute_utils_test.cc:436 | AbsoluteUtilsTest.CenterStaticPosition | geometry | formalized | `TestsBlock.CenterStaticPosition_vectors` |
| absolute_utils_test.cc:474 | AbsoluteUtilsTest.MinMax | geometry | formalized | `TestsBlock.MinMax_vectors`, `BlockAbsolute.clamp_bounds` |
| out_of_flow_layout_part_test.cc:46 | OutOfFlowLayoutPartTest.FixedInsideAbs | geometry | formalized | `TestsBlock.FixedInsideAbs_offsets`, `BlockAbsolute.explicit_inset_overrides_static`, `BlockAbsolute.auto_inset_uses_static` |
| out_of_flow_layout_part_test.cc:103 | OutOfFlowLayoutPartTest.PositionedInMulticol | geometry | formalized | `TestsBlock.PositionedInMulticol_vectors`, `ColumnLayout.multicol_oof_offset_zero` |
| out_of_flow_layout_part_test.cc:149 | OutOfFlowLayoutPartTest.SimplePositionedFragmentation | geometry | formalized | `TestsBlock.SimplePositionedFragmentation_vectors`, `ColumnLayout.fragment_oof_zero_frag` |
| out_of_flow_layout_part_test.cc:191 | OutOfFlowLayoutPartTest.PositionedFragmentationWithOverflow | geometry | formalized | `TestsBlock.PositionedFragmentationWithOverflow_vectors`, `ColumnLayout.fragment_oof_zero_content` |
| out_of_flow_layout_part_test.cc:238 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumns | geometry | formalized | `TestsBlock.PositionedFragmentationWithNewColumns_vectors`, `ColumnLayout.multicol_total_columns_empty` |
| out_of_flow_layout_part_test.cc:279 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewEmptyColumns | geometry | blocked | needs out-of-flow fragmentation in multicolumn with column spanners; not modelled |
| out_of_flow_layout_part_test.cc:320 | OutOfFlowLayoutPartTest.BreakInsideAvoid | behaviour | formalized | `TestsBlock.BreakInsideAvoid_vectors`, `BlockAbsolute.abspos_ignores_bi` |
| out_of_flow_layout_part_test.cc:359 | OutOfFlowLayoutPartTest.BreakBeforeColumn | behaviour | formalized | `TestsBlock.BreakBeforeColumn_vectors`, `BlockAbsolute.abspos_ignores_bb` |
| out_of_flow_layout_part_test.cc:398 | OutOfFlowLayoutPartTest.BreakAfterColumn | behaviour | formalized | `TestsBlock.BreakAfterColumn_vectors`, `BlockAbsolute.abspos_ignores_ba` |
| out_of_flow_layout_part_test.cc:437 | OutOfFlowLayoutPartTest.ChildBreakInsideAvoid | behaviour | formalized | `TestsBlock.ChildBreakInsideAvoid_vectors`, `BlockAbsolute.child_fits_col` |
| out_of_flow_layout_part_test.cc:479 | OutOfFlowLayoutPartTest.ChildBreakBeforeAvoid | behaviour | formalized | `TestsBlock.ChildBreakBeforeAvoid_vectors`, `BlockAbsolute.child_fits_col` |
| out_of_flow_layout_part_test.cc:523 | OutOfFlowLayoutPartTest.ChildBreakAfterAvoid | behaviour | formalized | `TestsBlock.ChildBreakAfterAvoid_vectors`, `BlockAbsolute.child_fits_col` |
| out_of_flow_layout_part_test.cc:568 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNegativeTopPropertyAndNewEmptyColumn | geometry | formalized | `TestsBlock.PositionedFragmentationWithNegativeTopPropertyAndNewEmptyColumn_vectors`, `ColumnLayout.resolve_multicol_oof_start_clamp_zero` |
| out_of_flow_layout_part_test.cc:610 | OutOfFlowLayoutPartTest.PositionedFragmentationWithBottomProperty | geometry | blocked | needs out-of-flow fragmentation in multicolumn with bottom property; not modelled |
| out_of_flow_layout_part_test.cc:649 | OutOfFlowLayoutPartTest.PositionedFragmentationInFlowWithAddedColumns | geometry | formalized | `TestsBlock.PositionedFragmentationInFlowWithAddedColumns_vectors`, `ColumnLayout.resolve_multicol_oof_start_zero_frag` |
| out_of_flow_layout_part_test.cc:694 | OutOfFlowLayoutPartTest.PositionedFragmentationAndColumnSpanners | geometry | formalized | `TestsBlock_ColumnFloatBreak.positionedFragmentationAndColumnSpanners`, `ColumnFloatBreak.layoutOofAfterSpanner` |
| out_of_flow_layout_part_test.cc:745 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNestedSpanner | geometry | formalized | `TestsBlock_ColumnFloatBreak.positionedFragmentationWithNestedSpanner`, `ColumnFloatBreak.layoutOofAfterSpanner` |
| out_of_flow_layout_part_test.cc:787 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNestedSpanners | geometry | blocked | needs nested column spanners with out-of-flow fragmentation; not modelled |
| out_of_flow_layout_part_test.cc:842 | OutOfFlowLayoutPartTest.AbsposInSpanner | geometry | formalized | `TestsBlock_ColumnFloatBreak.absposInSpanner`, `ColumnFloatBreak.layoutAbsposInSpanner` |
| out_of_flow_layout_part_test.cc:895 | OutOfFlowLayoutPartTest.AbsposInSpannerStaticPos | geometry | formalized | `TestsBlock_ColumnFloatBreak.absposInSpannerStaticPos`, `ColumnFloatBreak.layoutAbsposInSpanner` |
| out_of_flow_layout_part_test.cc:945 | OutOfFlowLayoutPartTest.SpannerInAbspos | geometry | formalized | `TestsBlock.SpannerInAbspos_vectors`, `ColumnLayout.spanner_inside_oof_not_effective` |
| out_of_flow_layout_part_test.cc:987 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumnsAndSpanners | geometry | formalized | `TestsBlock_ColumnFloatBreak.positionedFragmentationWithNewColumnsAndSpanners`, `ColumnFloatBreak.layoutOofBeforeSpanners` (opened column_layout_algorithm.cc to verify column balancing before spanners) |
| out_of_flow_layout_part_test.cc:1038 | OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumnsAfterSpanner | geometry | formalized | `TestsBlock_ColumnFloatBreak.positionedFragmentationWithNewColumnsAfterSpanner`, `ColumnFloatBreak.layoutOofBeforeSpanners` (opened column_layout_algorithm.cc to verify column balancing before spanners) |
| out_of_flow_layout_part_test.cc:1083 | OutOfFlowLayoutPartTest.AbsposFragWithSpannerAndNewColumnsAutoHeight | geometry | formalized | `TestsBlock.AbsposFragWithSpannerAndNewColumnsAutoHeight_vectors`, `ColumnLayout.auto_balanced_frag_h_one_col` |
| out_of_flow_layout_part_test.cc:1128 | OutOfFlowLayoutPartTest.AbsposFragWithSpannerAndNewEmptyColumns | geometry | formalized | `TestsBlock_ColumnFloatBreak.absposFragWithSpannerAndNewEmptyColumns`, `ColumnFloatBreak.layoutOofBeforeSpanners` |
| out_of_flow_layout_part_test.cc:1175 | OutOfFlowLayoutPartTest.AbsposFragmentationPctResolution | geometry | formalized | `TestsBlock.AbsposFragmentationPctResolution_vectors` |
| out_of_flow_layout_part_test.cc:1218 | OutOfFlowLayoutPartTest.AbsposFragmentationPctResolutionWithOverflow | geometry | formalized | `TestsBlock.AbsposFragmentationPctResolutionWithOverflow_vectors`, `ColumnLayout.resolve_pct_height_hundred` |
| out_of_flow_layout_part_test.cc:1278 | OutOfFlowLayoutPartTest.SimpleAbsposNestedFragmentation | geometry | formalized | `TestsBlock.SimpleAbsposNestedFragmentation_vectors` |
| out_of_flow_layout_part_test.cc:1322 | OutOfFlowLayoutPartTest.AbsposNestedFragmentationNewColumns | geometry | formalized | `TestsBlock.AbsposNestedFragmentationNewColumns_vectors` |
| out_of_flow_layout_part_test.cc:1375 | OutOfFlowLayoutPartTest.AbsposNestedFragmentationNewEmptyColumns | geometry | blocked | needs nested multicol out-of-flow fragmentation with new empty columns; not modelled |
| out_of_flow_layout_part_test.cc:1431 | OutOfFlowLayoutPartTest.PositionedFragmentationWithBottomPropertyAndHeightAuto | geometry | formalized | `TestsBlock_ColumnFloatBreak.positionedFragmentationWithBottomPropertyAndHeightAuto`, `ColumnFloatBreak.layoutAutoHeightBottomOof` |
| out_of_flow_layout_part_test.cc:1479 | OutOfFlowLayoutPartTest.AbsposFragWithInlineCBAndSpanner | geometry | formalized | `TestsBlock_ColumnFloatBreak.absposFragWithInlineCBAndSpanner`, `ColumnFloatBreak.layoutOofBeforeSpanners` |
| out_of_flow_layout_part_test.cc:1549 | OutOfFlowLayoutPartTest.PositionedObjectsInMulticol | behaviour | formalized | `TestsBlock.PositionedObjectsInMulticol_vectors`, `ColumnLayout.multicol_is_frag_context_root` |
| out_of_flow_layout_part_test.cc:1572 | OutOfFlowLayoutPartTest.PositionedObjectsInMulticolWithInline | behaviour | formalized | `TestsBlock.PositionedObjectsInMulticolWithInline_vectors`, `ColumnLayout.column_is_fragmentainer_not_root` |
| out_of_flow_layout_part_test.cc:1596 | OutOfFlowLayoutPartTest.FragmentainerBreakTokens | behaviour | formalized | `TestsBlock_ColumnFloatBreak.fragmentainerBreakTokens`, `ColumnFloatBreak.fragmentainerBreakTokensWithSpanner` |
| out_of_flow_layout_part_test.cc:1657 | OutOfFlowLayoutPartTest.FragmentainerBreakTokenBeforeSpanner | behaviour | formalized | `TestsBlock_ColumnFloatBreak.fragmentainerBreakTokenBeforeSpanner`, `ColumnFloatBreak.fragmentainerBreakTokensWithSpanner` |
| out_of_flow_layout_part_test.cc:1716 | OutOfFlowLayoutPartTest.RelayoutNestedMulticolWithOOF | behaviour | formalized | `TestsBlock_ColumnFloatBreak.relayoutNestedMulticolWithOOF`, `ColumnFloatBreak.layoutRelWithSingleColAbspos` |
| out_of_flow_layout_part_test.cc:1764 | OutOfFlowLayoutPartTest.EmptyFragmentainersBeforeOOF | behaviour | formalized | `TestsBlock_ColumnFloatBreak.emptyFragmentainersBeforeOOF`, `ColumnFloatBreak.oofFragmentainerBreakTokens`, `ColumnFloatBreak.oofFragmentainerBreakTokens_length` |
| out_of_flow_layout_part_test.cc:1810 | OutOfFlowLayoutPartTest.MultipleUnfragmentedOOFs | behaviour | formalized | `TestsBlock_ColumnFloatBreak.multipleUnfragmentedOOFs`, `ColumnFloatBreak.oofFragmentainerBreakTokens`, `ColumnFloatBreak.oofFragmentainerBreakTokens_length` |

| column_layout_algorithm_test.cc:41 | ColumnLayoutAlgorithmTest.EmptyEditable | geometry | formalized | `TestsBlock_ColumnFloatBreak.emptyEditable`, `ColumnFloatBreak.layoutEditableMulticol`, `ColumnFloatBreak.editableMulticol_height` |
| column_layout_algorithm_test.cc:56 | ColumnLayoutAlgorithmTest.EmptyEditableWithFloat | geometry | formalized | `TestsBlock_ColumnFloatBreak.emptyEditableWithFloat`, `ColumnFloatBreak.layoutEditableMulticol`, `ColumnFloatBreak.editableMulticol_height` |
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
| column_layout_algorithm_test.cc:429 | ColumnLayoutAlgorithmTest.OverflowedBlock | geometry | formalized | `TestsBlock.OverflowedBlock_vectors`, `ColumnLayout.box_fit_end_pos` |
| column_layout_algorithm_test.cc:467 | ColumnLayoutAlgorithmTest.OverflowedBlock2 | geometry | formalized | `TestsBlock.OverflowedBlock2_vectors`, `ColumnLayout.box_fit_end_pos` |
| column_layout_algorithm_test.cc:515 | ColumnLayoutAlgorithmTest.OverflowedBlock3 | geometry | formalized | `TestsBlock.OverflowedBlock3_vectors`, `ColumnLayout.box_fit_end_pos` |
| column_layout_algorithm_test.cc:554 | ColumnLayoutAlgorithmTest.UnusedSpaceInBlock | geometry | formalized | `TestsBlock.UnusedSpaceInBlock_vectors`, `ColumnLayout.box_fit_end_pos` |
| column_layout_algorithm_test.cc:589 | ColumnLayoutAlgorithmTest.FloatInOneColumn | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:617 | ColumnLayoutAlgorithmTest.TwoFloatsInOneColumn | geometry | formalized | `TestsBlock.TwoFloatsInOneColumn_vectors`, `ColumnLayout.right_float_aligns_right` |
| column_layout_algorithm_test.cc:647 | ColumnLayoutAlgorithmTest.TwoFloatsInTwoColumns | geometry | formalized | `TestsBlock.TwoFloatsInTwoColumns_vectors`, `ColumnLayout.right_float_aligns_right` |
| column_layout_algorithm_test.cc:680 | ColumnLayoutAlgorithmTest.FloatWithForcedBreak | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:717 | ColumnLayoutAlgorithmTest.FloatWithMargin | geometry | formalized | `TestsBlock.FloatWithMargin_vectors`, `ColumnLayout.right_float_aligns_right` |
| column_layout_algorithm_test.cc:747 | ColumnLayoutAlgorithmTest.FloatWithMarginBelowFloat | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:779 | ColumnLayoutAlgorithmTest.FloatWithLastResortBreak | geometry | formalized | `TestsBlock.FloatWithLastResortBreak_vectors`, `ColumnLayout.float_avoid_push_col` |
| column_layout_algorithm_test.cc:818 | ColumnLayoutAlgorithmTest.FloatWithAvoidBreak | geometry | formalized | `TestsBlock.FloatWithAvoidBreak_vectors`, `ColumnLayout.right_float_aligns_right` |
| column_layout_algorithm_test.cc:855 | ColumnLayoutAlgorithmTest.FloatWithMarginAndAvoidBreak | geometry | formalized | `TestsBlock.FloatWithMarginAndAvoidBreak_vectors`, `ColumnLayout.right_float_aligns_right` |
| column_layout_algorithm_test.cc:893 | ColumnLayoutAlgorithmTest.UnbreakableFloatBeforeBreakable | geometry | formalized | `TestsBlock.UnbreakableFloatBeforeBreakable_vectors`, `ColumnLayout.right_float_aligns_right` |
| column_layout_algorithm_test.cc:939 | ColumnLayoutAlgorithmTest.BlockWithTopMarginInThreeColumns | geometry | formalized | `TestsBlock.BlockWithTopMarginInThreeColumns_vectors` |
| column_layout_algorithm_test.cc:973 | ColumnLayoutAlgorithmTest.BlockStartAtColumnBoundary | geometry | formalized | `TestsBlock.BlockStartAtColumnBoundary_vectors` |
| column_layout_algorithm_test.cc:1004 | ColumnLayoutAlgorithmTest.NestedBlockAfterBlock | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:1042 | ColumnLayoutAlgorithmTest.BreakInsideAvoid | geometry | formalized | `TestsBlock.BreakInsideAvoid_vectors` |
| column_layout_algorithm_test.cc:1073 | ColumnLayoutAlgorithmTest.BreakInsideAvoidColumn | geometry | formalized | `TestsBlock.BreakInsideAvoidColumn_vectors` |
| column_layout_algorithm_test.cc:1104 | ColumnLayoutAlgorithmTest.BreakInsideAvoidPage | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:1137 | ColumnLayoutAlgorithmTest.BreakInsideAvoidTallBlock | geometry | formalized | `TestsBlock.BreakInsideAvoidTallBlock_vectors` |
| column_layout_algorithm_test.cc:1174 | ColumnLayoutAlgorithmTest.NestedBreakInsideAvoid | geometry | formalized | `TestsBlock.NestedBreakInsideAvoid_vectors` |
| column_layout_algorithm_test.cc:1215 | ColumnLayoutAlgorithmTest.NestedBreakInsideAvoidTall | geometry | formalized | `TestsBlock.NestedBreakInsideAvoidTall_vectors` |
| column_layout_algorithm_test.cc:1258 | ColumnLayoutAlgorithmTest.BreakInsideAvoidAtColumnBoundary | geometry | formalized | `TestsBlock.BreakInsideAvoidAtColumnBoundary_vectors` |
| column_layout_algorithm_test.cc:1292 | ColumnLayoutAlgorithmTest.MarginTopPastEndOfFragmentainer | geometry | formalized | `TestsBlock.MarginTopPastEndOfFragmentainer_vectors` |
| column_layout_algorithm_test.cc:1327 | ColumnLayoutAlgorithmTest.MarginBottomPastEndOfFragmentainer | geometry | formalized | `TestsBlock.MarginBottomPastEndOfFragmentainer_vectors` |
| column_layout_algorithm_test.cc:1362 | ColumnLayoutAlgorithmTest.MarginTopAtEndOfFragmentainer | geometry | formalized | `TestsBlock.MarginTopAtEndOfFragmentainer_vectors` |
| column_layout_algorithm_test.cc:1396 | ColumnLayoutAlgorithmTest.MarginBottomAtEndOfFragmentainer | geometry | formalized | `TestsBlock.MarginBottomAtEndOfFragmentainer_vectors` |
| column_layout_algorithm_test.cc:1430 | ColumnLayoutAlgorithmTest.LinesInMulticolExtraSpace | geometry | formalized | `TestsBlock.LinesInMulticolExtraSpace_vectors`, `ColumnLayout.line_moves_next_col` |
| column_layout_algorithm_test.cc:1470 | ColumnLayoutAlgorithmTest.LinesInMulticolExactFit | geometry | formalized | `TestsBlock.LinesInMulticolExactFit_vectors`, `ColumnLayout.line_moves_next_col` |
| column_layout_algorithm_test.cc:1510 | ColumnLayoutAlgorithmTest.LinesInMulticolChildExtraSpace | geometry | formalized | `TestsBlock.LinesInMulticolChildExtraSpace_vectors`, `ColumnLayout.line_moves_next_col` |
| column_layout_algorithm_test.cc:1552 | ColumnLayoutAlgorithmTest.LinesInMulticolChildExactFit | geometry | formalized | `TestsBlock.LinesInMulticolChildExactFit_vectors`, `ColumnLayout.line_moves_next_col` |
| column_layout_algorithm_test.cc:1594 | ColumnLayoutAlgorithmTest.LinesInMulticolChildNoSpaceForFirst | geometry | formalized | `TestsBlock.LinesInMulticolChildNoSpaceForFirst_vectors`, `ColumnLayout.line_moves_next_col` |
| column_layout_algorithm_test.cc:1637 | ColumnLayoutAlgorithmTest.LinesInMulticolChildInsufficientSpaceForFirst | geometry | formalized | `TestsBlock.LinesInMulticolChildInsufficientSpaceForFirst_vectors`, `ColumnLayout.line_moves_next_col` |
| column_layout_algorithm_test.cc:1681 | ColumnLayoutAlgorithmTest.LineAtColumnBoundaryInFirstBlock | geometry | formalized | `TestsBlock.LineAtColumnBoundaryInFirstBlock_vectors`, `ColumnBreak.box_slice_fills` |
| column_layout_algorithm_test.cc:1725 | ColumnLayoutAlgorithmTest.LinesAndFloatsMulticol | geometry | formalized | `TestsBlock_ColumnFloatBreak.linesAndFloatsMulticol`, `ColumnFloatBreak.layoutLinesAndFloats` |
| column_layout_algorithm_test.cc:1774 | ColumnLayoutAlgorithmTest.FloatBelowLastLineInColumn | geometry | blocked | needs float fragmentation in multicolumn |
| column_layout_algorithm_test.cc:1820 | ColumnLayoutAlgorithmTest.Orphans | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:1861 | ColumnLayoutAlgorithmTest.OrphansUnsatisfiable | geometry | formalized | `TestsBlock.OrphansUnsatisfiable_vectors`, `ColumnLayout.orphans_min_head` |
| column_layout_algorithm_test.cc:1905 | ColumnLayoutAlgorithmTest.Widows | geometry | formalized | `TestsBlock.Widows_vectors`, `ColumnLayout.widows_min_tail` |
| column_layout_algorithm_test.cc:1951 | ColumnLayoutAlgorithmTest.WidowsUnsatisfiable | geometry | formalized | `TestsBlock.WidowsUnsatisfiable_vectors`, `ColumnLayout.orphans_min_head` |
| column_layout_algorithm_test.cc:2017 | ColumnLayoutAlgorithmTest.OrphansAndUnsatisfiableWidows | geometry | formalized | `TestsBlock.OrphansAndUnsatisfiableWidows_vectors`, `ColumnLayout.orphans_min_head` |
| column_layout_algorithm_test.cc:2057 | ColumnLayoutAlgorithmTest.UnsatisfiableOrphansAndWidows | geometry | formalized | `TestsBlock.UnsatisfiableOrphansAndWidows_vectors`, `ColumnLayout.widows_min_tail` |
| column_layout_algorithm_test.cc:2097 | ColumnLayoutAlgorithmTest.WidowsAndAbspos | geometry | blocked | needs orphans and widows balancing in multicolumn |
| column_layout_algorithm_test.cc:2147 | ColumnLayoutAlgorithmTest.BreakBetweenLinesNotBefore | geometry | formalized | `TestsBlock.BreakBetweenLinesNotBefore_vectors`, `ColumnLayout.auto_box_start_col` |
| column_layout_algorithm_test.cc:2194 | ColumnLayoutAlgorithmTest.BreakBetweenLinesNotBefore2 | geometry | formalized | `TestsBlock.BreakBetweenLinesNotBefore2_vectors`, `ColumnLayout.auto_box_start_col` |
| column_layout_algorithm_test.cc:2236 | ColumnLayoutAlgorithmTest.BreakBetweenLinesNotBefore3 | geometry | formalized | `TestsBlock.BreakBetweenLinesNotBefore3_vectors`, `ColumnLayout.auto_box_start_col` |
| column_layout_algorithm_test.cc:2278 | ColumnLayoutAlgorithmTest.FloatInBlockMovedByOrphans | geometry | formalized | `TestsBlock_ColumnFloatBreak.floatInBlockMovedByOrphans`, `ColumnFloatBreak.layoutBlockWithMovedFloat`, `ColumnFloatBreak.linesInFirstColumn_lt_orphans` |
| column_layout_algorithm_test.cc:2318 | ColumnLayoutAlgorithmTest.FloatMovedWithWidows | geometry | formalized | `TestsBlock_ColumnFloatBreak.floatMovedWithWidows`, `ColumnFloatBreak.layoutBlockWithMovedFloat` |
| column_layout_algorithm_test.cc:2361 | ColumnLayoutAlgorithmTest.BorderAndPadding | geometry | formalized | `TestsBlock.BorderAndPadding_vectors`, `ColumnLayout.multicol_bp_size` |
| column_layout_algorithm_test.cc:2391 | ColumnLayoutAlgorithmTest.BreakInsideWithBorder | geometry | formalized | `TestsBlock.BreakInsideWithBorder_vectors`, `ColumnBreak.box_border_size` |
| column_layout_algorithm_test.cc:2427 | ColumnLayoutAlgorithmTest.ForcedBreaks | geometry | formalized | `TestsBlock_ColumnFloatBreak.forcedBreaks`, `ColumnFloatBreak.layoutWrapperForcedBreak` |
| column_layout_algorithm_test.cc:2480 | ColumnLayoutAlgorithmTest.ForcedBreakInSecondChild | geometry | formalized | `TestsBlock.ForcedBreakInSecondChild_vectors`, `ColumnLayout.forced_break_col` |
| column_layout_algorithm_test.cc:2517 | ColumnLayoutAlgorithmTest.ForcedAndUnforcedBreaksAtSameBoundary | geometry | formalized | `TestsBlock.ForcedAndUnforcedBreaksAtSameBoundary_vectors`, `ColumnLayout.forced_break_col` |
| column_layout_algorithm_test.cc:2568 | ColumnLayoutAlgorithmTest.ResumeInsideFormattingContextRoot | geometry | formalized | `TestsBlock.ResumeInsideFormattingContextRoot_vectors`, `ColumnLayout.forced_break_col` |
| column_layout_algorithm_test.cc:2602 | ColumnLayoutAlgorithmTest.NewFcAtColumnBoundary | geometry | formalized | `TestsBlock.NewFcAtColumnBoundary_vectors`, `ColumnLayout.forced_break_col` |
| column_layout_algorithm_test.cc:2633 | ColumnLayoutAlgorithmTest.NewFcWithMargin | geometry | formalized | `TestsBlock.NewFcWithMargin_vectors`, `ColumnLayout.forced_break_col` |
| column_layout_algorithm_test.cc:2665 | ColumnLayoutAlgorithmTest.NewFcBelowFloat | geometry | formalized | `TestsBlock.NewFcBelowFloat_vectors`, `ColumnLayout.new_fc_clears_float` |
| column_layout_algorithm_test.cc:2697 | ColumnLayoutAlgorithmTest.NewFcWithMarginPastColumnBoundary | geometry | formalized | `TestsBlock.NewFcWithMarginPastColumnBoundary_vectors`, `ColumnLayout.forced_break_col` |
| column_layout_algorithm_test.cc:2728 | ColumnLayoutAlgorithmTest.MinMax | geometry | formalized | `TestsBlock.MinMax_vectors`, `ColumnWidth.col_width_clamps_min` |
| column_layout_algorithm_test.cc:2799 | ColumnLayoutAlgorithmTest.ColumnBalancing | geometry | formalized | `TestsBlock.ColumnBalancing_vectors`, `ColumnLayout.bal_h_unconst` |
| column_layout_algorithm_test.cc:2829 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightExactMatch | geometry | formalized | `TestsBlock.ColumnBalancingFixedHeightExactMatch_vectors`, `ColumnLayout.bal_h_le_height` |
| column_layout_algorithm_test.cc:2860 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightLessContent | geometry | formalized | `TestsBlock.ColumnBalancingFixedHeightLessContent_vectors`, `ColumnLayout.bal_h_le_height` |
| column_layout_algorithm_test.cc:2891 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightOverflowingContent | geometry | formalized | `TestsBlock.ColumnBalancingFixedHeightOverflowingContent_vectors`, `ColumnLayout.bal_h_le_height` |
| column_layout_algorithm_test.cc:2927 | ColumnLayoutAlgorithmTest.ColumnBalancingMinHeight | geometry | formalized | `TestsBlock.ColumnBalancingMinHeight_vectors`, `ColumnLayout.cont_ge_min_h` |
| column_layout_algorithm_test.cc:2960 | ColumnLayoutAlgorithmTest.ColumnBalancingMaxHeight | geometry | formalized | `TestsBlock.ColumnBalancingMaxHeight_vectors`, `ColumnLayout.bal_h_le_max_h` |
| column_layout_algorithm_test.cc:2993 | ColumnLayoutAlgorithmTest.ColumnBalancingMinHeightLargerThanMaxHeight | geometry | formalized | `TestsBlock.ColumnBalancingMinHeightLargerThanMaxHeight_vectors`, `ColumnLayout.cont_ge_min_h` |
| column_layout_algorithm_test.cc:3027 | ColumnLayoutAlgorithmTest.ColumnBalancingFixedHeightMinHeight | geometry | formalized | `TestsBlock.ColumnBalancingFixedHeightMinHeight_vectors`, `ColumnLayout.bal_h_le_max_h` |
| column_layout_algorithm_test.cc:3063 | ColumnLayoutAlgorithmTest.ColumnBalancing100By3 | geometry | formalized | `TestsBlock.ColumnBalancing100By3_vectors`, `ColumnLayout.bal_col_count_ge_one` |
| column_layout_algorithm_test.cc:3086 | ColumnLayoutAlgorithmTest.ColumnBalancingEmpty | geometry | formalized | `TestsBlock.ColumnBalancingEmpty_vectors`, `ColumnLayout.bal_col_count_empty` |
| column_layout_algorithm_test.cc:3109 | ColumnLayoutAlgorithmTest.ColumnBalancingEmptyBlock | geometry | formalized | `TestsBlock.ColumnBalancingEmptyBlock_vectors`, `ColumnLayout.bal_col_count_empty` |
| column_layout_algorithm_test.cc:3135 | ColumnLayoutAlgorithmTest.ColumnBalancingSingleLine | geometry | formalized | `TestsBlock.ColumnBalancingSingleLine_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3163 | ColumnLayoutAlgorithmTest.ColumnBalancingSingleLineInNested | geometry | formalized | `TestsBlock.ColumnBalancingSingleLineNested_vectors`, `ColumnLayout.layoutBalancedMulticol`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §3.4, §4) |
| column_layout_algorithm_test.cc:3195 | ColumnLayoutAlgorithmTest.ColumnBalancingSingleLineInNestedSpanner | geometry | formalized | `TestsBlock.ColumnBalancingSingleLineNested_vectors`, `ColumnLayout.layoutBalancedMulticol`, `ColumnLayout.layoutMulticolWithSpanners` (CSS Multicol 1 §4, §6) |
| column_layout_algorithm_test.cc:3229 | ColumnLayoutAlgorithmTest.ColumnBalancingOverflow | geometry | formalized | `TestsBlock.ColumnBalancingOverflow_vectors`, `ColumnLayout.bal_h_unconst` |
| column_layout_algorithm_test.cc:3264 | ColumnLayoutAlgorithmTest.ColumnBalancingLines | geometry | formalized | `TestsBlock.ColumnBalancingLines_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3302 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesOrphans | geometry | formalized | `TestsBlock.ColumnBalancingLinesOrphans_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3348 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesForcedBreak | geometry | formalized | `TestsBlock.ColumnBalancingLinesForcedBreak_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3394 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesForcedBreak2 | geometry | formalized | `TestsBlock.ColumnBalancingLinesForcedBreak2_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3447 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesForcedBreak3 | geometry | formalized | `TestsBlock.ColumnBalancingLinesForcedBreak3_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3506 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesAvoidBreakInside | geometry | formalized | `TestsBlock.ColumnBalancingLinesAvoidBreakInside_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3552 | ColumnLayoutAlgorithmTest.ColumnBalancingLinesAvoidBreakInside2 | geometry | formalized | `TestsBlock.ColumnBalancingLinesAvoidBreakInside2_vectors`, `ColumnLayout.bal_h_step_multiple` |
| column_layout_algorithm_test.cc:3597 | ColumnLayoutAlgorithmTest.ColumnBalancingUnderflow | geometry | formalized | `TestsBlock_ColumnFloatBreak.columnBalancingUnderflow`, `ColumnFloatBreak.layoutBalancedNegativeMargin`, `ColumnFloatBreak.balancedNegativeMargin_le_childH` |
| column_layout_algorithm_test.cc:3623 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBfc | geometry | blocked | needs class C break point resolution in multicolumn |
| column_layout_algorithm_test.cc:3660 | ColumnLayoutAlgorithmTest.NoClassCBreakPointBeforeBfc | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.no_class_c_when_margin_clears_float` (CSS Fragmentation 3 §4.1, CSS 2.1 §9.5.2) |
| column_layout_algorithm_test.cc:3696 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBfcWithClearance | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.hasClassCBreakpoint` (CSS Fragmentation 3 §4.1, CSS 2.1 §9.5.2) |
| column_layout_algorithm_test.cc:3733 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBfcWithMargin | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.hasClassCBreakpoint` (CSS Fragmentation 3 §4.1, CSS 2.1 §9.5) |
| column_layout_algorithm_test.cc:3770 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeBlockMarginCollapsing | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.hasClassCBreakpoint` (CSS Fragmentation 3 §4.1, CSS 2.1 §8.3.1, §9.5.2; inner 33x20 grandchild shares 44x20 child block size) |
| column_layout_algorithm_test.cc:3813 | ColumnLayoutAlgorithmTest.NoClassCBreakPointBeforeBlockMarginCollapsing | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.no_class_c_when_margin_clears_float` (CSS Fragmentation 3 §4.1, CSS 2.1 §8.3.1, §9.5.2; inner 33x20 grandchild shares 44x20 child block size) |
| column_layout_algorithm_test.cc:3856 | ColumnLayoutAlgorithmTest.ClassCBreakPointBeforeLine | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.hasClassCBreakpoint` (CSS Fragmentation 3 §4.1, CSS 2.1 §9.5) |
| column_layout_algorithm_test.cc:3894 | ColumnLayoutAlgorithmTest.ForcedBreakAtClassCBreakPoint | geometry | formalized | `TestsBlock.ClassCBreakPoint_vectors`, `ColumnBreakAppeal.layoutClassC`, `ColumnBreakAppeal.hasClassCBreakpoint` (CSS Fragmentation 3 §3.1, §4.1) |
| column_layout_algorithm_test.cc:3931 | ColumnLayoutAlgorithmTest.Nested | geometry | formalized | `TestsBlock.ColumnNestedPaddingItems_vectors`, `ColumnNested.layoutNestedItems`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §3.4, §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:3982 | ColumnLayoutAlgorithmTest.NestedWithEdibleMargin | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4019 | ColumnLayoutAlgorithmTest.NestedNoInnerContent | geometry | formalized | `TestsBlock.ColumnNestedPaddingItems_vectors`, `ColumnNested.layoutNestedItems`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §3.4, §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:4051 | ColumnLayoutAlgorithmTest.NestedSomeInnerContent | geometry | formalized | `TestsBlock.ColumnNestedPaddingItems_vectors`, `ColumnNested.layoutNestedItems`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §3.4, §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:4086 | ColumnLayoutAlgorithmTest.NestedLimitedHeight | geometry | formalized | `TestsBlock.ColumnNestedOverflowAndAuto_vectors`, `ColumnNested.layoutNestedItems`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §4, §8.2 overflow columns) |
| column_layout_algorithm_test.cc:4143 | ColumnLayoutAlgorithmTest.NestedLimitedHeightWithPadding | geometry | formalized | `TestsBlock.ColumnNestedBlockChrome_vectors`, `ColumnNested.layoutNestedBlock` (CSS Multicol 1 §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:4179 | ColumnLayoutAlgorithmTest.NestedUnbalancedInnerAutoHeight | geometry | formalized | `TestsBlock.ColumnNestedOverflowAndAuto_vectors`, `ColumnNested.layoutNestedItems`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §4) |
| column_layout_algorithm_test.cc:4225 | ColumnLayoutAlgorithmTest.NestedAtOuterBoundary | geometry | formalized | `TestsBlock.ColumnNestedBlockChrome_vectors`, `ColumnNested.layoutNestedBlock` (CSS Multicol 1 §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:4258 | ColumnLayoutAlgorithmTest.NestedZeroHeightAtOuterBoundary | geometry | formalized | `TestsBlock.ColumnNestedBlockChrome_vectors`, `ColumnNested.layoutNestedBlock` (CSS Multicol 1 §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:4288 | ColumnLayoutAlgorithmTest.NestedWithMarginAtOuterBoundary | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:4321 | ColumnLayoutAlgorithmTest.NestedWithTallBorder | geometry | formalized | `TestsBlock.ColumnNestedBlockChrome_vectors`, `ColumnNested.layoutNestedBlock` (CSS Multicol 1 §4, CSS Fragmentation 3 §3.1) |
| column_layout_algorithm_test.cc:4353 | ColumnLayoutAlgorithmTest.NestedWithTallSpanner | geometry | formalized | `TestsBlock.ColumnNestedBlockChrome_vectors`, `ColumnNested.layoutNestedBlock` (CSS Multicol 1 §4, §6; outer col 0 empty 45x0 column and 22x100 spanner occupy the 100px topChrome) |
| column_layout_algorithm_test.cc:4388 | ColumnLayoutAlgorithmTest.AbsposFitsInOneColumn | geometry | formalized | `TestsBlock_ColumnFloatBreak.absposFitsInOneColumn`, `ColumnFloatBreak.layoutRelWithSingleColAbspos` |
| column_layout_algorithm_test.cc:4415 | ColumnLayoutAlgorithmTest.Spanner | geometry | formalized | `TestsBlock.Spanner_vectors`, `ColumnLayout.spanner_width_auto`, `ColumnLayout.spanner_offset_advances` |
| column_layout_algorithm_test.cc:4468 | ColumnLayoutAlgorithmTest.SpannerWithContent | geometry | formalized | `TestsBlock.SpannerWithContent_vectors` |
| column_layout_algorithm_test.cc:4528 | ColumnLayoutAlgorithmTest.TwoSpannersPercentWidth | geometry | formalized | `TestsBlock.TwoSpannersPercentWidth_vectors` |
| column_layout_algorithm_test.cc:4583 | ColumnLayoutAlgorithmTest.SpannerNoBalancing | geometry | formalized | `TestsBlock.SpannerNoBalancing_vectors` |
| column_layout_algorithm_test.cc:4638 | ColumnLayoutAlgorithmTest.SpannerAtStart | geometry | formalized | `TestsBlock.SpannerAtStart_vectors` |
| column_layout_algorithm_test.cc:4679 | ColumnLayoutAlgorithmTest.SpannerAtEnd | geometry | formalized | `TestsBlock.SpannerAtEnd_vectors` |
| column_layout_algorithm_test.cc:4719 | ColumnLayoutAlgorithmTest.SpannerAlone | geometry | formalized | `TestsBlock.SpannerAlone_vectors` |
| column_layout_algorithm_test.cc:4746 | ColumnLayoutAlgorithmTest.SpannerInBlock | geometry | formalized | `TestsBlock.SpannerAlone_vectors`, `ColumnLayout.layoutMulticolWithSpanners` (CSS Multicol 1 §6; empty 11x0 wrapper slices before/after spanner not separately nested) |
| column_layout_algorithm_test.cc:4781 | ColumnLayoutAlgorithmTest.SpannerWithSiblingsInBlock | geometry | formalized | `TestsBlock.SpannerInBlockAndRow_vectors`, `ColumnLayout.layoutMulticolWithSpanners` (CSS Multicol 1 §6; 11px wrapper inline size around the two 20px column slices not separately nested) |
| column_layout_algorithm_test.cc:4824 | ColumnLayoutAlgorithmTest.SpannerInBlockWithSiblings | geometry | formalized | `TestsBlock.SpannerInBlockAndRow_vectors`, `ColumnLayout.layoutMulticolWithSpanners` (CSS Multicol 1 §6; empty 11x0 wrapper slices not separately nested) |
| column_layout_algorithm_test.cc:4866 | ColumnLayoutAlgorithmTest.SpannerMargins | geometry | formalized | `TestsBlock.SpannerMargins_vectors`, `ColumnLayout.spanner_margin_collapsing` |
| column_layout_algorithm_test.cc:4902 | ColumnLayoutAlgorithmTest.SpannerMarginsRtl | geometry | formalized | `TestsBlock.SpannerMarginsRtl_vectors` |
| column_layout_algorithm_test.cc:4939 | ColumnLayoutAlgorithmTest.FixedSizeMulticolWithSpanner | geometry | formalized | `TestsBlock.FixedSizeMulticolWithSpanner_vectors` |
| column_layout_algorithm_test.cc:4980 | ColumnLayoutAlgorithmTest.MarginAndBorderTopWithSpanner | geometry | formalized | `TestsBlock_ColumnGapSpanner.marginAndBorderTopWithSpanner`, `ColumnGapSpanner.layoutMarginBorderWithSpanner` |
| column_layout_algorithm_test.cc:5018 | ColumnLayoutAlgorithmTest.BreakInsideSpannerWithMargins | geometry | blocked | needs margin collapsing across column boundaries in multicolumn |
| column_layout_algorithm_test.cc:5054 | ColumnLayoutAlgorithmTest.InvalidSpanners | geometry | formalized | `TestsBlock_ColumnGapSpanner.invalidSpanners`, `ColumnGapSpanner.layoutInvalidSpannersInBfc` |
| column_layout_algorithm_test.cc:5101 | ColumnLayoutAlgorithmTest.BreakInsideSpanner | geometry | formalized | `TestsBlock_ColumnGapSpanner.breakInsideSpanner`, `ColumnGapSpanner.fragmentInnerSpanner` |
| column_layout_algorithm_test.cc:5148 | ColumnLayoutAlgorithmTest.BreakInsideSpannerTwice | geometry | formalized | `TestsBlock_ColumnGapSpanner.breakInsideSpannerTwice`, `ColumnGapSpanner.fragmentInnerSpanner` |
| column_layout_algorithm_test.cc:5198 | ColumnLayoutAlgorithmTest.BreakInsideSpannerWithContent | geometry | formalized | `TestsBlock_ColumnGapSpanner.breakInsideSpannerWithContent`, `ColumnGapSpanner.fragmentInnerSpanner` |
| column_layout_algorithm_test.cc:5246 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §3.1, §4.4) |
| column_layout_algorithm_test.cc:5279 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners2 | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §3.1, §4.4) |
| column_layout_algorithm_test.cc:5312 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners3 | geometry | blocked | needs forced breaks (break-before/after: column/page) in multicolumn |
| column_layout_algorithm_test.cc:5351 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners4 | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §3.1 break-before propagation from first child) |
| column_layout_algorithm_test.cc:5390 | ColumnLayoutAlgorithmTest.ForcedBreakBetweenSpanners5 | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.marginAfterBreak` (CSS Fragmentation 3 §3.1, §5.2 margin retained after forced break) |
| column_layout_algorithm_test.cc:5424 | ColumnLayoutAlgorithmTest.SoftBreakBetweenSpanners | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.1, §4.4) |
| column_layout_algorithm_test.cc:5458 | ColumnLayoutAlgorithmTest.SoftBreakBetweenSpanners2 | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.1, §5.2) |
| column_layout_algorithm_test.cc:5493 | ColumnLayoutAlgorithmTest.AvoidSoftBreakBetweenSpanners | geometry | blocked | needs break-inside avoid / break avoid constraints in multicolumn |
| column_layout_algorithm_test.cc:5530 | ColumnLayoutAlgorithmTest.AvoidSoftBreakBetweenSpanners2 | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5574 | ColumnLayoutAlgorithmTest.AvoidSoftBreakBetweenSpanners3 | geometry | formalized | `TestsBlock.AvoidSoftBreakBetweenSpanners_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5624 | ColumnLayoutAlgorithmTest.SoftBreakBetweenRowAndSpanner | geometry | formalized | `TestsBlock.SpannerInBlockAndRow_vectors`, `ColumnLayout.layoutMulticolWithSpanners`, `ColumnBreakAppeal.layoutAppeal` (CSS Multicol 1 §6, CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5671 | ColumnLayoutAlgorithmTest.SpannerAsMulticol | geometry | formalized | `TestsBlock.ColumnNestedOverflowAndAuto_vectors`, `ColumnNested.layoutNestedItems`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §4, §6; middle 140px container splits as 50+50+40 across the 3 outer columns) |
| column_layout_algorithm_test.cc:5723 | ColumnLayoutAlgorithmTest.AvoidBreakBetween | geometry | formalized | `TestsBlock.AvoidBreakBetween_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5762 | ColumnLayoutAlgorithmTest.AvoidAndForceBreakBetween | geometry | formalized | `TestsBlock.AvoidAndForceBreakBetween_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4 Rule 1) |
| column_layout_algorithm_test.cc:5800 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenInFloat | geometry | formalized | `TestsBlock.AvoidBreakBetweenInFloat_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5845 | ColumnLayoutAlgorithmTest.IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid | geometry | formalized | `TestsBlock.IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5892 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenAndInsideIgnoreInside | geometry | formalized | `TestsBlock.AvoidBreakBetweenAndInsideIgnoreInside_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5938 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenAndInside | geometry | formalized | `TestsBlock.AvoidBreakBetweenAndInside_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:5984 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenInsideBreakableParent | geometry | formalized | `TestsBlock.AvoidBreakBetweenInsideBreakableParent_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:6037 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenAfterBreakableSibling | geometry | formalized | `TestsBlock.AvoidBreakBetweenAfterBreakableSibling_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:6092 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenBreakInsidePreviousSibling | geometry | formalized | `TestsBlock.AvoidBreakBetweenBreakInsidePreviousSibling_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:6136 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenHonorOrphansWidows | geometry | formalized | `TestsBlock.AvoidBreakBetweenHonorOrphansWidows_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §3.3, §4.4) |
| column_layout_algorithm_test.cc:6182 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenHonorOrphansWidows2 | geometry | formalized | `TestsBlock.AvoidBreakBetweenHonorOrphansWidows2_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §3.3, §4.4) |
| column_layout_algorithm_test.cc:6225 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenHonorOrphansWidows3 | geometry | formalized | `TestsBlock.AvoidBreakBetweenHonorOrphansWidows3_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §3.3, §4.4) |
| column_layout_algorithm_test.cc:6281 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenIgnoreOrphansWidows | geometry | formalized | `TestsBlock.AvoidBreakBetweenIgnoreOrphansWidows_vectors`, `ColumnBreakAppeal.layoutAppeal`, `ColumnBreakAppeal.avoid_before_dominates_orphans` (CSS Fragmentation 3 §3.3, §4.4 Rules 2–3) |
| column_layout_algorithm_test.cc:6326 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenLinesInsideBreakAvoid | geometry | formalized | `TestsBlock.AvoidBreakBetweenLinesInsideBreakAvoid_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:6375 | ColumnLayoutAlgorithmTest.AvoidBreakBetweenBreakAtEarlyClassC | geometry | formalized | `TestsBlock.AvoidBreakBetweenBreakAtEarlyClassC_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.1, §4.4) |
| column_layout_algorithm_test.cc:6416 | ColumnLayoutAlgorithmTest.AvoidBreakBeforeBlockReplacedContent | geometry | formalized | `TestsBlock.AvoidBreakReplacedContent_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §4.4) |
| column_layout_algorithm_test.cc:6451 | ColumnLayoutAlgorithmTest.TallReplacedContent | geometry | formalized | `TestsBlock.AvoidBreakReplacedContent_vectors`, `ColumnBreakAppeal.layoutAppeal` (CSS Fragmentation 3 §5.1 monolithic replaced elements) |
| column_layout_algorithm_test.cc:6480 | ColumnLayoutAlgorithmTest.GapDecorationBasic | geometry | formalized | `TestsBlock_ColumnGapSpanner.gapDecorationBasic`, `ColumnGapSpanner.crossGaps`, `ColumnGapSpanner.crossGaps_length` (opened column_gap_accumulator.cc to resolve BuildGapGeometry) |
| column_layout_algorithm_test.cc:6553 | ColumnLayoutAlgorithmTest.GapDecorationContentEndPastContainer | geometry | formalized | `TestsBlock_ColumnGapSpanner.gapDecorationContentEndPastContainer`, `ColumnGapSpanner.contentInlineBounds`, `ColumnGapSpanner.contentInlineEnd_ge_box` (opened column_gap_accumulator.cc to resolve BuildGapGeometry) |
| column_layout_algorithm_test.cc:6619 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapOneColumn | geometry | formalized | `TestsBlock_ColumnGapSpanner.gapDecorationColumnWrapOneColumn`, `ColumnGapSpanner.accumulateMainGaps` (opened column_layout_algorithm.cc and column_gap_accumulator.cc to resolve RemainingRowHeightAtOffset and spanner main gaps) |
| column_layout_algorithm_test.cc:6711 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapBasic | geometry | formalized | `TestsBlock_ColumnGapSpanner.gapDecorationColumnWrapBasic`, `ColumnGapSpanner.crossGaps`, `ColumnGapSpanner.accumulateMainGaps` |
| column_layout_algorithm_test.cc:6798 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapAndSpanner | geometry | formalized | `TestsBlock_ColumnGapSpanner.gapDecorationColumnWrapAndSpanner`, `ColumnGapSpanner.crossGaps`, `ColumnGapSpanner.accumulateMainGaps` (opened column_layout_algorithm.cc and column_gap_accumulator.cc to resolve RemainingRowHeightAtOffset and spanner main gaps) |
| column_layout_algorithm_test.cc:6893 | ColumnLayoutAlgorithmTest.GapDecorationColumnWrapLastRowNotFilled | geometry | blocked | needs column gap decorations layout |
| column_layout_algorithm_test.cc:6951 | ColumnLayoutAlgorithmTest.GapDecorationTwoSpanners | geometry | formalized | `TestsBlock_ColumnGapSpanner.gapDecorationTwoSpanners`, `ColumnGapSpanner.crossGaps`, `ColumnGapSpanner.accumulateMainGaps` (opened column_gap_accumulator.cc to resolve spanner main gap offsets) |

| fragmentation_test.cc:25 | FragmentationTest.MultipleFragments | geometry | formalized | `TestsBlock.MultipleFragments_vectors` |
| fragmentation_test.cc:68 | FragmentationTest.MultipleFragmentsAndColumnSpanner | geometry | formalized | `TestsBlock.FragmentationNestedAndSpanner_vectors`, `ColumnLayout.layoutMulticolWithSpanners` (CSS Multicol 1 §4, §6) |
| fragmentation_test.cc:132 | FragmentationTest.MultipleFragmentsNestedMulticol | geometry | formalized | `TestsBlock.FragmentationNestedAndSpanner_vectors`, `ColumnNested.sliceStream`, `ColumnNested.inner_cols_fit_outer` (CSS Multicol 1 §4, CSS Fragmentation 3 §3.1) |
| fragmentation_test.cc:187 | FragmentationTest.HasSeenAllChildrenIfc | behaviour | formalized | `TestsBlock.FragmentationNestedAndSpanner_vectors`, `ColumnNested.ifcBreakTokensHasSeenAll` (CSS Fragmentation 3 §3.1) |
| fragmentation_test.cc:235 | FragmentationTest.InkOverflowInline | geometry | formalized | `TestsBlock_ColumnFloatBreak.inkOverflowInline`, `ColumnFloatBreak.multicolInkOverflow` |
| fragmentation_test.cc:271 | FragmentationTest.OffsetFromOwnerLayoutBoxFloat | geometry | blocked | needs float fragmentation OffsetFromOwnerLayoutBox calculation |
| fragmentation_test.cc:303 | FragmentationTest.OffsetFromOwnerLayoutBoxNested | geometry | formalized | `TestsBlock_ColumnFloatBreak.offsetFromOwnerLayoutBoxNested`, `ColumnFloatBreak.nestedOffsetFromOwnerLayoutBox` |
| fragmentation_test.cc:345 | FragmentationTest.ConsumedBlockSizeOverflowInflow | geometry | formalized | `TestsBlock.ConsumedBlockSizeOverflowInflow_vectors`, `BlockFlow.consumedBlockSize_step` |
| fragmentation_test.cc:373 | FragmentationTest.ConsumedBlockSizeOverflowOutOfFlow | geometry | formalized | `TestsBlock_ColumnFloatBreak.consumedBlockSizeOverflowOutOfFlow`, `BlockFlow.consumedBlockSize_step` |

| flex/flex_layout_algorithm_test.cc:42 | FlexLayoutAlgorithmTest.DetailsFlexDoesntCrash | internal | internal | crash regression with details element styled as display:flex |
| flex/flex_layout_algorithm_test.cc:50 | FlexLayoutAlgorithmTest.ReplacedAspectRatioPrecision | geometry | formalized | `TestsBlock.ReplacedAspectRatioPrecision_vectors` |
| flex/flex_layout_algorithm_test.cc:72 | FlexLayoutAlgorithmTest.GapDecorationsOneLine | geometry | formalized | `TestsBlock.GapDecorationsOneLine_vectors`, `FlexLayout.compute_main_gaps_single` |
| flex/flex_layout_algorithm_test.cc:144 | FlexLayoutAlgorithmTest.GapDecorationsBasic | geometry | formalized | `TestsBlock.GapDecorationsBasic_vectors`, `FlexLayout.compute_main_gaps_empty` |
| flex/flex_layout_algorithm_test.cc:219 | FlexLayoutAlgorithmTest.GapDecorationsContentEndPastContainer | geometry | formalized | `TestsBlock.GapDecorationsContentEndPastContainer_vectors`, `FlexLayout.compute_main_gaps_single` |
| flex/flex_layout_algorithm_test.cc:285 | FlexLayoutAlgorithmTest.GapDecorationsNonAlignedColumn | geometry | formalized | `TestsBlock.GapDecorationsNonAlignedColumn_vectors`, `FlexLayout.compute_cross_gaps_empty` |
| flex/flex_layout_algorithm_test.cc:370 | FlexLayoutAlgorithmTest.GapDecorationsNonAlignedColumn2 | geometry | formalized | `TestsBlock.GapDecorationsNonAlignedColumn2_vectors`, `FlexLayout.compute_cross_gaps_empty` |
| flex/flex_layout_algorithm_test.cc:453 | FlexLayoutAlgorithmTest.GapDecorationsVerticalFlexAlignedCenter | geometry | formalized | `TestsBlock.GapDecorationsVerticalFlexAlignedCenter_vectors`, `FlexLayout.compute_main_gaps_empty` |
| flex/flex_layout_algorithm_test.cc:538 | FlexLayoutAlgorithmTest.GapDecorationsVerticalFlexAlignedStart | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:623 | FlexLayoutAlgorithmTest.GapDecorationsVerticalFlexAlignedStretch | geometry | blocked | needs CSS gap decorations geometry calculation in flexbox |
| flex/flex_layout_algorithm_test.cc:708 | FlexLayoutAlgorithmTest.GapDecorationsColumnFlexDirection | geometry | formalized | `TestsBlock.GapDecorationsColumnFlexDirection_vectors`, `FlexLayout.compute_cross_gaps_empty` |
| flex/flex_layout_algorithm_test.cc:790 | FlexLayoutAlgorithmTest.GapDecorationsContentDistributionGaps | geometry | formalized | `TestsBlock.GapDecorationsContentDistributionGaps_vectors`, `FlexLayout.space_between_gap_two_items` |
| flex/flex_layout_algorithm_test.cc:878 | FlexLayoutAlgorithmTest.GapDecorationsContentDistributionGapsBetweenLines | geometry | formalized | `TestsBlock.GapDecorationsContentDistributionGapsBetweenLines_vectors`, `FlexLayout.compute_main_gaps_empty` |
| flex/flex_layout_algorithm_test.cc:939 | FlexLayoutAlgorithmTest.DevtoolsBasic | behaviour | formalized | `TestsBlock.DevtoolsBasic_vectors` |
| flex/flex_layout_algorithm_test.cc:953 | FlexLayoutAlgorithmTest.DevtoolsWrap | behaviour | formalized | `TestsBlock.DevtoolsWrap_vectors` |
| flex/flex_layout_algorithm_test.cc:968 | FlexLayoutAlgorithmTest.DevtoolsCoordinates | behaviour | formalized | `TestsBlock.DevtoolsCoordinates_vectors` |
| flex/flex_layout_algorithm_test.cc:983 | FlexLayoutAlgorithmTest.DevtoolsOverflow | behaviour | formalized | `TestsBlock.DevtoolsOverflow_vectors` |
| flex/flex_layout_algorithm_test.cc:993 | FlexLayoutAlgorithmTest.DevtoolsWithRelPosItem | behaviour | formalized | `TestsBlock.DevtoolsWithRelPosItem_vectors`, `FlexLayout.flex_nowrap_at_most_one_line` |
| flex/flex_layout_algorithm_test.cc:1012 | FlexLayoutAlgorithmTest.DevtoolsBaseline | behaviour | formalized | `TestsBlock.DevtoolsBaseline_vectors`, `FlexLayout.space_between_gap_zero_free` |
| flex/flex_layout_algorithm_test.cc:1032 | FlexLayoutAlgorithmTest.DevtoolsOneImageItemCrash | internal | internal | crash regression with devtools flex layout on lone image item |
| flex/flex_layout_algorithm_test.cc:1040 | FlexLayoutAlgorithmTest.DevtoolsColumnWrap | behaviour | formalized | `TestsBlock.DevtoolsColumnWrap_vectors` |
| flex/flex_layout_algorithm_test.cc:1052 | FlexLayoutAlgorithmTest.DevtoolsColumnWrapOrtho | behaviour | formalized | `TestsBlock.DevtoolsColumnWrapOrtho_vectors` |
| flex/flex_layout_algorithm_test.cc:1064 | FlexLayoutAlgorithmTest.DevtoolsRowWrapOrtho | behaviour | formalized | `TestsBlock.DevtoolsRowWrapOrtho_vectors` |
| flex/flex_layout_algorithm_test.cc:1077 | FlexLayoutAlgorithmTest.DevtoolsLegacyItem | behaviour | formalized | `TestsBlock.DevtoolsLegacyItem_vectors`, `FlexLayout.flex_nowrap_at_most_one_line` |
| flex/flex_layout_algorithm_test.cc:1091 | FlexLayoutAlgorithmTest.DevtoolsFragmentedItemDoesntCrash | internal | internal | crash regression with fragmented flex item in devtools |
| flex/flex_layout_algorithm_test.cc:1103 | FlexLayoutAlgorithmTest.DevtoolsAutoScrollbar | internal | internal | crash regression / non-null DevtoolsFlexInfo pointer check with auto scrollbar |
| flex/flex_layout_algorithm_test.cc:1127 | FlexLayoutAlgorithmTest.SingleAxisScrollerAutoMinSizeUseCount | internal | internal | checks UseCounter for SingleAxisScrollerAutoMinSize feature |
| layout_flexible_box_test.cc:96 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowHTB | geometry | formalized | `TestsBlock.FlexScroll_row`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:123 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowVLR | geometry | formalized | `TestsBlock.FlexScroll_row`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:151 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowVRL | geometry | formalized | `TestsBlock.FlexScroll_row`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:160 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowReverseHTB | geometry | formalized | `TestsBlock.FlexScroll_rowReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:200 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowReverseVLR | geometry | blocked | held-out row (not transcribed or marked); its source was seen by accident while reading the whole file |
| layout_flexible_box_test.cc:229 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRowReverseVRL | geometry | formalized | `TestsBlock.FlexScroll_rowReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:238 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnHTB | geometry | formalized | `TestsBlock.FlexScroll_column`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:247 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnVLR | geometry | formalized | `TestsBlock.FlexScroll_column`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:256 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnVRL | geometry | formalized | `TestsBlock.FlexScroll_column`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:269 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnReverseHTB | geometry | blocked | held-out row (not transcribed or marked); its source was seen by accident while reading the whole file |
| layout_flexible_box_test.cc:292 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnReverseVLR | geometry | formalized | `TestsBlock.FlexScroll_columnReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:315 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsColumnReverseVRL | geometry | formalized | `TestsBlock.FlexScroll_columnReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:357 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowHTB | geometry | formalized | `TestsBlock.FlexScroll_rtlRow`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:366 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowVLR | geometry | formalized | `TestsBlock.FlexScroll_rtlRow`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:375 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowVRL | geometry | formalized | `TestsBlock.FlexScroll_rtlRow`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:384 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowReverseHTB | geometry | formalized | `TestsBlock.FlexScroll_rtlRowReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:409 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowReverseVLR | geometry | formalized | `TestsBlock.FlexScroll_rtlRowReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:418 | LayoutFlexibleBoxTest.GeometriesWithScrollbarsRTLRowReverseVRL | geometry | formalized | `TestsBlock.FlexScroll_rtlRowReverse`, `FlexScroll.layout` (CSS Flexbox 1 §5.1, CSS Overflow 3 §2.2; scrollbar widths 15/16 from the test's ::-webkit-scrollbar rule) |
| layout_flexible_box_test.cc:427 | LayoutFlexibleBoxTest.ResizedFlexChildRequiresVisualOverflowRecalc | behaviour | blocked | needs flexbox visual overflow invalidation tracking on child resize |
| table/layout_table_section_test.cc:18 | LayoutTableSectionTest.BackgroundIsKnownToBeOpaqueWithLayerAndCollapsedBorder | behaviour | formalized | `TestsBlock.BackgroundIsKnownToBeOpaqueWithLayerAndCollapsedBorder_vectors`, `TableLayout.table_section_background_never_opaque` |
| table/layout_table_section_test.cc:35 | LayoutTableSectionTest.BackgroundIsKnownToBeOpaqueWithBorderSpacing | behaviour | formalized | `TestsBlock.BackgroundIsKnownToBeOpaqueWithBorderSpacing_vectors`, `TableLayout.table_section_background_never_opaque` |
| table/layout_table_section_test.cc:50 | LayoutTableSectionTest.BackgroundIsKnownToBeOpaqueWithEmptyCell | behaviour | formalized | `TestsBlock.BackgroundIsKnownToBeOpaqueWithEmptyCell_vectors`, `TableLayout.table_section_background_never_opaque` |
| table/layout_table_section_test.cc:66 | LayoutTableSectionTest.VisualOverflowWithCollapsedBorders | geometry | formalized | `TestsBlock.SectionVisualOverflowWithCollapsedBorders_vectors`, `BlockOverflow.outline_expands_size` |
| table/layout_table_section_test.cc:99 | LayoutTableSectionTest.RowCollapseNegativeHeightCrash | internal | internal | crash regression in row collapse with negative height |
| table/layout_table_test.cc:21 | LayoutTableTest.OverflowViaOutline | geometry | formalized | `TestsBlock.OverflowViaOutline_vectors`, `BlockOverflow.outline_expands_size` |
| table/layout_table_test.cc:47 | LayoutTableTest.OverflowWithCollapsedBorders | geometry | formalized | `TestsBlock.OverflowWithCollapsedBorders_vectors`, `BlockOverflow.table_border_box_ge_content` |
| table/layout_table_test.cc:88 | LayoutTableTest.CollapsedBorders | geometry | formalized | `TestsBlock.CollapsedBorders_vectors`, `TableLayout.resolve_hidden_zero` |
| table/layout_table_test.cc:143 | LayoutTableTest.CollapsedBordersWithCol | geometry | formalized | `TestsBlock.CollapsedBordersWithCol_vectors`, `TableLayout.resolve_hidden_zero` |
| table/layout_table_test.cc:207 | LayoutTableTest.WidthPercentagesExceedHundred | geometry | blocked | needs table column percentage and max width resolution |
| table/layout_table_test.cc:230 | LayoutTableTest.CloseToMaxWidth | geometry | formalized | `TestsBlock.CloseToMaxWidth_vectors` |
| table/layout_table_test.cc:250 | LayoutTableTest.PaddingWithCollapsedBorder | geometry | formalized | `TestsBlock.PaddingWithCollapsedBorder_vectors`, `TableLayout.collapsed_border_padding_zero` |
| table/layout_table_test.cc:260 | LayoutTableTest.OutOfOrderHeadAndBody | geometry | formalized | `TestsBlock.OutOfOrderHeadAndBody_vectors` |
| table/layout_table_test.cc:279 | LayoutTableTest.OutOfOrderFootAndBody | geometry | formalized | `TestsBlock.OutOfOrderFootAndBody_vectors` |
| table/layout_table_test.cc:298 | LayoutTableTest.OutOfOrderHeadFootAndBody | geometry | formalized | `TestsBlock.OutOfOrderHeadFootAndBody_vectors` |
| table/layout_table_test.cc:330 | LayoutTableTest.VisualOverflowCleared | geometry | formalized | `TestsBlock.VisualOverflowCleared_vectors`, `BlockOverflow.shadow_initial_clears` |
| table/table_layout_utils_test.cc:55 | TableLayoutUtilsTest.DistributeColspanAutoPercent | geometry | formalized | `TestsBlock.DistributeColspanAutoPercent_vectors` |
| table/table_layout_utils_test.cc:93 | TableLayoutUtilsTest.DistributeColspanAutoSizeUnconstrained | geometry | formalized | `TestsBlock.DistributeColspanAutoSizeUnconstrained_vectors` |
| table/table_layout_utils_test.cc:121 | TableLayoutUtilsTest.DistributeColspanAutoSizeConstrained | geometry | formalized | `TestsBlock.DistributeColspanAutoSizeConstrained_vectors` |
| table/table_layout_utils_test.cc:149 | TableLayoutUtilsTest.DistributeColspanAutoExactMaxSize | geometry | formalized | `TestsBlock.DistributeColspanAutoExactMaxSize_vectors`, `TableLayout.sync_exact_max` |
| table/table_layout_utils_test.cc:187 | TableLayoutUtilsTest.ComputeGridInlineMinMax | geometry | formalized | `TestsBlock.ComputeGridInlineMinMax_vectors`, `TableLayout.grid_min_sum` |
| table/table_layout_utils_test.cc:246 | TableLayoutUtilsTest.DistributeRowspanCellToRows | geometry | blocked | needs table rowspan row height distribution algorithm |
| table/table_layout_utils_test.cc:280 | TableLayoutUtilsTest.DistributeSectionFixedBlockSizeToRows | geometry | formalized | `TestsBlock.DistributeSectionFixedBlockSizeToRows_vectors` |
| table/table_layout_utils_test.cc:294 | TableLayoutUtilsTest.DistributeTableBlockSizeToSections | geometry | formalized | `TestsBlock.DistributeTableBlockSizeToSections_vectors` |
| grid/grid_layout_algorithm_test.cc:171 | GridLayoutAlgorithmTest.GridLayoutAlgorithmAvailableRowSizes | geometry | formalized | `TestsBlock.GridLayoutAlgorithmAvailableRowSizes_vectors`, `GridLayout.item_available_size_two_tracks` |
| grid/grid_layout_algorithm_test.cc:209 | GridLayoutAlgorithmTest.GridLayoutAlgorithmGapGeometry | geometry | formalized | `TestsBlock.GridLayoutAlgorithmGapGeometry_vectors`, `GridLayout.compute_grid_gap_midpoints_two` |
| grid/grid_layout_algorithm_test.cc:290 | GridLayoutAlgorithmTest.GapGeomoetryWithSpanningItems | geometry | formalized | `TestsBlock.GapGeomoetryWithSpanningItems_vectors`, `GridLayout.cell_pair_status_same_item` |
| grid/grid_layout_algorithm_test.cc:421 | GridLayoutAlgorithmTest.GapGeometryWithEmptyCellsAndSpanningItems | geometry | formalized | `TestsBlock.GapGeometryWithEmptyCellsAndSpanningItems_vectors`, `GridLayout.cell_pair_status_both_none` |
| grid/grid_layout_algorithm_test.cc:603 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRanges | geometry | formalized | `TestsBlock.GridLayoutAlgorithmRanges_vectors`, `GridLayout.grid_ranges_pair` |
| grid/grid_layout_algorithm_test.cc:650 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesWithAutoRepeater | geometry | formalized | `TestsBlock.GridLayoutAlgorithmRangesWithAutoRepeater_vectors`, `GridLayout.grid_ranges_single` |
| grid/grid_layout_algorithm_test.cc:701 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicit | geometry | formalized | `TestsBlock.GridLayoutAlgorithmRangesImplicit_vectors`, `GridLayout.grid_ranges_length` |
| grid/grid_layout_algorithm_test.cc:764 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitAutoColumns | geometry | formalized | `TestsBlock.GridLayoutAlgorithmRangesImplicitAutoColumns_vectors`, `GridLayout.grid_ranges_empty` |
| grid/grid_layout_algorithm_test.cc:822 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitAutoRows | geometry | formalized | `TestsBlock.GridLayoutAlgorithmRangesImplicitAutoRows_vectors`, `GridLayout.grid_ranges_pair` |
| grid/grid_layout_algorithm_test.cc:881 | GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitMixed | geometry | blocked | needs CSS grid track sizing and range building algorithm |
| grid/grid_layout_algorithm_test.cc:929 | GridLayoutAlgorithmTest.GridLayoutAlgorithmAutoGridPositions | geometry | formalized | `TestsBlock.GridLayoutAlgorithmAutoGridPositions_vectors`, `GridLayout.resolve_auto_grid_positions_single_definite` |
| grid/grid_layout_algorithm_test.cc:1003 | GridLayoutAlgorithmTest.GridLayoutAlgorithmAutoDense | geometry | formalized | `TestsBlock.GridLayoutAlgorithmAutoDense_vectors`, `GridLayout.grid_area_overlaps_symm` |
| grid/grid_layout_algorithm_test.cc:1159 | GridLayoutAlgorithmTest.GridLayoutAlgorithmGridPositions | geometry | formalized | `TestsBlock.GridLayoutAlgorithmGridPositions_vectors`, `GridLayout.grid_ranges_length` |
| grid/grid_layout_algorithm_test.cc:1216 | GridLayoutAlgorithmTest.GridLayoutAlgorithmResolveFixedTrackSizes | geometry | formalized | `TestsBlock.GridLayoutAlgorithmResolveFixedTrackSizes_vectors`, `GridLayout.maximize_track_sizes_empty` |
| grid/grid_layout_algorithm_test.cc:1273 | GridLayoutAlgorithmTest.GridLayoutAlgorithmDetermineGridItemsSpanningIntrinsicOrFlexTracks | geometry | formalized | `TestsBlock.GridLayoutAlgorithmDetermineGridItemsSpanningIntrinsicOrFlexTracks_vectors`, `GridLayout.is_flexible_implies_intrinsic` |
| grid/grid_layout_algorithm_test.cc:1356 | GridLayoutAlgorithmTest.FixedSizePositioning | geometry | formalized | `TestsBlock.FixedSizePositioning_vectors`, `GridLayout.track_offset_zero` |
| grid/grid_layout_algorithm_test.cc:1405 | GridLayoutAlgorithmTest.FixedSizePositioningAutoRows | geometry | formalized | `TestsBlock.FixedSizePositioningAutoRows_vectors` |
| grid/grid_layout_algorithm_test.cc:1462 | GridLayoutAlgorithmTest.SpecifiedPositionsOutOfOrder | geometry | formalized | `TestsBlock.SpecifiedPositionsOutOfOrder_vectors` |
| grid/grid_layout_algorithm_test.cc:1536 | GridLayoutAlgorithmTest.GridWithGap | geometry | formalized | `TestsBlock.GridWithGap_vectors`, `GridLayout.grid_gap_positive` |
| grid/grid_layout_algorithm_test.cc:1586 | GridLayoutAlgorithmTest.GridWithPercentGap | geometry | formalized | `TestsBlock.GridWithPercentGap_vectors`, `GridLayout.resolve_gap_none` |
| grid/grid_layout_algorithm_test.cc:1640 | GridLayoutAlgorithmTest.AutoSizedGridWithGap | geometry | formalized | `TestsBlock.AutoSizedGridWithGap_vectors` |
| grid/grid_layout_algorithm_test.cc:1694 | GridLayoutAlgorithmTest.AutoSizedGridWithPercentageGap | geometry | blocked | needs CSS grid gap geometry calculation |
| grid/grid_layout_algorithm_test.cc:1739 | GridLayoutAlgorithmTest.ItemsSizeWithGap | geometry | formalized | `TestsBlock.ItemsSizeWithGap_vectors` |
| grid/grid_layout_algorithm_test.cc:1800 | GridLayoutAlgorithmTest.PositionedOutOfFlowItems | geometry | formalized | `TestsBlock.PositionedOutOfFlowItems_vectors`, `GridLayout.resolve_grid_oof_justify_end` |
| grid/grid_layout_algorithm_test.cc:1940 | GridLayoutAlgorithmTest.NGGridAxisType | geometry | formalized | `TestsBlock.NGGridAxisType_vectors`, `GridLayout.grid_axis_type_subgrid` |
| grid/grid_layout_algorithm_test.cc:1973 | GridLayoutAlgorithmTest.SubgridLineNameList | geometry | formalized | `TestsBlock.SubgridLineNameList_vectors`, `GridLayout.subgrid_line_names_empty` |
| grid/grid_layout_algorithm_test.cc:2019 | GridLayoutAlgorithmTest.SubgridLineNameListWithRepeaters | geometry | formalized | `TestsBlock.SubgridLineNameListWithRepeaters_vectors`, `GridLayout.expand_subgrid_repeater_length` |
| grid/grid_layout_algorithm_test.cc:2090 | GridLayoutAlgorithmTest.SingleAxisScrollerAutoMinSizeUseCount | internal | internal | checks UseCounter for SingleAxisScrollerAutoMinSize feature |
| grid/grid_layout_algorithm_test.cc:2136 | GridLayoutAlgorithmTest.FragmentedOofInGridPlaceItemsTwice | geometry | formalized | `TestsBlock.FragmentedOofInGridPlaceItemsTwice_vectors`, `GridLayout.uniform_fragment_count_zero_frag` |
| grid/grid_track_collection_test.cc:85 | GridTrackCollectionTest.TestRangeIndexFromGridLine | geometry | formalized | `TestsBlock.TestRangeIndexFromGridLine_vectors`, `GridLayout.range_index_first_track` |
| grid/grid_track_collection_test.cc:119 | GridTrackCollectionTest.TestGridTrackList | geometry | blocked | needs CSS grid track collection sizing and range normalization |
| grid/grid_track_collection_test.cc:171 | GridTrackCollectionTest.TestGridRangeBuilder | geometry | formalized | `TestsBlock.TestGridRangeBuilder_vectors` |
| grid/grid_track_collection_test.cc:188 | GridTrackCollectionTest.TestGridRangeBuilderCollapsed | geometry | formalized | `TestsBlock.TestGridRangeBuilderCollapsed_vectors`, `GridLayout.grid_ranges_start_zero` |
| grid/grid_track_collection_test.cc:208 | GridTrackCollectionTest.TestGridRangeBuilderImplicit | geometry | formalized | `TestsBlock.TestGridRangeBuilderImplicit_vectors`, `GridLayout.split_ranges_empty` |
| grid/grid_track_collection_test.cc:248 | GridTrackCollectionTest.TestGridSetTrackSizeNormalization | geometry | formalized | `TestsBlock.TestGridSetTrackSizeNormalization_vectors`, `GridLayout.normalize_no_flex_min` |
| grid/grid_track_collection_test.cc:300 | GridTrackCollectionTest.TestGridSizingTrackCollectionSetIterator | geometry | formalized | `TestsBlock.TestGridSizingTrackCollectionSetIterator_vectors`, `GridLayout.build_set_counts_empty` |
| grid/grid_track_collection_test.cc:351 | GridTrackCollectionTest.TestGridSizingTrackCollectionExplicitTracks | geometry | formalized | `TestsBlock.TestGridSizingTrackCollectionExplicitTracks_vectors`, `GridLayout.build_track_ranges_empty` |
| grid/grid_track_collection_test.cc:459 | GridTrackCollectionTest.TestGridSizingTrackCollectionImplicitTracks | geometry | formalized | `TestsBlock.TestGridSizingTrackCollectionImplicitTracks_vectors`, `GridLayout.coverage_indices_empty` |
| grid/grid_track_collection_test.cc:539 | GridTrackCollectionTest.TestGridSizingTrackCollectionIntrinsicAndFlexTracks | geometry | formalized | `TestsBlock.TestGridSizingTrackCollectionIntrinsicAndFlexTracks_vectors`, `GridLayout.fixed_track_not_flexible` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:259 | GridLanesLayoutAlgorithmTest.ConstructGridLanesItems | geometry | formalized | `TestsBlock_GridLanesItems.constructGridLanesItems`, `GridLanesItems.resolveSpan` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:310 | GridLanesLayoutAlgorithmTest.GridLanesAutoPlacedItems | geometry | formalized | `TestsBlock_GridLanesItems.gridLanesAutoPlacedItems`, `GridLanesItems.resolveSpan`, `GridLanesItems.resolveSpan_autoPlaced_iff` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:346 | GridLanesLayoutAlgorithmTest.ConstructGridLanesItemsParentAutoPlacedMarksAll | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:378 | GridLanesLayoutAlgorithmTest.BuildRanges | geometry | formalized | `TestsBlock_GridLanesItems.buildRanges`, `GridLanesItems.buildTrackRanges` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:425 | GridLanesLayoutAlgorithmTest.BuildFixedTrackSizes | geometry | formalized | `TestsBlock.GridLanesBuildFixedTrackSizes_vectors`, `GridTrackSizing.sizes` (CSS Grid 1 §11; item contributions hand-resolved from Ahem 10px, see test file) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:455 | GridLanesLayoutAlgorithmTest.CollectGridLanesItemGroups | geometry | formalized | `TestsBlock_GridLanesItems.collectGridLanesItemGroups`, `GridLanesItems.collectItemGroups` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:499 | GridLanesLayoutAlgorithmTest.CollectGridLanesItemGroupsWithBaseline | geometry | formalized | `TestsBlock_GridLanesItems.collectGridLanesItemGroupsWithBaseline`, `GridLanesItems.collectItemGroups` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:559 | GridLanesLayoutAlgorithmTest.ExplicitlyPlacedVirtualItems | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:608 | GridLanesLayoutAlgorithmTest.AutoPlacedVirtualItems | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:662 | GridLanesLayoutAlgorithmTest.BuildIntrinsicTrackSizes | geometry | formalized | `TestsBlock.GridLanesBuildIntrinsicTrackSizes_vectors`, `GridTrackSizing.sizes` (CSS Grid 1 §11; item contributions hand-resolved from Ahem 10px, see test file) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:697 | GridLanesLayoutAlgorithmTest.MaximizeAndStretchAutoTracks | geometry | formalized | `TestsBlock.GridLanesMaximizeAndStretchAutoTracks_vectors`, `GridTrackSizing.sizes` (CSS Grid 1 §11; item contributions hand-resolved from Ahem 10px, see test file) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:737 | GridLanesLayoutAlgorithmTest.ExpandFlexibleTracks | geometry | blocked | held-out row (not transcribed or marked); its source was seen by accident while reading neighbouring tests |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:766 | GridLanesLayoutAlgorithmTest.BuildRowSizes | geometry | formalized | `TestsBlock.GridLanesBuildRowSizes_vectors`, `GridTrackSizing.sizes` (CSS Grid 1 §11; item contributions hand-resolved from Ahem 10px, see test file) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:797 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoPlacement | geometry | formalized | `TestsBlock.AutoFitAutoPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 lane placement) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:837 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoAndExplicitPlacement | geometry | formalized | `TestsBlock.AutoFitAutoAndExplicitPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 lane placement) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:877 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitAutoPlacement | geometry | formalized | `TestsBlock.AutoFillAutoFitAutoPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 lane placement) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:919 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitNoCollapse | geometry | formalized | `TestsBlock.AutoFillAutoFitNoCollapse_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 lane placement) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:962 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoSizeAutoPlacement | geometry | formalized | `TestsBlock.AutoFitAutoSizeAutoPlacement_vectors`, `GridLanes.laneSizes`, `GridLanes.expand_fixed_length` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit; opened grid_lanes_layout_algorithm.cc to resolve ComputeGeometry virtual-item pass) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1005 | GridLanesLayoutAlgorithmTest.ColumnAutoFitAutoSizeAndAutoAndExplicitPlacement | geometry | formalized | `TestsBlock.AutoFitAutoSizeAndAutoAndExplicitPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1050 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitAutoAndAutoPlacement | geometry | formalized | `TestsBlock.ColumnAutoFillAutoFitAutoAndAutoPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1095 | GridLanesLayoutAlgorithmTest.ColumnAutoFillAutoFitAutoNoCollapse | geometry | formalized | `TestsBlock.AutoFillAutoFitAutoNoCollapse_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1138 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoPlacement | geometry | formalized | `TestsBlock.AutoFitAutoPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1180 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoAndExplicitPlacement | geometry | formalized | `TestsBlock.AutoFitAutoAndExplicitPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1222 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitAutoPlacement | geometry | formalized | `TestsBlock.AutoFillAutoFitAutoPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1266 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitNoCollapse | geometry | formalized | `TestsBlock.AutoFillAutoFitNoCollapse_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1311 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoSizeAutoPlacement | geometry | formalized | `TestsBlock.AutoFitAutoSizeAutoPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1356 | GridLanesLayoutAlgorithmTest.RowAutoFitAutoSizeAndAutoAndExplicitPlacement | geometry | formalized | `TestsBlock.AutoFitAutoSizeAndAutoAndExplicitPlacement_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1401 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitAutoAndAutoPlacement | geometry | blocked | needs grid lanes auto-fit / auto-fill placement algorithm |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1447 | GridLanesLayoutAlgorithmTest.RowAutoFillAutoFitAutoNoCollapse | geometry | formalized | `TestsBlock.AutoFillAutoFitAutoNoCollapse_vectors`, `GridLanes.laneSizes` (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1492 | GridLanesLayoutAlgorithmTest.GetFirstEligibleLine | geometry | formalized | `TestsBlock_GridLanesItems.getFirstEligibleLine`, `GridLanesItems.firstEligibleLine` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1533 | GridLanesLayoutAlgorithmTest.GetMaxPositionsForAllTracks | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1549 | GridLanesLayoutAlgorithmTest.IncludeSubgriddedItemsIncludesNestedDescendants | geometry | formalized | `TestsBlock_GridLanesSubgrid.includeSubgriddedItemsIncludesNestedDescendants`, `GridLanesSubgrid.nodeItemLists` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1580 | GridLanesLayoutAlgorithmTest.ItemsSubgriddedToParentExcludesDirectItems | geometry | formalized | `TestsBlock_GridLanesSubgrid.itemsSubgriddedToParentExcludesDirectItems`, `GridLanesSubgrid.nodeItemLists` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1609 | GridLanesLayoutAlgorithmTest.AppendSubgriddedItemsColumns | geometry | formalized | `TestsBlock_GridLanesSubgrid.appendSubgriddedItemsColumns`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.singleSubgridCounts` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1659 | GridLanesLayoutAlgorithmTest.AppendSubgriddedItemsRows | geometry | formalized | `TestsBlock_GridLanesSubgrid.appendSubgriddedItemsRows`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.singleSubgridCounts` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1710 | GridLanesLayoutAlgorithmTest.SubgridRowsIgnoredInColumnGridLanes | geometry | formalized | `TestsBlock_GridLanesSubgrid.subgridRowsIgnoredInColumnGridLanes`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.singleSubgridCounts` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1758 | GridLanesLayoutAlgorithmTest.SubgridColumnsIgnoredInRowGridLanes | geometry | formalized | `TestsBlock_GridLanesSubgrid.subgridColumnsIgnoredInRowGridLanes`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.singleSubgridCounts` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1807 | GridLanesLayoutAlgorithmTest.OrthogonalAppendSubgriddedItemsColumns | geometry | formalized | `TestsBlock_GridLanesSubgrid.orthogonalAppendSubgriddedItemsColumns`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.orthogonal_swaps_axes` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1859 | GridLanesLayoutAlgorithmTest.OrthogonalAppendSubgriddedItemsRows | geometry | formalized | `TestsBlock_GridLanesSubgrid.orthogonalAppendSubgriddedItemsRows`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.orthogonal_swaps_axes` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1914 | GridLanesLayoutAlgorithmTest.AutoPlacedSubgriddedItemsAreAutoPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.autoPlacedSubgriddedItemsAreAutoPlaced`, `GridLanesSubgrid.childAutoPlaced`, `GridLanesSubgrid.childAutoPlaced_of_parentAuto` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:1973 | GridLanesLayoutAlgorithmTest.DefiniteSubgridChildrenAreExplicitlyPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.definiteSubgridChildrenAreExplicitlyPlaced`, `GridLanesSubgrid.childAutoPlaced`, `GridLanesSubgrid.translateSpan` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2036 | GridLanesLayoutAlgorithmTest.OppositeDirectionSubgridReversesChildSpans | geometry | formalized | `TestsBlock_GridLanesSubgrid.oppositeDirectionSubgridReversesChildSpans`, `GridLanesSubgrid.translateSpan`, `GridLanesSubgrid.translateSpan_length` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2093 | GridLanesLayoutAlgorithmTest.OrthogonalSubgridColumnsIgnoredInColumnGridLanes | geometry | formalized | `TestsBlock_GridLanesSubgrid.orthogonalSubgridColumnsIgnoredInColumnGridLanes`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.orthogonal_swaps_axes` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2145 | GridLanesLayoutAlgorithmTest.OrthogonalSubgridRowsIgnoredInRowGridLanes | geometry | formalized | `TestsBlock_GridLanesSubgrid.orthogonalSubgridRowsIgnoredInRowGridLanes`, `GridLanesSubgrid.subgridFlags`, `GridLanesSubgrid.orthogonal_swaps_axes` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2201 | GridLanesLayoutAlgorithmTest.DefiniteSubgridsAtDifferentPositionsProduceSeparateVirtualItems | geometry | formalized | `TestsBlock_GridLanesSubgrid.definiteSubgridsAtDifferentPositionsProduceSeparateVirtualItems`, `GridLanesSubgrid.expandVirtualItems`, `GridLanesSubgrid.translateSpan` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2261 | GridLanesLayoutAlgorithmTest.AutoPlacedSubgridChildrenAreAutoPlacedForVirtualItems | geometry | formalized | `TestsBlock_GridLanesSubgrid.autoPlacedSubgridChildrenAreAutoPlacedForVirtualItems`, `GridLanesSubgrid.expandVirtualItems` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2327 | GridLanesLayoutAlgorithmTest.DefiniteSubgridAutoPlacedChildProducesDefiniteVirtualItem | geometry | formalized | `TestsBlock_GridLanesSubgrid.definiteSubgridAutoPlacedChildProducesDefiniteVirtualItem`, `GridLanesSubgrid.expandVirtualItems`, `GridLanesSubgrid.translateSpan` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2386 | GridLanesLayoutAlgorithmTest.NestedSubgridInAutoPlacedSubgridIsAutoPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.nestedSubgridInAutoPlacedSubgridIsAutoPlaced`, `GridLanesSubgrid.childAutoPlaced`, `GridLanesSubgrid.chainAutoPlaced` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2448 | GridLanesLayoutAlgorithmTest.ExplicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.explicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced`, `GridLanesSubgrid.childAutoPlaced_of_parentAuto`, `GridLanesSubgrid.chainAutoPlaced` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2503 | GridLanesLayoutAlgorithmTest.NestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.nestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced`, `GridLanesSubgrid.childAutoPlaced`, `GridLanesSubgrid.chainAutoPlaced` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2558 | GridLanesLayoutAlgorithmTest.DeepNestedAutoPlacedSubgridsAreAllAutoPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.deepNestedAutoPlacedSubgridsAreAllAutoPlaced`, `GridLanesSubgrid.chainAutoPlaced` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2621 | GridLanesLayoutAlgorithmTest.AllChildrenOfAutoPlacedSubgridAreAutoPlaced | geometry | formalized | `TestsBlock_GridLanesSubgrid.allChildrenOfAutoPlacedSubgridAreAutoPlaced`, `GridLanesSubgrid.childAutoPlaced_of_parentAuto` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2668 | GridLanesLayoutAlgorithmTest.AppendColumnSubgriddedGridLanesItems | geometry | formalized | `TestsBlock_GridLanesSubgrid.appendColumnSubgriddedGridLanesItems`, `GridLanesSubgrid.sizingTreeSize`, `GridLanesSubgrid.singleSubgridCounts` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2709 | GridLanesLayoutAlgorithmTest.AppendRowSubgriddedGridLanesItems | geometry | formalized | `TestsBlock_GridLanesSubgrid.appendRowSubgriddedGridLanesItems`, `GridLanesSubgrid.sizingTreeSize`, `GridLanesSubgrid.singleSubgridCounts` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2744 | GridLanesLayoutAlgorithmTest.GridLanesSubgridIgnoresNonGridAxis | geometry | formalized | `TestsBlock_GridLanesSubgrid.gridLanesSubgridIgnoresNonGridAxis`, `GridLanesSubgrid.sizingTreeSize`, `GridLanesSubgrid.subgridFlags` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2778 | GridLanesLayoutAlgorithmTest.OrthogonalGridLanesSubgridMapsGridAxis | geometry | formalized | `TestsBlock_GridLanesSubgrid.orthogonalGridLanesSubgridMapsGridAxis`, `GridLanesSubgrid.sizingTreeSize`, `GridLanesSubgrid.hasSubCols` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2807 | GridLanesLayoutAlgorithmTest.BuildsNestedGridLanesSubgrids | geometry | formalized | `TestsBlock_GridLanesSubgrid.buildsNestedGridLanesSubgrids`, `GridLanesSubgrid.sizingTreeSize` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2842 | GridLanesLayoutAlgorithmTest.GridLanesDirectionChangeMarksPlacementDirty | behaviour | formalized | `TestsBlock_GridLanesSubgrid.gridLanesDirectionChangeMarksPlacementDirty`, `GridLanesSubgrid.placementDirty` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2870 | GridLanesLayoutAlgorithmTest.GridLanesPackChangeMarksPlacementDirty | behaviour | formalized | `TestsBlock_GridLanesSubgrid.gridLanesPackChangeMarksPlacementDirty`, `GridLanesSubgrid.placementDirty` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2899 | GridLanesLayoutAlgorithmTest.ResolvedGridAxisFlipMarksPlacementDirty | behaviour | formalized | `TestsBlock_GridLanesSubgrid.resolvedGridAxisFlipMarksPlacementDirty`, `GridLanesSubgrid.resolveAxis`, `GridLanesSubgrid.placementDirty` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2925 | GridLanesLayoutAlgorithmTest.GapGeometryColumn | geometry | formalized | `TestsBlock.GapGeometryColumn_vectors`, `GridLanesGap.gridAxisGaps` (CSS Gap Decorations 1 §3.1, §3.2; C++ container-type and main-direction enum tags on GapGeometry not modelled) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:2979 | GridLanesLayoutAlgorithmTest.GapGeometryRow | geometry | formalized | `TestsBlock.GapGeometryRow_vectors`, `GridLanesGap.gridAxisGaps` (CSS Gap Decorations 1 §3.1, §3.2; C++ main-direction enum tag on GapGeometry not modelled) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3031 | GridLanesLayoutAlgorithmTest.GapGeometryEmptyExplicitTracks | geometry | formalized | `TestsBlock.GapGeometryEmptyExplicitTracks_vectors`, `GridLanesGap.gridAxisGaps` (CSS Gap Decorations 1 §3.1, §3.2) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3066 | GridLanesLayoutAlgorithmTest.GapGeometrySingleTrack | geometry | formalized | `TestsBlock.GapGeometrySingleTrack_vectors`, `GridLanesGap.gridAxisGaps` (CSS Gap Decorations 1 §3.1, §3.2) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3096 | GridLanesLayoutAlgorithmTest.GapGeometryRequiresGapRule | geometry | formalized | `TestsBlock.GapGeometryRequiresGapRule_vectors`, `GridLanesGap.gridAxisGaps` (CSS Gap Decorations 1 §3.1, §3.2) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3125 | GridLanesLayoutAlgorithmTest.GapGeometryCollapsedAutoFitTracks | geometry | formalized | `TestsBlock.GapGeometryCollapsedAutoFitTracks_vectors`, `GridLanesGap.gridAxisGaps`, `GridLanes.laneSizes` (CSS Gap Decorations 1 §3.2, CSS Grid 3 §repeat-auto-fit) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3171 | GridLanesLayoutAlgorithmTest.GapGeometryGridAxisAlignment | geometry | formalized | `TestsBlock.GapGeometryGridAxisAlignment_vectors`, `GridLanesGap.centerStart`, `GridLanesGap.gridAxisGaps` (CSS Box Alignment 3 §5.3, CSS Gap Decorations 1 §3.2) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3219 | GridLanesLayoutAlgorithmTest.GapGeometryColumnStackingAxisOverflow | geometry | blocked | needs grid lanes gap geometry calculation |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3265 | GridLanesLayoutAlgorithmTest.GapGeometryRowStackingAxisOverflow | geometry | formalized | `TestsBlock.GapGeometryRowStackingAxisOverflow_vectors`, `GridLanesGap.stackContent`, `GridLanesGap.stackContent_ge_box` (CSS Gap Decorations 1 §3.3) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3310 | GridLanesLayoutAlgorithmTest.PopulateGridLanesBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateGridLanesBreakTokenData`, `GridLanesPlacement.directLaneCounts`, `GridLanesPlacement.placeAligned` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3346 | GridLanesLayoutAlgorithmTest.SharePlacementDataAcrossFragments | geometry | formalized | `TestsBlock_GridLanesPlacement.sharePlacementDataAcrossFragments`, `GridLanesPlacement.sharePlacementAcrossFragments` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3385 | GridLanesLayoutAlgorithmTest.ShareExpansionDataAcrossFragments | geometry | formalized | `TestsBlock_GridLanesPlacement.shareExpansionDataAcrossFragments`, `GridLanesPlacement.shareExpansionAcrossFragments` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3419 | GridLanesLayoutAlgorithmTest.PopulateRowGridLanesBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowGridLanesBreakTokenData`, `GridLanesPlacement.directLaneCounts`, `GridLanesPlacement.placeAligned` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3446 | GridLanesLayoutAlgorithmTest.PopulateSpannerBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3501 | GridLanesLayoutAlgorithmTest.PopulateDensePackedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateDensePackedBreakTokenData`, `GridLanesPlacement.placeDenseInOpening`, `GridLanesPlacement.alignOffset_le_avail` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3535 | GridLanesLayoutAlgorithmTest.PopulateDensePackedSpannerBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateDensePackedSpannerBreakTokenData`, `GridLanesPlacement.directLaneCounts`, `GridLanesPlacement.placeDenseInOpening` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3572 | GridLanesLayoutAlgorithmTest.PopulateDenseSpannerWithDifferentParentsPerLane | geometry | formalized | `TestsBlock_GridLanesPlacement.populateDenseSpannerWithDifferentParentsPerLane`, `GridLanesPlacement.directLaneCounts`, `GridLanesPlacement.placeDenseInOpening` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3637 | GridLanesLayoutAlgorithmTest.PopulateDenseItemAboveDenseSpannerUsesParentSpanner | geometry | formalized | `TestsBlock_GridLanesPlacement.populateDenseItemAboveDenseSpannerUsesParentSpanner`, `GridLanesPlacement.directLaneCounts`, `GridLanesPlacement.placeDenseInOpening` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3674 | GridLanesLayoutAlgorithmTest.PopulateDenseItemsUseCorrectSpannerForMultipleOpenings | geometry | blocked | needs grid lanes layout algorithm (masonry / lanes layout) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3718 | GridLanesLayoutAlgorithmTest.PopulateGridAxisAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateGridAxisAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.alignOffset_le_avail` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3752 | GridLanesLayoutAlgorithmTest.PopulateRowGridAxisAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowGridAxisAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.alignOffset_le_avail` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3785 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateStackingAxisAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize_none_of_explicit` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3810 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowStackingAxisAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize_none_of_explicit` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3835 | GridLanesLayoutAlgorithmTest.PopulateExplicitStackingAxisStretchBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateExplicitStackingAxisStretchBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize_none_of_explicit` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3862 | GridLanesLayoutAlgorithmTest.PopulateRowExplicitStackingAxisStretchBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowExplicitStackingAxisStretchBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize_none_of_explicit` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3889 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisStretchSpaceBreakTokenData | geometry | blocked | needs grid lanes fragmentation break token data tracking |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3914 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisStretchSpaceBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowStackingAxisStretchSpaceBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3940 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisStretchSpannerSpaceBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateStackingAxisStretchSpannerSpaceBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:3976 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisStretchSpannerSpaceBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowStackingAxisStretchSpannerSpaceBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4012 | GridLanesLayoutAlgorithmTest.PopulateLastStackingAxisAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateLastStackingAxisAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4042 | GridLanesLayoutAlgorithmTest.PopulateRowLastStackingAxisAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowLastStackingAxisAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.stretchSize` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4073 | GridLanesLayoutAlgorithmTest.PopulateStackingAxisAlignedSpannerBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateStackingAxisAlignedSpannerBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.alignOffset_le_avail` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4104 | GridLanesLayoutAlgorithmTest.PopulateRowStackingAxisAlignedSpannerBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowStackingAxisAlignedSpannerBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.alignOffset_le_avail` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4135 | GridLanesLayoutAlgorithmTest.PopulateContentAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateContentAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.contentShift` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4163 | GridLanesLayoutAlgorithmTest.PopulateRowContentAlignedBreakTokenData | geometry | formalized | `TestsBlock_GridLanesPlacement.populateRowContentAlignedBreakTokenData`, `GridLanesPlacement.placeAligned`, `GridLanesPlacement.contentShift` |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4191 | GridLanesLayoutAlgorithmTest.PopulateColumnFillAndTrackReverseBreakTokenData | geometry | formalized | `TestsBlock_GridLanesItems.populateColumnFillAndTrackReverseBreakTokenData`, `GridLanesItems.placeFillReverse`, `GridLanesItems.placeFillReverse_end_pos` (opened grid_lanes_layout_algorithm.cc to resolve fill-reverse alignment adjustment) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4236 | GridLanesLayoutAlgorithmTest.PopulateRowFillAndTrackReverseBreakTokenData | geometry | formalized | `TestsBlock_GridLanesItems.populateRowFillAndTrackReverseBreakTokenData`, `GridLanesItems.placeFillReverse`, `GridLanesItems.orderForFillReverse` (opened grid_lanes_layout_algorithm.cc to resolve fill-reverse alignment adjustment) |
| grid_lanes/grid_lanes_layout_algorithm_test.cc:4281 | GridLanesLayoutAlgorithmTest.PopulateIndefiniteFillReverseBreakTokenData | geometry | formalized | `TestsBlock_GridLanesItems.populateIndefiniteFillReverseBreakTokenData`, `GridLanesItems.placeFillReverse`, `GridLanesItems.orderForFillReverse` (opened grid_lanes_layout_algorithm.cc to resolve deferred fill-reverse in pre-fragmentation collection) |
| layout_box_test.cc:45 | LayoutBoxTest.BackgroundIsKnownToBeObscured | behaviour | formalized | `TestsBlock_BoxPaint.backgroundIsKnownToBeObscured`, `BlockBoxPaint.backgroundKnownObscured` |
| layout_box_test.cc:59 | LayoutBoxTest.BackgroundNotObscuredWithCssClippedChild | behaviour | formalized | `TestsBlock_BoxPaint.backgroundNotObscuredWithCssClippedChild`, `BlockBoxPaint.backgroundKnownObscured`, `BlockBoxPaint.backgroundKnownObscured_false_when_clipped` |
| layout_box_test.cc:88 | LayoutBoxTest.BackgroundNotObscuredWithCssClippedGrandChild | behaviour | formalized | `TestsBlock_BoxPaint.backgroundNotObscuredWithCssClippedGrandChild`, `BlockBoxPaint.backgroundKnownObscured`, `BlockBoxPaint.backgroundKnownObscured_false_when_clipped` |
| layout_box_test.cc:127 | LayoutBoxTest.ForegroundIsKnownToBeOpaqueInRect | behaviour | formalized | `TestsBlock_BoxPaint.foregroundIsKnownToBeOpaqueInRect`, `BlockBoxPaint.foregroundKnownOpaqueInRect` |
| layout_box_test.cc:161 | LayoutBoxTest.ForegroundIsKnownToBeOpaqueInRectVerticalRL | behaviour | formalized | `TestsBlock_BoxPaint.foregroundIsKnownToBeOpaqueInRectVerticalRL`, `BlockBoxPaint.foregroundKnownOpaqueInRect` |
| layout_box_test.cc:197 | LayoutBoxTest.BackgroundRect | behaviour | formalized | `TestsBlock_BoxPaint.backgroundRect`, `BlockBoxPaint.physicalBackgroundRects` |
| layout_box_test.cc:356 | LayoutBoxTest.LocationContainer | geometry | formalized | `TestsBlock_BoxPaint.locationContainer`, `BlockBoxPaint.resolveLocationContainer` |
| layout_box_test.cc:386 | LayoutBoxTest.TopLeftLocationFlipped | geometry | formalized | `TestsBlock.TopLeftLocationFlipped_vectors` |
| layout_box_test.cc:401 | LayoutBoxTest.TableRowCellTopLeftLocationFlipped | geometry | formalized | `TestsBlock.TableRowCellTopLeftLocationFlipped_vectors` |
| layout_box_test.cc:435 | LayoutBoxTest.LocationContainerOfSVG | geometry | formalized | `TestsBlock_BoxPaint.locationContainerOfSVG`, `BlockBoxPaint.resolveLocationContainer` |
| layout_box_test.cc:465 | LayoutBoxTest.ControlClip | geometry | formalized | `TestsBlock.ControlClip_vectors`, `BlockOverflow.control_clip_rect_bounds` |
| layout_box_test.cc:482 | LayoutBoxTest.VisualOverflowRectWithBlockChild | geometry | formalized | `TestsBlock.VisualOverflowRectWithBlockChild_vectors`, `BlockOverflow.visual_overflow_unclipped_ge_child` |
| layout_box_test.cc:494 | LayoutBoxTest.VisualOverflowRectWithLegacyChild | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:506 | LayoutBoxTest.VisualOverflowRectWithMask | geometry | formalized | `TestsBlock.VisualOverflowRectWithMask_vectors`, `BlockOverflow.mask_zero_outset_eq_border_box` |
| layout_box_test.cc:522 | LayoutBoxTest.VisualOverflowRectWithMaskAndOverflowHidden | geometry | formalized | `TestsBlock.VisualOverflowRectWithMaskAndOverflowHidden_vectors`, `BlockOverflow.mask_zero_outset_eq_border_box` |
| layout_box_test.cc:538 | LayoutBoxTest.VisualOverflowRectWithMaskWithOutset | geometry | blocked | needs LayoutBox visual overflow calculation with masks/filters |
| layout_box_test.cc:555 | LayoutBoxTest.VisualOverflowRectWithMaskWithOutsetAndOverflowHidden | geometry | formalized | `TestsBlock.VisualOverflowRectWithMaskWithOutsetAndOverflowHidden_vectors`, `BlockOverflow.mask_zero_outset_eq_border_box` |
| layout_box_test.cc:572 | LayoutBoxTest.VisualOverflowRectOverflowHidden | geometry | formalized | `TestsBlock.VisualOverflowRectOverflowHidden_vectors`, `BlockOverflow.visual_overflow_clipped_le_bound` |
| layout_box_test.cc:587 | LayoutBoxTest.VisualOverflowRectOverflowClip | geometry | formalized | `TestsBlock.VisualOverflowRectOverflowClip_vectors`, `BlockOverflow.visual_overflow_clipped_le_bound` |
| layout_box_test.cc:623 | LayoutBoxTest.VisualOverflowRectWithOverflowClipMargin | geometry | formalized | `TestsBlock.VisualOverflowRectWithOverflowClipMargin_vectors`, `BlockOverflow.visual_overflow_clipped_le_bound` |
| layout_box_test.cc:670 | LayoutBoxTest.ContentsVisualOverflowPropagation | geometry | formalized | `TestsBlock_BoxPaint.contentsVisualOverflowPropagation`, `BlockBoxPaint.rectUnion`, `BlockBoxPaint.rectUnion_comm` |
| layout_box_test.cc:717 | LayoutBoxTest.HitTestOverflowClipMargin | behaviour | formalized | `TestsBlock_BoxPaint.hitTestOverflowClipMargin`, `BlockBoxPaint.hitTestBoxWithClipAndResizer` |
| layout_box_test.cc:737 | LayoutBoxTest.HitTestContainPaint | behaviour | formalized | `TestsBlock_BoxPaint.hitTestContainPaint`, `BlockBoxPaint.hitTestBoxWithClipAndResizer` |
| layout_box_test.cc:751 | LayoutBoxTest.OverflowRectsContainPaint | geometry | formalized | `TestsBlock.OverflowRectsContainPaint_vectors`, `BlockOverflow.contain_paint_clips_both` |
| layout_box_test.cc:769 | LayoutBoxTest.OverflowRectsOverflowHidden | geometry | formalized | `TestsBlock.OverflowRectsOverflowHidden_vectors`, `BlockOverflow.visual_overflow_clipped_le_bound` |
| layout_box_test.cc:787 | LayoutBoxTest.SetTextFieldIntrinsicInlineSize | geometry | formalized | `TestsBlock.SetTextFieldIntrinsicInlineSize_vectors`, `BlockLength.textFieldIntrinsicInlineSize_fixed` |
| layout_box_test.cc:816 | LayoutBoxTest.DelayedInvalidation | behaviour | formalized | `TestsBlock_BoxPaint.delayedInvalidation`, `BlockBoxPaint.imageChangedInvalidation` |
| layout_box_test.cc:849 | LayoutBoxTest.DelayedInvalidationLayoutViewScrolled | behaviour | formalized | `TestsBlock_BoxPaint.delayedInvalidationLayoutViewScrolled`, `BlockBoxPaint.imageChangedInvalidation` |
| layout_box_test.cc:891 | LayoutBoxTest.MarkerContainerScrollableOverflowRect | geometry | formalized | `TestsBlock_BoxPaint.markerContainerScrollableOverflowRect` |
| layout_box_test.cc:934 | LayoutBoxTest.LocationOfAbsoluteChildWithContainerScrollbars | geometry | formalized | `TestsBlock.LocationOfAbsoluteChildWithContainerScrollbars_vectors`, `BlockScroll.abs_loc_eq_origin_add` |
| layout_box_test.cc:990 | LayoutBoxTest.LocationOfAbsoluteChildWithContainerScrollbarsDifferentWritingModes | geometry | formalized | `TestsBlock.LocationOfAbsoluteChildWithContainerScrollbarsDifferentWritingModes_vectors`, `BlockScroll.abs_loc_eq_origin_add` |
| layout_box_test.cc:1039 | LayoutBoxTest.LocationOfAbsoluteAutoTopLeftChildWithContainerScrollbars | geometry | formalized | `TestsBlock.LocationOfAbsoluteAutoTopLeftChildWithContainerScrollbars_vectors`, `BlockScroll.scrollbar_left_zero` |
| layout_box_test.cc:1103 | LayoutBoxTest.LocationOfAbsoluteAutoTopLeftGrandChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1165 | LayoutBoxTest.LocationOfInFlowChildWithContainerScrollbars | geometry | formalized | `TestsBlock.LocationOfInFlowChildWithContainerScrollbars_vectors`, `BlockScroll.scrollbar_left_zero` |
| layout_box_test.cc:1234 | LayoutBoxTest.LocationOfRelativeChildWithContainerScrollbars | geometry | formalized | `TestsBlock.LocationOfRelativeChildWithContainerScrollbars_vectors`, `BlockScroll.rel_loc_eq_inflow_add` |
| layout_box_test.cc:1289 | LayoutBoxTest.LocationOfFloatLeftChildWithContainerScrollbars | geometry | formalized | `TestsBlock.LocationOfFloatLeftChildWithContainerScrollbars_vectors`, `BlockScroll.scrollbar_left_zero` |
| layout_box_test.cc:1345 | LayoutBoxTest.LocationOfFloatRightChildWithContainerScrollbars | geometry | blocked | needs LayoutBox physical location resolution under scrollbars/writing modes |
| layout_box_test.cc:1405 | LayoutBoxTest.GeometriesWithScrollbarsNonScrollable | geometry | formalized | `TestsBlock.FlexScroll_nonScrollable`, `FlexScroll.no_overflow_zero_scroll`, `FlexScroll.layout` (CSS Overflow 3 §2.2, §2.3) |
| layout_box_test.cc:1500 | LayoutBoxTest.GeometriesWithScrollbarsScrollable | geometry | formalized | `TestsBlock.FlexScroll_row`, `TestsBlock.FlexScroll_rtlRow`, `FlexScroll.layout` (CSS Overflow 3 §2.2, §2.3) |
| layout_box_test.cc:1624 | LayoutBoxTest.ThickScrollbarSubpixelSizeMarginNoDirtyLayoutAfterLayout | internal | internal | checks LayoutBox internal flag/crash regression |
| layout_box_test.cc:1652 | LayoutBoxTest.MenuListIntrinsicBlockSize | internal | internal | crash regression test for content-visibility: hidden select menu list (crbug.com/1108270) |
| layout_box_test.cc:1664 | LayoutBoxTest.HasReflection | geometry | formalized | `TestsBlock_BoxPaint.hasReflection`, `BlockBoxPaint.supportsLayerAndReflection` |
| layout_box_test.cc:1693 | LayoutBoxTest.VisualOverflowRectIncludingFilters | geometry | formalized | `TestsBlock.VisualOverflowRectIncludingFilters_vectors`, `BlockOverflow.filter_blur_outset_nonneg` |
| layout_box_test.cc:1709 | LayoutBoxTest.SetNeedsOverflowRecalcLayoutBox | behaviour | formalized | `TestsBlock_BoxPaint.setNeedsOverflowRecalcLayoutBox`, `BlockBoxPaint.overflowRecalcOnTransformChange` |
| layout_box_test.cc:1732 | LayoutBoxTest.SetNeedsOverflowRecalcFlexBox | behaviour | formalized | `TestsBlock_BoxPaint.setNeedsOverflowRecalcFlexBox`, `BlockBoxPaint.overflowRecalcOnTransformChange` |
| layout_box_test.cc:1755 | LayoutBoxTest.ScrollsWithViewportRelativePosition | behaviour | formalized | `TestsBlock.ScrollsWithViewportRelativePosition_vectors`, `BlockOverflow.fixed_to_view_no_transform` |
| layout_box_test.cc:1760 | LayoutBoxTest.ScrollsWithViewportFixedPosition | behaviour | formalized | `TestsBlock.ScrollsWithViewportFixedPosition_vectors`, `BlockOverflow.fixed_to_view_no_transform` |
| layout_box_test.cc:1765 | LayoutBoxTest.ScrollsWithViewportFixedPositionInsideTransform | behaviour | formalized | `TestsBlock.ScrollsWithViewportFixedPositionInsideTransform_vectors`, `BlockOverflow.transform_cb_not_fixed_to_view` |
| layout_box_test.cc:1775 | LayoutBoxTest.HitTestResizerWithTextAreaChild | behaviour | formalized | `TestsBlock_BoxPaint.hitTestResizerWithTextAreaChild`, `BlockBoxPaint.hitTestBoxWithClipAndResizer` |
| layout_box_test.cc:1790 | LayoutBoxTest.HitTestResizerStackedWithTextAreaChild | behaviour | blocked | needs LayoutBox hit-testing model |
| layout_box_test.cc:1805 | LayoutBoxTest.AnchorInFragmentedContainingBlock | geometry | formalized | `TestsBlock.AnchorInFragmentedContainingBlock_vectors`, `OutOfFlowAnchor.find_anchor_matches` |
| layout_box_test.cc:1849 | LayoutBoxTest.AnchorInInlineContainingBlock | geometry | formalized | `TestsBlock.AnchorInInlineContainingBlock_vectors`, `OutOfFlowAnchor.implicit_anchor_none` |
| layout_box_test.cc:1869 | LayoutBoxTest.AnchorInInlineContainingBlockWithNameConflicts | geometry | formalized | `TestsBlock.AnchorInInlineContainingBlockWithNameConflicts_vectors`, `OutOfFlowAnchor.find_anchor_mismatch` |
| layout_box_test.cc:1906 | LayoutBoxTest.IsUserScrollable | behaviour | formalized | `TestsBlock.IsUserScrollable_vectors`, `BlockOverflow.user_scrollable_implies_overflow` |
| layout_box_test.cc:1935 | LayoutBoxTest.IsUserScrollableLayoutView | behaviour | formalized | `TestsBlock.IsUserScrollableLayoutView_vectors`, `BlockOverflow.scrolls_overflow_hidden` |
| layout_box_test.cc:1957 | LayoutBoxTest.LogicalRectInContainer | geometry | formalized | `TestsBlock.LogicalRectInContainer_vectors`, `BlockWritingMode.logical_rect_in_container_horizontal_tb` |
| layout_box_test.cc:2006 | LayoutBoxTest.VisualOverflowRectWithEmptyInlineChildAndReflectAndOutline | geometry | formalized | `TestsBlock.VisualOverflowRectWithEmptyInlineChildAndReflectAndOutline_vectors`, `BlockOverflow.outline_shifts_origin` |
| layout_box_test.cc:2033 | LayoutBoxTest.ContentBoxFragmentedHtb | geometry | formalized | `TestsBlock.ContentBoxFragmentedHtb_vectors`, `BlockWritingMode.physicalContentBox_horizontal` |
| layout_box_test.cc:2045 | LayoutBoxTest.ContentBoxFragmentedVlr | geometry | formalized | `TestsBlock.ContentBoxFragmentedVlr_vectors`, `BlockWritingMode.physicalContentBox_vertical` |
| layout_box_test.cc:2057 | LayoutBoxTest.ContentBoxFragmentedVrl | geometry | formalized | `TestsBlock.ContentBoxFragmentedVrl_vectors`, `BlockWritingMode.physicalContentBox_vertical` |
| layout_box_test.cc:2069 | LayoutBoxTest.StitchedBlockSize | geometry | formalized | `TestsBlock.StitchedBlockSize_vectors`, `BlockFlow.fragmentation_conserves_size` |
| layout_box_test.cc:2087 | LayoutBoxTest.StitchedBlockSizeVrl | geometry | formalized | `TestsBlock.StitchedBlockSizeVrl_vectors`, `BlockFlow.fragmentation_conserves_size` |
| layout_box_test.cc:2105 | LayoutBoxTest.StitchedSizeWithOverflow | geometry | formalized | `TestsBlock.StitchedSizeWithOverflow_vectors` |
| layout_box_test.cc:2124 | LayoutBoxTest.StitchedSizeWithOverflowVrl | geometry | blocked | needs LayoutBox stitched size across writing modes / printing |
| layout_box_test.cc:2143 | LayoutBoxTest.StitchedSizeAfterRelayout | geometry | formalized | `TestsBlock.StitchedSizeAfterRelayout_vectors`, `BlockFlow.sliceCount_pos` |
| layout_box_test.cc:2166 | LayoutBoxTest.StitchedSizeRepeatedWhenPrinting | geometry | formalized | `TestsBlock.StitchedSizeRepeatedWhenPrinting_vectors`, `BlockFlow.sliceCount_pos` |
| layout_box_test.cc:2232 | LayoutBoxBackgroundPaintLocationTest.ContentBoxClipZeroPadding | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2245 | LayoutBoxBackgroundPaintLocationTest.AttachmentLocalContentBoxClipNonZeroPadding | behaviour | formalized | `TestsBlock_BoxPaint.attachmentLocalContentBoxClipNonZeroPadding`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2259 | LayoutBoxBackgroundPaintLocationTest.NonLocalImage | behaviour | formalized | `TestsBlock_BoxPaint.nonLocalImage`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2274 | LayoutBoxBackgroundPaintLocationTest.LocalImageAndColor | behaviour | formalized | `TestsBlock_BoxPaint.localImageAndColor`, `BlockBoxPaint.backgroundPaintLocation`, `BlockBoxPaint.backgroundPaintLocation_local_contentsSpace` |
| layout_box_test.cc:2288 | LayoutBoxBackgroundPaintLocationTest.LocalImageAndNonLocalClipPaddingColor | behaviour | formalized | `TestsBlock_BoxPaint.localImageAndNonLocalClipPaddingColor`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2306 | LayoutBoxBackgroundPaintLocationTest.LocalImageAndNonLocalClipContentColorNonZeroPadding | behaviour | formalized | `TestsBlock_BoxPaint.localImageAndNonLocalClipContentColorNonZeroPadding`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2323 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorNoBorder | behaviour | formalized | `TestsBlock_BoxPaint.borderBoxClipColorNoBorder`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2335 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorSolidBorder | behaviour | formalized | `TestsBlock_BoxPaint.borderBoxClipColorSolidBorder`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2349 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorSolidBorderWithBorderShape | behaviour | formalized | `TestsBlock_BoxPaint.borderBoxClipColorSolidBorderWithBorderShape`, `BlockBoxPaint.backgroundPaintLocation`, `BlockBoxPaint.backgroundPaintLocation_borderShape_borderBox` |
| layout_box_test.cc:2365 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorTranslucentBorder | behaviour | formalized | `TestsBlock_BoxPaint.borderBoxClipColorTranslucentBorder`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2381 | LayoutBoxBackgroundPaintLocationTest.BorderBoxClipColorDashedBorder | behaviour | formalized | `TestsBlock_BoxPaint.borderBoxClipColorDashedBorder`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2395 | LayoutBoxBackgroundPaintLocationTest.ContentClipColorZeroPadding | behaviour | formalized | `TestsBlock_BoxPaint.contentClipColorZeroPadding`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2407 | LayoutBoxBackgroundPaintLocationTest.ContentClipColorNonZeroPadding | behaviour | formalized | `TestsBlock_BoxPaint.contentClipColorNonZeroPadding`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2420 | LayoutBoxBackgroundPaintLocationTest.CustomScrollbar | behaviour | formalized | `TestsBlock_BoxPaint.customScrollbar`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2438 | LayoutBoxBackgroundPaintLocationTest.TranslucentColorAndTranslucentBorder | behaviour | formalized | `TestsBlock_BoxPaint.translucentColorAndTranslucentBorder`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2454 | LayoutBoxBackgroundPaintLocationTest.LocalImageTranslucentColorAndTransparentBorder | behaviour | blocked | needs LayoutBox background paint location resolution |
| layout_box_test.cc:2471 | LayoutBoxBackgroundPaintLocationTest.InsetBoxShadow | behaviour | formalized | `TestsBlock_BoxPaint.insetBoxShadow`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2485 | LayoutBoxBackgroundPaintLocationTest.OutsetBoxShadow | behaviour | formalized | `TestsBlock_BoxPaint.outsetBoxShadow`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2496 | LayoutBoxBackgroundPaintLocationTest.BorderImage | behaviour | formalized | `TestsBlock_BoxPaint.borderImage`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2509 | LayoutBoxBackgroundPaintLocationTest.ElasticOverscrollEnabledForSubscroll | behaviour | formalized | `TestsBlock_BoxPaint.elasticOverscrollEnabledForSubscroll`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_test.cc:2560 | LayoutBoxBackgroundPaintLocationTest.ElasticOverscrollSupportedForLayoutView | behaviour | formalized | `TestsBlock_BoxPaint.elasticOverscrollSupportedForLayoutView`, `BlockBoxPaint.backgroundPaintLocation` |
| layout_box_model_object_test.cc:48 | LayoutBoxModelObjectTest.LocalCaretRectForEmptyElementVertical | behaviour | formalized | `TestsBlock.LocalCaretRectForEmptyElementVertical_vectors`, `BlockWritingMode.vertical_lr_bar_x` |
| layout_box_model_object_test.cc:143 | LayoutBoxModelObjectTest.StickyPositionConstraints | behaviour | formalized | `TestsBlock.StickyPositionConstraints_vectors`, `BlockSticky.sticky_box_ge_cb_top` |
| layout_box_model_object_test.cc:184 | LayoutBoxModelObjectTest.StickyPositionVerticalRLConstraints | behaviour | formalized | `TestsBlock.StickyPositionVerticalRLConstraints_vectors`, `BlockSticky.sticky_box_ge_cb_top` |
| layout_box_model_object_test.cc:225 | LayoutBoxModelObjectTest.StickyPositionInlineConstraints | behaviour | formalized | `TestsBlock.StickyPositionInlineConstraints_vectors`, `BlockSticky.cb_interval_top_monotone` |
| layout_box_model_object_test.cc:275 | LayoutBoxModelObjectTest.StickyPositionVerticalRLInlineConstraints | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:330 | LayoutBoxModelObjectTest.StickyPositionTransforms | behaviour | formalized | `TestsBlock.StickyPositionTransforms_vectors`, `BlockSticky.sticky_box_ge_cb_top` |
| layout_box_model_object_test.cc:368 | LayoutBoxModelObjectTest.StickyPositionPercentageStyles | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:410 | LayoutBoxModelObjectTest.StickyPositionContainerIsScroller | behaviour | formalized | `TestsBlock.StickyPositionContainerIsScroller_vectors`, `BlockSticky.sticky_box_ge_cb_top` |
| layout_box_model_object_test.cc:440 | LayoutBoxModelObjectTest.SingleAxisScrollerPositionStickyUseCount | internal | internal | Blink use counter check |
| layout_box_model_object_test.cc:490 | LayoutBoxModelObjectTest.NoSingleAxisScrollerPositionStickyUseCountWhenDisabled | internal | internal | Blink use counter check |
| layout_box_model_object_test.cc:506 | LayoutBoxModelObjectTest.StickyPositionAnonymousContainer | behaviour | formalized | `TestsBlock.StickyPositionAnonymousContainer_vectors`, `BlockSticky.sticky_box_ge_cb_top` |
| layout_box_model_object_test.cc:540 | LayoutBoxModelObjectTest.StickyPositionTableContainers | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:571 | LayoutBoxModelObjectTest.StickyPositionConstraintInvalidation | behaviour | formalized | `TestsBlock.StickyPositionConstraintInvalidation_vectors`, `BlockSticky.sticky_offset_unscrolled` |
| layout_box_model_object_test.cc:610 | LayoutBoxModelObjectTest.StickyPositionStatusChange | behaviour | formalized | `TestsBlock.StickyPositionStatusChange_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:701 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectStickyBoxShiftingAncestor | behaviour | formalized | `TestsBlock.StickyPositionFindsCorrectStickyBoxShiftingAncestor_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:764 | LayoutBoxModelObjectTest.StickyPositionInlineBlockUnderStickyInline | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:805 | LayoutBoxModelObjectTest.StickyPositionFindsNearestStickyInlineForBlockChild | behaviour | formalized | `TestsBlock.StickyPositionFindsNearestStickyInlineForBlockChild_vectors`, `BlockSticky.find_nearest_sticky_box_empty` |
| layout_box_model_object_test.cc:843 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectContainingBlockShiftingAncestor | behaviour | formalized | `TestsBlock.StickyPositionFindsCorrectContainingBlockShiftingAncestor_vectors`, `BlockSticky.find_nearest_containing_block_empty` |
| layout_box_model_object_test.cc:905 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectContainingBlockShiftingAncestorRoot | behaviour | formalized | `TestsBlock.StickyPositionFindsCorrectContainingBlockShiftingAncestorRoot_vectors`, `BlockSticky.find_nearest_containing_block_empty` |
| layout_box_model_object_test.cc:940 | LayoutBoxModelObjectTest.StickyPositionFindsCorrectContainingBlockShiftingAncestorTable | behaviour | formalized | `TestsBlock.StickyPositionFindsCorrectContainingBlockShiftingAncestorTable_vectors`, `BlockSticky.find_nearest_containing_block_empty` |
| layout_box_model_object_test.cc:974 | LayoutBoxModelObjectTest.StickyPositionNested | geometry | formalized | `TestsBlock.StickyPositionNested_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1005 | LayoutBoxModelObjectTest.StickyPositionChildHasLargerTop | geometry | formalized | `TestsBlock.StickyPositionChildHasLargerTop_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1036 | LayoutBoxModelObjectTest.StickyPositionParentHasLargerTop | geometry | formalized | `TestsBlock.StickyPositionParentHasLargerTop_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1067 | LayoutBoxModelObjectTest.StickyPositionChildPushingOutsideParent | geometry | formalized | `TestsBlock.StickyPositionChildPushingOutsideParent_vectors`, `BlockSticky.sticky_offset_le_max_shift` |
| layout_box_model_object_test.cc:1100 | LayoutBoxModelObjectTest.StickyPositionTripleNestedDiv | geometry | formalized | `TestsBlock.StickyPositionTripleNestedDiv_vectors`, `BlockSticky.sticky_offset_le_max_shift` |
| layout_box_model_object_test.cc:1138 | LayoutBoxModelObjectTest.StickyPositionNestedStickyTable | geometry | formalized | `TestsBlock.StickyPositionNestedStickyTable_vectors`, `BlockSticky.sticky_offset_le_max_shift` |
| layout_box_model_object_test.cc:1197 | LayoutBoxModelObjectTest.StickyPositionComplexTableNesting | behaviour | blocked | model lacks sticky position constraints and dynamic scrolling |
| layout_box_model_object_test.cc:1230 | LayoutBoxModelObjectTest.StickyPositionNestedInlineElements | geometry | formalized | `TestsBlock.StickyPositionNestedInlineElements_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1268 | LayoutBoxModelObjectTest.StickyPositionNestedFixedPos | geometry | formalized | `TestsBlock.StickyPositionNestedFixedPos_vectors`, `BlockSticky.sticky_offset_le_max_shift` |
| layout_box_model_object_test.cc:1364 | LayoutBoxModelObjectTest.InvalidatePaintLayerOnStackedChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1406 | LayoutBoxModelObjectTest.BackfaceVisibilityChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1434 | LayoutBoxModelObjectTest.ChangingFilterWithWillChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1465 | LayoutBoxModelObjectTest.ChangingWillChangeFilter | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1500 | LayoutBoxModelObjectTest.ChangingBackdropFilterWithWillChange | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1531 | LayoutBoxModelObjectTest.ChangingWillChangeBackdropFilter | behaviour | blocked | model lacks paint layer invalidation and style mutation |
| layout_box_model_object_test.cc:1566 | LayoutBoxModelObjectTest.UpdateStackingContextForOption | internal | internal | Blink option element stacking context check |
| layout_box_model_object_test.cc:1589 | LayoutBoxModelObjectTest.StickyParentContainStrictChangeOverflowProperty | behaviour | formalized | `TestsBlock.StickyParentContainStrictChangeOverflowProperty_vectors`, `BlockSticky.find_containing_scroll_container_empty` |
| layout_box_model_object_test.cc:1618 | LayoutBoxModelObjectTest.RemoveStickyUnderContain | behaviour | formalized | `TestsBlock.RemoveStickyUnderContain_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1643 | LayoutBoxModelObjectTest.ChangeStickyStatusUnderContain | behaviour | formalized | `TestsBlock.ChangeStickyStatusUnderContain_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1671 | LayoutBoxModelObjectTest.ChangeStickyStatusKeepLayerUnderContain | behaviour | formalized | `TestsBlock.ChangeStickyStatusKeepLayerUnderContain_vectors`, `BlockSticky.sticky_offset_none` |
| layout_box_model_object_test.cc:1700 | LayoutBoxModelObjectTest.RemoveStickyStatusInNestedStickyElementsWithContain | behaviour | formalized | `TestsBlock.RemoveStickyStatusInNestedStickyElementsWithContain_vectors`, `BlockSticky.find_nearest_containing_block_empty` |
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
| layout_result_caching_test.cc:51 | LayoutResultCachingTest.HitDifferentExclusionSpace | behaviour | formalized | `TestsBlock_ResultCaching.hitDifferentExclusionSpace`, `BlockResultCache.checkBfcCache` (opened layout_utils.cc to resolve MaySkipLayoutWithinBlockFormattingContext) |
| layout_result_caching_test.cc:84 | LayoutResultCachingTest.HitDifferentBFCOffset | behaviour | formalized | `TestsBlock_ResultCaching.hitDifferentBFCOffset`, `BlockResultCache.checkBfcCache`, `BlockResultCache.shiftedExclusionOpportunities` |
| layout_result_caching_test.cc:144 | LayoutResultCachingTest.HitDifferentBFCOffsetSameMarginStrut | behaviour | formalized | `TestsBlock_ResultCaching.hitDifferentBFCOffsetSameMarginStrut`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:170 | LayoutResultCachingTest.MissDescendantAboveBlockStart1 | behaviour | formalized | `TestsBlock_ResultCaching.missDescendantAboveBlockStart1`, `BlockResultCache.checkBfcCache`, `BlockResultCache.checkBfcCache_aboveStart_floats` |
| layout_result_caching_test.cc:204 | LayoutResultCachingTest.MissDescendantAboveBlockStart2 | behaviour | formalized | `TestsBlock_ResultCaching.missDescendantAboveBlockStart2`, `BlockResultCache.checkBfcCache`, `BlockResultCache.checkBfcCache_aboveStart_floats` |
| layout_result_caching_test.cc:238 | LayoutResultCachingTest.HitOOFDescendantAboveBlockStart | behaviour | formalized | `TestsBlock_ResultCaching.hitOOFDescendantAboveBlockStart`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:272 | LayoutResultCachingTest.HitLineBoxDescendantAboveBlockStart | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:311 | LayoutResultCachingTest.MissFloatInitiallyIntruding1 | behaviour | formalized | `TestsBlock_ResultCaching.missFloatInitiallyIntruding1`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:343 | LayoutResultCachingTest.MissFloatInitiallyIntruding2 | behaviour | formalized | `TestsBlock_ResultCaching.missFloatInitiallyIntruding2`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:375 | LayoutResultCachingTest.MissFloatWillIntrude1 | behaviour | formalized | `TestsBlock_ResultCaching.missFloatWillIntrude1`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:406 | LayoutResultCachingTest.MissFloatWillIntrude2 | behaviour | formalized | `TestsBlock_ResultCaching.missFloatWillIntrude2`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:437 | LayoutResultCachingTest.HitPushedByFloats1 | behaviour | formalized | `TestsBlock_ResultCaching.hitPushedByFloats1`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:468 | LayoutResultCachingTest.HitPushedByFloats2 | behaviour | formalized | `TestsBlock_ResultCaching.hitPushedByFloats2`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:499 | LayoutResultCachingTest.MissPushedByFloats1 | behaviour | formalized | `TestsBlock_ResultCaching.missPushedByFloats1`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:531 | LayoutResultCachingTest.MissPushedByFloats2 | behaviour | formalized | `TestsBlock_ResultCaching.missPushedByFloats2`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:563 | LayoutResultCachingTest.HitDifferentRareData | behaviour | formalized | `TestsBlock_ResultCaching.hitDifferentRareData`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:588 | LayoutResultCachingTest.HitPercentageMinWidth | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:613 | LayoutResultCachingTest.HitFixedMinWidth | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:638 | LayoutResultCachingTest.HitShrinkToFit | behaviour | formalized | `TestsBlock_ResultCaching.hitShrinkToFit`, `BlockResultCache.checkShrinkToFitCache` |
| layout_result_caching_test.cc:685 | LayoutResultCachingTest.MissShrinkToFit | behaviour | formalized | `TestsBlock_ResultCaching.missShrinkToFit`, `BlockResultCache.checkShrinkToFitCache` |
| layout_result_caching_test.cc:765 | LayoutResultCachingTest.HitShrinkToFitSameIntrinsicSizes | behaviour | formalized | `TestsBlock_ResultCaching.hitShrinkToFitSameIntrinsicSizes`, `BlockResultCache.checkShrinkToFitCache` |
| layout_result_caching_test.cc:796 | LayoutResultCachingTest.HitShrinkToFitDifferentParent | behaviour | formalized | `TestsBlock_ResultCaching.hitShrinkToFitDifferentParent`, `BlockResultCache.checkShrinkToFitCache`, `BlockResultCache.checkShrinkToFitCache_same_avail` |
| layout_result_caching_test.cc:826 | LayoutResultCachingTest.MissQuirksModePercentageBasedChild | behaviour | formalized | `TestsBlock_ResultCaching.missQuirksModePercentageBasedChild`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:856 | LayoutResultCachingTest.HitQuirksModePercentageBasedParentAndChild | behaviour | formalized | `TestsBlock_ResultCaching.hitQuirksModePercentageBasedParentAndChild`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:891 | LayoutResultCachingTest.HitStandardsModePercentageBasedChild | behaviour | formalized | `TestsBlock_ResultCaching.hitStandardsModePercentageBasedChild`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:920 | LayoutResultCachingTest.ChangeTableCellBlockSizeConstrainedness | behaviour | formalized | `TestsBlock_ResultCaching.changeTableCellBlockSizeConstrainedness`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:979 | LayoutResultCachingTest.OptimisticFloatPlacementNoRelayout | behaviour | formalized | `TestsBlock_ResultCaching.optimisticFloatPlacementNoRelayout`, `BlockResultCache.forcedBfcForSelfCollapsing` |
| layout_result_caching_test.cc:1003 | LayoutResultCachingTest.SelfCollapsingShifting | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1078 | LayoutResultCachingTest.ClearancePastAdjoiningFloatsMovement | behaviour | formalized | `TestsBlock_ResultCaching.clearancePastAdjoiningFloatsMovement`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:1136 | LayoutResultCachingTest.MarginStrutMovementSelfCollapsing | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:1199 | LayoutResultCachingTest.MarginStrutMovementInFlow | behaviour | formalized | `TestsBlock_ResultCaching.marginStrutMovementInFlow`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:1286 | LayoutResultCachingTest.MarginStrutMovementPercentage | behaviour | formalized | `TestsBlock_ResultCaching.marginStrutMovementPercentage`, `BlockResultCache.checkBfcCache` |
| layout_result_caching_test.cc:1321 | LayoutResultCachingTest.HitIsFixedBlockSizeIndefinite | behaviour | formalized | `TestsBlock_ResultCaching.hitIsFixedBlockSizeIndefinite`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:1350 | LayoutResultCachingTest.MissIsFixedBlockSizeIndefinite | behaviour | formalized | `TestsBlock_ResultCaching.missIsFixedBlockSizeIndefinite`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:1380 | LayoutResultCachingTest.HitColumnFlexBoxMeasureAndLayout | behaviour | formalized | `TestsBlock_ResultCaching.hitColumnFlexBoxMeasureAndLayout`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1433 | LayoutResultCachingTest.HitRowFlexBoxMeasureAndLayout | behaviour | formalized | `TestsBlock_ResultCaching.hitRowFlexBoxMeasureAndLayout`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1488 | LayoutResultCachingTest.MissFlexReplaced | behaviour | formalized | `TestsBlock_ResultCaching.missFlexReplaced`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:1516 | LayoutResultCachingTest.HitFlexDefiniteChange | behaviour | formalized | `TestsBlock_ResultCaching.hitFlexDefiniteChange`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1539 | LayoutResultCachingTest.HitOrthogonalRoot | behaviour | formalized | `TestsBlock_ResultCaching.hitOrthogonalRoot`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:1562 | LayoutResultCachingTest.SimpleTable | behaviour | formalized | `TestsBlock_ResultCaching.simpleTable`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1592 | LayoutResultCachingTest.MissTableCellMiddleAlignment | behaviour | formalized | `TestsBlock_ResultCaching.missTableCellMiddleAlignment`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1615 | LayoutResultCachingTest.MissTableCellBottomAlignment | behaviour | formalized | `TestsBlock_ResultCaching.missTableCellBottomAlignment`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1638 | LayoutResultCachingTest.HitTableCellBaselineAlignment | behaviour | formalized | `TestsBlock_ResultCaching.hitTableCellBaselineAlignment`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1661 | LayoutResultCachingTest.MissTableCellBaselineAlignment | behaviour | formalized | `TestsBlock_ResultCaching.missTableCellBaselineAlignment`, `BlockResultCache.checkMeasureLayoutSlot` |
| layout_result_caching_test.cc:1687 | LayoutResultCachingTest.MissTablePercent | behaviour | formalized | `TestsBlock_ResultCaching.missTablePercent`, `BlockResultCache.checkSizeAndQuirksCache` |
| layout_result_caching_test.cc:1718 | LayoutResultCachingTest.HitTableRowAdd | behaviour | formalized | `TestsBlock_ResultCaching.hitTableRowAdd`, `BlockResultCache.checkTableRowSectionCache` |
| layout_result_caching_test.cc:1739 | LayoutResultCachingTest.MissTableRowAdd | behaviour | formalized | `TestsBlock_ResultCaching.missTableRowAdd`, `BlockResultCache.checkTableRowSectionCache` |
| layout_result_caching_test.cc:1760 | LayoutResultCachingTest.HitTableRowRemove | behaviour | formalized | `TestsBlock_ResultCaching.hitTableRowRemove`, `BlockResultCache.checkTableRowSectionCache` |
| layout_result_caching_test.cc:1781 | LayoutResultCachingTest.MissTableRowRemove | behaviour | formalized | `TestsBlock_ResultCaching.missTableRowRemove`, `BlockResultCache.checkTableRowSectionCache` |
| layout_result_caching_test.cc:1802 | LayoutResultCachingTest.HitTableSectionAdd | behaviour | formalized | `TestsBlock_ResultCaching.hitTableSectionAdd`, `BlockResultCache.checkTableRowSectionCache` |
| layout_result_caching_test.cc:1823 | LayoutResultCachingTest.HitTableSectionRemove | behaviour | formalized | `TestsBlock_ResultCaching.hitTableSectionRemove`, `BlockResultCache.checkTableRowSectionCache` |
| layout_result_caching_test.cc:1844 | LayoutResultCachingTest.FragmentainerSizeChange | behaviour | formalized | `TestsBlock_ResultCaching.fragmentainerSizeChange`, `BlockResultCache.checkFragmentationCache` |
| layout_result_caching_test.cc:1921 | LayoutResultCachingTest.BlockOffsetChangeInFragmentainer | behaviour | formalized | `TestsBlock_ResultCaching.blockOffsetChangeInFragmentainer`, `BlockResultCache.checkFragmentationCache`, `BlockResultCache.checkFragmentationCache_overflow` |
| layout_result_caching_test.cc:1963 | LayoutResultCachingTest.BfcRootBlockOffsetChangeInFragmentainer | behaviour | formalized | `TestsBlock_ResultCaching.bfcRootBlockOffsetChangeInFragmentainer`, `BlockResultCache.checkFragmentationCache`, `BlockResultCache.checkFragmentationCache_overflow` |
| layout_result_caching_test.cc:2005 | LayoutResultCachingTest.HitBlockOffsetUnchangedInFragmentainer | behaviour | formalized | `TestsBlock_ResultCaching.hitBlockOffsetUnchangedInFragmentainer`, `BlockResultCache.checkFragmentationCache` |
| layout_result_caching_test.cc:2035 | LayoutResultCachingTest.HitNewFormattingContextInFragmentainer | behaviour | formalized | `TestsBlock_ResultCaching.hitNewFormattingContextInFragmentainer`, `BlockResultCache.checkFragmentationCache` |
| layout_result_caching_test.cc:2066 | LayoutResultCachingTest.MissMonolithicChangeInFragmentainer | behaviour | blocked | model lacks incremental layout result caching |
| layout_result_caching_test.cc:2092 | LayoutResultCachingTest.MissGridIncorrectIntrinsicSize | behaviour | formalized | `TestsBlock_ResultCaching.missGridIncorrectIntrinsicSize`, `BlockResultCache.checkSizeAndQuirksCache` |
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
| anchor_evaluator_impl_test.cc:71 | AnchorEvaluatorImplTest.AnchorNameAdd | behaviour | formalized | `TestsBlock.AnchorNameAdd_vectors`, `OutOfFlowAnchor.anchor_lookup_empty` |
| anchor_evaluator_impl_test.cc:104 | AnchorEvaluatorImplTest.AnchorNameChange | behaviour | formalized | `TestsBlock.AnchorNameChange_vectors`, `OutOfFlowAnchor.anchor_lookup_empty` |
| anchor_evaluator_impl_test.cc:141 | AnchorEvaluatorImplTest.AnchorNameRemove | behaviour | formalized | `TestsBlock.AnchorNameRemove_vectors`, `OutOfFlowAnchor.anchor_lookup_empty` |
| anchor_evaluator_impl_test.cc:175 | AnchorEvaluatorImplTest.BlockFlow | behaviour | formalized | `TestsBlock.BlockFlow_vectors`, `OutOfFlowAnchor.anchor_top_le_bottom` |
| anchor_evaluator_impl_test.cc:221 | AnchorEvaluatorImplTest.Inline | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:284 | AnchorEvaluatorImplTest.OutOfFlow | behaviour | formalized | `TestsBlock.OutOfFlow_vectors`, `OutOfFlowAnchor.lookupAnchor` |
| anchor_evaluator_impl_test.cc:310 | AnchorEvaluatorImplTest.Relative | behaviour | blocked | model lacks CSS anchor positioning engine |
| anchor_evaluator_impl_test.cc:330 | AnchorEvaluatorImplTest.Transform | behaviour | formalized | `TestsBlock.Transform_vectors`, `OutOfFlowAnchor.transform_shifts_pos` |
| anchor_evaluator_impl_test.cc:351 | AnchorEvaluatorImplTest.Scroll | behaviour | formalized | `TestsBlock.Scroll_vectors`, `OutOfFlowAnchor.scroll_invariant` |
| anchor_evaluator_impl_test.cc:375 | AnchorEvaluatorImplTest.FragmentedContainingBlock | behaviour | formalized | `TestsBlock.FragmentedContainingBlock_vectors`, `OutOfFlowAnchor.lookupAnchor` |
| anchor_evaluator_impl_test.cc:437 | AnchorEvaluatorImplTest.FragmentHasRunningAnchorTransformAnimation | behaviour | formalized | `TestsBlock.FragmentHasRunningAnchorTransformAnimation_vectors`, `OutOfFlowAnchor.no_running_anchor_transform_animation` |
| anchor_evaluator_impl_test.cc:446 | AnchorEvaluatorImplTest.FrameViewHasRunningAnchorTransformAnimation | behaviour | formalized | `TestsBlock.FrameViewHasRunningAnchorTransformAnimation_vectors`, `OutOfFlowAnchor.no_running_anchor_transform_animation` |
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
| paint_containment_test.cc:34 | PaintContainmentTest.BlockPaintContainment | behaviour | formalized | `TestsBlock.BlockPaintContainment_vectors`, `BlockOverflow.contain_paint_creates_nfc`, `BlockOverflow.contain_paint_clips_both` |
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
| layout_video_test.cc:38 | LayoutVideoTest.PosterSizeWithNormal | behaviour | formalized | `TestsBlock.PosterSizeWithNormal_vectors`, `BlockReplaced.applyZoom_hundred` |
| layout_video_test.cc:55 | LayoutVideoTest.PosterSizeWithZoom | behaviour | formalized | `TestsBlock.PosterSizeWithZoom_vectors`, `BlockReplaced.applyZoom_monotone` |
| layout_video_test.cc:72 | LayoutVideoTest.PosterSizeAfterPlay | behaviour | formalized | `TestsBlock.PosterSizeAfterPlay_vectors`, `BlockReplaced.video_author_poster_dimensions` |
| layout_video_test.cc:98 | LayoutVideoTest.DefaultPosterImageSize | behaviour | formalized | `TestsBlock.DefaultPosterImageSize_vectors`, `BlockReplaced.video_default_poster_fallback` |
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
| geometry/writing_mode_converter_test.cc:15 | WritingModeConverterTest.ConvertLogicalOffsetToPhysicalOffset | geometry | formalized | `TestsBlock.ConvertLogicalOffsetToPhysicalOffset_vectors`, `BlockWritingModeConverter.toPhysical` (general over writing mode, direction, sizes) |
| geometry/writing_mode_converter_test.cc:73 | WritingModeConverterTest.ConvertPhysicalOffsetToLogicalOffset | geometry | formalized | `TestsBlock.ConvertPhysicalOffsetToLogicalOffset_vectors`, `BlockWritingModeConverter.toLogical` |
| geometry/box_sides_test.cc:13 | GeometryUnitsTest.LogicalBoxSidesToLineLogical | geometry | formalized | `TestsBlock.LogicalBoxSidesToLineLogical_vectors`, `BlockBoxSides.lineSides` |
| geometry/box_sides_test.cc:35 | GeometryUnitsTest.PhysicalBoxSidesToLogical | geometry | formalized | `TestsBlock.PhysicalBoxSidesToLogical_vectors`, `BlockBoxSides.toLogical` |
| geometry/static_position_test.cc:331 | StaticPositionTest.Convert | geometry | blocked | 48-row parameter table; a model of the static-position record cost 4.5 model tokens per result token under the mml gate, so it is not added |
| forms/fieldset_layout_algorithm_test.cc:59 | FieldsetLayoutAlgorithmTest.Empty | geometry | formalized | `TestsBlock.FieldsetEmpty_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:78 | FieldsetLayoutAlgorithmTest.NoLegend | geometry | formalized | `TestsBlock.FieldsetNoLegend_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:100 | FieldsetLayoutAlgorithmTest.Legend | geometry | formalized | `TestsBlock.FieldsetLegend_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:124 | FieldsetLayoutAlgorithmTest.SmallLegendLargeBorder | geometry | formalized | `TestsBlock.FieldsetSmallLegendLargeBorder_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:150 | FieldsetLayoutAlgorithmTest.LegendOrthogonalWritingMode | geometry | formalized | `TestsBlock.FieldsetLegendOrthogonal_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:176 | FieldsetLayoutAlgorithmTest.VerticalLr | geometry | formalized | `TestsBlock.FieldsetVerticalLr_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:202 | FieldsetLayoutAlgorithmTest.VerticalRl | geometry | formalized | `TestsBlock.FieldsetVerticalRl_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:228 | FieldsetLayoutAlgorithmTest.LegendAutoSize | geometry | formalized | `TestsBlock.FieldsetLegendAutoSize_vectors`, `BlockFieldset.layout` (HTML §15.3.13, CSS 2.1 §10.3.5 shrink-to-fit legend inline size) |
| forms/fieldset_layout_algorithm_test.cc:257 | FieldsetLayoutAlgorithmTest.PercentageHeightChild | geometry | formalized | `TestsBlock.FieldsetPercentageHeightChild_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:283 | FieldsetLayoutAlgorithmTest.AbsposChild | geometry | formalized | `TestsBlock.FieldsetAbsposChild_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:312 | FieldsetLayoutAlgorithmTest.ZeroHeight | geometry | formalized | `TestsBlock.FieldsetZeroHeight_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:340 | FieldsetLayoutAlgorithmTest.ZeroMaxHeight | geometry | formalized | `TestsBlock.FieldsetZeroMaxHeight_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:372 | FieldsetLayoutAlgorithmTest.PercentHeightQuirks | geometry | formalized | `TestsBlock.FieldsetPercentHeightQuirks_vectors`, `BlockFieldset.layout` (HTML §15.3.13, Quirks Mode §3.6 percentage height calculation quirk) |
| forms/fieldset_layout_algorithm_test.cc:404 | FieldsetLayoutAlgorithmTest.LegendPercentHeightQuirks | geometry | formalized | `TestsBlock.FieldsetPercentHeightQuirks_vectors`, `BlockFieldset.layout` (HTML §15.3.13, Quirks Mode §3.6 percentage height calculation quirk) |
| forms/fieldset_layout_algorithm_test.cc:433 | FieldsetLayoutAlgorithmTest.FieldsetPaddingWithLegend | geometry | formalized | `TestsBlock.FieldsetPaddingWithLegend_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:472 | FieldsetLayoutAlgorithmTest.MinMax | geometry | formalized | `TestsBlock.FieldsetMinMax_vectors`, `BlockFieldset.layout` |
| forms/fieldset_layout_algorithm_test.cc:540 | FieldsetLayoutAlgorithmTest.NoFragmentation | geometry | formalized | `TestsBlock.FieldsetNoFragmentation_size`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:567 | FieldsetLayoutAlgorithmTest.SimpleFragmentation | geometry | formalized | `TestsBlock.FieldsetSimpleFragmentation_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:604 | FieldsetLayoutAlgorithmTest.FragmentationNoPadding | geometry | formalized | `TestsBlock.FieldsetFragmentationNoPadding_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:645 | FieldsetLayoutAlgorithmTest.FieldsetContentFragmentationAutoHeight | geometry | formalized | `TestsBlock.FieldsetContentFragmentationAutoHeight_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:708 | FieldsetLayoutAlgorithmTest.FieldsetContentFragmentation | geometry | formalized | `TestsBlock.FieldsetContentFragmentation_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:771 | FieldsetLayoutAlgorithmTest.LegendFragmentationAutoHeight | geometry | formalized | `TestsBlock.FieldsetLegendFragmentation_vectors`, `BlockFieldset.fragment`, `BlockFieldset.fragment_tall_header` (CSS Fragmentation 3 §3.1, HTML §15.3.13) |
| forms/fieldset_layout_algorithm_test.cc:821 | FieldsetLayoutAlgorithmTest.LegendFragmentation | geometry | formalized | `TestsBlock.FieldsetLegendFragmentation_vectors`, `BlockFieldset.fragment`, `BlockFieldset.fragment_tall_header` (CSS Fragmentation 3 §3.1, HTML §15.3.13) |
| forms/fieldset_layout_algorithm_test.cc:871 | FieldsetLayoutAlgorithmTest.LegendAndContentFragmentationAutoHeight | geometry | formalized | `TestsBlock.FieldsetLegendAndContentFragmentation_vectors`, `BlockFieldset.fragment`, `BlockFieldset.fragment_tall_header` (CSS Fragmentation 3 §3.1, HTML §15.3.13) |
| forms/fieldset_layout_algorithm_test.cc:937 | FieldsetLayoutAlgorithmTest.LegendAndContentFragmentation | geometry | formalized | `TestsBlock.FieldsetLegendAndContentFragmentation_vectors`, `BlockFieldset.fragment`, `BlockFieldset.fragment_tall_header` (CSS Fragmentation 3 §3.1, HTML §15.3.13) |
| forms/fieldset_layout_algorithm_test.cc:1001 | FieldsetLayoutAlgorithmTest.LegendFragmentationWithOverflow | geometry | formalized | `TestsBlock.FieldsetLegendFragmentationWithOverflow_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:1052 | FieldsetLayoutAlgorithmTest.LegendAndContentFragmentationNegativeMargin | geometry | blocked | fieldset fragmentation with negative child margin not modelled |
| forms/fieldset_layout_algorithm_test.cc:1107 | FieldsetLayoutAlgorithmTest.OverflowedLegend | geometry | formalized | `TestsBlock.FieldsetOverflowedLegend_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1) |
| forms/fieldset_layout_algorithm_test.cc:1151 | FieldsetLayoutAlgorithmTest.OverflowedFieldsetContent | geometry | blocked | fieldset fragmentation with multiple children and nested overflow not modelled |
| forms/fieldset_layout_algorithm_test.cc:1224 | FieldsetLayoutAlgorithmTest.BreakInsideAvoid | geometry | formalized | `TestsBlock.FieldsetChildrenBreakAvoid_vectors`, `BlockFieldset.fragmentChildren` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1271 | FieldsetLayoutAlgorithmTest.BreakInsideAvoidTallBlock | geometry | formalized | `TestsBlock.FieldsetChildrenBreakAvoid_vectors`, `BlockFieldset.fragmentChildren` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1334 | FieldsetLayoutAlgorithmTest.LegendBreakInsideAvoid | geometry | formalized | `TestsBlock.FieldsetAfterSiblingBreakAvoid_vectors`, `BlockFieldset.fragmentAfterSibling`, `BlockFieldset.no_class_c_when_border_covers_legend` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1387 | FieldsetLayoutAlgorithmTest.BreakBeforeAvoid | geometry | formalized | `TestsBlock.FieldsetChildrenBreakAvoid_vectors`, `BlockFieldset.fragmentChildren` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1442 | FieldsetLayoutAlgorithmTest.LegendBreakBeforeAvoid | geometry | formalized | `TestsBlock.FieldsetAfterSiblingBreakAvoid_vectors`, `BlockFieldset.fragmentAfterSibling` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1494 | FieldsetLayoutAlgorithmTest.BreakAfterAvoid | geometry | formalized | `TestsBlock.FieldsetChildrenBreakAvoid_vectors`, `BlockFieldset.fragmentChildren` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1540 | FieldsetLayoutAlgorithmTest.LegendBreakAfterAvoid | geometry | formalized | `TestsBlock.FieldsetAfterSiblingBreakAvoid_vectors`, `BlockFieldset.fragmentAfterSibling` (CSS Fragmentation 3 §3.1, §4.4) |
| forms/fieldset_layout_algorithm_test.cc:1594 | FieldsetLayoutAlgorithmTest.MarginBottomPastEndOfFragmentainer | geometry | formalized | `TestsBlock.FieldsetMarginBottomPastEnd_vectors`, `BlockFieldset.fragment`, `BlockFieldset.fragment_tall_header` (CSS Fragmentation 3 §3.1, §3.2) |
| forms/fieldset_layout_algorithm_test.cc:1650 | FieldsetLayoutAlgorithmTest.SmallLegendLargeBorderFragmentation | geometry | formalized | `TestsBlock.FieldsetSmallLegendLargeBorderFragmentation_vectors`, `BlockFieldset.fragment`, `BlockFieldset.fragment_tall_header` (CSS Fragmentation 3 §3.1, HTML §15.3.13) |
| forms/fieldset_layout_algorithm_test.cc:1707 | FieldsetLayoutAlgorithmTest.SmallerLegendLargeBorderFragmentation | geometry | formalized | `TestsBlock.FieldsetSmallerLegendLargeBorder_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1, HTML §15.3.13; integer model truncates subpixel legend y 27.5 to 27) |
| forms/fieldset_layout_algorithm_test.cc:1766 | FieldsetLayoutAlgorithmTest.SmallerLegendLargeBorderFragmentation2 | geometry | formalized | `TestsBlock.FieldsetAfterSiblingBreakAvoid_vectors`, `BlockFieldset.fragmentAfterSibling`, `BlockFieldset.no_class_c_when_border_covers_legend` (CSS Fragmentation 3 §4.1, §4.4; integer model truncates subpixel legend y 12.5 to 12) |
| forms/fieldset_layout_algorithm_test.cc:1818 | FieldsetLayoutAlgorithmTest.SmallerLegendLargeBorderWithBreak | geometry | formalized | `TestsBlock.FieldsetSmallerLegendLargeBorder_vectors`, `BlockFieldset.fragment` (CSS Fragmentation 3 §3.1, HTML §15.3.13; integer model truncates subpixel legend y 27.5 to 27) |
| forms/layout_fieldset_test.cc:14 | LayoutFieldsetTest.AddChildWhitespaceCrash | internal | internal | crash regression in LayoutFieldset::AddChild, no layout rule |
| forms/layout_fieldset_test.cc:31 | LayoutFieldsetTest.AddChildAnonymousInlineCrash | internal | internal | crash regression in LayoutFieldset::AddChild, no layout rule |
| geometry/layout_unit_diffuser_test.cc:15 | LayoutUnitDiffuserTest.ThreeBuckets | geometry | formalized | `TestsBlock.ThreeBuckets_vectors`, `BlockDiffuser.share` |
| geometry/layout_unit_diffuser_test.cc:35 | LayoutUnitDiffuserTest.FourBuckets | geometry | formalized | `TestsBlock.FourBuckets_vectors`, `BlockDiffuser.share` |
| geometry/layout_unit_diffuser_test.cc:64 | LayoutUnitDiffuserTest.SevenBuckets | geometry | formalized | `TestsBlock.SevenBuckets_vectors`, `BlockDiffuser.share` |
| geometry/box_edge_test.cc:11 | BoxEdgeTest.Construction | internal | internal | value-type accessors of the BoxEdge (offset,size) pair; no layout rule |
| geometry/box_edge_test.cc:17 | BoxEdgeTest.End | internal | internal | value-type accessors of the BoxEdge (offset,size) pair; no layout rule |
| geometry/box_edge_test.cc:22 | BoxEdgeTest.IsEmpty | internal | internal | value-type accessors of the BoxEdge (offset,size) pair; no layout rule |
| geometry/box_edge_test.cc:28 | BoxEdgeTest.Move | internal | internal | value-type accessors of the BoxEdge (offset,size) pair; no layout rule |
| geometry/box_edge_test.cc:39 | BoxEdgeTest.Equality | internal | internal | value-type accessors of the BoxEdge (offset,size) pair; no layout rule |
| geometry/box_edge_test.cc:47 | BoxEdgeTest.MathOperators | internal | internal | value-type accessors of the BoxEdge (offset,size) pair; no layout rule |
| geometry/axis_test.cc:14 | AxisTest.StreamOperators | internal | internal | debug stream output of axis flag names; no layout rule |
| geometry/axis_test.cc:72 | AxisTest.LogicalAxesOperators | internal | internal | bit-flag operator overloads (| & ^ -) on axis sets; no layout rule |
| geometry/axis_test.cc:138 | AxisTest.PhysicalAxesOperators | internal | internal | bit-flag operator overloads (| & ^ -) on axis sets; no layout rule |
| geometry/axis_test.cc:213 | AxisTest.ToPhysicalAxes | geometry | formalized | `TestsBlock.AxisMap_vectors`, `BlockAxis.mapAxes` |
| geometry/axis_test.cc:239 | AxisTest.ToLogicalAxes | geometry | formalized | `TestsBlock.AxisMap_vectors`, `BlockAxis.mapAxes` |
| exclusions/exclusion_space_test.cc:92 | ExclusionSpaceTest.Empty | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:122 | ExclusionSpaceTest.LineLayoutOpportunityClampsNonDominantSide | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:169 | ExclusionSpaceTest.SingleExclusion | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:232 | ExclusionSpaceTest.TwoExclusions | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:273 | ExclusionSpaceTest.SolidEdges | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:325 | ExclusionSpaceTest.OverlappingWithShelf | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:373 | ExclusionSpaceTest.InsertBetweenShelves | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:408 | ExclusionSpaceTest.InitialLetterBasic | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:451 | ExclusionSpaceTest.InitialLetterDirectionRight | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:507 | ExclusionSpaceTest.InitialLetterFloatLeft1 | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:560 | ExclusionSpaceTest.InitialLetterFloatLeft2 | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:615 | ExclusionSpaceTest.InitialLetterFloatLeft2ClearLeft | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:672 | ExclusionSpaceTest.InitialLetterFloatLeftAndRight | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:738 | ExclusionSpaceTest.InitialLetterFloatLeftAfterBreak | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:796 | ExclusionSpaceTest.InitialLetterFloatRight2 | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:857 | ExclusionSpaceTest.ZeroInlineSizeOpportunity | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:877 | ExclusionSpaceTest.NegativeInlineSizeOpportunityLeft | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:907 | ExclusionSpaceTest.NegativeInlineSizeOpportunityRight | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:937 | ExclusionSpaceTest.PreInitialization | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:992 | ExclusionSpaceTest.MergeExclusionSpacesNoPreviousExclusions | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:1020 | ExclusionSpaceTest.MergeExclusionSpacesPreviousExclusions | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:1060 | ExclusionSpaceTest.MergeExclusionSpacesNoOutputExclusions | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:1083 | ExclusionSpaceTest.CopyOnWriteNoAllocationOnCopy | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| exclusions/exclusion_space_test.cc:1162 | ExclusionSpaceTest.CopyOnWriteDisabledFallback | geometry | blocked | Chromium layout-opportunity enumeration (order, zero-width cases, solid edges) has no CSS source; CSS 2.1 §9.5 constrains float placement only; model would be a lookup of the enumeration |
| geometry/physical_rect_test.cc:17 | PhysicalRectTest.AddOffset | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:58 | PhysicalRectUniteTest.Data | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:78 | PhysicalRectTest.SquaredDistanceTo | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:127 | PhysicalRectTest.InclusiveIntersect | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:146 | PhysicalRectTest.IntersectsInclusively | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:191 | PhysicalRectTest.ToEnclosingRect | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:243 | PhysicalRectTest.EdgesOnPixelBoundaries | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:281 | PhysicalRectTest.ExpandEdgesToPixelBoundaries | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/physical_rect_test.cc:335 | PhysicalRectTest.InfiniteIntRect | geometry | blocked | LayoutUnit rect primitive (saturating unite, float-to-LayoutUnit inputs, pixel snapping) has no CSS source; Unite offset on saturation is a Chromium heuristic in physical_rect.cc |
| geometry/logical_rect_test.cc:15 | LogicalRectTest.AddOffset | geometry | blocked | LayoutUnit rect primitive (saturating unite) has no CSS source; same rule as physical_rect_test |
| geometry/logical_rect_test.cc:55 | LogicalRectUniteTest.Data | geometry | blocked | LayoutUnit rect primitive (saturating unite) has no CSS source; same rule as physical_rect_test |
| hit_testing_test.cc:87 | HitTestingTest.OcclusionHitTest | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:111 | HitTestingTest.OcclusionHitTestSVGTextWithFilterCrash | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:136 | HitTestingTest.HitTestWithCallback | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:205 | HitTestingTest.OcclusionHitTestWithClipPath | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:253 | HitTestingTest.OcclusionHitTestWithBorderShapeStrokeMode | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:319 | HitTestingTest.OcclusionHitTestWithBorderShapeFillMode | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:384 | HitTestingTest.ScrolledInline | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:421 | HitTestingTest.ReferenceFilter | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:457 | HitTestingTest.OcclusionHitTestWith3DTransform | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:495 | HitTestingTest.OcclusionHitTestWithFlattenedPreserve3DOccluder | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:549 | SVGChild3DTransformHitTest.ShapeWithPerspectiveFunction | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:574 | SVGChild3DTransformHitTest.ShapeUnderSVGRootPerspective | behaviour | blocked | engine service, parked (hit testing) |
| hit_testing_test.cc:592 | SVGChild3DTransformHitTest.ContainerUnderSVGRootPerspective | behaviour | blocked | engine service, parked (hit testing) |
| forms/layout_text_control_test.cc:56 | LayoutTextControlTest.ChangingPseudoSelectionStyleShouldInvalidateSelectionSingle | internal | internal | selection-style invalidation flags on LayoutText; no layout rule |
| forms/layout_text_control_test.cc:74 | LayoutTextControlTest.ChangingPseudoSelectionStyleShouldInvalidateSelectionMulti | internal | internal | selection-style invalidation flags on LayoutText; no layout rule |
| forms/layout_text_control_test.cc:92 | LayoutTextControlTest.AddingPseudoSelectionStyleShouldInvalidateSelectionSingle | internal | internal | selection-style invalidation flags on LayoutText; no layout rule |
| forms/layout_text_control_test.cc:109 | LayoutTextControlTest.AddingPseudoSelectionStyleShouldInvalidateSelectionMulti | internal | internal | selection-style invalidation flags on LayoutText; no layout rule |
| forms/layout_text_control_test.cc:126 | LayoutTextControlTest.RemovingPseudoSelectionStyleShouldInvalidateSelectionSingle | internal | internal | selection-style invalidation flags on LayoutText; no layout rule |
| forms/layout_text_control_test.cc:142 | LayoutTextControlTest.RemovingPseudoSelectionStyleShouldInvalidateSelectionMulti | internal | internal | selection-style invalidation flags on LayoutText; no layout rule |
| forms/layout_text_control_test.cc:158 | LayoutTextControlTest.HitTestSearchInput | behaviour | blocked | engine service, parked (hit testing) |
| forms/layout_text_control_inner_editor_test.cc:12 | LayoutTextControlInnerEditorTest.AddChildWithoutTrailingLf | internal | internal | anonymous block / LayoutBR object structure of the inner editor, or crash regression; no layout rule |
| forms/layout_text_control_inner_editor_test.cc:43 | LayoutTextControlInnerEditorTest.AddChildWithTrailingLf | internal | internal | anonymous block / LayoutBR object structure of the inner editor, or crash regression; no layout rule |
| forms/layout_text_control_inner_editor_test.cc:85 | LayoutTextControlInnerEditorTest.RemoveChildWithoutTrailingLf | internal | internal | anonymous block / LayoutBR object structure of the inner editor, or crash regression; no layout rule |
| forms/layout_text_control_inner_editor_test.cc:114 | LayoutTextControlInnerEditorTest.AddChildBeforeTestRenderingHolder | internal | internal | anonymous block / LayoutBR object structure of the inner editor, or crash regression; no layout rule |
| forms/layout_text_control_inner_editor_test.cc:126 | LayoutTextControlInnerEditorTest.EnableDynamic | internal | internal | anonymous block / LayoutBR object structure of the inner editor, or crash regression; no layout rule |
| forms/layout_text_control_single_line_test.cc:13 | LayoutTextControlSingleLineTest.VisualOverflowCleared | behaviour | blocked | visual overflow of a box-shadowed input (ink overflow, engine service, parked) |






## Laws proved

- `BlockFlow.consumedBlockSize_step`: consumed block size increases by fragmentainer size with each fragment.
- `ColumnLayout.colStride_pos`: column stride is strictly positive when column width is positive.
- `ColumnLayout.columnInlineOffset_step`: column offset advances by stride for each subsequent column.
- `ColumnLayout.columns_non_overlapping`: columns do not overlap when gap is non-negative and column width is positive.
- `ColumnLayout.actualColumnCount_at_least_one`: multicolumn container always generates at least one column fragmentainer.
- `ColumnLayout.bal_col_count_ge_one`: multicolumn container always generates at least one column fragmentainer under balancing.
- `ColumnLayout.bal_col_count_empty`: empty balanced container generates exactly one column fragmentainer.
- `ColumnLayout.bal_h_step_multiple`: line-stepped balanced column height is a multiple of step.
- `FlexLayout.flex_empty_no_lines`: an empty flex container produces no lines (CSS Flexible Box Layout Level 1 §9.3).
- `FlexLayout.flex_nowrap_at_most_one_line`: a flex container with flex-wrap: nowrap always generates at most one line of items (CSS Flexible Box Layout Level 1 §5.2).
- `FlexLayout.flex_empty_container_lines`: layout of an empty flex container produces no laid out lines (CSS Flexible Box Layout Level 1 §9.3).
- `TableLayout.resolve_hidden_zero`: any border set containing a hidden border resolves to 0 width (CSS 2.1 §17.6.2.1).
- `TableLayout.sync_exact_max`: when assignable table size equals total max size, columns equal their max sizes without redistribution (CSS 2.1 §17.5.2).
- `TableLayout.grid_min_sum`: table grid minimum inline size is always the sum of column minimum sizes (CSS 2.1 §17.5.2.1, CSS Table 3 §3).
- `GridLayout.grid_ranges_start_zero`: first grid range always starts at line 0 (CSS Grid 1 §7.2.3).
- `GridLayout.normalize_no_flex_min`: a flex factor is never a track minimum in normalized track sizes (CSS Grid 1 §7.2.5).
- `GridLayout.resolve_gap_none`: percentage gap resolves to 0 when container dimension is indefinite (CSS Box Alignment 3 §8, CSS Grid 1 §10.1).
- `BlockWritingMode.physicalContentBox_vertical`: in vertical writing modes, physical width is logical block size and physical height is logical inline size (CSS Writing Modes 3 §6.4).
- `BlockFlow.sliceCount_pos`: non-empty content in positive fragmentainer always requires at least one slice (CSS Fragmentation 3 §2).
- `BlockSticky.sticky_offset_le_max_shift`: sticky offset is always bounded by the containing block headroom (CSS Positioned Layout 3 §2.3).
- `BlockSticky.sticky_offset_none`: if no top inset is specified, sticky offset is 0 (CSS Positioned Layout 3 §2.3).
- `BlockSticky.sticky_offset_unscrolled`: if target position is at or before starting position, sticky offset is 0 (CSS Positioned Layout 3 §2.3).
- `OutOfFlowAnchor.anchor_top_le_bottom`: top edge of an anchor is always at or before bottom edge (CSS Anchor Positioning 1 §4.1).
- `OutOfFlowAnchor.anchor_left_le_right`: left edge of an anchor is always at or before right edge (CSS Anchor Positioning 1 §4.1).
- `OutOfFlowAnchor.anchor_lookup_empty`: lookup in an empty anchor map always yields none (CSS Anchor Positioning 1 §3.1).


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
- `BlockWritingModeConverter.toLogical_toPhysical` / `toPhysical_toLogical`: offset conversion is a bijection for every writing mode, direction and size (CSS Writing Modes 4 §6).
- `BlockBoxSides.toLogical_inline_or`: physical-to-logical side conversion keeps an axis's presence (CSS Writing Modes 4 §6.2).
- `BlockFieldset.legend_above_anon`, `BlockFieldset.fragment_tall_header`: the rendered legend never overlaps the fieldset's anonymous content box in the block axis, and a legend/top-border reaching the fragmentainer height pushes the anonymous content box to the next fragmentainer (HTML §15.3.13, CSS Fragmentation 3 §3.1).
- `BlockDiffuser.given_all`: spreading a total over n buckets hands out exactly the total (no CSS text; browser rounding rule read from tests).
- `BlockAxis.mapAxes_mapAxes`: logical/physical axis mapping is an involution for every writing mode (CSS Writing Modes 4 §6.1).
- `GridTrackSizing.fixedLen_pct_le`: a percentage track resolves to at most the container size for percentages up to 100 (CSS Grid 1 §11.4).
- `GridLanes.expand_fixed_length`: expanding a fixed repetition produces the requested number of tracks (CSS Grid 3 §repeat-auto-fit).
- `GridLanesGap.gridAxisGaps_no_rule`, `GridLanesGap.gridAxisGaps_single`, `GridLanesGap.stackContent_ge_box`: gap decorations need a gap rule and at least two tracks, and stacking-axis content extent covers at least the content box (CSS Gap Decorations 1 §3.1, §3.3).
- `FlexScroll.scroll_range`, `FlexScroll.origin_eq_neg_min`, `FlexScroll.no_overflow_zero_scroll`: scrollable overflow contains the padding box so max scroll >= 0 >= min scroll, the scroll origin is minus the minimum, and a non-overflowing child has zero scroll range (CSS Overflow 3 §2.2, §2.3).
- `ColumnBreakAppeal.avoid_before_dominates_orphans`: `break-before: avoid` strictly dominates `orphans`/`widows` violations in unforced break appeal (CSS Fragmentation 3 §4.4 Rules 2–3).

## Merge notes

- `BlockFlow.lean` extends `MarginStrut` from `LayoutTypes.lean` with `MarginStrut.ofInt` /
  `MarginStrut.signedSum` (namespace `ChromiumLayout.MarginStrut`) instead of editing the shared file.
- `check.sh` gained one block (call to `tests/check_tests.sh`) before the final line; the other lane
  may add its own call next to it.
