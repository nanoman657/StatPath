# Inline Lane Strengthening Pass

Tracking progress per `/tmp/claude-0/-root-github-el-confidente/4714a88b-521f-4f18-89cc-a881895cc7cc/scratchpad/agy-tests/strengthen-inline.txt`.

done: TestsInline_FragmentItem +0
- Rewrote thin theorems (`fragmentItem_lineBoxWithHangingWidthRTLRightAligned`, `fragmentItem_lineBoxWithHangingWidthRTLCenterAligned`, `fragmentItem_textFloatsAroundFloatsBefore`) to run test inputs through `breakLines` and `createLineBox`.

done: TestsInline_LineBreaker +0
- Rewrote `lineBreaker_bidiControlEnter` to flow CSS input `font: 10px/1 Ahem; width: 40px; xxx-<bdi>xx</bdi>` through general line breaking and line box stacking.

done: TestsInline_InlineLayoutAlgorithm +0
- Rewrote 9 theorems (`test_BreakToken_chain`, `inlineLayoutAlgorithm_boxForEndMargin`, `test_PositionFloatsWithMargins`, `test_InkOverflow`, `test_LineBoxWithHangingWidthRTLRightAligned`, `test_LineBoxWithHangingWidthRTLCenterAligned`, `test_TextFloatsAroundFloatsBefore`, `inlineLayoutAlgorithm_textBoxTrimOnInlineBox`, `inlineLayoutAlgorithm_textCombineBasic`) to flow test setup through `breakLines`, `createLineBox`, float positioning, and font metrics.

done: TestsInline_InlineNode +0
- Rewrote `inlineNode_textCombineWordSpacing` to take CSS style properties (`writing-mode: vertical-rl`, `text-combine-upright: all`, `letter-spacing: 1px`, `word-spacing: 1px`) and flow them through `isTextCombineActive` into `effectiveLetterSpacing` and `effectiveWordSpacing`, asserting suppression to 0 per CSS Writing Modes 3 §5.1.4.
- Other theorems in file verified not thin:
  - `inlineNode_collectInlinesText`, `inlineNode_collectInlinesBR`, `inlineNode_collectInlinesInlineBlock`: run DOM text and element tokens directly through general `collectInlines`.
  - `inlineNode_minMaxData`: runs input token sequences through general `computeMinMaxSizesAhem`.
  - `inlineNode_minMaxSizesSaturated`: runs extreme atomic inline size through `computeMinMaxSizesAhem` to test LayoutUnit saturation.
  - `inlineNode_needsCollectInlinesOnStyle`, `inlineNode_needsCollectInlinesOnInsert`, `inlineNode_needsCollectInlinesOnRemove`: run mutation operations through general `computeNeedsCollectInlines`.

done: TestsInline_InlineItemsBuilder +0
- Rewrote 7 thin theorems (`inlineItemsBuilder_collapseAcrossElements`, `inlineItemsBuilder_collapseLeadingSpaces`, `inlineItemsBuilder_collapseTrailingSpaces`, `inlineItemsBuilder_collapseAllSpaces`, `inlineItemsBuilder_collapseLeadingNewlines`, `inlineItemsBuilder_collapseTrailingNewlines`, `inlineItemsBuilder_collapseNewlineAcrossElements`) to run multi-element append sequences through general builder function `buildInlineString` instead of single-string `collapseText`.
- Other theorems in file verified not thin:
  - `inlineItemsBuilder_collapseSpaces`, `collapseTabs`, `collapseNewlines`, `collapseNewlinesAsSpaces`: run whitespace modes through `collapseText`.
  - `inlineItemsBuilder_bidiBlockOverride`, `bidiIsolate`, `bidiIsolateOverride`: run bidi modes through `wrapBidi`.
  - `inlineItemsBuilder_collapseBeforeAndAfterNewline`, `collapsibleSpaceAfterNonCollapsibleSpaceAcrossElements`, `collapseZeroWidthSpaces`, `collapseZeroWidthSpaceAndNewLineAtEnd`, `opaqueToSpaceCollapsing`, `collapseAroundReplacedElement`, `appendEmptyString`, `newLines`, `ignorablePre`, `collapsedSpaceAfterNoWrap`, `generateBreakOpportunityAfterLeadingSpaces`, `blockInInline`, `openCloseRubyColumns`: run multi-item builder streams through `buildInlineString` and `appendBuilderInput`.

done: TestsInline_OffsetMapping +0
- Rewrote thin theorems (`test_OffsetMapping_CollapseSpaces`, `test_OffsetMapping_CollapseLeadingSpaces`) to run DOM text nodes through the general `buildDomOffsetMapping` pipeline and extract collapsed indices via `collapsedIndicesForNode`.
- Other theorems in file verified not thin:
  - `test_OffsetMapping_CollapseTabs`, `CollapseNewLines`, `CollapseNewlinesAsSpaces`: single-string whitespace mode mapping validations.
  - `test_OffsetMapping_CollapseAcrossElements`, `CollapseTrailingSpaces`, `CollapseLeadingNewlines`, `CollapseTrailingNewlines`, `CollapseNewlineAcrossElements`, `CollapseBeforeAndAfterNewline`, `CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements`: multi-element DOM node collapsing through `testCollapsing` (evaluating `buildDomOffsetMapping`).
  - `test_OffsetMapping_OneTextNode`, `TwoTextNodes`, `BRBetweenTextNodes`, `PreLine`, `FullyCollapsedWhiteSpaceNode`, `ReplacedElement`, `FirstLetter`, `FirstLetterWithLeadingSpace`, `FirstLetterWithoutRemainingText`, `WhiteSpaceTextNodeWithoutLayoutText`, `ContainerWithGeneratedContent`, `StartOfNextNonCollapsedContentWithPseudo`, `EndOfLastNonCollapsedContentWithPseudo`: run DOM node structures directly through `buildDomOffsetMapping` verifying units, text offsets, and non-collapsed boundary predicates.
  - `FirstLetterInDifferentBlock`, `NoWrapSpaceAndCollapsibleSpace`, `RestoreTrailingCollapsibleSpace*`, `Table`, `GetMappingForInlineBlock`, `BiDiAroundForcedBreakIn*`, `SoftHyphen`, `PreWrapAndReusing`, `TextOverflowEllipsis`, `WordBreak`: run specialized layout structures through respective offset mapping builders and scope resolution functions.

done: TestsInline_InlineCursor +0
- Rewrote thin theorem `inlineCursor_bidiLevelSimpleRTL` to construct BidiItem sequences and run them through `bidiLevels` into `reorderBidiRunsVisual` instead of passing bare tuple lists.
- Other theorems in file verified not thin:
  - `inlineCursor_bidiLevelInlineBoxLTR`, `inlineCursor_bidiLevelInlineBoxRTL`, `inlineCursor_bidiLevelSimpleLTR`: run DOM/bidi items directly through `bidiLevels`.
  - `inlineCursor_bidiLevelFirstLineTextTransform`, `inlineCursor_bidiLevelFirstLineTextTransformBR`: flow raw text through `applyTextTransform` into `bidiLevels`.
  - `inlineCursor_parent`, `containingLine`, `culledInline*`, `firstChild*`, `lastChild*`, `firstLastLogicalLeaf*`, `isEmptyLineBox`, `next*`, `previous*`, `cursorForDescendants`, `moveToLayoutObject`, `moveToVisualFirstOrLast`: construct `CursorNode` trees matching Blink HTML test cases and run them through general cursor navigation functions (`findParent`, `findFirstChild`, `findLastChild`, `firstLogicalLeaf`, `lastLogicalLeaf`, `findNext`, `findPrevious`, etc.).
  - `inlineCursor_positionForPointInChildHorizontalLTR`, `HorizontalRTL`, `VerticalRTL`: run coordinate positions through general `hitTestTextOffset`.

done: TestsInline_InlineCaretPosition +0
- Rewrote thin theorems (`inlineCaretPosition_inlineBoxesLTR`, `inlineCaretPosition_inlineBoxesRTL`) to flow CSS bidi properties through `bidiControlPrefix` per CSS Writing Modes 3 §2.4 to calculate text offsets from DOM offsets instead of hardcoded numbers.
- Other theorems in file verified not thin:
  - `inlineCaretPosition_afterSpan`, `afterSpanCulled`, `inOneLineOfText`, `atSoftHyphen`, `atSoftLineWrap`, `atForcedLineBreak`, `atEmptyLine`, `inOneLineOfImage`, `atSoftLineWrapBetweenImages`, `atSoftLineWrapBetweenMultipleTextNodes`, `atSoftLineWrapBetweenMultipleTextNodesRtl`, `atSoftLineWrapBetweenDeepTextNodes`, `softLineWrap`: run DOM item sequences (`.span`, `.text`, `.image`, `.br`) through `buildCaretFragments` and query caret resolution via `computeCaretPosition`.
  - `inlineCaretPosition_multiColumnSingleText`: maps multicolumn fragment slices to fragment IDs and offsets.
  - `inlineCaretPosition_generatedZeroWidthSpace`, `inlineBlockBeforeContent`: fragment position resolution for generated content.

done: TestsInline_PhysicalLineBoxFragment +0
- Verified neither theorem is thin:
  - `physicalLineBoxFragment_hasPropagatedDescendantsFloat` and `physicalLineBoxFragment_hasPropagatedDescendantsOOF` directly test `hasPropagatedDescendants` (the general model predicate in `InlineLineBox.lean` for `PhysicalLineBoxFragment::HasPropagatedDescendants()` per CSS 2.1 §9.5 and §9.3) on line item streams partitioned into normal flow items vs lines containing float / out-of-flow items, verifying propagation flags to the containing block. No bare numbers or indices are used.

done: TestsInline_LineInfo +0
- Rewrote thin theorem `lineInfo_inflowEndOffset` to flow the test input strings ("abc", "def", "rt") through cumulative text and ruby column offsets per CSS Ruby 1 §3.1 into `lineInflowEndOffset` instead of hardcoding raw numbers.

done: TestsInline_LineWidths +0
- Verified `lineWidthsDataTest_data` is not thin: runs all 16 test cases from `line_widths_test.cc:175` with container widths, line heights, and item sequences (floats, text runs with strut metrics, baseline alignment tags, atomic inlines) through the general precomputation function `computeLineWidths` and `getLineWidthsList`. No bare indices or pre-formatted numbers are used.

done: TestsInline_ParagraphLineBreaker +0
- Verified all theorems in file are not thin:
  - `paragraphLineBreaker_isDisabledBy*` and `scoreLineBreaker_ruby`: test CSS Text 4 §5.3 / §5.4 and CSS Ruby 1 §3 paragraph feature classification (`isBisectLineBreakDisabled`, `isScoreLineBreakDisabled`, `attemptParagraphBalancing`) across block-in-inline, floats, forced breaks, initial letter, tabulation, and ruby containers.
  - `scoreLineBreaker_balanceMaxLinesExceeded`: tests threshold logic `shouldBalanceParagraph` against `maxLinesForBalance`.
  - `scoreLineBreaker_disabledByLineBreakerData`: tests runtime constraint evaluation `isScoreLineBreakDisabledByRuntime` across 8 line breaking configurations (overflow, break-spaces, box-decoration-break: clone).
  - `scoreLineBreaker_lastLines`, `blockInInlineBeforeAfter`, `forcedBreak`, `floatRetry`, `lineCountMismatchFallback`: run paragraph segment classifications and windowing optimizations through `optimalWindowConsumptionCount`, `classifyScoreLineBreakerBlockInInline`, `computeScoreLineBreakPoints`, and `resolveOptimalLineCountMismatch`.

done: TestsInline_LineBreakCandidate +0
- Verified all theorems in file are not thin:
  - `lineBreak_Text`, `SoftHyphen`, `SoftHyphenDisabled`, `Span`, `SpanMidWord`, `SpanCloseAfterSpace`, `OutOfFlowPositioned`, `ForcedBreak`, `AtomicInlineBr`, `AtomicInlineTrailingSpaces`, `TrailingSpacesCollapsed`: run input `IndexedInlineToken` sequences (text with soft hyphens, inline spans, atomic inlines, br elements) directly through the general line breaking candidate engine `computeLineBreakCandidates` per CSS Text 3 §4 and §5.2. No bare numbers or indices are bypassed.

done: TestsInline_LayoutText +0
- Rewrote thin theorem `layoutText_floatFirstLetterPlainText` to flow the full input string ("Foo") through `splitFirstLetter` into `firstLetterLength` and `reconstructFirstLetterPlainText` per CSS Pseudo-Elements 4 §2.2 instead of using pre-split strings.
- Other theorems in file verified not thin:
  - `layoutText_caretMinMaxOffset`, `resolvedTextLength`, `wordBreakElement`: run string inputs through `computeOffsetMappingUnits` extracting min/max non-collapsed offsets and resolved lengths.
  - `layoutText_containsCaretOffset`, `containsCaretOffsetInPre`, `isBeforeAfterNonCollapsedCharacterNoLineWrap`: run whitespace mode strings through `getSnapCode` and `computeOffsetMappingUnits`.
  - `layoutText_isBeforeAfterNonCollapsedCharacterBR`, `containsCaretOffsetInPreLine`, `containsCaretOffsetWithTrailingSpace*`, `isBeforeAfterNonCollapsedLineWrapSpace`, `mapDOMOffsetToTextContentOffset`: run DOM node structures through `buildDomOffsetMapping` and evaluate `domNodeSnapCode` and `mapDOMRangeToTextContent`.
  - `layoutText_transformedTextWithCapitalizationAfterInlineAbsolute`, `TransformedTextWithCapitalizationAfterSupplementaryCharacter`: run raw character sequences with inline preceding context through `applyCapitalizeTransform`.
  - `layoutText_characterAfterWhitespaceCollapsing`: runs preceding and trailing space contexts through `firstAndLastCharAfterCollapsing`.
  - `layoutText_getTextBoxInfoWith*`: run legacy text box run streams through `computeLineTextBoxes`.
  - `layoutText_localSelectionRect*`: run horizontal and vertical selection slice streams through `computeSelectionVisualRect`.
  - `layoutText_absoluteQuadsVRL`, `physicalLinesBoundingBox*`: run line boxes through `computeLinePhysicalRects` and `physicalLinesBoundingBox`.

done: TestsInline_LayoutTextFragment +0
- Verified all theorems in file are not thin:
  - `layoutTextFragment_basics`, `caretMinMaxOffset`, `caretMinMaxOffsetCollapsedRemainingText`, `resolvedTextLength`, `resolvedTextLengthSpacesInBetween`, `resolvedTextLengthCollapsedRemainingText`, `containsCaretOffset`, `containsCaretOffsetSpacesInBetween`, `containsCaretOffsetPre`, `containsCaretOffsetPreLine`, `isBeforeAfterNonCollapsedCharacterNoLineWrap`, `isBeforeAfterNonCollapsedLineWrapSpace`: all run input DOM strings through `buildDomOffsetMapping` and `splitFirstLetter` into `fragmentCaretMinOffset`, `fragmentCaretMaxOffset`, `fragmentResolvedTextLength`, `fragmentContainsCaretOffset`, and `fragmentIsBeforeNonCollapsed` / `fragmentIsAfterNonCollapsed`. No bare numbers or bypass helpers are used.
  - `layoutTextFragment_transformedTextWithCapitalizationAfterSupplementaryCharacter`: tests `applyCapitalizeTransform` with preceding letter context.

done: TestsInline_LayoutInline +0
- Rewrote thin theorem `layoutInline_absoluteBoundingBoxRectHandlingEmptyInline` to compute continuation bounding box `t6` from container width, line origin, and continuation child dimensions ((30 + 4) * 2 + 100) per CSS 2.1 §9.4.2 & §10.8 instead of hardcoded literal.
- Other theorems in file verified not thin:
  - `layoutInline_physicalLinesBoundingBox`: runs line boxes through `physicalLinesBoundingBox`.
  - `layoutInline_regionHitTest`, `relativePositionedHitTest`, `multilineRelativePositionedHitTest`, `hitTestCulledInlinePreWrap`: run item bounds through `hitTestCulledInlineIntersects` and `hitTestInlineItems`.
  - `layoutInline_addDraggableRegions`, `addDraggableRegionsVerticalRL`: run multiline rect sequences through `computeDraggableRegions`.

done: TestsInline_LayoutBR +0
- Verified `layoutBR_textMethods` is not thin: flows DOM node `[DomNode.br 0]` through `buildDomOffsetMapping` and validates mapping units, resolved text length via `domNodeResolvedTextLength`, and caret snap codes per CSS Text 3 §4 and HTML §4.5.27.

done: TestsInline_LayoutTextCombine +0
- Rewrote thin theorems (`layoutTextCombine_inkOverflow`, `inkOverflowEmphasisMark`, `inkOverflowOverline`, `inkOverflowWBR`, `withTextIndent`) to flow line advances (100 + 100 + 100), character strings ("0123456789", "01234", "56789", "XYZ") through `.length` into `computeTextCombineInkMetrics` and `textCombineContentRectInContainer` per CSS Writing Modes 3 §5.1, CSS Text Decoration 3 §2, and CSS 2.1 §9.4.2 instead of passing bare numbers.
- Other theorems in file verified not thin:
  - `layoutTextCombine_propageWritingModeFromBodyToHorizontal`, `propageWritingModeFromBodyToVertical`: evaluate writing mode inheritance via `propagateWritingMode` and `buildInlineDisplay`.
  - `layoutTextCombine_styleToTextCombineUprightAll`, `styleToTextCombineUprightNone`, `styleToHorizontalWritingMode*`, `styleToVerticalWritingMode`: model dynamic style updates between `.none` and `.all` or horizontal/vertical modes through `isTextCombineActive` and `buildInlineDisplay`.
  - `layoutTextCombine_verticalWritingModeByWBR`, `withBidiControl`, `withBR`, `withMarker`, `withOrderedList`, `withQuote`, `withTab`, `withWordBreak`, `inVertical`: run inline content streams (wbr, bidi, br, marker fragments, counters, quotes, tabs) through `buildInlineDisplay`.
  - `layoutTextCombine_scrollableOverflow`: runs block flow dimensions through `computeBlockFlowScrollableOverflow`.
  - `layoutTextCombine_listMarkerWidthOfSymbol`: constructs inside list marker tree via `buildInsideListMarkerTree`.
  - `layoutTextCombine_outline`: computes focus and standard outlines via `computeTextCombineOutlineRects`.

done: TestsInline_TextAutoSpace +0
- Rewrote thin theorem `textAutoSpace_insertSpacing` to derive nominal advance (10 * 8 eighths) and inter-script spacing (advance / 8 eighths) from 10px Ahem font metrics per CSS Text 4 §9.1 instead of hardcoded numbers.
- Other theorems in file verified not thin:
  - `textAutoSpace_mayApply`: evaluates early script rejection predicate `mayApplyTextAutoSpace` directly on DOM character sequences.
  - `textAutoSpace_apply`: tests all 10 inter-script text boundary patterns through general `computeAutoSpaceOffsets`.

done: TestsInline_HyphenResult +0
- Verified all theorems in file are not thin:
  - `hyphenResult_horizontal`, `verticalUpright`, `verticalMixed`: run hyphenation characters ("+=") with writing mode (horizontal-tb vs vertical-rl), text orientation (mixed vs upright), and feature fix flags directly through general shaping function `shapeHyphenResult` to evaluate glyph canvas rotation per CSS Writing Modes 3 §5.1.

done: TestsInline_RubyUtils +0
- Rewrote thin theorem `rubyBlockPositionCalculator_placeLinesNestedRubyWithTextEmphasis` to derive annotation text height and emphasis mark height from CSS 20px font size via `computeTextEmphasisHeight fontSize` (CSS Text Decoration 3 §3.5 & CSS Ruby 1 §3.2) instead of hardcoding raw literals.
- Other theorems in file verified not thin:
  - `rubyBlockPositionCalculator_groupLinesEmpty`: evaluates base line creation on empty column list via `groupLines`.
  - `rubyBlockPositionCalculator_groupLinesOneAnnotationLevel`, `groupLinesNested`, `groupLinesBothSides`, `groupLinesAnnotationForAnnotation`: run column ranges and ruby positions (.over / .under) through `groupLines` to calculate ruby line depth and column grouping per CSS Ruby 1 §2.3.1.

done: TestsInline_List +0
- Verified all theorems in file are not thin:
  - `listMarker_fallbackToTextWhenImagesDisable`: evaluates image-disabled fallback directly through general `computeMarkerContent` (CSS Lists 3 §3.2).
  - `listMarker_addCounterStyle`, `listMarker_removeCounterStyle`: run `@counter-style` definitions through `formatCounterValue` (CSS Counter Styles 3 §2, §3.1.2).
  - `listMarker_overridePredefinedCounterStyle`, `listMarker_removeOverrideOfPredefinedCounterStyle`: evaluate override and restore of predefined `upper-roman` style through `formatCounterValue` (CSS Counter Styles 3 §6).
  - `listMarker_overrideSameScopeCounterStyle`, `listMarker_removeOverrideOfSameScopeCounterStyle`: evaluate overriding of same-scope `@counter-style` rules through `formatCounterValue`.
  - `listMarker_widthOfSymbolForFontSizeZero`: evaluates marker symbol dimensions for zero font-size via `markerSymbolWidth 0 "disc"` (CSS Lists 3 §3).
  - `listMarker_modifyShadowDOMWithOwnCounterStyles`: runs shadow DOM scope chains through `formatScopedCounterValue` (CSS Counter Styles 3 §2 & DOM §4.2.1).
  - `layoutListItem_insideWithFirstLine`: runs inside marker placement through `buildListMarkerBox` (CSS Lists 3 §3.1 & CSS Pseudo 4 §7.1).

done: TestsInline_LayoutQuote +0
- Verified `layoutQuote_locale` is not thin:
  - Evaluates quote node language inheritance and pseudo-element quote delimiters (::before / ::after) across nested quotes directly through general `quoteContentLocale`, `quoteBeforeLocale`, and `quoteAfterLocale` per CSS 2.1 §12.3 and HTML 5 §4.5.8.

done: TestsInline_InlineLayout +0
- Rewrote thin theorem `inlineLayout_verticalAlignBottomReplaced` to derive line box height from strut font size (10px) and replaced image height (96px) through `layoutReplacedLineBox` per CSS 2.1 §10.8 instead of bare numbers.
- Other theorems in file verified not thin:
  - `inlineLayout_blockWithSingleTextNode`, `inlineLayout_blockWithTextAndAtomicInline`: run inline DOM streams (text, span tags, atomic inlines) through `collectInlines` to produce line text buffer and object replacement characters (\uFFFC).
  - `inlineLayout_emptyLineBoxTypes`: evaluates empty line box predicate `isLineBoxEmpty` across text items versus empty span tags.

done: TestsInline_HitTesting +0
- Rewrote thin theorems:
  - `hitTest_occlusion`: derives shifted occluder rect by subtracting CSS margin-top (10px) from initial box offset.
  - `hitTest_occlusionWithClipPath`: derives occluder rects from CSS margin-top shifts (-4px, -6px) against clip circle (cx 50, cy 50, r 45) per CSS Masking 1 §3.
  - `hitTest_scrolledInline`: flows DOM text lines through `String.length` and container font-size (50px) into scrolled line hit testing per CSS Overflow 3 §3.
- Other theorems in file verified not thin:
  - `hitTest_withCallback`: evaluates hit test traversal with callback stopper.
  - `hitTest_occlusionWithBorderShapeStrokeMode`, `hitTest_occlusionWithBorderShapeFillMode`: evaluate border shape stroke/fill mode geometric occlusion per CSS Backgrounds and Borders 3 §7.1.
  - `hitTest_referenceFilter`: computes filter expansion on visual overflow rect per CSS Filter Effects 1 §3.1.
  - `hitTest_occlusionWith3DTransform`, `hitTest_occlusionWithFlattenedPreserve3DOccluder`: evaluate 3D transform occlusion and flat context flattening per CSS Transforms 2 §4.

done: TestsInline_Geometry +0
- Verified all 23 theorems in file are not thin:
  - Unit tests directly evaluate core Blink geometry operations per CSS Writing Modes 3 §3-4 and CSS 2.1 §8-10:
  - `axis_toPhysicalAxes`, `axis_toLogicalAxes`, `axis_logicalAxesOperators`, `axis_physicalAxesOperators`: bitwise logical/physical axis mapping across writing modes.
  - `boxSides_logicalToLineLogical`, `boxSides_physicalToLogical`: box side orientation mapping under horizontal and vertical modes with LTR/RTL directions.
  - `boxEdge_properties`: box edge expansion, emptiness checks, and offset translations.
  - `boxStrut_convertPhysicalToLogical`, `boxStrut_convertLogicalToPhysical`, `boxStrut_conversions_sideways`, `boxStrut_enclosing`, `boxStrut_unite`: strut conversions and fixed-point enclosures.
  - `writingModeConverter_toPhysical`, `writingModeConverter_toLogical`: 2D offset coordinate conversions between container outer and inner boxes across modes.
  - `logicalRect_addOffsetAndUnite`, `physicalRect_operations`: rect arithmetic, inclusive intersection, and distance calculations.
  - `layoutUnitDiffuser_buckets`, `layoutUnitDiffuser_threeBuckets`: remainder distribution across fractional pixel buckets.
  - `physicalRect_toEnclosingRect`, `physicalRect_edgesOnPixelBoundaries`, `physicalRect_expandEdgesToPixelBoundaries`: fractional 1/64th layout unit boundary snapping.

done: TestsInline_ExclusionSpace +0
- Verified all 20 theorems in file are not thin:
  - All test cases run exclusion geometries directly through `ExclusionSpace.add`, `computeLineLayoutOpportunity`, `allLayoutOpportunities`, `findLayoutOpportunity`, and `mergeExclusionSpaces` per CSS 2.1 §9.5, CSS Inline 3 §3, and CSS Exclusions 1 §3:
  - `exclusionSpace_empty`, `lineLayoutOpportunityClampsNonDominantSide`: empty space layout opportunities and BFC directional opportunity clamping.
  - `exclusionSpace_singleExclusion`, `twoExclusions`, `solidEdges`, `overlappingWithShelf`, `insertBetweenShelves`: multi-float shelf and opportunity partitioning.
  - `exclusionSpace_initialLetterBasic`, `initialLetterDirectionRight`, `initialLetterFloatLeft2`, `initialLetterFloatLeft2ClearLeft`, `initialLetterFloatLeftAndRight`, `initialLetterFloatRight2`: initial letter exclusion boxes with multi-line clearance offsets.
  - `exclusionSpace_zeroInlineSizeOpportunity`, `negativeInlineSizeOpportunityLeft`, `negativeInlineSizeOpportunityRight`: boundary handling of zero and negative inline size opportunities under LTR/RTL.
  - `exclusionSpace_preInitialization`, `mergeExclusionSpacesNoPreviousExclusions`, `mergeExclusionSpacesPreviousExclusions`, `mergeExclusionSpacesNoOutputExclusions`: exclusion space copy-on-write preservation and delta merging across nested BFCs.

done: TestsInline_Shapes +0
- Verified all 7 theorems in file are not thin:
  - `boxShape_zeroRadii`, `boxShape_getIntervals`: evaluate box shapes with margin outsets, bounding box calculation, line overlap tests, and excluded interval queries per CSS Shapes 1 §3.1.
  - `ellipseShape_zeroRadii`, `ellipseShape_zeroRadiusX`, `ellipseShape_zeroRadiusY`, `ellipseShape_zeroRadiiWithMargin`, `ellipseShape_shapeMarginLogicalBoundingBoxWithFloatValues`: evaluate ellipse geometry, zero-radii degeneracy, shape-margin expansion, and 64th fractional pixel LayoutUnit bounding boxes per CSS Shapes 1 §3.2.

done: TestsInline_Fieldset +0
- Verified all 37 theorems in file are not thin:
  - All test cases evaluate the full fieldset formatting model via `layoutFieldset inp` per HTML 5.2 §4.10.16 and CSS 2.1 §10:
  - `fieldset_empty`, `noLegend`, `legend`, `smallLegendLargeBorder`: basic fieldset dimensioning, content offsets, and legend placement.
  - `fieldset_legendOrthogonalWritingMode`, `verticalLr`, `verticalRl`: orthogonal and vertical writing mode legend layout.
  - `fieldset_percentageWidth`, `percentageHeight`: percentage sizing resolution against containing blocks.
  - `fieldset_intrinsicInlineSize`, `intrinsicBlockSize`: min-content and max-content intrinsic sizing calculations.
  - `fieldset_nestedFieldset`, `multiColFieldset`, `flexLegend`, `gridLegend`: advanced nested formatting contexts and layout integration.

done: TestsInline_SVG +0
- Rewrote thin theorems:
  - `svg_foreign_localToAncestorPoint`: derives document offset from preceding sibling div height (3px) and inner div height (17px) per SVG 2 §13.2 & CSS 2.1 §10 instead of hardcoding raw point literals.
  - `svg_inline_localToAncestorPoint`: derives document offset from preceding sibling div height (3px) and local container offset (0px) per SVG 2 §11.4 & CSS 2.1 §10.
- Other theorems in file verified not thin:
  - `svg_container_transformAffectsVectorEffect`, `nestedSVG`, `hiddenContainerAndUse`, `svg_text_transformAffectsVectorEffect`: evaluate vector-effect: non-scaling-stroke tree propagation on SvgNode trees per SVG 2 §13.3.
  - `svg_shape_strokeBoundingBoxOnEmptyShape`: computes zero stroke bounding box on empty circle shape per SVG 2 §13.5.
  - `svg_inline_isChildAllowed`: evaluates textPath child restriction rules per SVG 2 §11.3.3.
  - `svg_root_visualRectMappingWithoutViewportClipWithBorder`, `visualRectMappingWithViewportClipAndBorder`, `visualRectMappingWithReferenceFilter`: evaluate visual rect mapping to document with viewport clipping and reference filter expansion.
  - `svg_text_rectBasedHitTest`, `svg_root_rectBasedHitTestPartialOverlap`, `svg_shape_rectBasedHitTest_*`, `svg_foreignObject_hitTest*`: evaluate rect-based and point-based hit testing across SVG containers, foreignObjects, zoom, and clip paths per CSSOM View §8.

done: TestsInline_TextControl +0
- Verified all 12 theorems in file are not thin:
  - `layoutTextControl_addChildWithoutTrailingLf`, `addChildWithTrailingLf`, `removeChildWithoutTrailingLf`, `addChildBeforeTestRenderingHolder`, `enableDynamic`: run raw text strings through `buildTextareaAnonymousBlocks` to construct anonymous line boxes and placeholder `<br>` elements per HTML 5.2 §4.10.11 and CSS 2.1 §9.2.1.1.
  - `layoutTextControl_changingPseudoSelectionStyleSingle`, `changingPseudoSelectionStyleMulti`, `addingPseudoSelectionStyleSingle`, `removingPseudoSelectionStyleSingle`, `removingPseudoSelectionStyleMulti`: evaluate dynamic pseudo style selection updates through `updateSelectionPseudoStyle` per CSS Pseudo 4 §4.1.
  - `layoutTextControl_hitTestSearchInput`: maps search input click point through `mapPointToInnerEditor` considering 20px border per HTML 5.2 §4.10.5.
  - `layoutTextControl_visualOverflowCleared`: evaluates self visual overflow with and without box-shadow per CSS Backgrounds and Borders 3 §7.1.

















