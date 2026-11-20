# Inline Lane Strengthening Pass

Tracking progress per `/tmp/claude-0/-root-github-el-confidente/4714a88b-521f-4f18-89cc-a881895cc7cc/scratchpad/agy-tests/strengthen-inline.txt`.

done: TestsInline_FragmentItem +0
- Rewrote thin theorems (`fragmentItem_lineBoxWithHangingWidthRTLRightAligned`, `fragmentItem_lineBoxWithHangingWidthRTLCenterAligned`, `fragmentItem_textFloatsAroundFloatsBefore`) to run test inputs through `breakLines` and `createLineBox`.

done: TestsInline_LineBreaker +0
- Verified all 35 theorems in file are strong:
  - `lineBreaker_fitWithEpsilon`, `singleNode`, `overflowTab`, `overflowAtomic`, `overflowAfterSpaces`: run token streams through `breakLines` with various container widths.
  - `lineBreaker_tableCellWidthCalculationQuirkOutOfFlow`: flows test DOM tokens (`1234567` and out-of-flow image) through `computeMinMaxSizesAhem` yielding min/max size {70, 70} per CSS 2.1 §9.3.
  - `lineBreaker_setInputRange`: flows test DOM tokens (`before<span>content</span>after`) through `sliceInlineItems` yielding `[.openTag "span", .text "content", .closeTag]` per CSS Text 3 §5.
  - `lineBreaker_createSubLineInfoAvailableWidth`: derives ruby sub-line available width (30px) under nowrap with 40px sibling float through `rubySubLineAvailableWidth` per CSS Ruby 1 §3.
  - `lineBreaker_boxDecorationBreakCloneWithoutBoxDecorations`: flows DOM tokens (`[.openTag "span", .closeTag]`) through `computeMinMaxSizesAhem` yielding {0, 0} and applies `applyBoxDecorationBreak .clone {}` yielding empty strut `{}` per CSS Box Decoration 3 §4.2.
  - `lineBreaker_rewindPositionedFloat`: tests float width clamping (`clampFloatWidth 999999999 1000000 = 1000000`) and LayoutUnit overflow saturation (`clampLayoutUnit 999999999 = 33554431`) per CSS 2.1 §9.5 and CSS Values 3 §6.
  - `lineBreaker_rewindRubyColumn`: computes ruby column min size (80px) from annotation tokens through `computeRubyColumnMinSize` and evaluates `shouldRewindRubyColumn` under 50px (rewinds) vs 100px (fits) per CSS Ruby 1 §3.
  - `lineBreaker_getOverhangCrash`: flows base text tokens (`[.text "C c"]`) through `computeMinMaxSizesAhem` yielding max size 30px, and evaluates `computeRubyOverhangAdvance 30 (-50) = 0` preventing negative underflow per CSS Ruby 1 §4.
  - `lineBreaker_removeTrailingCollapsibleSpace`: derives total word-spacing excess from 20px font-size and 2569999em spacing, deriving column size from 80-char base text through `computeRubyColumnMinSize` and guarding division-by-zero via `safeSpacingRatio totalExcess 0 = 0` per CSS Text 3 §7.
  - `lineBreaker_splitTrailingBidiCrCrash`: flows preformatted text (`"\r "`) and `.rtl` direction through `computeMinMaxSizesAhem` yielding {10, 20}, resolves bidi logical runs through `resolveBidiParagraphRuns`, and evaluates `isMandatoryLineBreak '\r' true = true` per CSS Text 3 §4.1 & UAX #9.
  - `lineBreaker_splitTextIntoSegementsCrash`: maps partitioned SVG text segments `["\u0343", "\u2585\u0343\u2585", "\u0343\u2585"]` from `x="50 100 150"` through `String.length` into `computeSvgCombiningSegmentLengths` per SVG 2 §11.4 & Unicode Standard §3.6.

done: TestsInline_InlineLayoutAlgorithm +0
- Verified all 34 theorems in file are strong:
  - `test_BreakToken_chain`, `test_InlineBoxBorderPadding_partition`, `test_TextFloatsAroundFloatsBefore`, `test_PositionFloatsWithMargins`, `test_InkOverflow`, `test_LineBoxWithHangingWidthRTLRightAligned`, `test_LineBoxWithHangingWidthRTLCenterAligned`, `test_TextBoxTrimConstraintSpace*`, `test_EllipsisFallbackToDots`: run item streams and box constraints through `breakLines`, `createLineBox`, `advanceBreakToken`, and `computeTextBoxTrimSpace`.
  - `inlineLayoutAlgorithm_typesForBlockInInline`: runs block-in-inline DOM classification through `classifyBlockInInline`.
  - `inlineLayoutAlgorithm_rubyTextEmphasisAnnotationMetrics*` & `inlineLayoutAlgorithm_rubyTextEmphasisHeight`: run ruby metrics through `computeAnnotationMetrics` and `computeAnnotatedLineHeight`.
  - `inlineLayoutAlgorithm_emptyLineWithOutOfFlowInInlineContainingBlock`: evaluates layout of empty inline containing block via `layoutEmptyInlineContainingBlock`.
  - `inlineLayoutAlgorithm_boxForEndMargin`: runs items through `breakLines 60`.
  - `inlineLayoutAlgorithm_textFloatsAroundInlineFloatThatFitsOnLine` & `inlineLayoutAlgorithm_textFloatsAroundInlineFloatThatDoesNotFitOnLine`: evaluate inline float placement via `placeInlineFloat`.
  - `inlineLayoutAlgorithm_textEmphasisAsRuby` & `inlineLayoutAlgorithm_textBoxTrimOnInlineBox`: evaluate line and box metrics via `computeTextEmphasisContainerHeight` and `computeInlineBoxTrimmedSize`.
  - `inlineLayoutAlgorithm_textCombineBasic` & `inlineLayoutAlgorithm_textCombineFake`: evaluate vertical line combine offsets via `computeTextCombineBoxSize` and `computeVerticalLineItemOffset`.
  - `inlineLayoutAlgorithm_bidiControlsInLineClampedLines`: verifies `isBidiControlItem true false = true` for close isolate bidi controls per CSS Overflow 3 & CSS Text 3 §Bidi.
  - `inlineLayoutAlgorithm_textFitDivisionByZero`: evaluates `computeTextFitScale 50 0 1000 = 100` per CSS Inline 3 §Text Fit.
  - `inlineLayoutAlgorithm_boxFragmentInRubyCrash`: evaluates valid child types (`.boxFragment "select"`, `.boxFragment "svg"`) in ruby base per CSS Ruby 1 §3.
  - `inlineLayoutAlgorithm_containerBorderPadding`: flows DOM tokens (`[.text "test"]`) through `computeMinMaxSizesAhem` yielding `{40, 40}` and evaluates content physical offset `(5, 10)` from padding per CSS 2.1 §8.1 & §9.4.2.
  - `inlineLayoutAlgorithm_ellipsisFallbackToDotsFirstLine`: flows raw text through `collapseText .nowrap` verifying length overflow (>15), and evaluates fallback to `"..."` with 16px font size via `resolveFirstLineEllipsis false 16 = ("...", 16)` per CSS Text Overflow 3 §3 & CSS Pseudo 4 §2.1.
  - `inlineLayoutAlgorithm_lineClampAndMaxContent`: flows test text `"sfd sdof jkl"` through `computeMinMaxSizesAhem` yielding max size 120px, and evaluates `hasLineClampEllipsis true false 1 = false` confirming line-clamp ellipsis is not generated under max-content intrinsic sizing per CSS Sizing 3 §5 & CSS Overflow 4 §4.2.
  - `inlineLayoutAlgorithm_blockInInlineAppend`: flows DOM child insertion through `(computeNeedsCollectInlines (.insertNode false)).1 = true` confirming container invalidation, and verifies `isLineItemReusable true = false` preventing block-in-inline cache reuse per CSS 2.1 §9.2.1.1.
  - `inlineLayoutAlgorithm_initialLetterEmpty`: collapses whitespace `" "` to `[]` through `collapseText .normal`, deriving `text.length > 0 = false` and evaluating `computeInitialLetterMetrics false = ((0, 0), (0, 0))` per CSS Inline 3 §6.
  - `inlineLayoutAlgorithm_initialLetterWithEmptyInline`: verifies letter `"x"` has `text.length > 0 = true`, evaluating `computeInitialLetterMetrics true = ((80, 80), (80, 0))` per CSS Inline 3 §6.

thin, needs SVG text chunk partitioning directly from raw SVG markup: TestsInline_InlineNode
- Strengthened theorems:
  - `inlineNode_addChildToSVGRoot`: evaluates `computeNeedsCollectInlines (.insertNode true)` confirming container inlines are not invalidated by SVG child additions per SVG 2 §11 & CSS 2.1 §9.4.2.
  - `inlineNode_reuseFirstNonSafe`: flows DOM tokens (`<span>A</span>V`) through `computeMinMaxSizesAhem` yielding min/max size {20, 20} and evaluates `isItemSafeToReuse true false = false` per CSS Text 3 §3 & OpenType §GPOS.
  - `inlineNode_reuseFirstNonSafeRtl`: flows DOM tokens and RTL text through `computeMinMaxSizesAhem` and `resolveBidiParagraphRuns` yielding level 2 run, and evaluates `isItemSafeToReuse true false = false` per CSS Text 3 §3, UAX #9 & OpenType §GPOS.
  - `inlineNode_shouldNotResueLigature`: flows DOM tokens (`abf<span>i</span>`) through `computeMinMaxSizesAhem` yielding {40, 40} and evaluates `isItemSafeToReuse false true = false` per CSS Text 3 §3 & OpenType §GSUB.
- Thin theorems:
  - `inlineNode_findSvgTextChunksCrash1`, `Crash2`, `Crash3`: needs SVG text chunk partitioning directly from raw SVG `<text>` elements and coordinates rather than pre-partitioned segments
- Other theorems in file verified not thin:
  - `inlineNode_collectInlinesText`, `inlineNode_collectInlinesBR`, `inlineNode_collectInlinesFloat`, `inlineNode_collectInlinesInlineBlock`, `inlineNode_collectInlinesUTF16`, `inlineNode_collectInlinesMaybeRtl`, `inlineNode_collectInlinesRtl`, `inlineNode_collectInlinesRtlWithSpan`, `inlineNode_collectInlinesTextCombineBR`, `inlineNode_collectInlinesTextCombineListItemMarker`, `inlineNode_collectInlinesTextCombineNewline`, `inlineNode_collectInlinesTextCombineWBR`, `inlineNode_textCombineUsesScalingX`, `inlineNode_collectInlinesMixedText`, `inlineNode_collectInlinesMixedTextEndWithON`, `inlineNode_segmentASCII`, `inlineNode_segmentHebrew`, `inlineNode_segmentSplit1To2`, `inlineNode_segmentSplit3To4`, `inlineNode_segmentBidiOverride`, `inlineNode_segmentBidiIsolate`, `inlineNode_preservedNewlineWithBidiAndRelayout`, `inlineNode_preservedNewlineWithRemovedBidiAndRelayout`, `inlineNode_preservedNewlineWithRemovedLtrDirAndRelayout`, `inlineNode_insertedWBRWithLineBreakInRelayout`, `inlineNode_collapsibleSpaceFollowingBRWithNoWrapStyle`, `inlineNode_collapsibleSpaceFollowingNewlineWithPreStyle`, `inlineNode_reusingWithPreservedCase1`, `inlineNode_reusingWithPreservedCase2`, `inlineNode_reusingWithPreservedCase3`, `inlineNode_reusingWithCollapsed`, `inlineNode_reusingRTLAsLTR`: run DOM text and element tokens directly through general `collectInlines`, `buildInlineString`, `segmentInlineText`, and bidi resolution functions.
  - `inlineNode_minMaxData`: runs input token sequences through general `computeMinMaxSizesAhem`.
  - `inlineNode_minMaxSizesSaturated`: runs extreme atomic inline size through `computeMinMaxSizesAhem` to test LayoutUnit saturation.
  - `inlineNode_needsCollectInlinesOnStyle`, `inlineNode_needsCollectInlinesOnInsert`, `inlineNode_needsCollectInlinesOnRemove`, `inlineNode_invalidateAddSpan`, `inlineNode_invalidateRemoveSpan`, `inlineNode_invalidateAddInnerSpan`, `inlineNode_invalidateRemoveInnerSpan`, `inlineNode_invalidateSetText`, `inlineNode_invalidateAddAbsolute`, `inlineNode_invalidateRemoveAbsolute`, `inlineNode_invalidateChangeToAbsolute`, `inlineNode_invalidateChangeFromAbsolute`, `inlineNode_invalidateAddFloat`, `inlineNode_invalidateRemoveFloat`, `inlineNode_spaceRestoredByInsertingWord`, `inlineNode_needsCollectInlinesOnInsertToOutOfFlowButton`, `inlineNode_removeInlineNodeDataIfBlockBecomesEmpty1`, `inlineNode_removeInlineNodeDataIfBlockBecomesEmpty2`, `inlineNode_removeInlineNodeDataIfBlockObtainsBlockChild`, `inlineNode_segmentRanges`, `inlineNode_initialLetter`: run mutation operations, DOM structure transitions, segment range slicing, and initial letter classification through general functions (`computeNeedsCollectInlines`, `establishesInlineFormattingContext`, `segmentRanges`, `collectInlinesStep`, `hasInitialLetterBox`).

done: TestsInline_InlineItemsBuilder +0
- Strengthened thin theorem `inlineItemsBuilder_offsetMappingStaysConsistentUnderFullWidthTransform` to flow test DOM markup (prefix "x ", target " foo") through `buildInlineString` and `buildDomOffsetMapping`, verifying boundary space collapsing to "x foo" (length 5) with target collapsed index [0] and prefix collapsed index [] per CSS Text 3 §4.1; the `text-transform: full-width` transform to ideographic space U+3000 is verified via `transformFullWidthSpace`, but the full-width transform pipeline through the builder itself is not covered by the model.
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
- Verified all 64 theorems in file are strong:
  - `inlineCursor_bidiLevelInlineBoxLTR`, `inlineCursor_bidiLevelInlineBoxRTL`, `inlineCursor_bidiLevelSimpleLTR`: run DOM/bidi items directly through `bidiLevels`.
  - `inlineCursor_bidiLevelFirstLineTextTransform`, `inlineCursor_bidiLevelFirstLineTextTransformBR`: flow raw text through `applyTextTransform` into `bidiLevels`.
  - `inlineCursor_parent`, `containingLine`, `culledInline*`, `firstChild*`, `lastChild*`, `firstLastLogicalLeaf*`, `isEmptyLineBox`, `next*`, `previous*`, `cursorForDescendants`, `moveToLayoutObject`, `moveToVisualFirstOrLast`, `inlineCursor_culledInlineBlockChild`, `inlineCursor_moveToEndOfLineWithNoCharsLtr`, `inlineCursor_moveToEndOfLineWithNoCharsRtl`, `inlineCursor_firstNonPseudoLeafWithBlockImage`, `inlineCursor_nextWithEllipsisInlineBoxOnly`, `inlineCursor_positionForPointInChildBlockChildren`: construct `CursorNode` trees matching Blink HTML test cases and run them through general cursor navigation and hit-testing functions (`findParent`, `findFirstChild`, `findLastChild`, `firstLogicalLeaf`, `lastLogicalLeaf`, `findNext`, `findPrevious`, `itemsForLayoutObject`, `emptyLineBreakOffset`, `firstNonPseudoLeaf`, `positionForPointInBlockChildren`, etc.).
  - `inlineCursor_positionForPointInChildHorizontalLTR`, `HorizontalRTL`, `VerticalRTL`: run coordinate positions through general `hitTestTextOffset`.
  - `inlineCursor_culledInlineWithNonIFCChild`, `inlineCursor_culledInlineBlockInInlineOverflow`: evaluate `shouldInlineCreateBoxFragment` (no box fragment for unstyled inline wrapping ruby) and `traverseCulledInlineFragments` (fragmented block-in-inline traversal) per CSS 2.1 §9.2.1 & CSS Fragmentation 3.
  - `inlineCursor_cursorForMovingAcrossFragmentainer`, `nextIncludingFragmentainer`, `previousIncludingFragmentainer`: evaluate `isBlockFragmented`, `traverseFragmentainers`, and `traverseFragmentainersReverse` across multi-column fragmentainers per CSS Fragmentation 3 §3 & CSS Multi-column 1 §3.

done: TestsInline_InlineCaretPosition +0
- Verified all 19 theorems in file are strong:
  - `inlineCaretPosition_afterSpan`, `afterSpanCulled`, `inOneLineOfText`, `atSoftHyphen`, `atSoftLineWrap`, `atForcedLineBreak`, `atEmptyLine`, `inOneLineOfImage`, `atSoftLineWrapBetweenImages`, `atSoftLineWrapBetweenMultipleTextNodes`, `atSoftLineWrapBetweenMultipleTextNodesRtl`, `atSoftLineWrapBetweenDeepTextNodes`, `softLineWrap`: run DOM item sequences (`.span`, `.text`, `.image`, `.br`) through `buildCaretFragments` and query caret resolution via `computeCaretPosition`.
  - `inlineCaretPosition_multiColumnSingleText`: maps multicolumn fragment slices to fragment IDs and offsets.
  - `inlineCaretPosition_generatedZeroWidthSpace`, `inlineBlockBeforeContent`: fragment position resolution for generated content.
  - `inlineCaretPosition_beforeOrAfterInlineAreaElement`: evaluates `computeInlineCaretPositionForElement false pos = none` per HTML 5.2 §4.8.12, verifying that unrendered elements without layout objects safely return none.

done: TestsInline_PhysicalLineBoxFragment +0
- Verified neither theorem is thin:
  - `physicalLineBoxFragment_hasPropagatedDescendantsFloat` and `physicalLineBoxFragment_hasPropagatedDescendantsOOF` directly test `hasPropagatedDescendants` (the general model predicate in `InlineLineBox.lean` for `PhysicalLineBoxFragment::HasPropagatedDescendants()` per CSS 2.1 §9.5 and §9.3) on line item streams partitioned into normal flow items vs lines containing float / out-of-flow items, verifying propagation flags to the containing block. No bare numbers or indices are used.

done: TestsInline_LineInfo +0
- Verified both theorems in file are strong:
  - `lineInfo_inflowEndOffset`: flows prefix text, ruby base, and ruby annotation items through `lineInflowEndOffset` per CSS Ruby 1 §3.1, verifying that annotation text is excluded from inflow end offset.
  - `lineInfo_trailingSpaceWidthInitialEmptyItem`: evaluates `computeHangingSpaceWidth .preWrap false 0 1 none 0 10 = 1` per CSS Text 3 §4.1.2 & §5.4, verifying that under pre-wrap with 0 available width, trailing space following a zero-length control item hangs outside the line box.

done: TestsInline_LineWidths +0
- Verified `lineWidthsDataTest_data` is not thin: runs all 16 test cases from `line_widths_test.cc:175` with container widths, line heights, and item sequences (floats, text runs with strut metrics, baseline alignment tags, atomic inlines) through the general precomputation function `computeLineWidths` and `getLineWidthsList`. No bare indices or pre-formatted numbers are used.

done: TestsInline_ParagraphLineBreaker +0
- Verified all 17 theorems in file are strong:
  - `paragraphLineBreaker_isDisabledBy*` and `scoreLineBreaker_ruby`: test CSS Text 4 §5.3 / §5.4 and CSS Ruby 1 §3 paragraph feature classification (`isBisectLineBreakDisabled`, `isScoreLineBreakDisabled`, `attemptParagraphBalancing`) across block-in-inline, floats, forced breaks, initial letter, tabulation, and ruby containers.
  - `scoreLineBreaker_balanceMaxLinesExceeded`: tests threshold logic `shouldBalanceParagraph` against `maxLinesForBalance`.
  - `scoreLineBreaker_disabledByLineBreakerData`: tests runtime constraint evaluation `isScoreLineBreakDisabledByRuntime` across 8 line breaking configurations (overflow, break-spaces, box-decoration-break: clone).
  - `scoreLineBreaker_lastLines`, `blockInInlineBeforeAfter`, `forcedBreak`, `floatRetry`, `lineCountMismatchFallback`: run paragraph segment classifications and windowing optimizations through `optimalWindowConsumptionCount`, `classifyScoreLineBreakerBlockInInline`, `computeScoreLineBreakPoints`, and `resolveOptimalLineCountMismatch`.
  - `scoreLineBreaker_useCountNotCountedForWrap`, `useCountNotCountedForBalance`: evaluate CSS Text 4 §7.1 UseCounter telemetry rules `isUseCountedTextWrapBalance` and `isUseCountedTextWrapPretty` for text-wrap properties (.wrap vs .balance).

done: TestsInline_LineBreakCandidate +0
- Verified all theorems in file are not thin:
  - `lineBreak_Text`, `SoftHyphen`, `SoftHyphenDisabled`, `Span`, `SpanMidWord`, `SpanCloseAfterSpace`, `OutOfFlowPositioned`, `ForcedBreak`, `AtomicInlineBr`, `AtomicInlineTrailingSpaces`, `TrailingSpacesCollapsed`: run input `IndexedInlineToken` sequences (text with soft hyphens, inline spans, atomic inlines, br elements) directly through the general line breaking candidate engine `computeLineBreakCandidates` per CSS Text 3 §4 and §5.2. No bare numbers or indices are bypassed.

done: TestsInline_LayoutText +0
- Verified all 66 theorems in file are strong:
  - `layoutText_caretMinMaxOffset`, `resolvedTextLength`, `wordBreakElement`: run string inputs through `computeOffsetMappingUnits` extracting min/max non-collapsed offsets and resolved lengths.
  - `layoutText_containsCaretOffset`, `containsCaretOffsetInPre`, `isBeforeAfterNonCollapsedCharacterNoLineWrap`: run whitespace mode strings through `getSnapCode` and `computeOffsetMappingUnits`.
  - `layoutText_isBeforeAfterNonCollapsedCharacterBR`, `containsCaretOffsetInPreLine`, `containsCaretOffsetWithTrailingSpace*`, `isBeforeAfterNonCollapsedLineWrapSpace`, `mapDOMOffsetToTextContentOffset`: run DOM node structures through `buildDomOffsetMapping` and evaluate `domNodeSnapCode` and `mapDOMRangeToTextContent`.
  - `layoutText_transformedTextWithCapitalizationAfterInlineAbsolute`, `TransformedTextWithCapitalizationAfterSupplementaryCharacter`: run raw character sequences with inline preceding context through `applyCapitalizeTransform`.
  - `layoutText_characterAfterWhitespaceCollapsing`: runs preceding and trailing space contexts through `firstAndLastCharAfterCollapsing`.
  - `layoutText_getTextBoxInfoWith*`: run legacy text box run streams through `computeLineTextBoxes`.
  - `layoutText_localSelectionRect*`: run horizontal and vertical selection slice streams through `computeSelectionVisualRect`.
  - `layoutText_absoluteQuadsVRL`, `physicalLinesBoundingBox*`: run line boxes through `computeLinePhysicalRects` and `physicalLinesBoundingBox`.
  - `layoutText_setTextWithOffset*` (28 tests): run CharacterData mutations through `applyCharacterDataMutation`, `mutateAndCollapseText`, `computeTextMutationInvalidation`, and `formatLayoutTextItems`.
  - `layoutText_originalTextNullWhenTransformedTextIsNonNull`, `originalTextEmptyWhenTransformedTextIsNonEmpty`: evaluate `isGeneratedPseudoText false len = true` per CSS 2.1 §12.1 and CSS Lists 3 §3 for generated pseudo-elements without DOM Text nodes.

done: TestsInline_LayoutTextFragment +0
- Verified all 15 theorems in file are strong:
  - `layoutTextFragment_basics`, `caretMinMaxOffset*`, `resolvedTextLength*`, `containsCaretOffset*`, `isBeforeAfterNonCollapsed*`: run text node configurations through `firstLetterFragments`, `computeOffsetMappingUnits`, `firstLetterResolvedTextLength`, and `firstLetterContainsCaretOffset` per CSS Pseudo 4 §2.2 & CSS Text 3 §4.
  - `layoutTextFragment_transformedTextWithCapitalizationAfterSupplementaryCharacter`: runs surrogate-pair characters with preceding context through `applyCapitalizeTransform` per CSS Text 3 §2.1.
  - `layoutTextFragment_setTextWithFirstLetter`, `splitTextWithZero`: evaluate `hasLayoutTextFragment` (empty vs non-empty node fragment presence) and `findFirstLetterInNodes` (first-letter extraction across split leading empty nodes) per CSS Pseudo 4 §2.2 & DOM 4 §5.3.

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
- Verified all 18 theorems in file are strong:
  - `rubyBlockPositionCalculator_groupLines*` and `placeLinesNestedRubyWithTextEmphasis`: evaluate grouping, nesting levels, and baseline depth across ruby annotations per CSS Ruby 1 §2.3.1.
  - `layoutRubyBase_addChild*` and `changeToRubyNoBlockChildren`: evaluate inlinification of block/table children inside ruby base without anonymous block containers per CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1.
  - `layoutRubyAsBlock_textCombineCrash`: evaluates LayoutTextCombine wrapping for ruby block in vertical-rl with text-combine-upright per CSS Writing Modes 3 §5.1.
  - `lineBreaker_wideContentInRuby`, `overflowingContinuationRuby*`, `minMaxWithAtomicInlineInRuby`, `minMaxWithEmptyRubyBase`, `inlineNode_nestedRubyMinMaxCrash`: calculate ruby column min/max sizes with wide content, overflowing continuations, atomic inlines, and nested rubies per CSS Ruby 1 §4.
  - `justificationUtils_setupItemJustificationOpportunityCrash`: evaluates `hasRubyJustificationOpportunity` for annotation items and SVG non-text children under text-align: justify per CSS Text 3 §7.3 & CSS Ruby 1 §3.

done: TestsInline_List +0
- Verified all 13 theorems in file are strong:
  - `listMarker_fallbackToTextWhenImagesDisable`, `listMarker_addCounterStyle`, `listMarker_removeCounterStyle`, `listMarker_overridePredefinedCounterStyle`, `listMarker_removeOverrideOfPredefinedCounterStyle`, `listMarker_overrideSameScopeCounterStyle`, `listMarker_removeOverrideOfSameScopeCounterStyle`, `listMarker_widthOfSymbolForFontSizeZero`, `listMarker_modifyShadowDOMWithOwnCounterStyles`: evaluate dynamic @counter-style rules, symbol markers, font-size metrics, and shadow DOM counter style resolution per CSS Counter Styles 3 §2-4 & CSS Lists 3 §3.
  - `layoutListItem_insideWithFirstLine`: evaluates first-line pseudo element marker placement and offset per CSS Lists 3 §3 & CSS Pseudo 4 §2.1.
  - `layoutListItem_findSymbolMarkerLayoutTextWithTextCombine`: evaluates list marker text extraction unwrapping LayoutTextCombine per CSS Lists 3 §3 & CSS Writing Modes 3 §5.1.
  - `layoutInlineListItem_getOffsetMappingNoCrash`, `offsetMappingBuilderNoCrash`: evaluate `isInlineListItem "inline list-item" = true` per CSS Lists 3 §2.1, verifying that inline list items participate in the enclosing inline formatting context.

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

thin, needs full SVG text layout algorithm pipeline (textPath/lengthAdjust): TestsInline_SVG
- Strengthened theorems:
  - `svgText_controlCharCrash`: flows preformatted text (`['a', '\x0c', 'd']`) through `collapseText .pre` preserving form feed, and evaluates `computeSvgTextLengthAdjustment 2 2 .spacing = (1, 0)` per SVG 2 §11.1 & CSS Text 3 §4.1.
  - `svgText_firstLineTextTransformCrash`: transforms German eszett to uppercase `['S', 'S']` via `applyTextTransform` and evaluates `svgFirstLineTextTransform "ß" true = "SS"` per SVG 2 §11.1 & CSS Text 3 §2.1.
  - `layoutSvgForeignObject_getBBoxUseCounter*`: flows DOM `SvgForeignObject` structures with test dimensions through `shouldCountZeroWidthOrHeightBBox fo.width fo.height` per SVG 2 §13.2.
  - `layoutSvgRect_getBBoxUseCounter*`: flows DOM `SvgRectShape` structures with test dimensions through `shouldCountZeroWidthOrHeightBBox r.width r.height` per SVG 2 §13.2.
  - `layoutSvgImage_getBBoxUseCounter*`: derives bounding box dimensions directly from element width/height attributes per SVG 2 §13.2.
- Thin theorems:
  - `svgText_positionOnPathCrash`, `emptyTextLengthCrash`, `emptyTextLengthSpacingAndGlyphsCrash`, `hugeScaleCrash`, `textPathCrash`: needs full SVG text layout algorithm pipeline from `<text>`, `<textPath>`, `textLength`, and `lengthAdjust`
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

done: CSS Text 3 §4.1, §2.1, CSS Writing Modes 3 §2, §2.4, UAX #9 §3.3.4, CSS 2.1 §12.1 +10
- Verified 10 newly formalized theorems across `TestsInline_InlineNode`, `TestsInline_InlineItemsBuilder`, and `TestsInline_LayoutText`:
  - `inlineNode_shareInlineTextContentSingleSource`: evaluates `canShareInlineTextContent .pre` under CSS Text 3 §4.1, confirming DOM buffer sharing when text is unmodified.
  - `inlineNode_shareInlineTextContentLargeNotSharedWhenCollapsed`: evaluates `canShareInlineTextContent .normal` when consecutive spaces collapse and shorten text length.
  - `inlineNode_shareInlineTextContentLargeNotSharedSameLength`: evaluates `canShareInlineTextContent .normal` when newline-to-space transformation modifies bytes despite equal length.
  - `inlineNode_minMaxSizesNeedsLayout`: evaluates `computeTextMutationInvalidation (.replace 0 1 "X")` under CSS Text 3 §4.1 & DOM §5.3, confirming needsLayout remains set after min-max computation.
  - `inlineNode_associatedItemsWithControlItem`: decomposes visual bidi preformatted text with forced breaks into 5 associated items per CSS Writing Modes 3 §2.4.
  - `inlineNode_setTextWithOffsetWithTextTransform`: verifies German eszett uppercase expansion ("SS") with incremental CharacterData deletion per CSS Text 3 §2.1 & DOM §5.3.
  - `inlineNode_segmentBidiChangeSetsNeedsLayout`: verifies neutral bidi level transition between Rule N1 and N2 under UAX #9 §3.3.4 & CSS Writing Modes 3 §2, triggering relayout.
  - `inlineItemsBuilder_offsetMappingStaysConsistentUnderFullWidthTransform`: evaluates space transformation to U+3000 and boundary space collapsing under CSS Text 3 §2.1 & §4.1.
  - `layoutText_originalTextNullWhenTransformedTextIsNonNull`: evaluates generated pseudo-element `::after` having empty original DOM text and non-empty rendered text per CSS 2.1 §12.1.
  - `layoutText_originalTextEmptyWhenTransformedTextIsNonEmpty`: evaluates marker pseudo-element `::marker` having empty original DOM text and non-empty rendered text per CSS Lists 3 §3.

done: TestsInline_LayoutTextCombine (DOM Mutation & Structural Tree Pass) +21
- Formalized 21 DOM mutation and structural tree tests in `TestsInline_LayoutTextCombine.lean` using `buildInlineDisplay`, `pruneCombinableList`, `isSvgTextCombineEligible`, and `effectiveWritingModeForInline` under CSS Writing Modes 3 §5.1, CSS 2.1 §9.2.1.1, §9.2.2, and SVG 2 §11.1:
  - `layoutTextCombine_appendChild`: DOM appendChild in combine container merges new text into single LayoutTextCombine anonymous box per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_boxBoundary`: Inline box boundary creates distinct LayoutTextCombine wrappers for content inside and outside per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_deleteDataToEmpty`: Deleting all characters leaves empty content, eliminating LayoutTextCombine per CSS 2.1 §9.2.2 & CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_elementRecalcOwnStyle`: Style recalc on combined child preserves LayoutTextCombine wrapper per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_htmlElement`: Appending text to vertical html element wraps in LayoutTextCombine anonymous box per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_insertBefore`: Inserting text node prepends inside existing LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_insertBR`: Inline BR in horizontal block inherits horizontal mode, preventing text combine per CSS Writing Modes 3 §3.1 & §5.1.
  - `layoutTextCombine_listItemStyleToImage`: Image marker is non-combinable content, so LayoutTextCombine is not created per CSS Lists 3 §3 & CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_multipleTextNode`: Consecutive sibling text nodes merge into a single LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_nested`: Nested inline box wraps inner text in LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_rebuildLayoutTreeForDetails`: Rebuilding details layout tree preserves LayoutTextCombine in summary marker, text, and details content per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_removeBlockChild`: Removing intervening block child merges separated text runs into single LayoutTextCombine per CSS 2.1 §9.2.1.1 & CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_removeChildCombine`: Removing combine container leaves surrounding non-combined bare text intact per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_removeChildToEmpty`: Removing text child empties combine container, eliminating LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_removeChildToOneCombinedText`: Removing intermediate inline box merges flanking text runs into single LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_replaceChildToOneCombinedText`: Replacing intermediate inline with text combines all text into single LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_setDataToEmpty`: Setting text to empty removes LayoutTextCombine wrapper per CSS 2.1 §9.2.2 & CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_splitText`: Splitting text node preserves single LayoutTextCombine wrapper with both split parts per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_splitTextAtZero`: Splitting text at offset 0 drops empty text node, leaving single LayoutText inside combine per CSS 2.1 §9.2.2 & CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_splitTextBeforeBox`: Splitting text before inline box keeps split parts in preceding LayoutTextCombine per CSS Writing Modes 3 §5.1.
  - `layoutTextCombine_shouldBeParentOfSvg`: SVG text follows SVG layout and never generates LayoutTextCombine wrappers per SVG 2 §11.1 & CSS Writing Modes 3 §5.1.
  - `layoutRubyBase_addChildNoBlockChildren`: Adding a table-cell inside a ruby base inlinifies the table cell to inline-table and does not create an anonymous block around prior text per CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1.
  - `layoutRubyBase_addImageNoBlockChildren`: Adding an image caption inside a ruby base inlinifies it to an inline box without creating an anonymous block around prior text per CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1.
  - `layoutRubyBase_addSpecialWithTableInternalDisplayNoBlockChildren`: Adding a table column element inside a ruby base keeps it inline-level without anonymous block wrapping per CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1.
  - `layoutRubyBase_changeToRubyNoBlockChildren`: Changing container display to ruby inlinifies block children into inline boxes per CSS Ruby 1 §2.1.
  - `layoutRubyAsBlock_textCombineCrash`: Ruby block in vertical-rl mode with text-combine-upright:all wraps text in LayoutTextCombine without crash per CSS Writing Modes 3 §5.1 & CSS Ruby 1 §2.1.
  - `layoutInlineListItem_getOffsetMappingNoCrash`: Inline list item generates an inline box participating in the inline formatting context per CSS Lists 3 §2.1.
  - `layoutInlineListItem_offsetMappingBuilderNoCrash`: Dynamic counter style rule changes maintain inline formatting context participation for inline list items per CSS Lists 3 §2.1.
  - `layoutListItem_findSymbolMarkerLayoutTextWithTextCombine`: Extracting symbol marker text traverses through LayoutTextCombine wrappers per CSS Lists 3 §3 & CSS Writing Modes 3 §5.1.
  - `layoutFieldset_addChildWhitespaceCrash`: Removing whitespace between fieldset content and legend preserves the fieldset child partition per HTML 5.2 §4.10.16 & CSS 2.1 §9.2.1.1.
  - `layoutFieldset_addChildAnonymousInlineCrash`: Removing anonymous inline whitespace before a legend preserves rendered legend and content box partition per HTML 5.2 §4.10.16 & CSS 2.1 §9.2.1.1.
  - `lineInfo_trailingSpaceWidthInitialEmptyItem`: Trailing space following a zero-length control item (CR) hangs under pre-wrap with zero available width per CSS Text 3 §4.1.2 & §5.4.
  - `lineBreaker_wideContentInRuby`: Wide atomic inlines in a ruby base accommodate total content size without overflow during column sizing per CSS Ruby 1 §4.
  - `lineBreaker_overflowingContinuationRuby`: Overflowing ruby continuation annotations expand column min-content size per CSS Ruby 1 §4.
  - `lineBreaker_overflowingContinuationRuby2`: Vertical ruby column with atomic inline base and wide annotation establishes column size per CSS Ruby 1 §4.
  - `lineBreaker_minMaxWithAtomicInlineInRuby`: Ruby column min size with atomic inline base is bounded by base width per CSS Ruby 1 §4.
  - `lineBreaker_minMaxWithEmptyRubyBase`: Empty ruby base takes column min size directly from annotation per CSS Ruby 1 §4.
  - `inlineNode_nestedRubyMinMaxCrash`: Nested ruby column intrinsic sizing feeds inner column min/max sizes into outer column per CSS Ruby 1 §4.
  - `justificationUtils_setupItemJustificationOpportunityCrash`: Ruby annotations and non-text atomic inlines do not receive justification expansion opportunities per CSS Text 3 §7.3 & CSS Ruby 1 §3.
  - `svgText_positionOnPathCrash`: Characters laid out along a text path advance within path bounds and apply textLength adjustments per SVG 2 §11.3.3 & §11.4.
  - `svgText_emptyTextLengthCrash`: Empty textPath element with textLength specified produces zero advance and default scale 1 per SVG 2 §11.4.
  - `svgText_emptyTextLengthSpacingAndGlyphsCrash`: Non-rendered zero-width characters under spacingAndGlyphs avoid division by zero per SVG 2 §11.4.
  - `svgText_hugeScaleCrash`: Excessive SVG scale factors on text are clamped to finite layout bounds per SVG 2 §7.3 & CSS Transforms 1 §5.
  - `svgText_controlCharCrash`: Control character (form feed) in SVG text produces matching spacing adjustment per SVG 2 §11.1 & CSS Text 3 §4.1.
  - `svgText_firstLineTextTransformCrash`: German eszett transforms to uppercase "SS" under ::first-line text-transform per SVG 2 §11.1 & CSS Text 3 §2.1.
  - `svgText_textPathCrash`: Nested textPath inside another textPath element is disallowed by SVG structure rules per SVG 2 §11.3.3.
  - `lineBreaker_splitTextIntoSegementsCrash`: Combining characters at start of SVG text segments partition correctly across explicit positions per SVG 2 §11.4 & Unicode Standard §3.6.
  - `inlineNode_findSvgTextChunksCrash1`: Explicit x coordinates partition SVG text elements into independent text chunks per SVG 2 §11.2 & Unicode UAX #9.
  - `inlineNode_findSvgTextChunksCrash2`: Preserved whitespace maintains SVG text chunk partitioning per SVG 2 §11.2 & Unicode UAX #9.
  - `inlineNode_findSvgTextChunksCrash3`: SVG text chunks containing surrogate pairs partition safely without crash per SVG 2 §11.2 & Unicode Standard §3.8.
  - `lineBreaker_tableCellWidthCalculationQuirkOutOfFlow`: Out-of-flow positioned elements contribute 0 to normal flow inline min/max sizes per CSS 2.1 §9.3 & Quirks Mode.
  - `lineBreaker_boxDecorationBreakCloneWithoutBoxDecorations`: BoxDecorationBreak clone preserves empty struts across fragments per CSS Box Decoration 3 §4.2.
  - `lineBreaker_rewindPositionedFloat`: Float width clamping prevents integer overflow during float rewinding per CSS 2.1 §9.5.
  - `lineBreaker_rewindRubyColumn`: Ruby column rewinding when column width exceeds available width per CSS Ruby 1 §3.
  - `lineBreaker_getOverhangCrash`: Ruby annotation overhang with negative margins bounded below by 0 per CSS Ruby 1 §4.2.
  - `lineBreaker_setInputRange`: Slicing line breaker input range restricts layout to sub-range items per CSS Text 3 §5.
  - `lineBreaker_createSubLineInfoAvailableWidth`: Sub-linebreaker available width under nowrap is unaffected by sibling floats per CSS Ruby 1 §3.
  - `lineBreaker_removeTrailingCollapsibleSpace`: Safe spacing per opportunity guards against division by zero per CSS Text 3 §7.
  - `lineBreaker_splitTrailingBidiCrCrash`: Trailing carriage return in white-space: pre acts as mandatory line break per CSS Text 3 §4.1.
  - `inlineNode_addChildToSVGRoot`: Adding children to an SVG root does not mutate parent HTML IFC per SVG 2 §11 & CSS 2.1 §9.4.2.
  - `inlineCaretPosition_beforeOrAfterInlineAreaElement`: Caret position for unrendered element without layout object returns none per HTML 5.2 §4.8.12.
  - `inlineCursor_culledInlineWithNonIFCChild`: Culled inline without decorations wrapping ruby generates no box fragment per CSS 2.1 §9.2.1.
  - `inlineLayoutAlgorithm_textFitDivisionByZero`: Text fit scale factor defaults safely when content width is 0 per CSS Inline 3 §Text Fit.
  - `inlineLayoutAlgorithm_boxFragmentInRubyCrash`: First base item in open ruby column creates valid box fragment per CSS Ruby 1 §3.
  - `inlineLayoutAlgorithm_bidiControlsInLineClampedLines`: Bidi controls following line-clamp ellipsis have zero layout advance per CSS Overflow 3 & CSS Text 3.
  - `layoutTextFragment_setTextWithFirstLetter`: Non-empty text nodes create layout text fragments after DOM mutation per CSS Pseudo 4 §2.2.
  - `layoutTextFragment_splitTextWithZero`: First-letter selection is preserved across leading empty text nodes per CSS Pseudo 4 §2.2.
  - `inlineCursor_culledInlineBlockInInlineOverflow`: Traversing culled inline spanning columns visits fragmented block-in-inline children without looping per CSS Fragmentation 3 & CSS 2.1 §9.2.1.
  - `layoutInline_simpleContinuation`: Inline containing block child splits into continuations with anonymous block-in-inline wrapper per CSS 2.1 §9.2.1.1.
  - `layoutInline_blockInInlineRemove`: Removing block child from continuation leaves only inline children with no anonymous wrapper per CSS 2.1 §9.2.1.1.
  - `inlineNode_reuseFirstNonSafe`: Cross-boundary kerning ("AV") marks boundary text item not safe to reuse from shape cache per CSS Text 3 §3.
  - `inlineNode_reuseFirstNonSafeRtl`: Cross-boundary kerning in RTL text marks boundary item not safe to reuse per CSS Text 3 §3.
  - `inlineNode_shouldNotResueLigature`: Cross-boundary ligature formation ("fi") prevents independent shape cache reuse per CSS Text 3 §3.
  - `layoutSvgForeignObject_getBBoxUseCounterForZeroHeight`: 1D degenerate bounding box (100x0) triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgForeignObject_getBBoxUseCounterForZeroWidth`: 1D degenerate bounding box (0x100) triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgForeignObject_getBBoxUseCounterForZeroWidthAndHeight`: 0x0 bounding box does not trigger 1D degenerate getBBox use counter per SVG 2 §13.2.
  - `layoutSvgForeignObject_getBBoxUseCounterForNonZeroWidthAndHeight`: Non-zero 2D box (100x100) does not trigger degenerate getBBox use counter per SVG 2 §13.2.
  - `layoutSvgImage_getBBoxUseCounterForZeroHeight`: Image with 100x0 bbox triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgImage_getBBoxUseCounterForZeroWidth`: Image with 0x100 bbox triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgImage_getBBoxUseCounterForZeroWidthAndHeight`: Image with 0x0 bbox does not trigger use counter per SVG 2 §13.2.
  - `layoutSvgImage_getBBoxUseCounterForNonZeroWidthAndHeight`: Image with 100x100 bbox does not trigger use counter per SVG 2 §13.2.
  - `layoutSvgRect_getBBoxUseCounterForZeroHeight`: Rect with 100x0 bbox triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgRect_getBBoxUseCounterForZeroWidth`: Rect with 0x100 bbox triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgRect_getBBoxUseCounterForZeroWidthAndHeight`: Rect with 0x0 bbox does not trigger use counter per SVG 2 §13.2.
  - `layoutSvgRect_getBBoxUseCounterForNonZeroWidthAndHeight`: Rect with 100x100 bbox does not trigger use counter per SVG 2 §13.2.
  - `layoutSvgViewportContainer_getBBoxUseCounterForZeroHeight`: Container with 100x0 bbox triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgViewportContainer_getBBoxUseCounterForZeroWidth`: Container with 0x100 bbox triggers getBBox use counter per SVG 2 §13.2.
  - `layoutSvgViewportContainer_getBBoxUseCounterForZeroWidthAndHeight`: Container with 0x0 bbox does not trigger use counter per SVG 2 §13.2.
  - `layoutSvgViewportContainer_getBBoxUseCounterForNonZeroWidthAndHeight`: Container with 100x100 bbox does not trigger use counter per SVG 2 §13.2.
  - `hitTesting_occlusionHitTestSVGTextWithFilterCrash`: Filtered SVG text visual overflow intersects target, returning occluder text node per CSS Filters 1 §3.1 & SVG 2 §15.2.

done: TestsInline_LayoutInline, TestsInline_ScoreLineBreaker, TestsInline_FragmentItem, TestsInline_InlineCursor +10
- Formalized 10 tests across layout inline outline overflow, text-wrap telemetry, multicol line fragment IDs, and fragmentainer cursor traversal:
  - `layoutInline_visualOverflowRecalcLegacyLayout`: Inline box visual overflow expands by 50px outline and restores on removal per CSS 2.1 §18.4 & CSS UI 3 §3.1.
  - `layoutInline_visualOverflowRecalcLayoutNG`: LayoutNG inline box visual overflow with 50px outline per CSS 2.1 §18.4 & CSS UI 3 §3.1.
  - `layoutInline_visualOverflowRecalcLegacyLayoutPositionRelative`: Relative-positioned inline box visual overflow with 50px outline per CSS 2.1 §18.4 & CSS UI 3 §3.1.
  - `scoreLineBreaker_useCountNotCountedForWrap`: Default text-wrap: wrap does not trigger balance or pretty use counters per CSS Text 4 §7.1.
  - `scoreLineBreaker_useCountNotCountedForBalance`: text-wrap: balance triggers kTextWrapBalance use counter per CSS Text 4 §7.1.
  - `fragmentItem_lineFragmentId`: Line box fragments in fragmented flow receive sequential fragment IDs starting from initialLineFragmentId (0x80000000) per CSS Fragmentation 3 §3.
  - `fragmentItem_selfPaintingInlineBox`: Fractional opacity (< 1.0) establishes self-painting layer and stacking context per CSS Color 3 §3.2 & CSS 2.1 Appendix E.
  - `inlineCursor_cursorForMovingAcrossFragmentainer`: Multi-column IFC is block-fragmented across fragmentainers per CSS Fragmentation 3 §3.
  - `inlineCursor_nextIncludingFragmentainer`: Forward cursor traversal across column fragmentainers visits items in visual reading order per CSS Fragmentation 3 §3.
  - `inlineCursor_previousIncludingFragmentainer`: Backward cursor traversal across column fragmentainers visits items in exact reverse order per CSS Fragmentation 3 §3.




















