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



