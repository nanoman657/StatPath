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

