# Chromium Layout Lane Manifest — Inline

## Scope and Ordering
Test files in lane "inline" under `third_party/blink/renderer/core/layout/`:
1. `inline/line_breaker_test.cc`
2. `inline/inline_node_test.cc`
3. (remaining 20 test files in `inline/`)
4. `inline_layout_test.cc`
5. `layout_inline_test.cc`
6. `layout_text_test.cc`
7. `layout_text_fragment_test.cc`
8. `layout_br_test.cc`
9. `layout_text_combine_test.cc`
10. `layout_ruby_base_test.cc`
11. `layout_ruby_as_block_test.cc`
12. `list/`
13. `geometry/`

---

## Test Inventory and Status

### `inline/line_breaker_test.cc`

| File:Line | Test Name | Class | Status | Theorem / Vector | Notes |
|---|---|---|---|---|---|
| inline/line_breaker_test.cc:144 | FitWithEpsilon | geometry | formalized | `lineBreaker_fitWithEpsilon_pass` | 50px text fits container with 1-epsilon tolerance in 1 line |
| inline/line_breaker_test.cc:171 | SingleNode | geometry | formalized | `lineBreaker_singleNode_pass` | Greedily breaks 123 456 789 at 80px (2 lines) and 60px (3 lines) with trailing space collapse |
| inline/line_breaker_test.cc:197 | TextCombineCloseTag | geometry | blocked | - | Blink treats text-combine as unbreakable 1 line; model splits at AtomicInline (producing 3 lines) |
| inline/line_breaker_test.cc:223 | TextCombineBreak | geometry | blocked | - | Text-combine hyphen break depends on internal vertical-lr/tcy shaping |
| inline/line_breaker_test.cc:241 | TextCombineNoBreak | geometry | blocked | - | Blink keeps unbreakable text-combine on 1 line; model splits at AtomicInline (producing 3 lines) |
| inline/line_breaker_test.cc:258 | TextCombineNoBreakWithSpace | geometry | blocked | - | Space inside text-combine ignored in Blink; model treats space as break opportunity |
| inline/line_breaker_test.cc:275 | OverflowWord | geometry | partly formalized | `lineBreaker_overflowWord_pass` | Formalized width 40 (2 lines); width 20 blocked (model produces 3 lines due to space item on its own line; Blink collapses leading space producing 2 lines) |
| inline/line_breaker_test.cc:301 | OverflowTab | geometry | formalized | `lineBreaker_overflowTab_pass` | Tab characters expand to tab stops without breaking |
| inline/line_breaker_test.cc:323 | OverflowTabBreakWord | geometry | formalized | `lineBreaker_overflowTab_pass` | Tab characters do not break under word-wrap: break-word |
| inline/line_breaker_test.cc:346 | OverflowAtomicInline | geometry | formalized | `lineBreaker_overflowAtomic_pass` | Atomic inline wrapping at boundaries across widths 80, 70, 40, 20 |
| inline/line_breaker_test.cc:387 | OverflowMargin | geometry | blocked | - | Blink looks ahead at closing tag margins and wraps to line 2 (3 lines); model takeLineAux consumes word on line 1 and CloseTag on line 2 (2 lines) |
| inline/line_breaker_test.cc:423 | OverflowAfterSpacesAcrossElements | geometry | formalized | `lineBreaker_overflowAfterSpaces_pass` | Trailing spaces across element boundaries collapse at line end |
| inline/line_breaker_test.cc:447 | WrapLastWord | geometry | formalized | `lineBreaker_wrapLastWord_pass` | Wrap last word before inline span preserves subsequent items on next line |
| inline/line_breaker_test.cc:466 | WrapLetterSpacing | geometry | formalized | `lineBreaker_wrapLetterSpacing_pass` | Letter-spacing increases shaped segment advance width |
| inline/line_breaker_test.cc:486 | BoundaryInWord | geometry | blocked | - | Blink forbids breaking inside a word across span boundaries (3 lines); model takeLineAux does not check canBreakAfter (2 lines) |
| inline/line_breaker_test.cc:516 | BoundaryInFirstWord | geometry | partly formalized | `lineBreaker_boundaryInFirstWord_pass` | Formalized width 80 (2 lines); width 50/20 blocked (model takeLineAux does not check canBreakAfter on first word) |
| inline/line_breaker_test.cc:548 | IdeographicTrailingSpaces | geometry | formalized | `lineBreaker_ideographicTrailingSpaces_pass` | Ideographic spaces (U+3000) are preserved as non-collapsible text |
| inline/line_breaker_test.cc:624 | WhitespaceStateTest.WhitespaceState | behaviour | formalized | `lineBreaker_whitespaceState_none, lineBreaker_whitespaceState_collapsed, lineBreaker_whitespaceState_preserved, lineBreaker_whitespaceState_leading` | WhitespaceState classification (kNone, kCollapsed, kPreserved, kLeading) |
| inline/line_breaker_test.cc:684 | TrailingSpaceWidthTest.TrailingSpaceWidth | geometry | formalized | `lineBreaker_trailingSpaceWidth_pass` | Hanging space width calculation in pre-wrap |
| inline/line_breaker_test.cc:706 | FullyCollapsedSpaces | internal | internal | - | Asserts NeedsLayout flag clearing during layout lifecycle |
| inline/line_breaker_test.cc:732 | TrailingCollapsedSpaces | internal | internal | - | Asserts NeedsLayout flag clearing during layout lifecycle |
| inline/line_breaker_test.cc:762 | SplitTextZero | behaviour | formalized | `lineBreaker_splitTextZero_pass` | DOM splitText(0) zero-length node does not affect line breaking output |
| inline/line_breaker_test.cc:789 | ForcedBreakFollowedByCloseTag | geometry | blocked | - | Blink elides trailing empty lines created by CloseTag after ForcedBreak (1 line); model creates trailing line for CloseTag (2 lines) |
| inline/line_breaker_test.cc:821 | TableCellWidthCalculationQuirkOutOfFlow | internal | internal | - | Checks no DCHECK in quirks mode with out-of-flow child |
| inline/line_breaker_test.cc:842 | BoxDecorationBreakCloneWithoutBoxDecorations | internal | internal | - | Checks no DCHECK with -webkit-box-decoration-break: clone |
| inline/line_breaker_test.cc:849 | RewindPositionedFloat | internal | internal | - | Regression test for float rewinding with large border |
| inline/line_breaker_test.cc:864 | RewindRubyColumn | internal | internal | - | Regression test for ruby column rewinding |
| inline/line_breaker_test.cc:887 | SplitTextIntoSegements | behaviour | formalized | `lineBreaker_splitTextIntoSegments_conservation` | Advance width splitting preserves shaped segment length |
| inline/line_breaker_test.cc:913 | SplitTextIntoSegementsCrash | internal | internal | - | Crash regression test for SVG combining characters |
| inline/line_breaker_test.cc:940 | GetOverhangCrash | internal | internal | - | Crash regression test for ruby overhang |
| inline/line_breaker_test.cc:965 | IdeographicSpaceBeforeEndBracket | geometry | formalized | `lineBreaker_ideographicBeforeBracket_pass` | Ideographic space followed by closing bracket breaks at prior break opportunity |
| inline/line_breaker_test.cc:1002 | BreakAt | geometry | formalized | `lineBreaker_breakAt_pass` | Explicit breakpoints partition line widths (10, 40, 10, 30) |
| inline/line_breaker_test.cc:1044 | BreakAtTrailingSpaces | geometry | formalized | `lineBreaker_breakAt_pass` | Breakpoints with trailing spaces (40, 20) |
| inline/line_breaker_test.cc:1079 | BreakAtTrailingSpacesAfterAtomicInline | geometry | formalized | `lineBreaker_breakAt_pass` | Breakpoints with atomic inlines (10, 20) |
| inline/line_breaker_test.cc:1117 | WideContentInRuby | internal | internal | - | Crash regression test for ruby wider than LayoutUnit::Max() |
| inline/line_breaker_test.cc:1144 | SetInputRange | internal | internal | - | Unit test for internal C++ helper LineBreaker::SetInputRange |
| inline/line_breaker_test.cc:1169 | CreateSubLineInfoAvailableWidth | internal | internal | - | Regression test for sub-linebreaker float handling in ruby |
| inline/line_breaker_test.cc:1193 | OverflowingContinuationRuby | internal | internal | - | Crash regression test for ruby continuation |
| inline/line_breaker_test.cc:1208 | OverflowingContinuationRuby2 | internal | internal | - | Crash regression test for ruby continuation |
| inline/line_breaker_test.cc:1220 | MinMaxWithAtomicInlineInRuby | internal | internal | - | Crash regression test for atomic inline in ruby |
| inline/line_breaker_test.cc:1229 | RemoveTrailingCollapsibleSpace | internal | internal | - | Crash regression test (division by zero) |
| inline/line_breaker_test.cc:1241 | MinMaxWithEmptyRubyBase | internal | internal | - | Crash regression test for empty ruby base |
| inline/line_breaker_test.cc:1288 | CanBreakInsideTest.Data | behaviour | formalized | `lineBreaker_canBreakInside_single, lineBreaker_canBreakInside_space, lineBreaker_canBreakInside_nowrap, lineBreaker_canBreakInside_atomicPair, lineBreaker_canBreakInside_wordAtomic, lineBreaker_canBreakInside_singleAtomic` | CanBreakInside predicate across whitespace, nowrap, and atomic inlines |
| inline/line_breaker_test.cc:1323 | SplitTrailingBidiCrCrash | internal | internal | - | Crash regression test for CR in RTL bidi |
| inline/line_breaker_test.cc:1331 | BidiControlEnterFlag | geometry | formalized | `lineBreaker_bidiControlEnter_pass` | Container line height matches single line font height (10px) |

### `inline/inline_node_test.cc`

| File:Line | Test Name | Class | Status | Theorem / Vector | Notes |
|---|---|---|---|---|---|
| inline/inline_node_test.cc:192 | CollectInlinesText | geometry | formalized | `inlineNode_collectText_pass` | Collects 5 items (Text, OpenTag, Text, CloseTag, Text) |
| inline/inline_node_test.cc:206 | CollectInlinesBR | geometry | formalized | `inlineNode_collectBR_pass` | Collects 3 items (Text, ForcedBreak, Text) |
| inline/inline_node_test.cc:245 | ShareInlineTextContentSingleSource | internal | internal | - | String sharing optimization for single Text node |
| inline/inline_node_test.cc:256 | ShareInlineTextContentLargeNotSharedWhenCollapsed | internal | internal | - | String sharing optimization with whitespace collapse |
| inline/inline_node_test.cc:274 | ShareInlineTextContentLargeNotSharedSameLength | internal | internal | - | String sharing optimization |
| inline/inline_node_test.cc:284 | CollectInlinesFloat | behaviour | internal | - | Float items in inline formatting context |
| inline/inline_node_test.cc:306 | CollectInlinesInlineBlock | geometry | formalized | `inlineNode_collectInlineBlock_pass` | Collects 3 items with AtomicInline for inline-block |
| inline/inline_node_test.cc:322 | CollectInlinesUTF16 | geometry | internal | - | UTF-16 surrogate pairs in inline items |
| inline/inline_node_test.cc:331 | CollectInlinesMaybeRtl | behaviour | internal | - | LTR text does not enable bidi |
| inline/inline_node_test.cc:344 | CollectInlinesRtl | behaviour | internal | - | RTL text sets bidi enabled |
| inline/inline_node_test.cc:353 | CollectInlinesRtlWithSpan | behaviour | internal | - | RTL inside span enables bidi |
| inline/inline_node_test.cc:369 | CollectInlinesMixedText | behaviour | internal | - | Mixed LTR/RTL text |
| inline/inline_node_test.cc:385 | CollectInlinesMixedTextEndWithON | behaviour | internal | - | Bidi neutral character resolution |
| inline/inline_node_test.cc:402 | CollectInlinesTextCombineBR | geometry | internal | - | Text combine with BR |
| inline/inline_node_test.cc:418 | CollectInlinesTextCombineListItemMarker | geometry | internal | - | Text combine list marker |
| inline/inline_node_test.cc:438 | CollectInlinesTextCombineNewline | geometry | internal | - | Text combine newline |
| inline/inline_node_test.cc:453 | CollectInlinesTextCombineWBR | geometry | internal | - | Text combine WBR |
| inline/inline_node_test.cc:468 | SegmentASCII | behaviour | internal | - | ASCII run segmentation |
| inline/inline_node_test.cc:477 | SegmentHebrew | behaviour | internal | - | Hebrew run segmentation |
| inline/inline_node_test.cc:487 | SegmentSplit1To2 | behaviour | internal | - | Mixed script segmentation |
| inline/inline_node_test.cc:497 | SegmentSplit3To4 | behaviour | internal | - | Script run splitting |
| inline/inline_node_test.cc:511 | SegmentBidiOverride | behaviour | internal | - | Bidi-override segmentation |
| inline/inline_node_test.cc:541 | SegmentBidiIsolate | behaviour | internal | - | Bidi-isolate segmentation |
| inline/inline_node_test.cc:649 | MinMaxTest.Data | geometry | formalized | `inlineNode_minMax_pass` | ComputeMinMaxSizes (min size = longest word, max size = sum of all words/spaces) |
| inline/inline_node_test.cc:675 | MinMaxSizesSaturated | geometry | formalized | `inlineNode_minMaxSaturated_pass` | MinMax sizes saturate at kLayoutUnitMax 33554431 |
| inline/inline_node_test.cc:698 | MinMaxSizesNeedsLayout | internal | internal | - | NeedsLayout flag on DOM text change |
| inline/inline_node_test.cc:716 | AssociatedItemsWithControlItem | internal | internal | - | Visual bidi ordering item association |
| inline/inline_node_test.cc:734 | NeedsCollectInlinesOnSetText | behaviour | formalized | `inlineNode_invalidation_rule` | DOM setData marks NeedsCollectInlines up to container |
| inline/inline_node_test.cc:767 | SetTextWithOffsetWithTextTransform | internal | internal | - | Crash regression in OffsetMapping |
| inline/inline_node_test.cc:838 | StyleChangeTest.NeedsCollectInlinesOnStyle | behaviour | formalized | `inlineNode_invalidation_rule` | Font/display change marks NeedsCollectInlines |
| inline/inline_node_test.cc:927 | NodeInsertTest.NeedsCollectInlinesOnInsert | behaviour | formalized | `inlineNode_invalidation_rule` | Inserting child marks NeedsCollectInlines up to container |
| inline/inline_node_test.cc:960 | NeedsCollectInlinesOnInsertToOutOfFlowButton | internal | internal | - | Out of flow button insert |
| inline/inline_node_test.cc:987 | NodeRemoveTest.NeedsCollectInlinesOnRemove | behaviour | formalized | `inlineNode_invalidation_rule` | Removing child marks NeedsCollectInlines up to container |
| inline/inline_node_test.cc:1034 | CollectInlinesShouldNotClearFirstInlineFragment | internal | internal | - | FirstInlineFragment preservation |
| inline/inline_node_test.cc:1058 | SegmentBidiChangeSetsNeedsLayout | internal | internal | - | Bidi level change sets NeedsLayout |
| inline/inline_node_test.cc:1082 | InvalidateAddSpan | behaviour | internal | - | Adding span adds OpenTag/CloseTag items |
| inline/inline_node_test.cc:1097 | InvalidateRemoveSpan | behaviour | internal | - | Removing span sets NeedsCollectInlines |
| inline/inline_node_test.cc:1107 | InvalidateAddInnerSpan | behaviour | internal | - | Adding inner span adds items |
| inline/inline_node_test.cc:1123 | InvalidateRemoveInnerSpan | behaviour | internal | - | Removing inner span sets NeedsCollectInlines |
| inline/inline_node_test.cc:1133 | InvalidateSetText | behaviour | internal | - | SetTextIfNeeded marks NeedsCollectInlines |
| inline/inline_node_test.cc:1142 | InvalidateAddAbsolute | behaviour | internal | - | Adding absolute child adds OOF item |
| inline/inline_node_test.cc:1159 | InvalidateRemoveAbsolute | behaviour | internal | - | Removing absolute child sets NeedsCollectInlines |
| inline/inline_node_test.cc:1171 | InvalidateChangeToAbsolute | behaviour | internal | - | Changing to position:absolute replaces span items with OOF |
| inline/inline_node_test.cc:1189 | InvalidateChangeFromAbsolute | behaviour | internal | - | Changing from absolute replaces OOF with span items |
| inline/inline_node_test.cc:1207 | InvalidateAddFloat | behaviour | internal | - | Adding float child adds float item |
| inline/inline_node_test.cc:1224 | InvalidateRemoveFloat | behaviour | internal | - | Removing float child sets NeedsCollectInlines |
| inline/inline_node_test.cc:1236 | SpaceRestoredByInsertingWord | behaviour | internal | - | Inserting word between collapsed spaces restores space |
| inline/inline_node_test.cc:1251 | RemoveInlineNodeDataIfBlockBecomesEmpty1 | internal | internal | - | Clearing InlineNodeData when container becomes empty |
| inline/inline_node_test.cc:1262 | RemoveInlineNodeDataIfBlockBecomesEmpty2 | internal | internal | - | Clearing InlineNodeData on innerHTML="" |
| inline/inline_node_test.cc:1272 | RemoveInlineNodeDataIfBlockObtainsBlockChild | internal | internal | - | Clearing InlineNodeData when block child added |
| inline/inline_node_test.cc:1285 | ClearFirstInlineFragmentOnSplitFlow | internal | internal | - | SplitFlow layout tree mutation |
| inline/inline_node_test.cc:1336 | AddChildToSVGRoot | internal | internal | - | SVG text root element traversal |
| inline/inline_node_test.cc:1353 | PreservedNewlineWithBidiAndRelayout | behaviour | internal | - | Bidi isolate characters around \n |
| inline/inline_node_test.cc:1367 | PreservedNewlineWithRemovedBidiAndRelayout | behaviour | internal | - | Removing dir attribute removes bidi characters |
| inline/inline_node_test.cc:1379 | PreservedNewlineWithRemovedLtrDirAndRelayout | behaviour | internal | - | Removing dir=ltr attribute removes bidi characters |
| inline/inline_node_test.cc:1392 | InsertedWBRWithLineBreakInRelayout | geometry | internal | - | wbr causes \n to collapse to zero-width space |
| inline/inline_node_test.cc:1405 | CollapsibleSpaceFollowingBRWithNoWrapStyle | geometry | internal | - | Collapsible space after br collapses to empty |
| inline/inline_node_test.cc:1414 | CollapsibleSpaceFollowingNewlineWithPreStyle | geometry | internal | - | Collapsible space after newline in pre collapses |
| inline/inline_node_test.cc:1425 | RemoveSegmentBreakFromJapaneseInRelayout | internal | internal | - | Disabled under SEGMENT_BREAK_TRANSFORMATION_FOR_EAST_ASIAN_WIDTH=0 |
| inline/inline_node_test.cc:1442 | RemoveSegmentBreakFromJapaneseInRelayout2 | internal | internal | - | Disabled under SEGMENT_BREAK_TRANSFORMATION_FOR_EAST_ASIAN_WIDTH=0 |
| inline/inline_node_test.cc:1459 | SegmentRanges | behaviour | internal | - | Segment offset range slicing |
| inline/inline_node_test.cc:1504 | ReusingWithPreservedCase1 | behaviour | internal | - | Text content after removing br with pre-wrap |
| inline/inline_node_test.cc:1518 | ReusingWithPreservedCase2 | behaviour | internal | - | Text content after removing br in pre-wrap container |
| inline/inline_node_test.cc:1532 | ReusingWithPreservedCase3 | behaviour | internal | - | Text content with multiple pre-wrap spaces |
| inline/inline_node_test.cc:1550 | ReusingWithCollapsed | behaviour | internal | - | Removing br with float preserves single space |
| inline/inline_node_test.cc:1564 | ReusingRTLAsLTR | behaviour | internal | - | Removing dir=rtl attribute updates items from 8 to 3 |
| inline/inline_node_test.cc:1590 | ReuseFirstNonSafe | internal | internal | - | Shape cache safe-to-reuse flag |
| inline/inline_node_test.cc:1617 | ReuseFirstNonSafeRtl | internal | internal | - | Shape cache safe-to-reuse flag in RTL |
| inline/inline_node_test.cc:1643 | ShouldNotResueLigature | internal | internal | - | Ligature shaping cache invalidation |
| inline/inline_node_test.cc:1671 | InitialLetter | geometry | internal | - | Initial letter box fragment and kInitialLetterBox item |
| inline/inline_node_test.cc:1692 | TextCombineUsesScalingX | geometry | internal | - | Text combine > 1 char uses scaleX |
| inline/inline_node_test.cc:1713 | TextCombineWordSpacing | geometry | formalized | `inlineNode_textCombine_zeroes_spacing` | Text combine zeroes word-spacing and letter-spacing |
| inline/inline_node_test.cc:1733 | FindSvgTextChunksCrash1 | internal | internal | - | Crash regression test for SVG text chunks |
| inline/inline_node_test.cc:1749 | FindSvgTextChunksCrash2 | internal | internal | - | Crash regression test for SVG text chunks |
| inline/inline_node_test.cc:1765 | FindSvgTextChunksCrash3 | internal | internal | - | Crash regression test for surrogate pairs |
| inline/inline_node_test.cc:1786 | NestedRubyMinMaxCrash | internal | internal | - | Crash regression for nested ruby min/max |
| inline/fragment_item_test.cc:67 | CopyMove | internal | internal | - | Copy and move constructors of FragmentItem |
| inline/fragment_item_test.cc:126 | BasicText | geometry | formalized | `fragmentItem_basicText_vector` | Text node wrapping into 2 line fragments |
| inline/fragment_item_test.cc:173 | RtlText | geometry | formalized | `fragmentItem_rtlText_vector` | BiDi reordering in RTL container |
| inline/fragment_item_test.cc:235 | BasicInlineBox | geometry | formalized | `fragmentItem_basicInlineBox_vector` | Inline box fragmentation and ink overflow |
| inline/fragment_item_test.cc:291 | CulledInlineBox | geometry | formalized | `fragmentItem_culledInlineBox_vector` | Culled inline bounding box aggregation |
| inline/fragment_item_test.cc:328 | SelfPaintingInlineBox | behaviour | internal | - | Invalidation and visual overflow recalc on self-painting layer |
| inline/fragment_item_test.cc:357 | StartOffsetInContainer | geometry | formalized | `fragmentItem_startOffsetInContainer_vector` | Soft hyphen generated text container offsets |
| inline/fragment_item_test.cc:383 | EllipsizedAtomicInline | behaviour | formalized | `fragmentItem_ellipsizedAtomicInline_rule` | Atomic inline ellipsization marks isLastForNode |
| inline/fragment_item_test.cc:417 | LineFragmentId | behaviour | internal | - | Multicol column line fragment ID tagging |
| inline/fragment_item_test.cc:451 | Outline | geometry | formalized | `fragmentItem_outline_vector` | Outline rect computation for inline box and inline block |
| inline/fragment_item_test.cc:526 | MarkLineBoxesDirtyOnInsert | behaviour | internal | - | Incremental layout dirty line index tracking on insert |
| inline/fragment_item_test.cc:543 | MarkLineBoxesDirtyOnAppend | behaviour | internal | - | Dirty line index tracking on append |
| inline/fragment_item_test.cc:560 | MarkLineBoxesDirtyOnAppend2 | behaviour | internal | - | Dirty line index tracking on append to second line |
| inline/fragment_item_test.cc:578 | MarkLineBoxesDirtyOnAppendAfterBR | behaviour | internal | - | Dirty line index tracking on append after br |
| inline/fragment_item_test.cc:596 | MarkLineBoxesDirtyOnRemove | behaviour | internal | - | Dirty line index tracking on remove child |
| inline/fragment_item_test.cc:609 | MarkLineBoxesDirtyOnRemoveFirst | behaviour | internal | - | Dirty line index tracking on remove first child |
| inline/fragment_item_test.cc:624 | MarkLineBoxesDirtyOnRemove2 | behaviour | internal | - | Dirty line index tracking on remove second child |
| inline/fragment_item_test.cc:638 | MarkLineBoxesDirtyOnRemoveAfterBR | behaviour | internal | - | Dirty line index tracking on remove after br |
| inline/fragment_item_test.cc:654 | MarkLineBoxesDirtyOnEndSpaceCollapsed | behaviour | internal | - | Dirty line index tracking when end space collapsed |
| inline/fragment_item_test.cc:685 | MarkLineBoxesDirtyOnNeedsLayoutFirst | behaviour | internal | - | Dirty line index tracking on child needs layout |
| inline/fragment_item_test.cc:699 | MarkLineBoxesDirtyOnNeedsLayoutFirstWithBox | behaviour | internal | - | Dirty line index tracking on child with box needs layout |
| inline/fragment_item_test.cc:712 | MarkLineBoxesDirtyOnNeedsLayout | behaviour | internal | - | Dirty line index tracking on needs layout |
| inline/fragment_item_test.cc:727 | MarkLineBoxesDirtyOnNeedsLayoutWithBox | behaviour | internal | - | Dirty line index tracking with box needs layout |
| inline/fragment_item_test.cc:743 | MarkLineBoxesDirtyOnChildOfWrappedBox | behaviour | internal | - | Dirty line index tracking on child of wrapped box |
| inline/fragment_item_test.cc:760 | MarkLineBoxesDirtyInInlineBlock | behaviour | internal | - | Dirty line index tracking in inline block |
| inline/fragment_item_test.cc:773 | MarkLineBoxesDirtyByRemoveChildAfterForcedBreak | behaviour | internal | - | Dirty line index tracking by removing child after forced break |
| inline/fragment_item_test.cc:787 | MarkLineBoxesDirtyByRemoveForcedBreak | behaviour | internal | - | Dirty line index tracking by removing forced break |
| inline/fragment_item_test.cc:801 | MarkLineBoxesDirtyByRemoveSpanWithForcedBreak | behaviour | internal | - | Dirty line index tracking by removing span with forced break |
| inline/fragment_item_test.cc:816 | MarkLineBoxesDirtyByInsertAtStart | behaviour | internal | - | Dirty line index tracking on insert at start |
| inline/fragment_item_test.cc:832 | MarkLineBoxesDirtyByInsertAtLast | behaviour | internal | - | Dirty line index tracking on insert at end |
| inline/fragment_item_test.cc:846 | MarkLineBoxesDirtyByInsertAtMiddle | behaviour | internal | - | Dirty line index tracking on insert in middle |
| inline/fragment_item_test.cc:862 | MarkLineBoxesDirtyByTextSetData | behaviour | internal | - | Dirty line index tracking on Text.data update |
| inline/fragment_item_test.cc:876 | MarkLineBoxesDirtyWrappedLine | behaviour | internal | - | Dirty line index tracking on wrapped line modification |
| inline/fragment_item_test.cc:895 | MarkLineBoxesDirtyInsideInlineBlock | behaviour | internal | - | Dirty line index tracking inside inline block |
| inline/fragment_item_test.cc:910 | Disabled_DebugVisualizers | internal | internal | - | MSVC natvis debugger visualization check |
| inline/fragment_item_test.cc:931 | CaretInlinePositionForOffset_TextFit | geometry | formalized | `fragmentItem_caretPosition_textFit_vector` | Caret position with text-fit: grow font scaling |
| inline/fragment_item_test.cc:952 | IsRubyAnnotationLine | behaviour | formalized | `fragmentItem_isRubyAnnotationLine_rule` | Identifying ruby annotation line vs base line |
| inline/fragment_items_builder_test.cc:23 | MultipleLogicalLineItems | behaviour | formalized | `fragmentItemsBuilder_multipleLines_vector` | FragmentItemsBuilder multi-line assembly and reordering |
| inline/fragment_items_test.cc:20 | DirtyLinesFromNeedsLayoutWithOrthogonalWritingMode | behaviour | internal | - | Regression test for orthogonal writing mode incremental layout |
| inline/fragment_items_test.cc:46 | IsContainerForCulledInline | geometry | formalized | `fragmentItems_isContainerForCulledInline_vector` | Multicolumn fragmentation of culled inline |

---

## Merge Notes
- Shared types in `LayoutTypes.lean` were left untouched.
- `Inhabited LineInfo` was declared locally in `TestsInline_LineBreaker.lean`.
