# Chromium Layout Lane Manifest — Inline

## Formalization rule
A row is "formalized" only if ALL hold:
(a) the test's input (its HTML/CSS, viewport and constraints) is written as a value of a model input type, e.g. a box tree or item list;
(b) a GENERAL model function, one that works on any input of that type and does not mention any test, computes the output from that input;
(c) the theorem compares that computed output with the test's EXPECT_* values written as literals on the right-hand side. No model function may branch on test names, test ids, or an enum invented to stand for one test's case. A function whose body is a table of a test's expected numbers is a lookup, not a model.

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

| File:Line | Test Name | Class | Status | Theorem / Vector | Notes |
|---|---|---|---|---|---|
| inline/line_breaker_test.cc:144 | FitWithEpsilon | geometry | formalized | `lineBreaker_fitWithEpsilon` | 50px text fits container with 1-epsilon tolerance in 1 line |
| inline/line_breaker_test.cc:171 | SingleNode | geometry | formalized | `lineBreaker_singleNode` | Greedily breaks 123 456 789 at 80px (2 lines) and 60px (3 lines) with trailing space collapse |
| inline/line_breaker_test.cc:197 | TextCombineCloseTag | geometry | formalized | `lineBreaker_textCombineCloseTag` | CSS Writing Modes 3 §5.1: Text combine white-space: pre does not affect outer wrapping |
| inline/line_breaker_test.cc:223 | TextCombineBreak | geometry | formalized | `lineBreaker_textCombineBreak` | CSS Writing Modes 3 §5.1: Combined hyphen element breaks line after combine |
| inline/line_breaker_test.cc:241 | TextCombineNoBreak | geometry | formalized | `lineBreaker_textCombineNoBreak` | CSS Writing Modes 3 §5.1: Combined alphanumeric word has no break opportunities |
| inline/line_breaker_test.cc:258 | TextCombineNoBreakWithSpace | geometry | formalized | `lineBreaker_textCombineNoBreakWithSpace` | CSS Writing Modes 3 §5.1: Internal space does not permit breaking inside text combine |
| inline/line_breaker_test.cc:275 | OverflowWord | geometry | blocked | - | Blocked: model lacks leading space collapse on second line |
| inline/line_breaker_test.cc:301 | OverflowTab | geometry | formalized | `lineBreaker_overflowTab` | Tab characters expand to tab stops without breaking |
| inline/line_breaker_test.cc:323 | OverflowTabBreakWord | geometry | formalized | `lineBreaker_overflowTab` | Tab characters do not break under word-wrap: break-word |
| inline/line_breaker_test.cc:346 | OverflowAtomicInline | geometry | formalized | `lineBreaker_overflowAtomic` | Atomic inline wrapping at boundaries across widths 80, 70, 40, 20 |
| inline/line_breaker_test.cc:387 | OverflowMargin | geometry | blocked | - | Blocked: model lacks OverflowMargin layout support |
| inline/line_breaker_test.cc:423 | OverflowAfterSpacesAcrossElements | geometry | formalized | `lineBreaker_overflowAfterSpaces` | Trailing spaces across element boundaries collapse at line end |
| inline/line_breaker_test.cc:447 | WrapLastWord | geometry | formalized | `lineBreaker_wrapLastWord` | Wrap last word before inline span preserves subsequent items on next line |
| inline/line_breaker_test.cc:466 | WrapLetterSpacing | geometry | formalized | `lineBreaker_wrapLetterSpacing` | Letter-spacing increases shaped segment advance width |
| inline/line_breaker_test.cc:486 | BoundaryInWord | geometry | blocked | - | Blocked: model lacks BoundaryInWord layout support |
| inline/line_breaker_test.cc:516 | BoundaryInFirstWord | geometry | blocked | - | Blocked: model lacks first-word break prevention |
| inline/line_breaker_test.cc:548 | IdeographicTrailingSpaces | geometry | formalized | `lineBreaker_ideographicTrailingSpaces` | Ideographic spaces (U+3000) are preserved as non-collapsible text |
| inline/line_breaker_test.cc:624 | WhitespaceStateTest.WhitespaceState | behaviour | formalized | `lineBreaker_whitespaceState` | Line breaker trailing whitespace state across line wrapping conditions |
| inline/line_breaker_test.cc:684 | TrailingSpaceWidthTest.TrailingSpaceWidth | geometry | blocked | - | Blocked: model lacks trailing space hanging width computation in LineBreaker |
| inline/line_breaker_test.cc:706 | FullyCollapsedSpaces | internal | internal | - | Asserts NeedsLayout flag clearing during layout lifecycle |
| inline/line_breaker_test.cc:732 | TrailingCollapsedSpaces | internal | internal | - | Asserts NeedsLayout flag clearing during layout lifecycle |
| inline/line_breaker_test.cc:762 | SplitTextZero | behaviour | blocked | - | Blocked: model lacks DOM text node split synchronization |
| inline/line_breaker_test.cc:789 | ForcedBreakFollowedByCloseTag | geometry | blocked | - | Blocked: model lacks ForcedBreakFollowedByCloseTag layout support |
| inline/line_breaker_test.cc:821 | TableCellWidthCalculationQuirkOutOfFlow | internal | internal | - | Checks no DCHECK in quirks mode with out-of-flow child |
| inline/line_breaker_test.cc:842 | BoxDecorationBreakCloneWithoutBoxDecorations | internal | internal | - | Checks no DCHECK with -webkit-box-decoration-break: clone |
| inline/line_breaker_test.cc:849 | RewindPositionedFloat | internal | internal | - | Regression test for float rewinding with large border |
| inline/line_breaker_test.cc:864 | RewindRubyColumn | internal | internal | - | Regression test for ruby column rewinding |
| inline/line_breaker_test.cc:887 | SplitTextIntoSegements | behaviour | formalized | `lineBreaker_splitTextIntoSegments` | Grapheme cluster length segmentation preserving combining marks and surrogate pairs |
| inline/line_breaker_test.cc:913 | SplitTextIntoSegementsCrash | internal | internal | - | Crash regression test for SVG combining characters |
| inline/line_breaker_test.cc:940 | GetOverhangCrash | internal | internal | - | Crash regression test for ruby overhang |
| inline/line_breaker_test.cc:965 | IdeographicSpaceBeforeEndBracket | geometry | formalized | `lineBreaker_ideographicBeforeBracket` | Ideographic space followed by closing bracket breaks at prior break opportunity |
| inline/line_breaker_test.cc:1002 | BreakAt | geometry | formalized | `lineBreaker_breakAt` | Explicit breakpoints partition line widths (10, 40, 10, 30) |
| inline/line_breaker_test.cc:1044 | BreakAtTrailingSpaces | geometry | formalized | `lineBreaker_breakAt` | Breakpoints with trailing spaces (40, 20) |
| inline/line_breaker_test.cc:1079 | BreakAtTrailingSpacesAfterAtomicInline | geometry | formalized | `lineBreaker_breakAt` | Breakpoints with atomic inlines (10, 20) |
| inline/line_breaker_test.cc:1117 | WideContentInRuby | internal | internal | - | Crash regression test for ruby wider than LayoutUnit::Max() |
| inline/line_breaker_test.cc:1144 | SetInputRange | internal | internal | - | Unit test for internal C++ helper LineBreaker::SetInputRange |
| inline/line_breaker_test.cc:1169 | CreateSubLineInfoAvailableWidth | internal | internal | - | Regression test for sub-linebreaker float handling in ruby |
| inline/line_breaker_test.cc:1193 | OverflowingContinuationRuby | internal | internal | - | Crash regression test for ruby continuation |
| inline/line_breaker_test.cc:1208 | OverflowingContinuationRuby2 | internal | internal | - | Crash regression test for ruby continuation |
| inline/line_breaker_test.cc:1220 | MinMaxWithAtomicInlineInRuby | internal | internal | - | Crash regression test for atomic inline in ruby |
| inline/line_breaker_test.cc:1229 | RemoveTrailingCollapsibleSpace | internal | internal | - | Crash regression test (division by zero) |
| inline/line_breaker_test.cc:1241 | MinMaxWithEmptyRubyBase | internal | internal | - | Crash regression test for empty ruby base |
| inline/line_breaker_test.cc:1288 | CanBreakInsideTest.Data | behaviour | formalized | `lineBreaker_canBreakInside` | CanBreakInside predicate for line breaking opportunities |
| inline/line_breaker_test.cc:1323 | SplitTrailingBidiCrCrash | internal | internal | - | Crash regression test for CR in RTL bidi |
| inline/line_breaker_test.cc:1331 | BidiControlEnterFlag | geometry | formalized | `lineBreaker_bidiControlEnter` | Container line height matches single line font height (10px) |
| inline/inline_node_test.cc:192 | CollectInlinesText | geometry | formalized | `inlineNode_collectInlinesText` | Flattening inline tokens into text and open/close tag items with offsets |
| inline/inline_node_test.cc:206 | CollectInlinesBR | geometry | formalized | `inlineNode_collectInlinesBR` | Flattening inline tokens with BR into newline text and control item |
| inline/inline_node_test.cc:245 | ShareInlineTextContentSingleSource | internal | internal | - | String sharing optimization for single Text node |
| inline/inline_node_test.cc:256 | ShareInlineTextContentLargeNotSharedWhenCollapsed | internal | internal | - | String sharing optimization with whitespace collapse |
| inline/inline_node_test.cc:274 | ShareInlineTextContentLargeNotSharedSameLength | internal | internal | - | String sharing optimization |
| inline/inline_node_test.cc:284 | CollectInlinesFloat | behaviour | internal | - | Float items in inline formatting context |
| inline/inline_node_test.cc:306 | CollectInlinesInlineBlock | geometry | formalized | `inlineNode_collectInlinesInlineBlock` | Inline block flattening to object replacement character and atomic inline item |
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
| inline/inline_node_test.cc:649 | MinMaxTest.Data | geometry | formalized | `inlineNode_minMaxData` | Intrinsic min/max sizes calculation under 10px fixed-width font across word boundaries |
| inline/inline_node_test.cc:675 | MinMaxSizesSaturated | geometry | blocked | - | Blocked: model lacks LayoutUnit saturation in min-max computation |
| inline/inline_node_test.cc:698 | MinMaxSizesNeedsLayout | internal | internal | - | NeedsLayout flag on DOM text change |
| inline/inline_node_test.cc:716 | AssociatedItemsWithControlItem | internal | internal | - | Visual bidi ordering item association |
| inline/inline_node_test.cc:734 | NeedsCollectInlinesOnSetText | behaviour | blocked | - | Blocked: model lacks layout invalidation tracking |
| inline/inline_node_test.cc:767 | SetTextWithOffsetWithTextTransform | internal | internal | - | Crash regression in OffsetMapping |
| inline/inline_node_test.cc:838 | StyleChangeTest.NeedsCollectInlinesOnStyle | behaviour | blocked | - | Blocked: model lacks layout invalidation tracking |
| inline/inline_node_test.cc:927 | NodeInsertTest.NeedsCollectInlinesOnInsert | behaviour | blocked | - | Blocked: model lacks layout invalidation tracking |
| inline/inline_node_test.cc:960 | NeedsCollectInlinesOnInsertToOutOfFlowButton | internal | internal | - | Out of flow button insert |
| inline/inline_node_test.cc:987 | NodeRemoveTest.NeedsCollectInlinesOnRemove | behaviour | blocked | - | Blocked: model lacks layout invalidation tracking |
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
| inline/inline_node_test.cc:1713 | TextCombineWordSpacing | geometry | blocked | - | Blocked: model lacks text combine word spacing resolution |
| inline/inline_node_test.cc:1733 | FindSvgTextChunksCrash1 | internal | internal | - | Crash regression test for SVG text chunks |
| inline/inline_node_test.cc:1749 | FindSvgTextChunksCrash2 | internal | internal | - | Crash regression test for SVG text chunks |
| inline/inline_node_test.cc:1765 | FindSvgTextChunksCrash3 | internal | internal | - | Crash regression test for surrogate pairs |
| inline/inline_node_test.cc:1786 | NestedRubyMinMaxCrash | internal | internal | - | Crash regression for nested ruby min/max |
| inline/fragment_item_test.cc:67 | CopyMove | internal | internal | - | Copy and move constructors of FragmentItem |
| inline/fragment_item_test.cc:126 | BasicText | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:173 | RtlText | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:235 | BasicInlineBox | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:291 | CulledInlineBox | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:328 | SelfPaintingInlineBox | behaviour | internal | - | Invalidation and visual overflow recalc on self-painting layer |
| inline/fragment_item_test.cc:357 | StartOffsetInContainer | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:383 | EllipsizedAtomicInline | behaviour | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:417 | LineFragmentId | behaviour | internal | - | Multicol column line fragment ID tagging |
| inline/fragment_item_test.cc:451 | Outline | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
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
| inline/fragment_item_test.cc:931 | CaretInlinePositionForOffset_TextFit | geometry | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_item_test.cc:952 | IsRubyAnnotationLine | behaviour | blocked | - | Blocked: model lacks FragmentItems generator from box tree |
| inline/fragment_items_builder_test.cc:23 | MultipleLogicalLineItems | behaviour | blocked | - | Blocked: model lacks FragmentItemsBuilder line assembly |
| inline/fragment_items_test.cc:20 | DirtyLinesFromNeedsLayoutWithOrthogonalWritingMode | behaviour | internal | - | Regression test for orthogonal writing mode incremental layout |
| inline/fragment_items_test.cc:46 | IsContainerForCulledInline | geometry | blocked | - | Blocked: model lacks multicolumn culled inline container resolution |
| inline/hyphen_result_test.cc:37 | Horizontal | geometry | formalized | `hyphenResult_horizontal` | CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1: Horizontal writing hyphen glyph orientation |
| inline/hyphen_result_test.cc:53 | VerticalUpright | geometry | formalized | `hyphenResult_verticalUpright` | CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1: Vertical upright hyphen glyph orientation |
| inline/hyphen_result_test.cc:70 | VerticalMixed | geometry | formalized | `hyphenResult_verticalMixed` | CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1: Vertical mixed hyphen glyph orientation and feature fix |
| inline/inline_caret_position_test.cc:69 | AfterSpan | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:79 | AfterSpanCulled | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:89 | InlineCaretPositionInOneLineOfText | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:115 | InlineCaretPositionAtSoftHyphen | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:130 | InlineCaretPositionAtSoftLineWrap | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:146 | InlineCaretPositionAtSoftLineWrapWithSpace | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:169 | InlineCaretPositionAtForcedLineBreak | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:190 | InlineCaretPositionAtEmptyLine | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:203 | InlineCaretPositionInOneLineOfImage | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:221 | InlineCaretPositionAtSoftLineWrapBetweenImages | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:238 | InlineCaretPositionAtSoftLineWrapBetweenMultipleTextNodes | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:263 | InlineCaretPositionAtSoftLineWrapBetweenMultipleTextNodesRtl | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:288 | InlineCaretPositionAtSoftLineWrapBetweenDeepTextNodes | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:315 | GeneratedZeroWidthSpace | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:345 | MultiColumnSingleText | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:452 | SoftLineWrap | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:481 | ZeroWidthSpace | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:509 | InlineBlockBeforeContent | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:528 | InlineBoxesLTR | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:559 | InlineBoxesRTL | behaviour | blocked | - | Blocked: model lacks InlineCaretPosition resolution algorithm from layout tree |
| inline/inline_caret_position_test.cc:591 | BeforeOrAfterInlineAreaElement | internal | internal | - | Crash regression test for area element without layout object |
| inline/inline_cursor_test.cc:125 | BidiLevelInlineBoxLTR | behaviour | formalized | `inlineCursor_bidiLevelInlineBoxLTR` | Bidi levels for plain text, atomic inlines, and RTL bidi-override in LTR |
| inline/inline_cursor_test.cc:135 | BidiLevelInlineBoxRTL | behaviour | formalized | `inlineCursor_bidiLevelInlineBoxRTL` | Bidi levels for Latin text and RTL bidi-override in RTL |
| inline/inline_cursor_test.cc:145 | BidiLevelSimpleLTR | behaviour | formalized | `inlineCursor_bidiLevelSimpleLTR` | Nested RTL and LTR bidi-override levels in LTR |
| inline/inline_cursor_test.cc:155 | BidiLevelSimpleRTL | behaviour | blocked | - | Blocked: model lacks visual bidi reordering for RTL lines |
| inline/inline_cursor_test.cc:166 | BidiLevelFirstLineTextTransform | behaviour | formalized | `inlineCursor_bidiLevelFirstLineTextTransform` | First line uppercase text-transform with eszett at level 0 |
| inline/inline_cursor_test.cc:175 | BidiLevelFirstLineTextTransformBR | behaviour | formalized | `inlineCursor_bidiLevelFirstLineTextTransformBR` | First line uppercase text-transform with BR element at level 0 |
| inline/inline_cursor_test.cc:184 | GetLayoutBlockFlowWithScopedCursor | internal | internal | - | Scoped cursor block flow pointer equality |
| inline/inline_cursor_test.cc:191 | Parent | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:226 | ContainingLine | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:257 | CulledInlineWithAtomicInline | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:271 | CulledInlineWithFloat | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:281 | CulledInlineWithOOF | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:292 | CulledInlineNested | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:303 | CulledInlineBlockChild | behaviour | internal | - | Block in inline anonymous wrapper splitting |
| inline/inline_cursor_test.cc:318 | CulledInlineWithRoot | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:328 | CulledInlineWithoutRoot | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:339 | CursorForMovingAcrossFragmentainer | behaviour | internal | - | Multicolumn fragmentainer boundary crossing |
| inline/inline_cursor_test.cc:365 | FirstChild | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:375 | FirstChild2 | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:388 | FirstLastLogicalLeafInSimpleText | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:403 | FirstLastLogicalLeafInRtlText | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:420 | FirstLastLogicalLeafInTextAsDeepDescendants | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:439 | MoveToEndOfLineWithNoCharsLtr | behaviour | internal | - | End of empty line cursor in textarea LTR |
| inline/inline_cursor_test.cc:470 | MoveToEndOfLineWithNoCharsRtl | behaviour | internal | - | End of empty line cursor in textarea RTL |
| inline/inline_cursor_test.cc:502 | FirstLastLogicalLeafWithInlineBlock | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:520 | FirstLastLogicalLeafWithImages | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:534 | FirstNonPseudoLeafWithBlockImage | behaviour | internal | - | Block-in-inline image leaf traversal |
| inline/inline_cursor_test.cc:554 | IsEmptyLineBox | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:565 | LastChild | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:575 | LastChild2 | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:588 | Next | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:614 | NextIncludingFragmentainer | behaviour | internal | - | Next traversal across multicol fragmentainers |
| inline/inline_cursor_test.cc:635 | NextWithEllipsis | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:650 | NextWithEllipsisInlineBoxOnly | behaviour | internal | - | Empty inline box ellipsis traversal |
| inline/inline_cursor_test.cc:665 | NextWithListItem | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:675 | NextWithSoftHyphens | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:685 | NextInlineLeaf | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:698 | NextInlineLeafOnLineFromLayoutInline | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:716 | NextInlineLeafOnLineFromNestedLayoutInline | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:738 | NextInlineLeafOnLineFromLayoutText | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:756 | NextInlineLeafWithEllipsis | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:776 | NextInlineLeafWithSoftHyphens | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:788 | NextInlineLeafIgnoringLineBreak | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:800 | NextLine | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:821 | NextWithImage | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:827 | NextWithInlineBox | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:839 | NextForSameLayoutObject | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:847 | NextForSameLayoutObjectWithRange | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:882 | Sibling | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:893 | Sibling2 | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:905 | NextSkippingChildren | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:938 | EmptyOutOfFlow | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:952 | PositionForPointInChildHorizontalLTR | geometry | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:988 | PositionForPointInChildHorizontalRTL | geometry | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1025 | PositionForPointInChildVerticalLTR | geometry | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1061 | PositionForPointInChildVerticalRTL | geometry | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1099 | PositionForPointInChildBlockChildren | behaviour | internal | - | Hit testing on inline-block with block children |
| inline/inline_cursor_test.cc:1110 | Previous | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1124 | PreviousIncludingFragmentainer | behaviour | internal | - | Backward traversal across multicol fragmentainers |
| inline/inline_cursor_test.cc:1145 | PreviousInlineLeaf | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1158 | PreviousInlineLeafIgnoringLineBreak | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1171 | PreviousInlineLeafOnLineFromLayoutInline | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1189 | PreviousInlineLeafOnLineFromNestedLayoutInline | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1211 | PreviousInlineLeafOnLineFromLayoutText | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1229 | PreviousLine | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1250 | CursorForDescendants | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1292 | MoveToVisualFirstOrLast | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1318 | MoveToLayoutObject | behaviour | blocked | - | Blocked: model lacks InlineCursor tree iterator |
| inline/inline_cursor_test.cc:1455 | CulledInlineBlockInInlineOverflow | internal | internal | - | Crash regression test for block-in-inline overflow |
| inline/inline_cursor_test.cc:1473 | CulledInlineWithNonIFCChild | internal | internal | - | Crash regression test for non-IFC ruby child |
| inline/inline_items_builder_test.cc:206 | CollapseSpaces | behaviour | formalized | `inlineItemsBuilder_collapseSpaces` | Whitespace space collapsing rules across modes |
| inline/inline_items_builder_test.cc:216 | CollapseTabs | behaviour | formalized | `inlineItemsBuilder_collapseTabs` | Whitespace tab collapsing rules |
| inline/inline_items_builder_test.cc:226 | CollapseNewLines | behaviour | formalized | `inlineItemsBuilder_collapseNewlines` | Whitespace newline collapsing rules |
| inline/inline_items_builder_test.cc:236 | CollapseNewlinesAsSpaces | behaviour | formalized | `inlineItemsBuilder_collapseNewlinesAsSpaces` | Newlines collapsing to single spaces |
| inline/inline_items_builder_test.cc:243 | CollapseAcrossElements | behaviour | formalized | `inlineItemsBuilder_collapseAcrossElements` | Space collapsing across element boundaries |
| inline/inline_items_builder_test.cc:248 | CollapseLeadingSpaces | behaviour | formalized | `inlineItemsBuilder_collapseLeadingSpaces` | Leading spaces removal at block start |
| inline/inline_items_builder_test.cc:254 | CollapseTrailingSpaces | behaviour | formalized | `inlineItemsBuilder_collapseTrailingSpaces` | Trailing spaces removal at block end |
| inline/inline_items_builder_test.cc:260 | CollapseAllSpaces | behaviour | formalized | `inlineItemsBuilder_collapseAllSpaces` | All-whitespace text collapsing to empty |
| inline/inline_items_builder_test.cc:267 | CollapseLeadingNewlines | behaviour | formalized | `inlineItemsBuilder_collapseLeadingNewlines` | Leading newlines removal |
| inline/inline_items_builder_test.cc:281 | CollapseTrailingNewlines | behaviour | formalized | `inlineItemsBuilder_collapseTrailingNewlines` | Trailing newlines removal |
| inline/inline_items_builder_test.cc:289 | CollapseNewlineAcrossElements | behaviour | formalized | `inlineItemsBuilder_collapseNewlineAcrossElements` | Newline across element boundaries collapsing |
| inline/inline_items_builder_test.cc:295 | CollapseBeforeAndAfterNewline | behaviour | blocked | - | Blocked: model lacks CollapseBeforeAndAfterNewline handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:301 | CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements | behaviour | blocked | - | Blocked: model lacks CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:309 | CollapseZeroWidthSpaces | behaviour | blocked | - | Blocked: model lacks CollapseZeroWidthSpaces handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:334 | CollapseZeroWidthSpaceAndNewLineAtEnd | behaviour | blocked | - | Blocked: model lacks CollapseZeroWidthSpaceAndNewLineAtEnd handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:340 | CollapseEastAsianWidth | internal | internal | - | Disabled under SEGMENT_BREAK_TRANSFORMATION_FOR_EAST_ASIAN_WIDTH=0 |
| inline/inline_items_builder_test.cc:357 | OpaqueToSpaceCollapsing | behaviour | blocked | - | Blocked: model lacks OpaqueToSpaceCollapsing handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:367 | CollapseAroundReplacedElement | behaviour | blocked | - | Blocked: model lacks CollapseAroundReplacedElement handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:375 | CollapseNewlineAfterObject | behaviour | blocked | - | Blocked: model lacks CollapseNewlineAfterObject handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:387 | AppendEmptyString | behaviour | blocked | - | Blocked: model lacks AppendEmptyString handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:393 | NewLines | behaviour | blocked | - | Blocked: model lacks NewLines handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:405 | IgnorablePre | behaviour | blocked | - | Blocked: model lacks IgnorablePre handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:426 | Empty | behaviour | blocked | - | Blocked: model lacks Empty handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:446 | CollapsedSpaceAfterNoWrap | behaviour | blocked | - | Blocked: model lacks CollapsedSpaceAfterNoWrap handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:455 | GenerateBreakOpportunityAfterLeadingSpaces | behaviour | blocked | - | Blocked: model lacks GenerateBreakOpportunityAfterLeadingSpaces handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:469 | BidiBlockOverride | behaviour | formalized | `inlineItemsBuilder_bidiBlockOverride` | Injection of RLO and PDF bidi control characters for bidi-override block |
| inline/inline_items_builder_test.cc:501 | BidiIsolate | behaviour | formalized | `inlineItemsBuilder_bidiIsolate` | Injection of RLI and PDI bidi control characters for isolated inline |
| inline/inline_items_builder_test.cc:526 | BidiIsolateOverride | behaviour | formalized | `inlineItemsBuilder_bidiIsolateOverride` | Injection of FSI, RLO, PDF, and PDI for isolate-override inline |
| inline/inline_items_builder_test.cc:551 | BlockInInline | behaviour | blocked | - | Blocked: model lacks BlockInInline handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:561 | OpenCloseRubyColumns | behaviour | blocked | - | Blocked: model lacks OpenCloseRubyColumns handling in InlineItemsBuilder |
| inline/inline_items_builder_test.cc:638 | OffsetMappingStaysConsistentUnderFullWidthTransform | behaviour | internal | - | Full-width text transform offset mapping consistency check |
| inline/inline_layout_algorithm_test.cc:97 | Types | behaviour | formalized | `inlineLayout_emptyLineBoxTypes` | Empty inline tags generate empty line box, text does not |
| inline/inline_layout_algorithm_test.cc:113 | TypesForFirstLine | behaviour | blocked | - | Blocked: model lacks TypesForFirstLine layout algorithm support |
| inline/inline_layout_algorithm_test.cc:137 | TypesForBlockInInline | behaviour | blocked | - | Blocked: model lacks TypesForBlockInInline layout algorithm support |
| inline/inline_layout_algorithm_test.cc:192 | BreakToken | behaviour | formalized | `test_BreakToken_chain` | Chaining of inline break tokens across line layout passes |
| inline/inline_layout_algorithm_test.cc:245 | EmptyLineWithOutOfFlowInInlineContainingBlock | geometry | blocked | - | Blocked: model lacks EmptyLineWithOutOfFlowInInlineContainingBlock layout algorithm support |
| inline/inline_layout_algorithm_test.cc:291 | BoxForEndMargin | behaviour | blocked | - | Blocked: model lacks BoxForEndMargin layout algorithm support |
| inline/inline_layout_algorithm_test.cc:333 | InlineBoxBorderPadding | geometry | formalized | `test_InlineBoxBorderPadding_partition` | Border and padding partitioning across line breaks |
| inline/inline_layout_algorithm_test.cc:397 | ContainerBorderPadding | geometry | blocked | - | Blocked: model lacks ContainerBorderPadding layout algorithm support |
| inline/inline_layout_algorithm_test.cc:431 | MAYBE_VerticalAlignBottomReplaced | geometry | formalized | `inlineLayout_verticalAlignBottomReplaced` | CSS 2.1 §10.8: bottom-aligned replaced element taller than strut determines line height with top offset 0 |
| inline/inline_layout_algorithm_test.cc:454 | TextFloatsAroundFloatsBefore | geometry | formalized | `test_TextFloatsAroundFloatsBefore` | Line offsets around multiple active left floats |
| inline/inline_layout_algorithm_test.cc:519 | TextFloatsAroundInlineFloatThatFitsOnLine | geometry | blocked | - | Blocked: model lacks TextFloatsAroundInlineFloatThatFitsOnLine layout algorithm support |
| inline/inline_layout_algorithm_test.cc:565 | TextFloatsAroundInlineFloatThatDoesNotFitOnLine | geometry | blocked | - | Blocked: model lacks TextFloatsAroundInlineFloatThatDoesNotFitOnLine layout algorithm support |
| inline/inline_layout_algorithm_test.cc:596 | FloatsArePositionedWithRespectToTopEdgeAlignmentRule | geometry | blocked | - | Blocked: model lacks FloatsArePositionedWithRespectToTopEdgeAlignmentRule layout algorithm support |
| inline/inline_layout_algorithm_test.cc:635 | BlockInInlineAppend | behaviour | blocked | - | Blocked: model lacks BlockInInlineAppend layout algorithm support |
| inline/inline_layout_algorithm_test.cc:670 | PositionFloatsWithMargins | geometry | formalized | `test_PositionFloatsWithMargins` | Percentage margins on floats accounted for in line positioning |
| inline/inline_layout_algorithm_test.cc:694 | InkOverflow | geometry | formalized | `test_InkOverflow` | Glyph bounding box half-leading creates vertical ink overflow |
| inline/inline_layout_algorithm_test.cc:718 | TextCombineBasic | geometry | blocked | - | Blocked: model lacks TextCombineBasic layout algorithm support |
| inline/inline_layout_algorithm_test.cc:745 | TextCombineFake | geometry | blocked | - | Blocked: model lacks TextCombineFake layout algorithm support |
| inline/inline_layout_algorithm_test.cc:775 | InitialLetterEmpty | geometry | blocked | - | Blocked: model lacks InitialLetterEmpty layout algorithm support |
| inline/inline_layout_algorithm_test.cc:790 | InitialLetterWithEmptyInline | geometry | blocked | - | Blocked: model lacks InitialLetterWithEmptyInline layout algorithm support |
| inline/inline_layout_algorithm_test.cc:806 | LineBoxWithHangingWidthRTLRightAligned | geometry | formalized | `test_LineBoxWithHangingWidthRTLRightAligned` | RTL right-aligned hanging spaces conditional vs unconditional |
| inline/inline_layout_algorithm_test.cc:839 | LineBoxWithHangingWidthRTLCenterAligned | geometry | formalized | `test_LineBoxWithHangingWidthRTLCenterAligned` | RTL center-aligned hanging spaces centering calculation |
| inline/inline_layout_algorithm_test.cc:888 | TextBoxTrimConstraintSpace | behaviour | formalized | `test_TextBoxTrimConstraintSpace` | text-box-trim trim-both applies only to first and last in-flow child |
| inline/inline_layout_algorithm_test.cc:944 | TextBoxTrimConstraintSpaceSingle | behaviour | formalized | `test_TextBoxTrimConstraintSpaceSingle` | Single in-flow child before empty child start trim |
| inline/inline_layout_algorithm_test.cc:967 | TextBoxTrimConstraintSpaceEmptyOnly | behaviour | formalized | `test_TextBoxTrimConstraintSpaceEmptyOnly` | Sole in-flow child receives both start and end trim |
| inline/inline_layout_algorithm_test.cc:984 | TextBoxTrimConstraintSpaceNone | behaviour | formalized | `test_TextBoxTrimConstraintSpaceNone` | Empty parent receives neither start nor end trim |
| inline/inline_layout_algorithm_test.cc:999 | TextFitDivisionByZero | internal | internal | - | Crash regression test for text-fit grow per-line |
| inline/inline_layout_algorithm_test.cc:1008 | BoxFragmentInRubyCrash | internal | internal | - | Crash regression test for ruby column box fragment |
| inline/inline_layout_algorithm_test.cc:1026 | BidiControlsInLineClampedLines | internal | internal | - | Crash regression test for bidi controls in line clamp |
| inline/inline_layout_algorithm_test.cc:1044 | LineClampAndMaxContent | behaviour | blocked | - | Blocked: model lacks LineClampAndMaxContent layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1086 | EllipsisFallbackToDots | behaviour | formalized | `test_EllipsisFallbackToDots` | Missing U+2026 glyph falls back to three dots |
| inline/inline_layout_algorithm_test.cc:1129 | EllipsisFallbackToDotsFirstLine | behaviour | blocked | - | Blocked: model lacks EllipsisFallbackToDotsFirstLine layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1175 | TextEmphasisAsRuby | geometry | blocked | - | Blocked: model lacks TextEmphasisAsRuby layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1272 | RubyTextEmphasisAnnotationMetricsVerticalLr | geometry | blocked | - | Blocked: model lacks RubyTextEmphasisAnnotationMetricsVerticalLr layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1276 | RubyTextEmphasisAnnotationMetricsVerticalRl | geometry | blocked | - | Blocked: model lacks RubyTextEmphasisAnnotationMetricsVerticalRl layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1280 | RubyTextEmphasisAnnotationMetricsHorizontal | geometry | blocked | - | Blocked: model lacks RubyTextEmphasisAnnotationMetricsHorizontal layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1373 | RubyTextEmphasisHeight | geometry | blocked | - | Blocked: model lacks RubyTextEmphasisHeight layout algorithm support |
| inline/inline_layout_algorithm_test.cc:1406 | TextBoxTrimOnInlineBox | geometry | blocked | - | Blocked: model lacks TextBoxTrimOnInlineBox layout algorithm support |

| inline/inline_node_shape_cache_test.cc:51 | ShapeCacheMultipleItems | internal | internal | - | Tests IsNGShapeCacheAllowed flag for multiple items |
| inline/inline_node_shape_cache_test.cc:58 | ShapeCacheOpenAndCloseTags | internal | internal | - | Tests IsNGShapeCacheAllowed flag for open/close tags |
| inline/inline_node_shape_cache_test.cc:65 | ShapeCacheSpacingRequired | internal | internal | - | Tests IsNGShapeCacheAllowed flag with letter-spacing |
| inline/inline_node_shape_cache_test.cc:73 | ShapeCacheNewLine | internal | internal | - | Tests IsNGShapeCacheAllowed flag with newline |
| inline/inline_node_shape_cache_test.cc:79 | ShapeCacheBreakLine | internal | internal | - | Tests IsNGShapeCacheAllowed flag with br |
| inline/inline_node_shape_cache_test.cc:85 | ShapeCacheBreakWord | internal | internal | - | Tests IsNGShapeCacheAllowed flag with wbr |
| inline/inline_node_shape_cache_test.cc:91 | ShapeResultPointerEqualNewLine | internal | internal | - | Pointer equality check for ShapeResult cache across newline and br |
| inline/inline_node_shape_cache_test.cc:105 | ShapeCacheFloating | internal | internal | - | Tests IsNGShapeCacheAllowed flag with float |
| inline/inline_node_shape_cache_test.cc:111 | ShapeCacheOutOfFlowPositioned | internal | internal | - | Tests IsNGShapeCacheAllowed flag with abspos |
| inline/inline_node_shape_cache_test.cc:118 | ShapeCacheFontFeatures | internal | internal | - | Tests IsNGShapeCacheAllowed flag with font-feature-settings |
| inline/inline_node_shape_cache_test.cc:126 | ShapeCacheSpacing | internal | internal | - | Tests IsNGShapeCacheAllowed flag with letter-spacing and float |
| inline/inline_node_shape_cache_test.cc:135 | ShapeResultPointerEqualFloatsAndOutOfFlow | internal | internal | - | Pointer equality check for ShapeResult cache across floats and abspos |
| inline/inline_node_shape_cache_test.cc:152 | ShapeResultPointerEqualInline | internal | internal | - | Pointer equality check for ShapeResult cache across inline span |
| inline/justification_utils_test.cc:14 | SetupItemJustificationOpportunityCrash | internal | internal | - | Crash regression test for null dereference in InlineItem::Style |
| inline/line_break_candidate_test.cc:50 | Text | geometry | formalized | `lineBreak_Text` | CSS Text 3 §4: Soft wrap opportunity at word boundary with collapsed trailing space |
| inline/line_break_candidate_test.cc:76 | SoftHyphen | geometry | formalized | `lineBreak_SoftHyphen` | CSS Text 3 §4.1: Soft hyphen break opportunity with hyphen glyph expansion |
| inline/line_break_candidate_test.cc:104 | SoftHyphenDisabled | geometry | formalized | `lineBreak_SoftHyphenDisabled` | CSS Text 3 §4.1: hyphens: none disables soft hyphen break opportunities |
| inline/line_break_candidate_test.cc:130 | Span | geometry | formalized | `lineBreak_Span` | CSS Text 3 §4: Break candidate offsets across inline span boundaries |
| inline/line_break_candidate_test.cc:157 | SpanMidWord | geometry | formalized | `lineBreak_SpanMidWord` | CSS Text 3 §4: Mid-word span boundary does not create break opportunity |
| inline/line_break_candidate_test.cc:183 | SpanCloseAfterSpace | geometry | formalized | `lineBreak_SpanCloseAfterSpace` | CSS Text 3 §4: Break candidate offset advances past closing tag to next in-flow item |
| inline/line_break_candidate_test.cc:210 | TrailingSpacesCollapsed | geometry | blocked | - | Blocked: model lacks LineBreakCandidate opportunity analysis |
| inline/line_break_candidate_test.cc:247 | AtomicInline | geometry | blocked | - | Blocked: model lacks LineBreakCandidate opportunity analysis |
| inline/line_break_candidate_test.cc:276 | AtomicInlineBr | geometry | blocked | - | Blocked: model lacks LineBreakCandidate opportunity analysis |
| inline/line_break_candidate_test.cc:307 | AtomicInlineTrailingSpaces | geometry | blocked | - | Blocked: model lacks LineBreakCandidate opportunity analysis |
| inline/line_break_candidate_test.cc:339 | ForcedBreak | geometry | blocked | - | Blocked: model lacks LineBreakCandidate opportunity analysis |
| inline/line_break_candidate_test.cc:368 | OutOfFlowPositioned | geometry | blocked | - | Blocked: model lacks LineBreakCandidate opportunity analysis |
| inline/line_info_list_test.cc:15 | Get | internal | internal | - | Tests LineInfoListOf ring buffer caching and pointer identity |
| inline/line_info_test.cc:23 | InflowEndOffset | behaviour | formalized | `lineInfo_inflowEndOffset` | Ruby base text establishes inflow end offset excluding annotations |
| inline/line_info_test.cc:42 | TrailingSpaceWidthInitialEmptyItem | internal | internal | - | Crash regression / DCHECK test for zero-length control item in trailing spaces |
| inline/line_widths_test.cc:175 | LineWidthsDataTest.Data | geometry | formalized | `lineWidthsDataTest_data` | CSS 2.1 §9.5, §10.8 & CSS Inline 3 §3: Precomputed line widths with float exclusions |
| inline/offset_mapping_test.cc:213 | CollapseSpaces | behaviour | formalized | `test_OffsetMapping_CollapseSpaces` | Whitespace collapsing indices across normal, nowrap, pre, pre-wrap |
| inline/offset_mapping_test.cc:224 | CollapseTabs | behaviour | formalized | `test_OffsetMapping_CollapseTabs` | Tab character collapsing indices |
| inline/offset_mapping_test.cc:235 | CollapseNewLines | behaviour | formalized | `test_OffsetMapping_CollapseNewLines` | Newline character collapsing indices |
| inline/offset_mapping_test.cc:246 | CollapseNewlinesAsSpaces | behaviour | formalized | `test_OffsetMapping_CollapseNewlinesAsSpaces` | Consecutive newline character collapsing indices |
| inline/offset_mapping_test.cc:253 | CollapseAcrossElements | behaviour | formalized | `test_OffsetMapping_CollapseAcrossElements` | Spaces collapsed across element boundaries |
| inline/offset_mapping_test.cc:258 | CollapseLeadingSpaces | behaviour | formalized | `test_OffsetMapping_CollapseLeadingSpaces` | Leading space character collapsing indices |
| inline/offset_mapping_test.cc:266 | CollapseTrailingSpaces | behaviour | formalized | `test_OffsetMapping_CollapseTrailingSpaces` | Trailing spaces collapsed at element and block ends |
| inline/offset_mapping_test.cc:276 | DISABLED_CollapseAllSpaces | internal | internal | - | Disabled upstream unit test |
| inline/offset_mapping_test.cc:283 | CollapseLeadingNewlines | behaviour | formalized | `test_OffsetMapping_CollapseLeadingNewlines` | Leading newlines collapsed at block start |
| inline/offset_mapping_test.cc:299 | CollapseTrailingNewlines | behaviour | formalized | `test_OffsetMapping_CollapseTrailingNewlines` | Trailing newlines collapsed at block end |
| inline/offset_mapping_test.cc:309 | CollapseNewlineAcrossElements | behaviour | formalized | `test_OffsetMapping_CollapseNewlineAcrossElements` | Newlines collapsed across element boundaries |
| inline/offset_mapping_test.cc:315 | CollapseBeforeAndAfterNewline | behaviour | formalized | `test_OffsetMapping_CollapseBeforeAndAfterNewline` | Spaces collapsed before and after newlines in pre-line |
| inline/offset_mapping_test.cc:321 | CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements | behaviour | formalized | `test_OffsetMapping_CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements` | Collapsible space preserved after non-collapsible pre-wrap element |
| inline/offset_mapping_test.cc:333 | CollapseZeroWidthSpaces | behaviour | blocked | - | Blocked: model lacks zero-width space offset mapping |
| inline/offset_mapping_test.cc:358 | CollapseEastAsianWidth | internal | internal | - | Disabled under SEGMENT_BREAK_TRANSFORMATION_FOR_EAST_ASIAN_WIDTH=0 |
| inline/offset_mapping_test.cc:389 | StoredResult | internal | internal | - | Checks offset_mapping pointer storage on LayoutBlockFlow |
| inline/offset_mapping_test.cc:396 | NGInlineFormattingContextOf | internal | internal | - | Checks formatting context container lookup pointer equality |
| inline/offset_mapping_test.cc:429 | OneTextNode | behaviour | formalized | `test_OffsetMapping_OneTextNode` | OffsetMappingUnit for single text node |
| inline/offset_mapping_test.cc:492 | TwoTextNodes | behaviour | formalized | `test_OffsetMapping_TwoTextNodes` | Offset mapping and positions across two sibling text nodes |
| inline/offset_mapping_test.cc:558 | BRBetweenTextNodes | behaviour | formalized | `test_OffsetMapping_BRBetweenTextNodes` | Offset mapping units across text nodes separated by BR element |
| inline/offset_mapping_test.cc:613 | OneTextNodeWithCollapsedSpace | behaviour | formalized | `test_OffsetMapping_OneTextNodeWithCollapsedSpace` | OffsetMappingUnits partitioning into identity and collapsed runs |
| inline/offset_mapping_test.cc:686 | FullyCollapsedWhiteSpaceNode | behaviour | blocked | - | Blocked: model lacks empty whitespace node offset mapping |
| inline/offset_mapping_test.cc:748 | ReplacedElement | behaviour | blocked | - | Blocked: model lacks replaced element offset mapping |
| inline/offset_mapping_test.cc:805 | FirstLetter | behaviour | blocked | - | Blocked: model lacks first-letter offset mapping |
| inline/offset_mapping_test.cc:835 | FirstLetterWithLeadingSpace | behaviour | blocked | - | Blocked: model lacks first-letter leading space offset mapping |
| inline/offset_mapping_test.cc:871 | FirstLetterWithoutRemainingText | behaviour | blocked | - | Blocked: model lacks first-letter text offset mapping |
| inline/offset_mapping_test.cc:902 | FirstLetterInDifferentBlock | behaviour | blocked | - | Blocked: model lacks first-letter block offset mapping |
| inline/offset_mapping_test.cc:967 | WhiteSpaceTextNodeWithoutLayoutText | behaviour | blocked | - | Blocked: model lacks whitespace node offset mapping |
| inline/offset_mapping_test.cc:976 | ContainerWithGeneratedContent | behaviour | blocked | - | Blocked: model lacks generated content offset mapping |
| inline/offset_mapping_test.cc:1006 | InlineBlockWithGeneratedContent | behaviour | blocked | - | Blocked: model lacks generated content offset mapping |
| inline/offset_mapping_test.cc:1046 | Table | behaviour | blocked | - | Blocked: model lacks table offset mapping |
| inline/offset_mapping_test.cc:1070 | GetMappingForInlineBlock | behaviour | blocked | - | Blocked: model lacks inline block offset mapping |
| inline/offset_mapping_test.cc:1098 | NoWrapSpaceAndCollapsibleSpace | behaviour | blocked | - | Blocked: model lacks nowrap offset mapping |
| inline/offset_mapping_test.cc:1128 | PreLine | behaviour | formalized | `test_OffsetMapping_PreLine` | OffsetMappingUnits partitioning with preserved newlines in pre-line |
| inline/offset_mapping_test.cc:1152 | BiDiAroundForcedBreakInPreLine | behaviour | blocked | - | Blocked: model lacks bidi pre-line offset mapping |
| inline/offset_mapping_test.cc:1176 | BiDiAroundForcedBreakInPreWrap | behaviour | blocked | - | Blocked: model lacks bidi pre-wrap offset mapping |
| inline/offset_mapping_test.cc:1200 | BiDiAroundForcedBreakInPre | behaviour | blocked | - | Blocked: model lacks bidi pre offset mapping |
| inline/offset_mapping_test.cc:1224 | SoftHyphen | behaviour | blocked | - | Blocked: model lacks soft hyphen offset mapping |
| inline/offset_mapping_test.cc:1241 | PreWrapAndReusing | behaviour | blocked | - | Blocked: model lacks pre-wrap reuse offset mapping |
| inline/offset_mapping_test.cc:1266 | RestoreTrailingCollapsibleSpaceReplace | behaviour | blocked | - | Blocked: model lacks trailing space restore offset mapping |
| inline/offset_mapping_test.cc:1295 | RestoreTrailingCollapsibleSpaceReplaceKeep | behaviour | blocked | - | Blocked: model lacks trailing space restore offset mapping |
| inline/offset_mapping_test.cc:1324 | RestoreTrailingCollapsibleSpaceNone | behaviour | blocked | - | Blocked: model lacks trailing space restore offset mapping |
| inline/offset_mapping_test.cc:1349 | RestoreTrailingCollapsibleSpaceSplit | behaviour | blocked | - | Blocked: model lacks trailing space restore offset mapping |
| inline/offset_mapping_test.cc:1378 | RestoreTrailingCollapsibleSpaceSplitKeep | behaviour | blocked | - | Blocked: model lacks trailing space restore offset mapping |
| inline/offset_mapping_test.cc:1409 | TextOverflowEllipsis | behaviour | blocked | - | Blocked: model lacks ellipsis offset mapping |
| inline/offset_mapping_test.cc:1426 | StartOfNextNonCollapsedContentWithPseudo | behaviour | blocked | - | Blocked: model lacks pseudo element offset mapping |
| inline/offset_mapping_test.cc:1444 | EndOfLastNonCollapsedContentWithPseudo | behaviour | blocked | - | Blocked: model lacks pseudo element offset mapping |
| inline/offset_mapping_test.cc:1461 | WordBreak | behaviour | blocked | - | Blocked: model lacks word break offset mapping |
| inline/offset_mapping_test.cc:1481 | NoCrashByListStyleTypeChange | internal | internal | - | Crash regression test for list-style-type change |
| inline/offset_mapping_test.cc:1497 | OffsetMappingGetterTest.Get | internal | internal | - | Checks OffsetMapping getter caching plumbing |
| inline/offset_mapping_test.cc:1515 | LayoutObjectConverter | internal | internal | - | Checks LayoutObject converter internal plumbing |
| inline/paragraph_line_breaker_test.cc:27 | IsDisabledByBlockInInline | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:52 | IsDisabledByFirstLine | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:75 | IsDisabledByFloatLeading | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:97 | IsDisabledByFloat | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:119 | IsDisabledByForcedBreak | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:140 | IsDisabledByForcedBreakReusing | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:163 | IsDisabledByInitialLetter | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/paragraph_line_breaker_test.cc:186 | IsDisabledByTabulationCharacters | behaviour | blocked | - | Blocked: model lacks ParagraphLineBreaker |
| inline/physical_line_box_fragment_test.cc:44 | HasPropagatedDescendantsFloat | behaviour | blocked | - | Blocked: model lacks LineBoxFragment descendant flag propagation |
| inline/physical_line_box_fragment_test.cc:62 | HasPropagatedDescendantsOOF | behaviour | blocked | - | Blocked: model lacks LineBoxFragment descendant flag propagation |
| inline/ruby_utils_test.cc:25 | GroupLinesEmpty | geometry | formalized | `rubyBlockPositionCalculator_groupLinesEmpty` | Empty ruby column list produces exactly one base-level ruby line |
| inline/ruby_utils_test.cc:32 | GroupLinesOneAnnotationLevel | geometry | formalized | `rubyBlockPositionCalculator_groupLinesOneAnnotationLevel` | Non-overlapping columns form a single annotation level [1] on the base |
| inline/ruby_utils_test.cc:49 | GroupLinesNested | geometry | formalized | `rubyBlockPositionCalculator_groupLinesNested` | Nested ruby columns form tiered annotation levels [1] and [2] |
| inline/ruby_utils_test.cc:67 | GroupLinesBothSides | geometry | formalized | `rubyBlockPositionCalculator_groupLinesBothSides` | Over and under annotations group into separate lines with negative and positive depths |
| inline/ruby_utils_test.cc:106 | GroupLinesAnnotationForAnnotation | geometry | formalized | `rubyBlockPositionCalculator_groupLinesAnnotationForAnnotation` | Sub-columns of an annotation column form sub-levels such as [1, -1] |
| inline/ruby_utils_test.cc:129 | PlaceLinesTreePlacement | geometry | blocked | - | Blocked: model lacks RubyBlockPositionCalculator |
| inline/ruby_utils_test.cc:146 | PlaceLinesNestedRubyWithTextEmphasis | geometry | blocked | - | Blocked: model lacks RubyBlockPositionCalculator |
| inline/score_line_breaker_test.cc:78 | LastLines | geometry | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:136 | BalanceMaxLinesExceeded | behaviour | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:172 | BlockInInlineTest.BeforeAfter | geometry | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:237 | ForcedBreak | geometry | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:370 | DisabledByLineBreakerTest.Data | behaviour | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:408 | FloatRetry | geometry | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:433 | Ruby | geometry | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:453 | Zoom | geometry | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/score_line_breaker_test.cc:490 | UseCountNotCountedForWrap | internal | internal | - | UseCounter metric check |
| inline/score_line_breaker_test.cc:498 | UseCountNotCountedForBalance | internal | internal | - | UseCounter metric check |
| inline/score_line_breaker_test.cc:506 | LineCountMismatchFallback | behaviour | blocked | - | Blocked: model lacks ScoreLineBreaker |
| inline/text_auto_space_test.cc:85 | MayApplyTest.MayApply | behaviour | formalized | `textAutoSpace_mayApply` | Early rejection check for East Asian ideograph presence |
| inline/text_auto_space_test.cc:95 | InsertSpacing | geometry | formalized | `textAutoSpace_insertSpacing` | Inter-script 1/8 em spacing insertion between ideograph and Latin text |
| inline/text_auto_space_test.cc:173 | HtmlTest.Apply | geometry | formalized | `textAutoSpace_apply` | Auto-space boundary offset detection across scripts |
| inline_layout_test.cc:32 | BlockWithSingleTextNode | behaviour | formalized | `inlineLayout_blockWithSingleTextNode` | CSS 2.1 §9.4.2: Inline formatting context flattens DOM nodes into text stream |
| inline_layout_test.cc:59 | BlockWithTextAndAtomicInline | behaviour | formalized | `inlineLayout_blockWithTextAndAtomicInline` | CSS 2.1 §9.4.2 & §10.8: Replaced atomic inline represented by object replacement character |
| layout_inline_test.cc:38 | PhysicalLinesBoundingBox | geometry | formalized | `layoutInline_physicalLinesBoundingBox` | CSS 2.1 §9.4.2 & CSS Writing Modes 3 §4: Union of line fragment rectangles across LTR, RTL, and vertical-rl |
| layout_inline_test.cc:69 | SimpleContinuation | internal | internal | - | LayoutObject tree continuation structure |
| layout_inline_test.cc:93 | BlockInInlineRemove | internal | internal | - | DOM mutation and LayoutObject tree continuation updates |
| layout_inline_test.cc:139 | RegionHitTest | behaviour | blocked | - | Blocked: model lacks inline hit testing |
| layout_inline_test.cc:194 | RelativePositionedHitTest | behaviour | blocked | - | Blocked: model lacks inline hit testing |
| layout_inline_test.cc:241 | MultilineRelativePositionedHitTest | behaviour | blocked | - | Blocked: model lacks inline hit testing |
| layout_inline_test.cc:319 | HitTestCulledInlinePreWrap | behaviour | blocked | - | Blocked: model lacks inline hit testing |
| layout_inline_test.cc:350 | DISABLED_FocusRingRecursiveContinuations | internal | internal | - | Disabled upstream test for continuation focus ring |
| layout_inline_test.cc:382 | DISABLED_FocusRingRecursiveInlinesVerticalRL | internal | internal | - | Disabled upstream test for vertical focus ring |
| layout_inline_test.cc:417 | DISABLED_FocusRingRecursiveContinuationsVerticalRL | internal | internal | - | Disabled upstream test for vertical continuation focus ring |
| layout_inline_test.cc:452 | DISABLED_FocusRingRecursiveInlines | internal | internal | - | Disabled upstream test for inline focus ring |
| layout_inline_test.cc:483 | AbsoluteBoundingBoxRectHandlingEmptyInline | geometry | blocked | - | Blocked: model lacks LayoutInline::AbsoluteBoundingBoxRectHandlingEmptyInline |
| layout_inline_test.cc:529 | AbsoluteBoundingBoxRectHandlingEmptyInlineVerticalRL | geometry | blocked | - | Blocked: model lacks LayoutInline::AbsoluteBoundingBoxRectHandlingEmptyInline |
| layout_inline_test.cc:575 | AddDraggableRegions | behaviour | blocked | - | Blocked: model lacks AddDraggableRegions |
| layout_inline_test.cc:609 | AddDraggableRegionsVerticalRL | behaviour | blocked | - | Blocked: model lacks AddDraggableRegions |
| layout_inline_test.cc:643 | VisualOverflowRecalcLegacyLayout | internal | internal | - | LayoutObject visual overflow invalidation lifecycle |
| layout_inline_test.cc:689 | VisualOverflowRecalcLayoutNG | internal | internal | - | LayoutObject visual overflow invalidation lifecycle |
| layout_inline_test.cc:733 | VisualOverflowRecalcLegacyLayoutPositionRelative | internal | internal | - | LayoutObject visual overflow invalidation lifecycle |
| layout_text_test.cc:166 | PrewarmFamily | internal | internal | - | Font prewarming plumbing |
| layout_text_test.cc:184 | PrewarmFontFace | internal | internal | - | Font prewarming plumbing |
| layout_text_test.cc:212 | PrewarmGenericFamily | internal | internal | - | Font prewarming plumbing |
| layout_text_test.cc:265 | MapDOMOffsetToTextContentOffset.Basic | behaviour | blocked | - | Blocked: model lacks parameterized multi-node DOM-to-text mapping |
| layout_text_test.cc:282 | CharacterAfterWhitespaceCollapsing | behaviour | blocked | - | Blocked: model lacks multi-element whitespace context |
| layout_text_test.cc:326 | CaretMinMaxOffset | behaviour | formalized | `layoutText_caretMinMaxOffset` | DOM caret minimum and maximum offsets under CSS whitespace collapsing |
| layout_text_test.cc:344 | ResolvedTextLength | behaviour | formalized | `layoutText_resolvedTextLength` | Resolved non-collapsed text length for normal whitespace |
| layout_text_test.cc:358 | ContainsCaretOffset | behaviour | formalized | `layoutText_containsCaretOffset` | Caret snap codes at all offsets of whitespace-collapsed text |
| layout_text_test.cc:383 | ContainsCaretOffsetInPre | behaviour | formalized | `layoutText_containsCaretOffsetInPre` | Caret snap codes under white-space: pre preserving whitespace and newline barriers |
| layout_text_test.cc:420 | ContainsCaretOffsetInPreLine | behaviour | formalized | `layoutText_containsCaretOffsetInPreLine` | Caret snap codes in pre-line text preserving newline identity unit |
| layout_text_test.cc:525 | ContainsCaretOffsetWithTrailingSpace | behaviour | formalized | `layoutText_containsCaretOffsetWithTrailingSpace` | Caret snap codes across text nodes with intermediate BR element |
| layout_text_test.cc:541 | ContainsCaretOffsetWithTrailingSpace1 | behaviour | formalized | `layoutText_containsCaretOffsetWithTrailingSpace1` | Caret snap codes with collapsed trailing and leading spaces around BR |
| layout_text_test.cc:568 | ContainsCaretOffsetWithTrailingSpace2 | behaviour | formalized | `layoutText_containsCaretOffsetWithTrailingSpace2` | Caret snap codes with multiple collapsed spaces around BR |
| layout_text_test.cc:599 | ContainsCaretOffsetWithTrailingSpace3 | behaviour | blocked | - | Blocked: model lacks multi-sibling trailing space caret resolution |
| layout_text_test.cc:625 | GetTextBoxInfoWithCollapsedWhiteSpace | geometry | blocked | - | Blocked: model lacks LayoutText::GetTextBoxInfo |
| layout_text_test.cc:654 | GetTextBoxInfoWithGeneratedContent | geometry | blocked | - | Blocked: model lacks LayoutText::GetTextBoxInfo |
| layout_text_test.cc:696 | GetTextBoxInfoWithHidden | geometry | blocked | - | Blocked: model lacks LayoutText::GetTextBoxInfo |
| layout_text_test.cc:726 | GetTextBoxInfoWithEllipsis | geometry | blocked | - | Blocked: model lacks LayoutText::GetTextBoxInfo |
| layout_text_test.cc:757 | GetTextBoxInfoWithEllipsisForPseudoAfter | geometry | blocked | - | Blocked: model lacks LayoutText::GetTextBoxInfo |
| layout_text_test.cc:788 | PlainTextInPseudo | behaviour | blocked | - | Blocked: model lacks pseudo element PlainText |
| layout_text_test.cc:826 | IsBeforeAfterNonCollapsedCharacterNoLineWrap | behaviour | formalized | `layoutText_isBeforeAfterNonCollapsedCharacterNoLineWrap` | Non-collapsed snap codes on plain strings, inner runs, and leading spaces |
| layout_text_test.cc:907 | IsBeforeAfterNonCollapsedLineWrapSpace | behaviour | blocked | - | Blocked: model lacks line-wrap aware caret positioning |
| layout_text_test.cc:972 | IsBeforeAfterNonCollapsedCharacterBR | behaviour | formalized | `layoutText_isBeforeAfterNonCollapsedCharacterBR` | Line break element emits newline with caret barrier after newline |
| layout_text_test.cc:978 | AbsoluteQuads | geometry | blocked | - | Blocked: model lacks LayoutText::AbsoluteQuads |
| layout_text_test.cc:998 | AbsoluteQuadsVRL | geometry | blocked | - | Blocked: model lacks LayoutText::AbsoluteQuads |
| layout_text_test.cc:1020 | PhysicalLinesBoundingBox | geometry | blocked | - | Blocked: model lacks LayoutText::PhysicalLinesBoundingBox |
| layout_text_test.cc:1064 | PhysicalLinesBoundingBoxTextCombine | geometry | blocked | - | Blocked: model lacks text-combine-upright bounding box |
| layout_text_test.cc:1097 | PhysicalLinesBoundingBoxVerticalRL | geometry | blocked | - | Blocked: model lacks vertical-rl LayoutText bounding box |
| layout_text_test.cc:1134 | WordBreakElement | behaviour | formalized | `layoutText_wordBreakElement` | `<wbr>` word-break opportunity element has 0 resolved length and min/max offset |
| layout_text_test.cc:1146 | LocalSelectionRect | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1169 | LocalSelectionRectLineBreak | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1177 | LocalSelectionRectLineBreakPre | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1187 | LocalSelectionRectRTL | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1199 | LocalSelectionRectVertical | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1211 | LocalSelectionRectVerticalRTL | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1224 | LocalSelectionRectLineHeight | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1237 | LocalSelectionRectNegativeLeading | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1253 | LocalSelectionRectLineHeightVertical | geometry | blocked | - | Blocked: model lacks LocalSelectionVisualRect |
| layout_text_test.cc:1269 | PositionForPointAtLeading | behaviour | blocked | - | Blocked: model lacks LayoutText::PositionForPoint |
| layout_text_test.cc:1321 | FloatFirstLetterPlainText | behaviour | blocked | - | Blocked: model lacks first-letter layout |
| layout_text_test.cc:1334 | SetTextWithOffsetAppendBidi | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1345 | SetTextWithOffsetAppendControl | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1357 | SetTextWithOffsetAppendCollapseWhiteSpace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1366 | SetTextWithOffsetAppend | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1379 | SetTextWithOffsetAppendEmojiWithZWJ | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1413 | SetTextWithOffsetDelete | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1425 | SetTextWithOffsetDeleteCollapseWhiteSpace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1434 | SetTextWithOffsetDeleteCollapseWhiteSpaceEnd | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1444 | SetTextWithOffsetCopyItemBefore | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1463 | SetTextWithOffsetDeleteNbspInPreWrap | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1475 | SetTextWithOffsetDeleteRTL | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1488 | SetTextWithOffsetDeleteRTL2 | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1502 | SetTextWithOffsetDeleteThenNonCollapse | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1515 | SetTextWithOffsetDeleteThenNonCollapse2 | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1528 | SetTextWithOffsetDeleteWithBidiControl | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1541 | SetTextWithOffsetDeleteWithGeneratedBreakOpportunity | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1556 | SetTextWithOffsetEditingTextCollapsedSpace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1568 | SetTextWithOffsetInsert | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1580 | SetTextWithOffsetInsertAfterSpace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1589 | SetTextWithOffsetInserBeforetSpace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1599 | SetTextWithOffsetInsertSameCharacters | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1612 | SetTextWithOffsetNoRelocation | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1624 | SetTextWithOffsetPrepend | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1636 | SetTextWithOffsetReplace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1648 | SetTextWithOffsetReplaceCollapseWhiteSpace | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1657 | SetTextWithOffsetReplaceToExtend | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1669 | SetTextWithOffsetReplaceToShrink | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1681 | SetTextWithOffsetToEmpty | internal | internal | - | Incremental layout mutation and invalidation |
| layout_text_test.cc:1694 | TransformedTextWithCapitalizationAfterInlineAbsolute | behaviour | blocked | - | Blocked: model lacks text-transform: capitalize |
| layout_text_test.cc:1707 | TransformedTextWithCapitalizationAfterSupplementaryCharacter | behaviour | blocked | - | Blocked: model lacks text-transform: capitalize |
| layout_text_test.cc:1727 | OriginalTextNullWhenTransformedTextIsNonNull | internal | internal | - | Pseudo element text node presence check |
| layout_text_test.cc:1755 | OriginalTextEmptyWhenTransformedTextIsNonEmpty | internal | internal | - | Marker pseudo element text presence check |
| layout_text_fragment_test.cc:47 | Basics | behaviour | formalized | `layoutTextFragment_basics` | Basic caret offset and resolved text length for first-letter and remaining text |
| layout_text_fragment_test.cc:61 | TransformedTextWithCapitalizationAfterSupplementaryCharacter | behaviour | blocked | - | Blocked: model lacks first-letter LayoutTextFragment splitting |
| layout_text_fragment_test.cc:81 | CaretMinMaxOffset | behaviour | formalized | `layoutTextFragment_caretMinMaxOffset` | Caret min/max offset queries with punctuation and surrounding whitespace |
| layout_text_fragment_test.cc:107 | CaretMinMaxOffsetSpacesInBetween | behaviour | blocked | - | Blocked: model lacks first-letter LayoutTextFragment splitting |
| layout_text_fragment_test.cc:133 | CaretMinMaxOffsetCollapsedRemainingText | behaviour | formalized | `layoutTextFragment_caretMinMaxOffsetCollapsedRemainingText` | Fully collapsed remaining text returns 0 and fragment length |
| layout_text_fragment_test.cc:151 | ResolvedTextLength | behaviour | formalized | `layoutTextFragment_resolvedTextLength` | Resolved text length for first-letter and remaining text with punctuation |
| layout_text_fragment_test.cc:169 | ResolvedTextLengthSpacesInBetween | behaviour | formalized | `layoutTextFragment_resolvedTextLengthSpacesInBetween` | Consecutive spaces between first-letter and remaining text collapse |
| layout_text_fragment_test.cc:187 | ResolvedTextLengthCollapsedRemainingText | behaviour | formalized | `layoutTextFragment_resolvedTextLengthCollapsedRemainingText` | Fully collapsed remaining text has resolved text length 0 |
| layout_text_fragment_test.cc:197 | ContainsCaretOffset | behaviour | formalized | `layoutTextFragment_containsCaretOffset` | Caret offset membership across whitespace collapsed first-letter and remaining text |
| layout_text_fragment_test.cc:244 | ContainsCaretOffsetSpacesInBetween | behaviour | formalized | `layoutTextFragment_containsCaretOffsetSpacesInBetween` | Caret offset membership across consecutive spaces between fragments |
| layout_text_fragment_test.cc:258 | ContainsCaretOffsetPre | behaviour | formalized | `layoutTextFragment_containsCaretOffsetPre` | Caret offset membership under white-space: pre preserving spaces and terminating at newline |
| layout_text_fragment_test.cc:273 | ContainsCaretOffsetPreLine | behaviour | formalized | `layoutTextFragment_containsCaretOffsetPreLine` | Caret offset membership under white-space: pre-line collapsing spaces before newline |
| layout_text_fragment_test.cc:288 | IsBeforeAfterNonCollapsedCharacterNoLineWrap | behaviour | formalized | `layoutTextFragment_isBeforeAfterNonCollapsedCharacterNoLineWrap` | Before/after non-collapsed character queries across first-letter and remaining text fragments |
| layout_text_fragment_test.cc:356 | IsBeforeAfterNonCollapsedLineWrapSpace | behaviour | blocked | - | Blocked: model lacks first-letter LayoutTextFragment splitting |
| layout_text_fragment_test.cc:386 | SetTextWithFirstLetter | internal | internal | - | First-letter LayoutTextFragment mutation |
| layout_text_fragment_test.cc:442 | SplitTextWithZero | internal | internal | - | DOM text split mutation |
| layout_br_test.cc:14 | TextMethods | behaviour | formalized | `layoutBR_textMethods` | `<br>` generates an identity mapping unit with resolved length 1 and newline snap code |
| layout_text_combine_test.cc:52 | AppendChild | internal | internal | - | DOM mutation in text-combine container |
| layout_text_combine_test.cc:84 | BoxBoundary | internal | internal | - | Box boundary traversal in text combine |
| layout_text_combine_test.cc:106 | DeleteDataToEmpty | internal | internal | - | CharacterData deletion in text combine |
| layout_text_combine_test.cc:137 | ElementRecalcOwnStyle | internal | internal | - | Style recalc in text combine |
| layout_text_combine_test.cc:166 | HtmlElement | internal | internal | - | Text combine inside html element |
| layout_text_combine_test.cc:191 | InkOverflow | geometry | blocked | - | Blocked: model lacks text-combine-upright layout |
| layout_text_combine_test.cc:248 | InkOverflowEmphasisMark | geometry | blocked | - | Blocked: model lacks text-combine-upright layout |
| layout_text_combine_test.cc:307 | InkOverflowOverline | geometry | blocked | - | Blocked: model lacks text-combine-upright layout |
| layout_text_combine_test.cc:364 | InkOverflowUnderline | geometry | blocked | - | Blocked: model lacks text-combine-upright layout |
| layout_text_combine_test.cc:421 | InkOverflowWBR | geometry | blocked | - | Blocked: model lacks text-combine-upright layout |
| layout_text_combine_test.cc:488 | InsertBefore | internal | internal | - | DOM insertion in text combine |
| layout_text_combine_test.cc:523 | InsertBR | internal | internal | - | BR insertion in text combine |
| layout_text_combine_test.cc:540 | ScrollableOverflow | geometry | blocked | - | Blocked: model lacks text-combine-upright layout |
| layout_text_combine_test.cc:582 | ListItemStyleToImage | internal | internal | - | List item marker mutation |
| layout_text_combine_test.cc:621 | ListMarkerWidthOfSymbol | geometry | blocked | - | Blocked: model lacks text-combine-upright list marker layout |
| layout_text_combine_test.cc:644 | MultipleTextNode | internal | internal | - | Multiple text nodes in text combine |
| layout_text_combine_test.cc:664 | Nested | internal | internal | - | Nested text combine elements |
| layout_text_combine_test.cc:684 | Outline | geometry | blocked | - | Blocked: model lacks text-combine-upright outline layout |
| layout_text_combine_test.cc:758 | PropageWritingModeFromBodyToHorizontal | behaviour | formalized | `layoutTextCombine_propageWritingModeFromBodyToHorizontal` | HTML writing mode propagation from body to html |
| layout_text_combine_test.cc:783 | PropageWritingModeFromBodyToVertical | behaviour | formalized | `layoutTextCombine_propageWritingModeFromBodyToVertical` | HTML writing mode propagation to vertical |
| layout_text_combine_test.cc:810 | RebuildLayoutTreeForDetails | internal | internal | - | Layout tree rebuild in details element |
| layout_text_combine_test.cc:854 | RemoveBlockChild | internal | internal | - | DOM block removal in text combine |
| layout_text_combine_test.cc:886 | RemoveChildCombine | internal | internal | - | DOM combine child removal |
| layout_text_combine_test.cc:914 | RemoveChildToEmpty | internal | internal | - | DOM child removal to empty |
| layout_text_combine_test.cc:944 | RemoveChildToOneCombinedText | internal | internal | - | DOM child removal to single combine |
| layout_text_combine_test.cc:979 | ReplaceChildToOneCombinedText | internal | internal | - | DOM child replacement |
| layout_text_combine_test.cc:1016 | SetDataToEmpty | internal | internal | - | Text mutation to empty |
| layout_text_combine_test.cc:1046 | SplitText | internal | internal | - | Text split mutation |
| layout_text_combine_test.cc:1081 | SplitTextAtZero | internal | internal | - | Text split at zero offset |
| layout_text_combine_test.cc:1116 | SplitTextBeforeBox | internal | internal | - | Text split before box |
| layout_text_combine_test.cc:1157 | StyleToTextCombineUprightAll | behaviour | formalized | `layoutTextCombine_styleToTextCombineUprightAll` | Dynamic style update to text-combine-upright: all |
| layout_text_combine_test.cc:1190 | StyleToTextCombineUprightNone | behaviour | formalized | `layoutTextCombine_styleToTextCombineUprightNone` | Dynamic style update to text-combine-upright: none |
| layout_text_combine_test.cc:1224 | StyleToHorizontalWritingMode | behaviour | formalized | `layoutTextCombine_styleToHorizontalWritingMode` | Dynamic writing mode update to horizontal |
| layout_text_combine_test.cc:1258 | StyleToHorizontalWritingModeWithWordBreak | behaviour | formalized | `layoutTextCombine_styleToHorizontalWritingModeWithWordBreak` | Dynamic writing mode update with WBR |
| layout_text_combine_test.cc:1282 | StyleToVerticalWritingMode | behaviour | formalized | `layoutTextCombine_styleToVerticalWritingMode` | Dynamic writing mode update to vertical |
| layout_text_combine_test.cc:1314 | VerticalWritingModeByBR | behaviour | blocked | - | Blocked: model lacks text-combine-upright style change |
| layout_text_combine_test.cc:1329 | VerticalWritingModeByWBR | behaviour | formalized | `layoutTextCombine_verticalWritingModeByWBR` | Writing mode specified on inline WBR does not apply |
| layout_text_combine_test.cc:1344 | WithBidiControl | behaviour | formalized | `layoutTextCombine_withBidiControl` | Text combine with visual bidi ordering |
| layout_text_combine_test.cc:1363 | WithBR | behaviour | formalized | `layoutTextCombine_withBR` | LayoutBR inside text combine container |
| layout_text_combine_test.cc:1385 | WithMarker | behaviour | formalized | `layoutTextCombine_withMarker` | List marker with text combine |
| layout_text_combine_test.cc:1412 | WithOrderedList | behaviour | formalized | `layoutTextCombine_withOrderedList` | Ordered list marker and items with text combine |
| layout_text_combine_test.cc:1431 | WithQuote | behaviour | formalized | `layoutTextCombine_withQuote` | Quotes with text combine |
| layout_text_combine_test.cc:1456 | WithTab | behaviour | formalized | `layoutTextCombine_withTab` | Preserved tab whitespace with text combine |
| layout_text_combine_test.cc:1476 | WithTextIndent | geometry | blocked | - | Blocked: model lacks text-combine-upright text-indent |
| layout_text_combine_test.cc:1493 | WithWordBreak | behaviour | formalized | `layoutTextCombine_withWordBreak` | WBR inside text combine container |
| layout_text_combine_test.cc:1515 | ShouldBeParentOfSvg | internal | internal | - | Svg parent LayoutObject check |
| layout_text_combine_test.cc:1531 | InHorizontal | behaviour | blocked | - | Blocked: model lacks text-combine-upright in horizontal mode |
| layout_text_combine_test.cc:1545 | InVertical | behaviour | formalized | `layoutTextCombine_inVertical` | Text combine in vertical writing mode |
| layout_ruby_base_test.cc:16 | AddChildNoBlockChildren | internal | internal | - | Ruby base anonymous block child insertion |
| layout_ruby_base_test.cc:30 | AddImageNoBlockChildren | internal | internal | - | Ruby base inline child insertion |
| layout_ruby_base_test.cc:52 | AddSpecialWithTableInternalDisplayNoBlockChildren | internal | internal | - | Ruby base table child insertion |
| layout_ruby_base_test.cc:73 | ChangeToRubyNoBlockChildren | internal | internal | - | Ruby base display style mutation |
| layout_ruby_as_block_test.cc:14 | TextCombineCrash | internal | internal | - | Crash regression test for ruby block with text combine |
| list/layout_inline_list_item_test.cc:15 | GetOffsetMappingNoCrash | internal | internal | - | Crash regression test for layout inline list item offset mapping |
| list/layout_inline_list_item_test.cc:41 | OffsetMappingBuilderNoCrash | internal | internal | - | Crash regression test for offset mapping builder |
| list/layout_list_item_test.cc:18 | FindSymbolMarkerLayoutTextWithTextCombine | internal | internal | - | Traversal check for symbol marker text inside text combine |
| list/layout_list_item_test.cc:37 | InsideWithFirstLine | behaviour | formalized | `layoutListItem_insideWithFirstLine` | CSS Lists 3 §3.1 & CSS Pseudo 4 §7.1: Inside list marker retains single child under ::first-line |
| list/list_marker_test.cc:51 | FallbackToTextWhenImagesDisable | behaviour | formalized | `listMarker_fallbackToTextWhenImagesDisable` | CSS Lists 3 §3.2: Image marker falls back to text when images are disabled |
| list/list_marker_test.cc:71 | AddCounterStyle | behaviour | formalized | `listMarker_addCounterStyle` | CSS Counter Styles 3 §2 & §3.1.2: Adding scoped @counter-style rules |
| list/list_marker_test.cc:105 | RemoveCounterStyle | behaviour | formalized | `listMarker_removeCounterStyle` | CSS Counter Styles 3 §2: Removing @counter-style falls back to predefined style |
| list/list_marker_test.cc:135 | OverridePredefinedCounterStyle | behaviour | formalized | `listMarker_overridePredefinedCounterStyle` | CSS Counter Styles 3 §2: Overriding predefined counter style with author rule |
| list/list_marker_test.cc:160 | RemoveOverrideOfPredefinedCounterStyle | behaviour | formalized | `listMarker_removeOverrideOfPredefinedCounterStyle` | CSS Counter Styles 3 §2: Removing author override restores predefined counter style |
| list/list_marker_test.cc:190 | OverrideSameScopeCounterStyle | behaviour | formalized | `listMarker_overrideSameScopeCounterStyle` | CSS Counter Styles 3 §2: Cascading override in same scope |
| list/list_marker_test.cc:220 | RemoveOverrideOfSameScopeCounterStyle | behaviour | formalized | `listMarker_removeOverrideOfSameScopeCounterStyle` | CSS Counter Styles 3 §2: Removing same-scope override unshadows previous rule |
| list/list_marker_test.cc:256 | ModifyShadowDOMWithOwnCounterStyles | behaviour | formalized | `listMarker_modifyShadowDOMWithOwnCounterStyles` | CSS Counter Styles 3 §2 & DOM Standard §4.2.1: Scoped counter style resolution and shadow tree isolation |
| list/list_marker_test.cc:335 | WidthOfSymbolForFontSizeZero | geometry | formalized | `listMarker_widthOfSymbolForFontSizeZero` | CSS Lists 3 §3: Zero font size produces zero width symbol marker |
| list/list_marker_test.cc:349 | InlineMarginsForOutside | geometry | blocked | - | Blocked: model lacks ListMarker::InlineMarginsForOutside |
| geometry/axis_test.cc:14 | StreamOperators | internal | internal | - | Stream operator debugging output |
| geometry/axis_test.cc:72 | LogicalAxesOperators | geometry | blocked | - | Blocked: model lacks bitwise enum operators for LogicalAxes |
| geometry/axis_test.cc:138 | PhysicalAxesOperators | geometry | blocked | - | Blocked: model lacks bitwise enum operators for PhysicalAxes |
| geometry/axis_test.cc:213 | ToPhysicalAxes | geometry | formalized | `axis_toPhysicalAxes` | Converts logical axes to physical axes under horizontal and vertical writing modes |
| geometry/axis_test.cc:239 | ToLogicalAxes | geometry | formalized | `axis_toLogicalAxes` | Converts physical axes to logical axes under horizontal and vertical writing modes |
| geometry/box_edge_test.cc:10 | Construction | geometry | formalized | `boxEdge_properties` | Constructs BoxEdge with offset and size |
| geometry/box_edge_test.cc:16 | End | geometry | formalized | `boxEdge_properties` | Computes BoxEdge end offset as offset + size |
| geometry/box_edge_test.cc:21 | IsEmpty | geometry | formalized | `boxEdge_properties` | Tests whether BoxEdge size is non-positive |
| geometry/box_edge_test.cc:27 | Move | geometry | formalized | `boxEdge_properties` | Shifts BoxEdge offset by positive or negative delta |
| geometry/box_edge_test.cc:38 | Equality | geometry | formalized | `boxEdge_properties` | Tests BoxEdge equality comparison |
| geometry/box_edge_test.cc:46 | MathOperators | geometry | formalized | `boxEdge_properties` | Tests BoxEdge offset addition and subtraction |
| geometry/box_sides_test.cc:14 | LogicalBoxSidesToLineLogical | geometry | formalized | `boxSides_logicalToLineLogical` | Converts logical box sides to line-logical box sides under LTR and RTL |
| geometry/box_sides_test.cc:33 | PhysicalBoxSidesToLogical | geometry | formalized | `boxSides_physicalToLogical` | Converts physical box sides to logical box sides across writing modes and directions |
| geometry/box_strut_test.cc:17 | ConvertPhysicalStrutToLogical | geometry | formalized | `boxStrut_convertPhysicalToLogical` | Converts physical box strut to logical box strut across writing modes and directions |
| geometry/box_strut_test.cc:52 | ConvertLogicalStrutToPhysical | geometry | formalized | `boxStrut_convertLogicalToPhysical` | Roundtrip conversion between logical and physical box struts |
| geometry/box_strut_test.cc:89 | Constructors | geometry | blocked | - | Blocked: model lacks 64-bit saturated LayoutUnit arithmetic |
| geometry/box_strut_test.cc:99 | Enclosing | geometry | blocked | - | Blocked: model lacks floating point OutsetsF conversions |
| geometry/box_strut_test.cc:114 | Unite | geometry | formalized | `boxStrut_unite` | Unites two physical box struts taking maximum along each edge |
| geometry/layout_unit_diffuser_test.cc:17 | ThreeBuckets | geometry | blocked | - | Blocked: model lacks fractional LayoutUnit division remainder |
| geometry/layout_unit_diffuser_test.cc:35 | FourBuckets | geometry | formalized | `layoutUnitDiffuser_buckets` | Diffuses fractional epsilon across 4 buckets using Bresenham stepping |
| geometry/layout_unit_diffuser_test.cc:64 | SevenBuckets | geometry | formalized | `layoutUnitDiffuser_buckets` | Diffuses fractional epsilon across 7 buckets using Bresenham stepping |
| geometry/logical_rect_test.cc:15 | AddOffset | geometry | formalized | `logicalRect_addOffsetAndUnite` | Translates LogicalRect by LogicalOffset |
| geometry/logical_rect_test.cc:56 | Data | geometry | formalized | `logicalRect_addOffsetAndUnite` | Unites logical rectangles computing bounding box |
| geometry/physical_rect_test.cc:17 | AddOffset | geometry | formalized | `physicalRect_operations` | Translates PhysicalRect by offset coordinates |
| geometry/physical_rect_test.cc:58 | Data | geometry | formalized | `physicalRect_operations` | Unites physical rectangles computing bounding box |
| geometry/physical_rect_test.cc:78 | SquaredDistanceTo | geometry | formalized | `physicalRect_operations` | Computes squared Euclidean distance from point to PhysicalRect |
| geometry/physical_rect_test.cc:127 | InclusiveIntersect | geometry | formalized | `physicalRect_operations` | Computes inclusive intersection rectangle of two physical rects |
| geometry/physical_rect_test.cc:146 | IntersectsInclusively | geometry | formalized | `physicalRect_operations` | Tests whether two physical rectangles intersect inclusively |
| geometry/physical_rect_test.cc:191 | ToEnclosingRect | geometry | blocked | - | Blocked: model lacks floating point EnclosingRect |
| geometry/physical_rect_test.cc:243 | EdgesOnPixelBoundaries | geometry | blocked | - | Blocked: model lacks pixel boundary checks |
| geometry/physical_rect_test.cc:281 | ExpandEdgesToPixelBoundaries | geometry | blocked | - | Blocked: model lacks pixel boundary checks |
| geometry/physical_rect_test.cc:335 | InfiniteIntRect | geometry | blocked | - | Blocked: model lacks InfiniteIntRect |
| geometry/static_position_test.cc:331 | Convert | geometry | blocked | - | Blocked: model lacks StaticPosition::Convert |
| geometry/writing_mode_converter_test.cc:15 | ConvertLogicalOffsetToPhysicalOffset | geometry | formalized | `writingModeConverter_toPhysical` | Converts logical offset to physical offset across writing modes and directions |
| geometry/writing_mode_converter_test.cc:73 | ConvertPhysicalOffsetToLogicalOffset | geometry | formalized | `writingModeConverter_toLogical` | Converts physical offset to logical offset across writing modes and directions |
| svg/layout_svg_container_test.cc:19 | TransformAffectsVectorEffect | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_container_test.cc:70 | TransformAffectsVectorEffectNestedSVG | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_container_test.cc:100 | TransformAffectsVectorEffectHiddenContainerAndUse | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_container_test.cc:127 | PatternWithContentVisibility | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_container_test.cc:161 | BoundingBoxesWith3DTransformedChild | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_container_test.cc:180 | MaskCacheClearedOnLastClientRemovedBeforeGCAndDisplayLock | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:18 | DivInForeignObject | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:76 | IframeInForeignObject | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:149 | HitTestZoomedForeignObject | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_foreign_object_test.cc:216 | HitTestViewBoxForeignObject | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_foreign_object_test.cc:247 | HitTestUnderClipPath | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_foreign_object_test.cc:283 | HitTestUnderClippedPositionedForeignObjectDescendant | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_foreign_object_test.cc:317 | HitTestUnderTransformedForeignObjectDescendant | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_foreign_object_test.cc:351 | HitTestUnderScrollingAncestor | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_foreign_object_test.cc:389 | BBoxPropagationZoomed | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_foreign_object_test.cc:411 | SetNeedsCollectInlines | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:424 | SubtreeLayoutCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_foreign_object_test.cc:451 | ZoomChangesInvalidatePaintProperties | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:489 | DisplayLocked | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:507 | LocalToAncestorPoint | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_foreign_object_test.cc:525 | GetBBoxUseCounterForZeroHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_foreign_object_test.cc:545 | GetBBoxUseCounterForZeroWidth | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_foreign_object_test.cc:565 | GetBBoxUseCounterForZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_foreign_object_test.cc:585 | GetBBoxUseCounterForNonZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_image_test.cc:16 | GetBBoxUseCounterForZeroHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_image_test.cc:34 | GetBBoxUseCounterForZeroWidth | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_image_test.cc:52 | GetBBoxUseCounterForZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_image_test.cc:70 | GetBBoxUseCounterForNonZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_inline_test.cc:13 | IsChildAllowed | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_inline_test.cc:25 | LocalToAncestorPoint | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_rect_test.cc:16 | GetBBoxUseCounterForZeroHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_rect_test.cc:34 | GetBBoxUseCounterForZeroWidth | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_rect_test.cc:52 | GetBBoxUseCounterForZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_rect_test.cc:70 | GetBBoxUseCounterForNonZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_root_test.cc:27 | VisualRectMappingWithoutViewportClipWithBorder | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_root_test.cc:54 | VisualOverflowExpandsLayer | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_root_test.cc:74 | VisualRectMappingWithViewportClipAndBorder | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_root_test.cc:101 | RectBasedHitTestPartialOverlap | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_root_test.cc:132 | PaintLayerType | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_root_test.cc:155 | VisualRectMappingWithReferenceFilter | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_shape_test.cc:12 | StrokeBoundingBoxOnEmptyShape | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_shape_test.cc:23 | RectBasedHitTest_CircleEllipse | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_shape_test.cc:77 | RectBasedHitTest_Rect | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_shape_test.cc:137 | RectBasedHitTest_Path | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_text_test.cc:13 | RectBasedHitTest | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_text_test.cc:38 | RectBasedHitTest_RotatedText | behaviour | blocked | - | Blocked: model lacks SVG hit testing |
| svg/layout_svg_text_test.cc:67 | TransformAffectsVectorEffect | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_text_test.cc:96 | AbsoluteQuads | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/layout_svg_text_test.cc:115 | ObjectBoundingBox | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/layout_svg_text_test.cc:136 | SubtreeLayout | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_text_test.cc:161 | WillBeRemovedFromTree | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_viewport_container_test.cc:16 | GetBBoxUseCounterForZeroHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_viewport_container_test.cc:36 | GetBBoxUseCounterForZeroWidth | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_viewport_container_test.cc:56 | GetBBoxUseCounterForZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/layout_svg_viewport_container_test.cc:76 | GetBBoxUseCounterForNonZeroWidthAndHeight | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_hit_test_perftest.cc:84 | HandleMouseMoveEvent | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/svg_hit_test_perftest.cc:105 | IntersectsClipPath | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/svg_layout_support_test.cc:14 | FindClosestLayoutSVGText | behaviour | blocked | - | Blocked: model lacks SVG layout algorithm |
| svg/svg_layout_support_test.cc:35 | VisualRectInAncestorSpaceContainerWithFilter | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/svg_layout_support_test.cc:64 | VisualRectInDocumentWith3DTransform | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/svg_layout_support_test.cc:80 | VisualRectInDocumentUnderSVGRootPerspective | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/svg_layout_support_test.cc:95 | AbsoluteBoundingBoxUnderSVGRootPerspective | geometry | blocked | - | Blocked: model lacks SVG bounding box layout |
| svg/svg_text_layout_algorithm_test.cc:12 | PositionOnPathCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_text_layout_algorithm_test.cc:27 | EmptyTextLengthCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_text_layout_algorithm_test.cc:38 | EmptyTextLengthSpacingAndGlyphsCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_text_layout_algorithm_test.cc:47 | HugeScaleCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_text_layout_algorithm_test.cc:62 | ControlCharCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_text_layout_algorithm_test.cc:70 | FirstLineTextTransformCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| svg/svg_text_layout_attributes_builder_test.cc:13 | TextPathCrash | internal | internal | - | Crash regression / lifecycle plumbing |
| forms/fieldset_layout_algorithm_test.cc:59 | Empty | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:78 | NoLegend | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:100 | Legend | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:124 | SmallLegendLargeBorder | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:150 | LegendOrthogonalWritingMode | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:176 | VerticalLr | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:202 | VerticalRl | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:228 | LegendAutoSize | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:257 | PercentageHeightChild | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:283 | AbsposChild | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:312 | ZeroHeight | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:340 | ZeroMaxHeight | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:372 | PercentHeightQuirks | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:404 | LegendPercentHeightQuirks | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:433 | FieldsetPaddingWithLegend | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:472 | MinMax | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:540 | NoFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:567 | SimpleFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:604 | FragmentationNoPadding | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:645 | FieldsetContentFragmentationAutoHeight | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:708 | FieldsetContentFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:771 | LegendFragmentationAutoHeight | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:821 | LegendFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:871 | LegendAndContentFragmentationAutoHeight | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:937 | LegendAndContentFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1001 | LegendFragmentationWithOverflow | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1052 | LegendAndContentFragmentationNegativeMargin | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1107 | OverflowedLegend | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1151 | OverflowedFieldsetContent | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1224 | BreakInsideAvoid | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1271 | BreakInsideAvoidTallBlock | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1334 | LegendBreakInsideAvoid | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1387 | BreakBeforeAvoid | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1442 | LegendBreakBeforeAvoid | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1494 | BreakAfterAvoid | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1540 | LegendBreakAfterAvoid | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1594 | MarginBottomPastEndOfFragmentainer | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1650 | SmallLegendLargeBorderFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1707 | SmallerLegendLargeBorderFragmentation | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1766 | SmallerLegendLargeBorderFragmentation2 | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/fieldset_layout_algorithm_test.cc:1818 | SmallerLegendLargeBorderWithBreak | geometry | blocked | - | Blocked: model lacks FieldsetLayoutAlgorithm |
| forms/layout_fieldset_test.cc:14 | AddChildWhitespaceCrash | internal | internal | - | Crash regression test |
| forms/layout_fieldset_test.cc:31 | AddChildAnonymousInlineCrash | internal | internal | - | Crash regression test |
| forms/layout_text_control_inner_editor_test.cc:12 | AddChildWithoutTrailingLf | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_inner_editor_test.cc:43 | AddChildWithTrailingLf | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_inner_editor_test.cc:85 | RemoveChildWithoutTrailingLf | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_inner_editor_test.cc:114 | AddChildBeforeTestRenderingHolder | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_inner_editor_test.cc:126 | EnableDynamic | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_single_line_test.cc:13 | VisualOverflowCleared | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:56 | ChangingPseudoSelectionStyleShouldInvalidateSelectionSingle | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:74 | ChangingPseudoSelectionStyleShouldInvalidateSelectionMulti | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:92 | AddingPseudoSelectionStyleShouldInvalidateSelectionSingle | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:109 | AddingPseudoSelectionStyleShouldInvalidateSelectionMulti | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:126 | RemovingPseudoSelectionStyleShouldInvalidateSelectionSingle | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:142 | RemovingPseudoSelectionStyleShouldInvalidateSelectionMulti | behaviour | blocked | - | Blocked: model lacks text control layout |
| forms/layout_text_control_test.cc:158 | HitTestSearchInput | behaviour | blocked | - | Blocked: model lacks text control layout |
| shapes/box_shape_test.cc:82 | zeroRadii | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/box_shape_test.cc:143 | getIntervals | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/ellipse_shape_test.cc:32 | ZeroRadii | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/ellipse_shape_test.cc:41 | ZeroRadiusX | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/ellipse_shape_test.cc:50 | ZeroRadiusY | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/ellipse_shape_test.cc:59 | ZeroRadiiWithMargin | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/ellipse_shape_test.cc:87 | NonZeroRadiiWithMargin | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| shapes/ellipse_shape_test.cc:115 | ShapeMarginLogicalBoundingBoxWithFloatValues | geometry | blocked | - | Blocked: model lacks shape-outside geometry |
| exclusions/exclusion_space_test.cc:92 | Empty | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:122 | LineLayoutOpportunityClampsNonDominantSide | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:169 | SingleExclusion | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:232 | TwoExclusions | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:273 | SolidEdges | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:325 | OverlappingWithShelf | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:373 | InsertBetweenShelves | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:408 | InitialLetterBasic | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:451 | InitialLetterDirectionRight | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:507 | InitialLetterFloatLeft1 | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:560 | InitialLetterFloatLeft2 | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:615 | InitialLetterFloatLeft2ClearLeft | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:672 | InitialLetterFloatLeftAndRight | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:738 | InitialLetterFloatLeftAfterBreak | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:796 | InitialLetterFloatRight2 | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:857 | ZeroInlineSizeOpportunity | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:877 | NegativeInlineSizeOpportunityLeft | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:907 | NegativeInlineSizeOpportunityRight | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:937 | PreInitialization | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:992 | MergeExclusionSpacesNoPreviousExclusions | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:1020 | MergeExclusionSpacesPreviousExclusions | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:1060 | MergeExclusionSpacesNoOutputExclusions | geometry | blocked | - | Blocked: model lacks ExclusionSpace |
| exclusions/exclusion_space_test.cc:1083 | CopyOnWriteNoAllocationOnCopy | internal | internal | - | ExclusionSpace copy-on-write memory optimization |
| exclusions/exclusion_space_test.cc:1162 | CopyOnWriteDisabledFallback | internal | internal | - | ExclusionSpace copy-on-write memory optimization |
| layout_quote_test.cc:40 | Locale | behaviour | formalized | `layoutQuote_locale` | `<q>` element delimiters use language from parent, while quote text uses element language |
| hit_testing_test.cc:87 | OcclusionHitTest | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:111 | OcclusionHitTestSVGTextWithFilterCrash | internal | internal | - | Crash regression test |
| hit_testing_test.cc:136 | HitTestWithCallback | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:205 | OcclusionHitTestWithClipPath | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:253 | OcclusionHitTestWithBorderShapeStrokeMode | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:319 | OcclusionHitTestWithBorderShapeFillMode | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:384 | ScrolledInline | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:421 | ReferenceFilter | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:457 | OcclusionHitTestWith3DTransform | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:495 | OcclusionHitTestWithFlattenedPreserve3DOccluder | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:549 | ShapeWithPerspectiveFunction | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:574 | ShapeUnderSVGRootPerspective | behaviour | blocked | - | Blocked: model lacks hit testing |
| hit_testing_test.cc:592 | ContainerUnderSVGRootPerspective | behaviour | blocked | - | Blocked: model lacks hit testing |
---

## Merge Notes
- Shared types in `LayoutTypes.lean` were left untouched.
- `Inhabited LineInfo` was declared locally in `TestsInline_LineBreaker.lean`.
