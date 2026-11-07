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

---

## Merge Notes
- Shared types in `LayoutTypes.lean` were left untouched.
- `Inhabited LineInfo` was declared locally in `TestsInline_LineBreaker.lean`.
