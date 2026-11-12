import BlockScroll

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow

-- The window is 800x600 (scrollbars_test.cc, every row). Each row states whether the body makes a
-- vertical scrollbar (box height 600) and a horizontal one (box width 800) appear, using
-- `needsScrollbarAlong`. Percentages resolve against the window, or the html element at 100%
-- height, which is also 600.

-- scrollbars_test.cc:2343: WideBodyShouldNotHaveScrollbars (799x10 body)
theorem WideBodyShouldNotHaveScrollbars_vectors :
    needsScrollbarAlong true 600 10 = false ∧ needsScrollbarAlong true 800 799 = false := by
  decide

-- scrollbars_test.cc:2367: TallBodyShouldNotHaveScrollbars (10x599 body)
theorem TallBodyShouldNotHaveScrollbars_vectors :
    needsScrollbarAlong true 600 599 = false ∧ needsScrollbarAlong true 800 10 = false := by
  decide

-- scrollbars_test.cc:2392: TallAndWideBodyShouldNotHaveScrollbars (799x599 body)
theorem TallAndWideBodyShouldNotHaveScrollbars_vectors :
    needsScrollbarAlong true 600 599 = false ∧ needsScrollbarAlong true 800 799 = false := by
  decide

-- scrollbars_test.cc:2417: BodySizeEqualWindowSizeShouldNotHaveScrollbars (800x600 body)
theorem BodySizeEqualWindowSizeShouldNotHaveScrollbars_vectors :
    needsScrollbarAlong true 600 600 = false ∧ needsScrollbarAlong true 800 800 = false := by
  decide

-- scrollbars_test.cc:2442: WidePercentageBodyShouldHaveScrollbar (width 101%, height 10px)
theorem WidePercentageBodyShouldHaveScrollbar_vectors :
    needsScrollbarAlong true 600 10 = false ∧
    needsScrollbarAlong true 800 (800 * 101 / 100) = true := by
  decide

-- scrollbars_test.cc:2494: TallPercentageBodyShouldHaveScrollbar (width 10px, height 101%)
theorem TallPercentageBodyShouldHaveScrollbar_vectors :
    needsScrollbarAlong true 600 (600 * 101 / 100) = true ∧
    needsScrollbarAlong true 800 10 = false := by
  decide

-- scrollbars_test.cc:2520: TallPercentageAndWideBodyShouldHaveScrollbar (width 100%, height 101%)
theorem TallPercentageAndWideBodyShouldHaveScrollbar_vectors :
    needsScrollbarAlong true 600 (600 * 101 / 100) = true ∧
    needsScrollbarAlong true 800 (800 * 100 / 100) = false := by
  decide

-- scrollbars_test.cc:2546: TallAndWidePercentageBodyShouldHaveScrollbars (101% both ways)
theorem TallAndWidePercentageBodyShouldHaveScrollbars_vectors :
    needsScrollbarAlong true 600 (600 * 101 / 100) = true ∧
    needsScrollbarAlong true 800 (800 * 101 / 100) = true := by
  decide

-- The gutter rows use 100px boxes with no content, so `auto` shows no scrollbar, and a
-- classic scrollbar is 15px wide (the test's expected value). Each row states the physical
-- reservation (left, right, top, bottom) and the padding-box size along the inline axis.

-- scrollbars_test.cc:5026: ScrollbarGutterWithHorizontalTextAndClassicScrollbars
-- horizontal-tb: `stable` reserves the right edge, `stable both-edges` reserves both.
theorem ScrollbarGutterWithHorizontalTextAndClassicScrollbars_vectors :
    physicalGutter false (gutterInlineEdges false false false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges false false false (needsScrollbarAlong true 100 0) 15)
        = 100 ∧
    physicalGutter false (gutterInlineEdges false true false (needsScrollbarAlong true 100 0) 15)
        = (0, 15, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges false true false (needsScrollbarAlong true 100 0) 15)
        = 85 ∧
    physicalGutter false (gutterInlineEdges false true true (needsScrollbarAlong true 100 0) 15)
        = (15, 15, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges false true true (needsScrollbarAlong true 100 0) 15)
        = 70 := by
  decide

-- scrollbars_test.cc:5090: ScrollbarGutterWithVerticalTextAndClassicScrollbars
-- vertical-rl: the inline axis is vertical, so `stable` reserves the bottom edge.
theorem ScrollbarGutterWithVerticalTextAndClassicScrollbars_vectors :
    physicalGutter true (gutterInlineEdges false false false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges false false false (needsScrollbarAlong true 100 0) 15)
        = 100 ∧
    physicalGutter true (gutterInlineEdges false true false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 15) ∧
    paddingInline 100 (gutterInlineEdges false true false (needsScrollbarAlong true 100 0) 15)
        = 85 ∧
    physicalGutter true (gutterInlineEdges false true true (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 15, 15) ∧
    paddingInline 100 (gutterInlineEdges false true true (needsScrollbarAlong true 100 0) 15)
        = 70 := by
  decide

-- scrollbars_test.cc:5154: ScrollbarGutterWithHorizontalTextAndOverlayScrollbars
-- Overlay scrollbars take no space, so no gutter is reserved in any mode.
theorem ScrollbarGutterWithHorizontalTextAndOverlayScrollbars_vectors :
    physicalGutter false (gutterInlineEdges true false false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges true false false (needsScrollbarAlong true 100 0) 15)
        = 100 ∧
    physicalGutter false (gutterInlineEdges true true false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges true true false (needsScrollbarAlong true 100 0) 15)
        = 100 ∧
    physicalGutter false (gutterInlineEdges true true true (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges true true true (needsScrollbarAlong true 100 0) 15)
        = 100 := by
  decide

-- scrollbars_test.cc:5219: ScrollbarGutterWithVerticalTextAndOverlayScrollbars
-- The vertical-rl version of the overlay case: again no reservation in any mode.
theorem ScrollbarGutterWithVerticalTextAndOverlayScrollbars_vectors :
    physicalGutter true (gutterInlineEdges true false false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges true false false (needsScrollbarAlong true 100 0) 15)
        = 100 ∧
    physicalGutter true (gutterInlineEdges true true false (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges true true false (needsScrollbarAlong true 100 0) 15)
        = 100 ∧
    physicalGutter true (gutterInlineEdges true true true (needsScrollbarAlong true 100 0) 15)
        = (0, 0, 0, 0) ∧
    paddingInline 100 (gutterInlineEdges true true true (needsScrollbarAlong true 100 0) 15)
        = 100 := by
  decide

end TestsBlock
end ChromiumLayout
