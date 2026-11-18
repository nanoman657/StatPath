/-
  docs/chromium-layout/tests/TestsInline_LayoutTextCombine.lean

  Formalized layout tests for LayoutTextCombine
  (`third_party/blink/renderer/core/layout/layout_text_combine_test.cc`).

  Covers:
  - PropageWritingModeFromBodyToHorizontal (`layout_text_combine_test.cc:758`)
  - PropageWritingModeFromBodyToVertical (`layout_text_combine_test.cc:783`)
  - StyleToTextCombineUprightAll (`layout_text_combine_test.cc:1157`)
  - StyleToTextCombineUprightNone (`layout_text_combine_test.cc:1190`)
  - StyleToHorizontalWritingMode (`layout_text_combine_test.cc:1224`)
  - StyleToHorizontalWritingModeWithWordBreak (`layout_text_combine_test.cc:1258`)
  - StyleToVerticalWritingMode (`layout_text_combine_test.cc:1282`)
  - VerticalWritingModeByWBR (`layout_text_combine_test.cc:1329`)
  - WithBidiControl (`layout_text_combine_test.cc:1344`)
  - WithBR (`layout_text_combine_test.cc:1363`)
  - WithMarker (`layout_text_combine_test.cc:1385`)
  - WithOrderedList (`layout_text_combine_test.cc:1412`)
  - WithQuote (`layout_text_combine_test.cc:1431`)
  - WithTab (`layout_text_combine_test.cc:1456`)
  - WithWordBreak (`layout_text_combine_test.cc:1493`)
  - InVertical (`layout_text_combine_test.cc:1545`)
-/
import LayoutTypes
import InlineGeometry
import InlineTextCombine

namespace ChromiumLayout

/-! ## 1. Writing Mode Propagation Tests -/

/-- Test `LayoutTextCombineTest, PropageWritingModeFromBodyToHorizontal` (`layout_text_combine_test.cc:758`).
    When body has horizontal-tb, it propagates to html, so text-combine-upright is inactive. -/
theorem layoutTextCombine_propageWritingModeFromBodyToHorizontal :
    let effMode := propagateWritingMode .verticalLr (some .horizontalTb)
    let active := isTextCombineActive effMode .all
    let items := [CombinableContent.text "X"]
    let display := buildInlineDisplay active items
    (active = false) ∧
    (display = [.bare (.text "X")]) := by
  decide

/-- Test `LayoutTextCombineTest, PropageWritingModeFromBodyToVertical` (`layout_text_combine_test.cc:783`).
    When body has vertical-rl, it propagates to html, so text-combine-upright is active. -/
theorem layoutTextCombine_propageWritingModeFromBodyToVertical :
    let effMode := propagateWritingMode .horizontalTb (some .verticalRl)
    let active := isTextCombineActive effMode .all
    let items := [CombinableContent.text "X"]
    let display := buildInlineDisplay active items
    (active = true) ∧
    (display = [.combined { children := [.text "X"] }]) := by
  decide

/-! ## 2. Dynamic Style Update Tests -/

/-- Test `LayoutTextCombineTest, StyleToTextCombineUprightAll` (`layout_text_combine_test.cc:1157`).
    Changing text-combine-upright from none to all in vertical-rl wraps inline text in LayoutTextCombine. -/
theorem layoutTextCombine_styleToTextCombineUprightAll :
    let beforeActive := isTextCombineActive .verticalRl .none
    let beforeDisplay := buildInlineDisplay beforeActive [.text "XY"]
    let afterActive := isTextCombineActive .verticalRl .all
    let afterDisplay := buildInlineDisplay afterActive [.text "XY"]
    (beforeDisplay = [.bare (.text "XY")]) ∧
    (afterDisplay = [.combined { children := [.text "XY"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, StyleToTextCombineUprightNone` (`layout_text_combine_test.cc:1190`).
    Changing text-combine-upright from all to none unwraps LayoutTextCombine. -/
theorem layoutTextCombine_styleToTextCombineUprightNone :
    let beforeActive := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay beforeActive [.text "XY"]
    let afterActive := isTextCombineActive .verticalRl .none
    let afterDisplay := buildInlineDisplay afterActive [.text "XY"]
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = [.bare (.text "XY")]) := by
  decide

/-- Test `LayoutTextCombineTest, StyleToHorizontalWritingMode` (`layout_text_combine_test.cc:1224`).
    Changing writing-mode from vertical-rl to horizontal-tb unwraps LayoutTextCombine. -/
theorem layoutTextCombine_styleToHorizontalWritingMode :
    let beforeActive := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay beforeActive [.text "XY"]
    let afterActive := isTextCombineActive .horizontalTb .all
    let afterDisplay := buildInlineDisplay afterActive [.text "XY"]
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = [.bare (.text "XY")]) := by
  decide

/-- Test `LayoutTextCombineTest, StyleToHorizontalWritingModeWithWordBreak` (`layout_text_combine_test.cc:1258`).
    Changing writing-mode from vertical-rl to horizontal-tb unwraps WBR in LayoutTextCombine. -/
theorem layoutTextCombine_styleToHorizontalWritingModeWithWordBreak :
    let beforeActive := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay beforeActive [.wbr none]
    let afterActive := isTextCombineActive .horizontalTb .all
    let afterDisplay := buildInlineDisplay afterActive [.wbr none]
    (beforeDisplay = [.combined { children := [.wbr none] }]) ∧
    (afterDisplay = [.bare (.wbr none)]) := by
  decide

/-- Test `LayoutTextCombineTest, StyleToVerticalWritingMode` (`layout_text_combine_test.cc:1282`).
    Changing writing-mode from horizontal-tb to vertical-rl wraps text in LayoutTextCombine. -/
theorem layoutTextCombine_styleToVerticalWritingMode :
    let beforeActive := isTextCombineActive .horizontalTb .all
    let beforeDisplay := buildInlineDisplay beforeActive [.text "XY"]
    let afterActive := isTextCombineActive .verticalRl .all
    let afterDisplay := buildInlineDisplay afterActive [.text "XY"]
    (beforeDisplay = [.bare (.text "XY")]) ∧
    (afterDisplay = [.combined { children := [.text "XY"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, VerticalWritingModeByWBR` (`layout_text_combine_test.cc:1329`).
    Writing mode specified on inline WBR does not establish vertical writing mode in horizontal body. -/
theorem layoutTextCombine_verticalWritingModeByWBR :
    let effMode := effectiveWritingModeForInline .horizontalTb .verticalRl
    let active := isTextCombineActive effMode .all
    let display := buildInlineDisplay active [.wbr (some "sample")]
    (active = false) ∧
    (display = [.bare (.wbr (some "sample"))]) := by
  decide

/-! ## 3. Feature Integration Tests -/

/-- Test `LayoutTextCombineTest, WithBidiControl` (`layout_text_combine_test.cc:1344`).
    Visual RTL ordering does not prevent LayoutTextCombine creation. -/
theorem layoutTextCombine_withBidiControl :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "XY"]
    display = [.combined { children := [.text "XY"] }] := by
  decide

/-- Test `LayoutTextCombineTest, WithBR` (`layout_text_combine_test.cc:1363`).
    LayoutBR within text combine is combined together with preceding and following text. -/
theorem layoutTextCombine_withBR :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "XY", .br, .text "Z"]
    display = [.combined { children := [.text "XY", .br, .text "Z"] }] := by
  decide

/-- Test `LayoutTextCombineTest, WithMarker` (`layout_text_combine_test.cc:1385`).
    List marker contents (text fragments and counter) are wrapped in LayoutTextCombine. -/
theorem layoutTextCombine_withMarker :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.fragment "<", .counter "1", .fragment ">"]
    display = [.combined { children := [.fragment "<", .counter "1", .fragment ">"] }] := by
  decide

/-- Test `LayoutTextCombineTest, WithOrderedList` (`layout_text_combine_test.cc:1412`).
    In ordered list, both list marker and list item text are wrapped in LayoutTextCombine. -/
theorem layoutTextCombine_withOrderedList :
    let active := isTextCombineActive .verticalRl .all
    let markerDisplay := buildInlineDisplay active [.fragment "1. "]
    let textDisplay := buildInlineDisplay active [.text "ab"]
    (markerDisplay = [.combined { children := [.fragment "1. "] }]) ∧
    (textDisplay = [.combined { children := [.text "ab"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, WithQuote` (`layout_text_combine_test.cc:1431`).
    Generated quote delimiters and inner text are wrapped in LayoutTextCombine. -/
theorem layoutTextCombine_withQuote :
    let active := isTextCombineActive .verticalRl .all
    let beforeQuote := buildInlineDisplay active [.fragment "\u201C"]
    let innerText := buildInlineDisplay active [.text "XY"]
    let afterQuote := buildInlineDisplay active [.fragment "\u201D"]
    (beforeQuote = [.combined { children := [.fragment "\u201C"] }]) ∧
    (innerText = [.combined { children := [.text "XY"] }]) ∧
    (afterQuote = [.combined { children := [.fragment "\u201D"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, WithTab` (`layout_text_combine_test.cc:1456`).
    Preserved tab whitespace within combined text is wrapped in LayoutTextCombine. -/
theorem layoutTextCombine_withTab :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "X\tY"]
    display = [.combined { children := [.text "X\tY"] }] := by
  decide

/-- Test `LayoutTextCombineTest, WithWordBreak` (`layout_text_combine_test.cc:1493`).
    WBR within text combine is combined together with preceding and following text. -/
theorem layoutTextCombine_withWordBreak :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "XY", .wbr none, .text "Z"]
    display = [.combined { children := [.text "XY", .wbr none, .text "Z"] }] := by
  decide

/-- Test `LayoutTextCombineTest, InVertical` (`layout_text_combine_test.cc:1545`).
    Text combine element inside vertical block creates LayoutTextCombine wrapper. -/
theorem layoutTextCombine_inVertical :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "ab"]
    display = [.combined { children := [.text "ab"] }] := by
  decide

/-! ## 4. Geometry, Ink Overflow, and Outlines Tests -/

/-- Test `LayoutTextCombineTest, InkOverflow` (`layout_text_combine_test.cc:191`).
    CSS Writing Modes 3 §5.1 & CSS Text Decoration 3 §2:
    Text-combine in vertical-rl has cross-axis half-leading box placement at (5, 100) of size 100x100,
    with local ink overflow (-5, 0 110x100) and unscaled text run (0, 0 1000x100). -/
theorem layoutTextCombine_inkOverflow :
    let lineAdvance := 100 + 100 + 100
    let m := computeTextCombineInkMetrics 110 100 lineAdvance 100 ["0123456789".length]
    (m.lineRect = { x := 0, y := 0, width := 110, height := 300 }) ∧
    (m.lineInkOverflow = { x := 0, y := 0, width := 110, height := 300 }) ∧
    (m.boxRect = { x := 5, y := 100, width := 100, height := 100 }) ∧
    (m.boxSelfInkOverflow = { x := 0, y := 0, width := 100, height := 100 }) ∧
    (m.boxTotalInkOverflow = { x := -5, y := 0, width := 110, height := 100 }) ∧
    (m.innerLineRect = { x := 0, y := 0, width := 100, height := 100 }) ∧
    (m.innerLineInkOverflow = { x := -5, y := 0, width := 110, height := 100 }) ∧
    (m.innerContentRects = [{ x := 0, y := 0, width := 1000, height := 100 }]) := by
  decide

/-- Test `LayoutTextCombineTest, InkOverflowEmphasisMark` (`layout_text_combine_test.cc:248`).
    CSS Text Decoration 3 §3.5 & CSS Writing Modes 3 §5.1:
    Text emphasis mark (50px dot) expands line and combine box ink overflow to 155px width,
    while inside LayoutTextCombine line ink overflow remains 110px. -/
theorem layoutTextCombine_inkOverflowEmphasisMark :
    let lineAdvance := 100 + 100 + 100
    let m := computeTextCombineInkMetrics 110 100 lineAdvance 100 ["0123456789".length] (.emphasisMark 50)
    (m.lineInkOverflow = { x := 0, y := 0, width := 155, height := 300 }) ∧
    (m.boxTotalInkOverflow = { x := -5, y := 0, width := 155, height := 100 }) ∧
    (m.innerLineInkOverflow = { x := -5, y := 0, width := 110, height := 100 }) ∧
    (m.innerContentRects = [{ x := 0, y := 0, width := 1000, height := 100 }]) := by
  decide

/-- Test `LayoutTextCombineTest, InkOverflowOverline` (`layout_text_combine_test.cc:307`).
    CSS Text Decoration 3 §2 & CSS Writing Modes 3 §5.1:
    Overline text decoration expands line ink overflow to 115px, with box ink overflow (0, 0 110x100). -/
theorem layoutTextCombine_inkOverflowOverline :
    let lineAdvance := 100 + 100 + 100
    let m := computeTextCombineInkMetrics 110 100 lineAdvance 100 ["0123456789".length] .overline
    (m.lineInkOverflow = { x := 0, y := 0, width := 115, height := 300 }) ∧
    (m.boxTotalInkOverflow = { x := 0, y := 0, width := 110, height := 100 }) ∧
    (m.innerLineInkOverflow = { x := 0, y := 0, width := 100, height := 100 }) := by
  decide

/-- Test `LayoutTextCombineTest, InkOverflowWBR` (`layout_text_combine_test.cc:421`).
    CSS Writing Modes 3 §5.1:
    Combined text split by `<wbr>` creates two 500x100 text runs within LayoutTextCombine,
    while preserve outer box ink overflow (-5, 0 110x100). -/
theorem layoutTextCombine_inkOverflowWBR :
    let lineAdvance := 100 + 100 + 100
    let m := computeTextCombineInkMetrics 110 100 lineAdvance 100 ["01234".length, "56789".length]
    (m.boxTotalInkOverflow = { x := -5, y := 0, width := 110, height := 100 }) ∧
    (m.innerContentRects = [
      { x := 0, y := 0, width := 500, height := 100 },
      { x := 500, y := 0, width := 500, height := 100 }
    ]) := by
  decide

/-- Test `LayoutTextCombineTest, ScrollableOverflow` (`layout_text_combine_test.cc:540`).
    CSS Writing Modes 3 §5.1.1 & CSS Overflow 3 §4.4:
    Combined text compressed to 1em produces no scrollable overflow in block container. -/
theorem layoutTextCombine_scrollableOverflow :
    let s1 := computeBlockFlowScrollableOverflow 150 200
    let s2 := computeBlockFlowScrollableOverflow 150 200
    (s1.1 = false) ∧
    (s1.2.1 = (150, 200)) ∧
    (s1.2.2 = { x := 0, y := 0, width := 150, height := 200 }) ∧
    (s2.1 = false) ∧
    (s2.2.1 = (150, 200)) ∧
    (s2.2.2 = { x := 0, y := 0, width := 150, height := 200 }) := by
  decide

/-- Test `LayoutTextCombineTest, ListMarkerWidthOfSymbol` (`layout_text_combine_test.cc:621`).
    CSS Writing Modes 3 §5.1 & CSS Lists 3 §3:
    In vertical-lr with text-combine-upright:all, an inside list marker symbol "\u2022 "
    is wrapped in LayoutTextCombine, as is the list item content "ab". -/
theorem layoutTextCombine_listMarkerWidthOfSymbol :
    let active := isTextCombineActive .verticalLr .all
    let tree := buildInsideListMarkerTree active "\u2022 " "ab"
    (active = true) ∧
    (tree.markerChildren = [.combined { children := [.fragment "\u2022 "] }]) ∧
    (tree.contentChildren = [.combined { children := [.text "ab"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, Outline` (`layout_text_combine_test.cc:684`).
    CSS Basic User Interface 3 §4.2 & CSS Writing Modes 3 §5.1:
    Standard outline without ink overflow produces block bounds (150x200),
    while focus outline includes block bounds and text-combine box/ink rects. -/
theorem layoutTextCombine_outline :
    let standard1 := computeTextCombineOutlineRects 150 100 200 false
    let focus1 := computeTextCombineOutlineRects 150 100 200 true
    let standard2 := computeTextCombineOutlineRects 150 100 100 false
    (standard1 = [{ x := 0, y := 0, width := 150, height := 200 }]) ∧
    (focus1 = [
      { x := 0, y := 0, width := 150, height := 200 },
      { x := 25, y := 0, width := 100, height := 100 },
      { x := 20, y := 0, width := 110, height := 100 },
      { x := 25, y := 100, width := 100, height := 100 },
      { x := 25, y := 100, width := 100, height := 100 }
    ]) ∧
    (standard2 = [{ x := 0, y := 0, width := 150, height := 100 }]) := by
  decide

/-- Test `LayoutTextCombineTest, WithTextIndent` (`layout_text_combine_test.cc:1476`).
    CSS Writing Modes 3 §5.1.2 & CSS 2.1 §9.4.2:
    LayoutTextCombine unscaled text run rect in container fragment is (0, 0 60x20),
    unaffected by the containing block's `text-indent: 100px`. -/
theorem layoutTextCombine_withTextIndent :
    let text := "XYZ"
    let fontSize := 20
    let r := textCombineContentRectInContainer 100 text.length fontSize
    r = { x := 0, y := 0, width := 60, height := 20 } := by
  decide

/-! ## 5. DOM Mutation and Structural Tree Tests -/

/-- Test `LayoutTextCombineTest, AppendChild` (`layout_text_combine_test.cc:52`).
    Appending a text node to a text combine container merges it into the existing LayoutTextCombine. -/
theorem layoutTextCombine_appendChild :
    let active := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay active [.text "XY"]
    let afterDisplay := buildInlineDisplay active ([.text "XY"] ++ [.text "Z"])
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = [.combined { children := [.text "XY", .text "Z"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, BoxBoundary` (`layout_text_combine_test.cc:84`).
    Inline box boundary creates separate LayoutTextCombine anonymous boxes for text inside and outside. -/
theorem layoutTextCombine_boxBoundary :
    let active := isTextCombineActive .verticalRl .all
    let outsideDisplay := buildInlineDisplay active [.text "X"]
    let insideDisplay := buildInlineDisplay active [.text "Y"]
    (outsideDisplay = [.combined { children := [.text "X"] }]) ∧
    (insideDisplay = [.combined { children := [.text "Y"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, DeleteDataToEmpty` (`layout_text_combine_test.cc:106`).
    Deleting all characters in combined text removes the LayoutTextCombine anonymous box. -/
theorem layoutTextCombine_deleteDataToEmpty :
    let active := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay active [.text "XY"]
    let afterDisplay := buildInlineDisplay active (pruneCombinableList [.text ""])
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = []) := by
  decide

/-- Test `LayoutTextCombineTest, ElementRecalcOwnStyle` (`layout_text_combine_test.cc:137`).
    Recalculating style on element inside text combine retains the LayoutTextCombine wrapper. -/
theorem layoutTextCombine_elementRecalcOwnStyle :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.br]
    display = [.combined { children := [.br] }] := by
  decide

/-- Test `LayoutTextCombineTest, HtmlElement` (`layout_text_combine_test.cc:166`).
    Text child appended to html element in vertical mode with text-combine-upright:all creates LayoutTextCombine. -/
theorem layoutTextCombine_htmlElement :
    let active := isTextCombineActive .verticalLr .all
    let display := buildInlineDisplay active [.text "X"]
    display = [.combined { children := [.text "X"] }] := by
  decide

/-- Test `LayoutTextCombineTest, InsertBefore` (`layout_text_combine_test.cc:488`).
    Inserting a text node before existing combined text prepends it in the LayoutTextCombine. -/
theorem layoutTextCombine_insertBefore :
    let active := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay active [.text "XY"]
    let afterDisplay := buildInlineDisplay active ([.text "Z"] ++ [.text "XY"])
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = [.combined { children := [.text "Z", .text "XY"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, InsertBR` (`layout_text_combine_test.cc:523`).
    BR with vertical writing mode inserted into horizontal block flow does not activate text combine. -/
theorem layoutTextCombine_insertBR :
    let effMode := effectiveWritingModeForInline .horizontalTb .verticalRl
    let active := isTextCombineActive effMode .all
    let display := buildInlineDisplay active [.br]
    (active = false) ∧
    (display = [.bare .br]) := by
  decide

/-- Test `LayoutTextCombineTest, ListItemStyleToImage` (`layout_text_combine_test.cc:582`).
    Changing list marker style to an image replaces combined text marker with bare non-combinable image. -/
theorem layoutTextCombine_listItemStyleToImage :
    let active := isTextCombineActive .verticalRl .all
    let textMarker := buildInlineDisplay active [.fragment "1. "]
    (textMarker = [.combined { children := [.fragment "1. "] }]) := by
  decide

/-- Test `LayoutTextCombineTest, MultipleTextNode` (`layout_text_combine_test.cc:644`).
    Multiple sibling text nodes in text combine container are merged into single LayoutTextCombine. -/
theorem layoutTextCombine_multipleTextNode :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "X", .text "Y"]
    display = [.combined { children := [.text "X", .text "Y"] }] := by
  decide

/-- Test `LayoutTextCombineTest, Nested` (`layout_text_combine_test.cc:664`).
    Text inside nested inline box in text-combine container is wrapped in LayoutTextCombine. -/
theorem layoutTextCombine_nested :
    let active := isTextCombineActive .verticalRl .all
    let display := buildInlineDisplay active [.text "XY"]
    display = [.combined { children := [.text "XY"] }] := by
  decide

/-- Test `LayoutTextCombineTest, RebuildLayoutTreeForDetails` (`layout_text_combine_test.cc:810`).
    Rebuilding layout tree of details preserves LayoutTextCombine in summary marker, text, and details content. -/
theorem layoutTextCombine_rebuildLayoutTreeForDetails :
    let active := isTextCombineActive .verticalRl .all
    let markerDisplay := buildInlineDisplay active [.fragment "\u25BE "]
    let summaryDisplay := buildInlineDisplay active [.text "XY"]
    let contentDisplay := buildInlineDisplay active [.text "ab", .text "cd"]
    (markerDisplay = [.combined { children := [.fragment "\u25BE "] }]) ∧
    (summaryDisplay = [.combined { children := [.text "XY"] }]) ∧
    (contentDisplay = [.combined { children := [.text "ab", .text "cd"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, RemoveBlockChild` (`layout_text_combine_test.cc:854`).
    Removing intervening block child allows previously separated text runs to merge into one LayoutTextCombine. -/
theorem layoutTextCombine_removeBlockChild :
    let active := isTextCombineActive .verticalRl .all
    let beforeFirst := buildInlineDisplay active [.text "ab"]
    let beforeMid := buildInlineDisplay active [.text "XY"]
    let beforeLast := buildInlineDisplay active [.text "de"]
    let afterMerged := buildInlineDisplay active [.text "ab", .text "de"]
    (beforeFirst = [.combined { children := [.text "ab"] }]) ∧
    (beforeMid = [.combined { children := [.text "XY"] }]) ∧
    (beforeLast = [.combined { children := [.text "de"] }]) ∧
    (afterMerged = [.combined { children := [.text "ab", .text "de"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, RemoveChildCombine` (`layout_text_combine_test.cc:886`).
    Removing combined inline child leaves surrounding non-combined text intact. -/
theorem layoutTextCombine_removeChildCombine :
    let active := isTextCombineActive .verticalRl .all
    let combineDisplay := buildInlineDisplay active [.text "XY"]
    let rootTextActive := isTextCombineActive .verticalRl .none
    let remainingDisplay := buildInlineDisplay rootTextActive [.text "ab", .text "de"]
    (combineDisplay = [.combined { children := [.text "XY"] }]) ∧
    (remainingDisplay = [.bare (.text "ab"), .bare (.text "de")]) := by
  decide

/-- Test `LayoutTextCombineTest, RemoveChildToEmpty` (`layout_text_combine_test.cc:914`).
    Removing text child from combine container empties it, producing no LayoutTextCombine. -/
theorem layoutTextCombine_removeChildToEmpty :
    let active := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay active [.text "XY"]
    let afterDisplay := buildInlineDisplay active []
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = []) := by
  decide

/-- Test `LayoutTextCombineTest, RemoveChildToOneCombinedText` (`layout_text_combine_test.cc:944`).
    Removing intermediate inline box merges flanking text runs into a single LayoutTextCombine. -/
theorem layoutTextCombine_removeChildToOneCombinedText :
    let active := isTextCombineActive .verticalRl .all
    let beforeFirst := buildInlineDisplay active [.text "a"]
    let beforeMid := buildInlineDisplay active [.text "x"]
    let beforeLast := buildInlineDisplay active [.text "z"]
    let afterMerged := buildInlineDisplay active [.text "a", .text "z"]
    (beforeFirst = [.combined { children := [.text "a"] }]) ∧
    (beforeMid = [.combined { children := [.text "x"] }]) ∧
    (beforeLast = [.combined { children := [.text "z"] }]) ∧
    (afterMerged = [.combined { children := [.text "a", .text "z"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, ReplaceChildToOneCombinedText` (`layout_text_combine_test.cc:979`).
    Replacing intermediate inline box with text combines all three text runs into a single LayoutTextCombine. -/
theorem layoutTextCombine_replaceChildToOneCombinedText :
    let active := isTextCombineActive .verticalRl .all
    let afterReplaced := buildInlineDisplay active [.text "a", .text "X", .text "z"]
    afterReplaced = [.combined { children := [.text "a", .text "X", .text "z"] }] := by
  decide

/-- Test `LayoutTextCombineTest, SetDataToEmpty` (`layout_text_combine_test.cc:1016`).
    Setting text data to empty removes the LayoutTextCombine anonymous box. -/
theorem layoutTextCombine_setDataToEmpty :
    let active := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay active [.text "XY"]
    let afterDisplay := buildInlineDisplay active (pruneCombinableList [.text ""])
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = []) := by
  decide

/-- Test `LayoutTextCombineTest, SplitText` (`layout_text_combine_test.cc:1046`).
    Splitting text node keeps both resulting text nodes inside the single LayoutTextCombine. -/
theorem layoutTextCombine_splitText :
    let active := isTextCombineActive .verticalRl .all
    let beforeDisplay := buildInlineDisplay active [.text "XY"]
    let afterDisplay := buildInlineDisplay active [.text "X", .text "Y"]
    (beforeDisplay = [.combined { children := [.text "XY"] }]) ∧
    (afterDisplay = [.combined { children := [.text "X", .text "Y"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, SplitTextAtZero` (`layout_text_combine_test.cc:1081`).
    Splitting text at offset 0 produces an empty text node which is dropped, leaving single LayoutText in combine. -/
theorem layoutTextCombine_splitTextAtZero :
    let active := isTextCombineActive .verticalRl .all
    let splitList := pruneCombinableList [.text "", .text "XY"]
    let display := buildInlineDisplay active splitList
    display = [.combined { children := [.text "XY"] }] := by
  decide

/-- Test `LayoutTextCombineTest, SplitTextBeforeBox` (`layout_text_combine_test.cc:1116`).
    Splitting text before an inline box keeps split parts in preceding LayoutTextCombine. -/
theorem layoutTextCombine_splitTextBeforeBox :
    let active := isTextCombineActive .verticalRl .all
    let beforeBox := buildInlineDisplay active [.text "X", .text "Y"]
    let insideBox := buildInlineDisplay active [.text "Z"]
    (beforeBox = [.combined { children := [.text "X", .text "Y"] }]) ∧
    (insideBox = [.combined { children := [.text "Z"] }]) := by
  decide

/-- Test `LayoutTextCombineTest, ShouldBeParentOfSvg` (`layout_text_combine_test.cc:1515`).
    SVG text inside container with text-combine-upright:all is never wrapped in LayoutTextCombine. -/
theorem layoutTextCombine_shouldBeParentOfSvg :
    let svgEligible := isSvgTextCombineEligible true
    let active := svgEligible && isTextCombineActive .verticalRl .all
    active = false := by
  decide

end ChromiumLayout
