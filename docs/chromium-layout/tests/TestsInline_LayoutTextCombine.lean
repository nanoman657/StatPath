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

end ChromiumLayout
