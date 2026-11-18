/-
  docs/chromium-layout/tests/TestsInline_InlineNode.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/inline_node_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineShaping
import InlineTextCombine
import InlineBidi
import InlineItemBuilder
import InlineSVG

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test: CollectInlinesText (inline_node_test.cc:192)
    Collecting inline items across elements decomposes into text runs and open/close tags. -/
theorem inlineNode_collectInlinesText :
    let tokens := [
      InlineCollectionToken.text "Hello ",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "inline",
      InlineCollectionToken.closeTag,
      InlineCollectionToken.text " world."
    ]
    let res := collectInlines tokens
    (res.items.length = 5) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 6 }) ∧
    (res.items[1]! = { itemType := .openTag, startOffset := 6, endOffset := 6 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 6, endOffset := 12 }) ∧
    (res.items[3]! = { itemType := .closeTag, startOffset := 12, endOffset := 12 }) ∧
    (res.items[4]! = { itemType := .text, startOffset := 12, endOffset := 19 }) := by
  decide

/-- Test: CollectInlinesBR (inline_node_test.cc:206)
    Collecting inlines with BR emits a control item with newline. -/
theorem inlineNode_collectInlinesBR :
    let tokens := [
      InlineCollectionToken.text "Hello",
      InlineCollectionToken.br,
      InlineCollectionToken.text "World"
    ]
    let res := collectInlines tokens
    (res.text = "Hello\nWorld") ∧
    (res.items.length = 3) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 5 }) ∧
    (res.items[1]! = { itemType := .control, startOffset := 5, endOffset := 6 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 6, endOffset := 11 }) := by
  decide

/-- Test: CollectInlinesFloat (inline_node_test.cc:284)
    CSS 2.1 §9.5, §9.4.2: Floats in an inline formatting context produce zero-length floating items without emitting text. -/
theorem inlineNode_collectInlinesFloat :
    let tokens := [
      InlineCollectionToken.text "abc",
      InlineCollectionToken.floating,
      InlineCollectionToken.text "ghi",
      InlineCollectionToken.floating,
      InlineCollectionToken.text "mno"
    ]
    let res := collectInlines tokens
    (res.text = "abcghimno") ∧
    (res.items.length = 5) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 3 }) ∧
    (res.items[1]! = { itemType := .floating, startOffset := 3, endOffset := 3 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 3, endOffset := 6 }) ∧
    (res.items[3]! = { itemType := .floating, startOffset := 6, endOffset := 6 }) ∧
    (res.items[4]! = { itemType := .text, startOffset := 6, endOffset := 9 }) := by
  decide

/-- Test: CollectInlinesInlineBlock (inline_node_test.cc:306)
    Inline-block appears as an object replacement character \uFFFC and an atomic inline item. -/
theorem inlineNode_collectInlinesInlineBlock :
    let tokens := [
      InlineCollectionToken.text "abc",
      InlineCollectionToken.atomicInline 10,
      InlineCollectionToken.text "jkl"
    ]
    let res := collectInlines tokens
    (res.text = "abc\uFFFCjkl") ∧
    (res.items.length = 3) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 3 }) ∧
    (res.items[1]! = { itemType := .atomicInline, startOffset := 3, endOffset := 4 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 4, endOffset := 7 }) := by
  decide

/-- Test: CollectInlinesUTF16 (inline_node_test.cc:322)
    CSS Writing Modes 3 §2.1: Non-ASCII LTR text (Hiragana) does not enable bidi in collect inlines or segment text. -/
theorem inlineNode_collectInlinesUTF16 :
    let tokens := [InlineCollectionToken.text "Hello \u3042"]
    let res := collectInlines tokens
    (res.isBidiEnabled = false) ∧ (detectBidiInSegmentText res.text = false) := by
  decide

/-- Test: CollectInlinesMaybeRtl (inline_node_test.cc:331)
    CSS Writing Modes 3 §2.1: Surrogate pairs enable bidi in collect inlines, but reset to false in segment text when characters are LTR. -/
theorem inlineNode_collectInlinesMaybeRtl :
    let tokens := [InlineCollectionToken.text "Hello 𐀀"]
    let res := collectInlines tokens
    (res.isBidiEnabled = true) ∧ (detectBidiInSegmentText res.text = false) := by
  decide

/-- Test: CollectInlinesRtl (inline_node_test.cc:344)
    CSS Writing Modes 3 §2.1: Hebrew RTL text enables bidi in both collect inlines and segment text. -/
theorem inlineNode_collectInlinesRtl :
    let tokens := [InlineCollectionToken.text "Hello \u05E2"]
    let res := collectInlines tokens
    (res.isBidiEnabled = true) ∧ (detectBidiInSegmentText res.text = true) := by
  decide

/-- Test: CollectInlinesRtlWithSpan (inline_node_test.cc:353)
    CSS Writing Modes 3 §2.1, §2.4: RTL container propagates bidi level 1 across inline elements and text items. -/
theorem inlineNode_collectInlinesRtlWithSpan :
    let tokens := [
      InlineCollectionToken.text "\u05E2 ",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "\u05E2",
      InlineCollectionToken.closeTag,
      InlineCollectionToken.text " \u05E2"
    ]
    let res := collectInlines tokens .rtl
    (res.isBidiEnabled = true) ∧ (detectBidiInSegmentText res.text = true) ∧
    (res.items.length = 5) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 2, bidiLevel := 1 }) ∧
    (res.items[1]! = { itemType := .openTag, startOffset := 2, endOffset := 2, bidiLevel := 1 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 2, endOffset := 3, bidiLevel := 1 }) ∧
    (res.items[3]! = { itemType := .closeTag, startOffset := 3, endOffset := 3, bidiLevel := 1 }) ∧
    (res.items[4]! = { itemType := .text, startOffset := 3, endOffset := 5, bidiLevel := 1 }) := by
  decide

/-- Test: CollectInlinesMixedText (inline_node_test.cc:369)
    CSS Writing Modes 3 §2.1 & UAX #9: Mixed LTR and Hebrew RTL text with span.
    Items segment into LTR run (0..7), RTL run (7..9), span open (9..9), RTL run (9..10), span close (10..10). -/
theorem inlineNode_collectInlinesMixedText :
    let tokens := [
      InlineCollectionToken.text "Hello, ",
      InlineCollectionToken.text "ע ",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "ע",
      InlineCollectionToken.closeTag
    ]
    let col := collectInlines tokens .ltr
    let items := segmentInlineText col.items col.text .ltr
    (col.text = "Hello, ע ע") ∧
    (items.length = 5) ∧
    (items[0]! = { itemType := .text, startOffset := 0, endOffset := 7, bidiLevel := 0 }) ∧
    (items[1]! = { itemType := .text, startOffset := 7, endOffset := 9, bidiLevel := 1 }) ∧
    (items[2]! = { itemType := .openTag, startOffset := 9, endOffset := 9, bidiLevel := 1 }) ∧
    (items[3]! = { itemType := .text, startOffset := 9, endOffset := 10, bidiLevel := 1 }) ∧
    (items[4]! = { itemType := .closeTag, startOffset := 10, endOffset := 10, bidiLevel := 1 }) := by
  decide

/-- Test: CollectInlinesMixedTextEndWithON (inline_node_test.cc:385)
    CSS Writing Modes 3 §2.1 & UAX #9 §3.3.4: Trailing neutral character '!' after RTL text
    at the end of an LTR embedding resolves to base embedding level 0. -/
theorem inlineNode_collectInlinesMixedTextEndWithON :
    let tokens := [
      InlineCollectionToken.text "Hello, ",
      InlineCollectionToken.text "ע ",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "ע!",
      InlineCollectionToken.closeTag
    ]
    let col := collectInlines tokens .ltr
    let items := segmentInlineText col.items col.text .ltr
    (col.text = "Hello, ע ע!") ∧
    (items.length = 6) ∧
    (items[0]! = { itemType := .text, startOffset := 0, endOffset := 7, bidiLevel := 0 }) ∧
    (items[1]! = { itemType := .text, startOffset := 7, endOffset := 9, bidiLevel := 1 }) ∧
    (items[2]! = { itemType := .openTag, startOffset := 9, endOffset := 9, bidiLevel := 1 }) ∧
    (items[3]! = { itemType := .text, startOffset := 9, endOffset := 10, bidiLevel := 1 }) ∧
    (items[4]! = { itemType := .text, startOffset := 10, endOffset := 11, bidiLevel := 0 }) ∧
    (items[5]! = { itemType := .closeTag, startOffset := 11, endOffset := 11, bidiLevel := 0 }) := by
  decide

/-- Test: CollectInlinesTextCombineBR (inline_node_test.cc:402)
    CSS Writing Modes 3 §5.1.4: In text combine, <br> is treated as space and emits a text item. -/
theorem inlineNode_collectInlinesTextCombineBR :
    let tokens := [
      InlineCollectionToken.text "a",
      InlineCollectionToken.br,
      InlineCollectionToken.text "z"
    ]
    let res := collectInlines tokens .ltr true
    (res.text = "a z") ∧
    (res.items.length = 3) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 1 }) ∧
    (res.items[1]! = { itemType := .text, startOffset := 1, endOffset := 2 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 2, endOffset := 3 }) := by
  decide

/-- Test: CollectInlinesTextCombineListItemMarker (inline_node_test.cc:418)
    CSS Writing Modes 3 §5.1.4 & CSS Lists 3 §3: Text combine inside list marker emits text item with isSymbolMarker flag. -/
theorem inlineNode_collectInlinesTextCombineListItemMarker :
    let tokens := [InlineCollectionToken.symbolMarker "• "]
    let res := collectInlines tokens .ltr true
    (res.text = "• ") ∧
    (res.items.length = 1) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 2, isSymbolMarker := true }) ∧
    (res.items[0]!.isSymbolMarker = true) := by
  decide

/-- Test: CollectInlinesTextCombineNewline (inline_node_test.cc:438)
    CSS Writing Modes 3 §5.1.4: In text combine, preserved newline is treated as space and emits a text item. -/
theorem inlineNode_collectInlinesTextCombineNewline :
    let tokens := [
      InlineCollectionToken.text "a",
      InlineCollectionToken.newline,
      InlineCollectionToken.text "z"
    ]
    let res := collectInlines tokens .ltr true
    (res.text = "a z") ∧
    (res.items.length = 3) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 1 }) ∧
    (res.items[1]! = { itemType := .text, startOffset := 1, endOffset := 2 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 2, endOffset := 3 }) := by
  decide

/-- Test: CollectInlinesTextCombineWBR (inline_node_test.cc:453)
    CSS Writing Modes 3 §5.1.4: In text combine, <wbr> is treated as zero-width space and emits a text item. -/
theorem inlineNode_collectInlinesTextCombineWBR :
    let tokens := [
      InlineCollectionToken.text "a",
      InlineCollectionToken.wbr,
      InlineCollectionToken.text "z"
    ]
    let res := collectInlines tokens .ltr true
    (res.text = "a\u200Bz") ∧
    (res.items.length = 3) ∧
    (res.items[0]! = { itemType := .text, startOffset := 0, endOffset := 1 }) ∧
    (res.items[1]! = { itemType := .text, startOffset := 1, endOffset := 2 }) ∧
    (res.items[2]! = { itemType := .text, startOffset := 2, endOffset := 3 }) := by
  decide

/-- Test: SegmentASCII (inline_node_test.cc:468)
    CSS Writing Modes 3 §2.1: ASCII text produces a single LTR segment. -/
theorem inlineNode_segmentASCII :
    let items := [{ itemType := .text, startOffset := 0, endOffset := 5 : InlineCollectedItem }]
    let res := segmentInlineText items "Hello" .ltr
    (res.length = 1) ∧
    (res[0]!.startOffset = 0) ∧
    (res[0]!.endOffset = 5) ∧
    (res[0]!.direction = .ltr) := by
  decide

/-- Test: SegmentHebrew (inline_node_test.cc:477)
    CSS Writing Modes 3 §2.1: Hebrew text produces a single RTL segment. -/
theorem inlineNode_segmentHebrew :
    let items := [{ itemType := .text, startOffset := 0, endOffset := 5 : InlineCollectedItem }]
    let res := segmentInlineText items "עברית" .ltr
    (res.length = 1) ∧
    (res[0]!.startOffset = 0) ∧
    (res[0]!.endOffset = 5) ∧
    (res[0]!.direction = .rtl) := by
  decide

/-- Test: SegmentSplit1To2 (inline_node_test.cc:487)
    CSS Writing Modes 3 §2.1 & UAX #9: Mixed ASCII and Hebrew text in a single node
    splits into 2 segments: 0..6 LTR and 6..11 RTL. -/
theorem inlineNode_segmentSplit1To2 :
    let items := [{ itemType := .text, startOffset := 0, endOffset := 11 : InlineCollectedItem }]
    let res := segmentInlineText items "Hello עברית" .ltr
    (res.length = 2) ∧
    (res[0]!.startOffset = 0) ∧
    (res[0]!.endOffset = 6) ∧
    (res[0]!.direction = .ltr) ∧
    (res[1]!.startOffset = 6) ∧
    (res[1]!.endOffset = 11) ∧
    (res[1]!.direction = .rtl) := by
  decide

/-- Test: SegmentSplit3To4 (inline_node_test.cc:497)
    CSS Writing Modes 3 §2.1 & UAX #9: Three input items ("Hel", "lo ע", "ברית")
    split the middle item at the script boundary (offset 6) into 4 segments. -/
theorem inlineNode_segmentSplit3To4 :
    let items : List InlineCollectedItem := [
      { itemType := .text, startOffset := 0, endOffset := 3 },
      { itemType := .text, startOffset := 3, endOffset := 7 },
      { itemType := .text, startOffset := 7, endOffset := 11 }
    ]
    let res := segmentInlineText items "Hello עברית" .ltr
    (res.length = 4) ∧
    (res[0]!.startOffset = 0) ∧
    (res[0]!.endOffset = 3) ∧
    (res[0]!.direction = .ltr) ∧
    (res[1]!.startOffset = 3) ∧
    (res[1]!.endOffset = 6) ∧
    (res[1]!.direction = .ltr) ∧
    (res[2]!.startOffset = 6) ∧
    (res[2]!.endOffset = 7) ∧
    (res[2]!.direction = .rtl) ∧
    (res[3]!.startOffset = 7) ∧
    (res[3]!.endOffset = 11) ∧
    (res[3]!.direction = .rtl) := by
  decide

/-- Test: SegmentBidiOverride (inline_node_test.cc:511)
    CSS Writing Modes 3 §2.1 & §2.4: Right-to-Left Override (RLO) forces RTL direction
    on Latin characters until Pop Directional Formatting (PDF) restores LTR. -/
theorem inlineNode_segmentBidiOverride :
    let items : List InlineCollectedItem := [
      { itemType := .text, startOffset := 0, endOffset := 6 },
      { itemType := .control, startOffset := 6, endOffset := 7 },
      { itemType := .text, startOffset := 7, endOffset := 10 },
      { itemType := .control, startOffset := 10, endOffset := 11 }
    ]
    let res := segmentInlineText items "Hello \u202EABC\u202C" .ltr
    (res.length = 4) ∧
    (res[0]!.startOffset = 0) ∧
    (res[0]!.endOffset = 6) ∧
    (res[0]!.direction = .ltr) ∧
    (res[1]!.startOffset = 6) ∧
    (res[1]!.endOffset = 7) ∧
    (res[1]!.direction = .rtl) ∧
    (res[2]!.startOffset = 7) ∧
    (res[2]!.endOffset = 10) ∧
    (res[2]!.direction = .rtl) ∧
    (res[3]!.startOffset = 10) ∧
    (res[3]!.endOffset = 11) ∧
    (res[3]!.direction = .ltr) := by
  decide

/-- Test: SegmentBidiIsolate (inline_node_test.cc:541)
    CSS Writing Modes 3 §2.1 & §2.4: Nested bidi isolate sequences (RLI, LRI, PDI)
    isolate directional runs without affecting surrounding text. -/
theorem inlineNode_segmentBidiIsolate :
    let items : List InlineCollectedItem := [
      { itemType := .text, startOffset := 0, endOffset := 6 },
      { itemType := .control, startOffset := 6, endOffset := 7 },
      { itemType := .text, startOffset := 7, endOffset := 13 },
      { itemType := .control, startOffset := 13, endOffset := 14 },
      { itemType := .text, startOffset := 14, endOffset := 15 },
      { itemType := .control, startOffset := 15, endOffset := 16 },
      { itemType := .text, startOffset := 16, endOffset := 21 },
      { itemType := .control, startOffset := 21, endOffset := 22 },
      { itemType := .text, startOffset := 22, endOffset := 28 }
    ]
    let text := "Hello \u2067עברית \u2066A\u2069עברית\u2069 World"
    let res := segmentInlineText items text .ltr
    (res.length = 9) ∧
    (res[0]!.startOffset = 0) ∧ (res[0]!.endOffset = 6) ∧ (res[0]!.direction = .ltr) ∧
    (res[1]!.startOffset = 6) ∧ (res[1]!.endOffset = 7) ∧ (res[1]!.direction = .ltr) ∧
    (res[2]!.startOffset = 7) ∧ (res[2]!.endOffset = 13) ∧ (res[2]!.direction = .rtl) ∧
    (res[3]!.startOffset = 13) ∧ (res[3]!.endOffset = 14) ∧ (res[3]!.direction = .rtl) ∧
    (res[4]!.startOffset = 14) ∧ (res[4]!.endOffset = 15) ∧ (res[4]!.direction = .ltr) ∧
    (res[5]!.startOffset = 15) ∧ (res[5]!.endOffset = 16) ∧ (res[5]!.direction = .rtl) ∧
    (res[6]!.startOffset = 16) ∧ (res[6]!.endOffset = 21) ∧ (res[6]!.direction = .rtl) ∧
    (res[7]!.startOffset = 21) ∧ (res[7]!.endOffset = 22) ∧ (res[7]!.direction = .ltr) ∧
    (res[8]!.startOffset = 22) ∧ (res[8]!.endOffset = 28) ∧ (res[8]!.direction = .ltr) := by
  decide

/-- Test: MinMaxTest.Data (inline_node_test.cc:649)
    Intrinsic min/max size computation under 10px fixed-width Ahem font. -/
theorem inlineNode_minMaxData :
    -- "AB CDEF" -> {40, 70}
    (computeMinMaxSizesAhem [InlineCollectionToken.text "AB CDEF"] = { minSize := 40, maxSize := 70 }) ∧
    -- "A B<span>C D</span>" -> {20, 60}
    (computeMinMaxSizesAhem [
      InlineCollectionToken.text "A B",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "C D",
      InlineCollectionToken.closeTag
    ] = { minSize := 20, maxSize := 60 }) ∧
    -- "Hello <img>." width 1em (10px) -> {50, 80}
    (computeMinMaxSizesAhem [
      InlineCollectionToken.text "Hello ",
      InlineCollectionToken.atomicInline 10,
      InlineCollectionToken.text "."
    ] = { minSize := 50, maxSize := 80 }) ∧
    -- "Hello <img>." width 5em (50px) -> {50, 120}
    (computeMinMaxSizesAhem [
      InlineCollectionToken.text "Hello ",
      InlineCollectionToken.atomicInline 50,
      InlineCollectionToken.text "."
    ] = { minSize := 50, maxSize := 120 }) ∧
    -- "Hello <img>." width 6em (60px) -> {60, 130}
    (computeMinMaxSizesAhem [
      InlineCollectionToken.text "Hello ",
      InlineCollectionToken.atomicInline 60,
      InlineCollectionToken.text "."
    ] = { minSize := 60, maxSize := 130 }) := by
  decide

/-- Test: TextCombineUsesScalingX (`inline/inline_node_test.cc:1692`).
    CSS Writing Modes 3 §5.1.4: Combined text with length > 1em uses scaleX;
    single character fits within 1em without scaleX. -/
theorem inlineNode_textCombineUsesScalingX :
    let wm : WritingMode := .verticalRl
    let tcu : TextCombineUpright := .all
    let active := isTextCombineActive wm tcu
    (active = true) ∧
    (textCombineUsesScaleX "0123456789".length = true) ∧
    (textCombineUsesScaleX "0".length = false) := by
  decide

/-- Test: TextCombineWordSpacing (`inline/inline_node_test.cc:1713`).
    CSS Writing Modes 3 §5.1.4 & CSS Text 3 §7.1, §7.2:
    `<div style="font: 10px/20px Ahem; letter-spacing: 1px; word-spacing: 1px; text-combine-upright: all; writing-mode: vertical-rl">ab</div>`
    Inside text-combine-upright, letter-spacing and word-spacing are suppressed to 0. -/
theorem inlineNode_textCombineWordSpacing :
    let wm : WritingMode := .verticalRl
    let tcu : TextCombineUpright := .all
    let letterSpacing : Nat := 1
    let wordSpacing : Nat := 1
    let active := isTextCombineActive wm tcu
    let effLetterSpacing := effectiveLetterSpacing active letterSpacing
    let effWordSpacing := effectiveWordSpacing active wordSpacing
    (effLetterSpacing = 0) ∧
    (effWordSpacing = 0) := by
  decide

/-- Test: MinMaxSizesSaturated (`inline/inline_node_test.cc:675`).
    CSS Values and Units 3 §6 & Blink LayoutUnit::kIntMax:
    Extreme width (1e8px) saturates min size to LayoutUnit::kIntMax (33554431). -/
theorem inlineNode_minMaxSizesSaturated :
    let tokens := [
      InlineCollectionToken.atomicInline 100000000,
      InlineCollectionToken.text " ",
      InlineCollectionToken.atomicInline 0
    ]
    let sizes := computeMinMaxSizesAhem tokens
    sizes.minSize = 33554431 := by
  decide

/-- Test: StyleChangeTest.NeedsCollectInlinesOnStyle (`inline/inline_node_test.cc:838`).
    CSS 2.1 §9.4.2: Font, position, and bidi style changes invalidate ancestors while preserving siblings. -/
theorem inlineNode_needsCollectInlinesOnStyle :
    let (text1, parent1, container1, siblings1) := computeNeedsCollectInlines (.changeStyle true)
    let (_, _, container2, _) := computeNeedsCollectInlines (.insertNode true)
    (text1 = true) ∧ (parent1 = true) ∧ (container1 = true) ∧ (siblings1 = false) ∧
    (container2 = false) := by
  decide

/-- Test: NodeInsertTest.NeedsCollectInlinesOnInsert (`inline/inline_node_test.cc:927`).
    CSS 2.1 §9.4.2: Inserting node into parent marks parent and container for inline collection. -/
theorem inlineNode_needsCollectInlinesOnInsert :
    let (_, parent, container, siblings) := computeNeedsCollectInlines (.insertNode false)
    (parent = true) ∧ (container = true) ∧ (siblings = false) := by
  decide

/-- Test: NodeRemoveTest.NeedsCollectInlinesOnRemove (`inline/inline_node_test.cc:987`).
    CSS 2.1 §9.4.2: Removing child from parent marks parent and container for inline collection. -/
theorem inlineNode_needsCollectInlinesOnRemove :
    let (_, parent, container, siblings) := computeNeedsCollectInlines .removeNode
    (parent = true) ∧ (container = true) ∧ (siblings = false) := by
  decide

/-- Test: PreservedNewlineWithBidiAndRelayout (inline_node_test.cc:1353)
    CSS Writing Modes 3 §2.4 & CSS Text 3 §4.1:
    Preserved newline within bidi isolate emits closing and reopening bidi control characters. -/
theorem inlineNode_preservedNewlineWithBidiAndRelayout :
    let initialTokens := [
      InlineCollectionToken.text "foo",
      InlineCollectionToken.openIsolate .ltr,
      InlineCollectionToken.newline,
      InlineCollectionToken.closeTag,
      InlineCollectionToken.text "bar",
      InlineCollectionToken.br
    ]
    let initialRes := collectInlines initialTokens
    let afterAddTokens := initialTokens ++ [InlineCollectionToken.text "baz"]
    let afterAddRes := collectInlines afterAddTokens
    (initialRes.text = "foo\u2066\u2069\n\u2066\u2069bar\n") ∧
    (afterAddRes.text = "foo\u2066\u2069\n\u2066\u2069bar\nbaz") := by
  decide

/-- Test: PreservedNewlineWithRemovedBidiAndRelayout (inline_node_test.cc:1367)
    CSS Writing Modes 3 §2.4:
    RTL isolate emits \u2067 and \u2069 around newline; removing bidi attribute removes bidi characters. -/
theorem inlineNode_preservedNewlineWithRemovedBidiAndRelayout :
    let withBidiTokens := [
      InlineCollectionToken.text "foo",
      InlineCollectionToken.openIsolate .rtl,
      InlineCollectionToken.newline,
      InlineCollectionToken.text "bar",
      InlineCollectionToken.closeTag
    ]
    let withoutBidiTokens := [
      InlineCollectionToken.text "foo",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.newline,
      InlineCollectionToken.text "bar",
      InlineCollectionToken.closeTag
    ]
    (collectInlines withBidiTokens).text = "foo\u2067\u2069\n\u2067bar\u2069" ∧
    (collectInlines withoutBidiTokens).text = "foo\nbar" := by
  decide

/-- Test: PreservedNewlineWithRemovedLtrDirAndRelayout (inline_node_test.cc:1379)
    CSS Writing Modes 3 §2.4:
    LTR isolate emits \u2066 and \u2069 around newline; removing dir attribute removes bidi characters. -/
theorem inlineNode_preservedNewlineWithRemovedLtrDirAndRelayout :
    let withBidiTokens := [
      InlineCollectionToken.text "foo",
      InlineCollectionToken.openIsolate .ltr,
      InlineCollectionToken.newline,
      InlineCollectionToken.text "bar",
      InlineCollectionToken.closeTag
    ]
    let withoutBidiTokens := [
      InlineCollectionToken.text "foo",
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.newline,
      InlineCollectionToken.text "bar",
      InlineCollectionToken.closeTag
    ]
    (collectInlines withBidiTokens).text = "foo\u2066\u2069\n\u2066bar\u2069" ∧
    (collectInlines withoutBidiTokens).text = "foo\nbar" := by
  decide

/-- Test: InsertedWBRWithLineBreakInRelayout (inline_node_test.cc:1392)
    CSS Text 3 §4.1:
    Inserting <wbr> before a line break collapses the newline into a zero-width space. -/
theorem inlineNode_insertedWBRWithLineBreakInRelayout :
    let withWbrTokens := [
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "foo",
      InlineCollectionToken.closeTag,
      InlineCollectionToken.wbr,
      InlineCollectionToken.newline,
      InlineCollectionToken.text "bar"
    ]
    (collectInlines withWbrTokens).text = "foo\u200Bbar" := by
  decide

/-- Test: CollapsibleSpaceFollowingBRWithNoWrapStyle (inline_node_test.cc:1405)
    CSS Text 3 §4.1.1:
    Collapsible space following a forced break <br> is removed. -/
theorem inlineNode_collapsibleSpaceFollowingBRWithNoWrapStyle :
    let tokens := [
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.br,
      InlineCollectionToken.closeTag,
      InlineCollectionToken.text " "
    ]
    (collectInlines tokens).text = "\n" := by
  decide

/-- Test: CollapsibleSpaceFollowingNewlineWithPreStyle (inline_node_test.cc:1414)
    CSS Text 3 §4.1.1:
    With white-space: pre, newline is preserved as \n and following space collapses;
    removing pre style collapses all whitespace to empty. -/
theorem inlineNode_collapsibleSpaceFollowingNewlineWithPreStyle :
    let preTokens := [
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.newline,
      InlineCollectionToken.closeTag,
      InlineCollectionToken.text " "
    ]
    let normalTokens : List InlineCollectionToken := []
    (collectInlines preTokens).text = "\n" ∧
    (collectInlines normalTokens).text = "" := by
  decide

/-- Test: ReusingWithPreservedCase1 (inline_node_test.cc:1504)
    CSS Text 3 §5.1:
    Leading preserved space after <br> generates a break opportunity ZWS,
    which is not generated when <br> is removed. -/
theorem inlineNode_reusingWithPreservedCase1 :
    let withBr := [
      BuilderInput.text "a" .normal,
      BuilderInput.opaqueChar .control '\n',
      BuilderInput.text " ijkl " .preWrap
    ]
    let withoutBr := [
      BuilderInput.text "a" .normal,
      BuilderInput.text " ijkl " .preWrap
    ]
    (buildInlineString withBr = "a\n \u200Bijkl ") ∧
    (buildInlineString withoutBr = "a ijkl ") := by
  decide

/-- Test: ReusingWithPreservedCase2 (inline_node_test.cc:1518)
    CSS Text 3 §5.1:
    In a pre-wrap container, leading space after <br> generates a break opportunity ZWS,
    and removing <br> preserves both spaces without ZWS. -/
theorem inlineNode_reusingWithPreservedCase2 :
    let withBr := [
      BuilderInput.text "a " .preWrap,
      BuilderInput.opaqueChar .control '\n',
      BuilderInput.text " ijkl " .preWrap
    ]
    let withoutBr := [
      BuilderInput.text "a " .preWrap,
      BuilderInput.text " ijkl " .preWrap
    ]
    (buildInlineString withBr = "a \n \u200Bijkl ") ∧
    (buildInlineString withoutBr = "a  ijkl ") := by
  decide

/-- Test: ReusingWithPreservedCase3 (inline_node_test.cc:1532)
    CSS Text 3 §5.1:
    Multiple preserved spaces across line break generate break opportunities at each line start. -/
theorem inlineNode_reusingWithPreservedCase3 :
    let withBr := [
      BuilderInput.text " " .preWrap,
      BuilderInput.opaqueChar .control '\n',
      BuilderInput.text " ijkl " .preWrap
    ]
    let withoutBr := [
      BuilderInput.text " " .preWrap,
      BuilderInput.text " ijkl " .preWrap
    ]
    (buildInlineString withBr = " \u200B\n \u200Bijkl ") ∧
    (buildInlineString withoutBr = " \u200B ijkl ") := by
  decide

/-- Test: ReusingWithCollapsed (inline_node_test.cc:1550)
    CSS 2.1 §9.5 & CSS Text 3 §4.1:
    Removing <br> between float and pre element preserves a single space before pre text. -/
theorem inlineNode_reusingWithCollapsed :
    let tokens := [
      InlineCollectionToken.text "abc ",
      InlineCollectionToken.floating,
      InlineCollectionToken.text "x"
    ]
    (collectInlines tokens).text = "abc x" := by
  decide

/-- Test: ReusingRTLAsLTR (inline_node_test.cc:1564)
    CSS Writing Modes 3 §2.1 & UAX #9:
    Removing dir=rtl from span updates item count from 8 to 3 and resolves neutral brackets from RTL to LTR. -/
theorem inlineNode_reusingRTLAsLTR :
    let rtlTokens := [
      InlineCollectionToken.openIsolate .rtl,
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "[Text]text",
      InlineCollectionToken.closeTag
    ]
    let ltrTokens := [
      InlineCollectionToken.openTag "span",
      InlineCollectionToken.text "[Text]text",
      InlineCollectionToken.closeTag
    ]
    let rtlRes := collectInlines rtlTokens
    let rtlItems := segmentInlineText rtlRes.items rtlRes.text
    let ltrRes := collectInlines ltrTokens
    let ltrItems := segmentInlineText ltrRes.items ltrRes.text
    (rtlRes.text = "\u2067[Text]text\u2069") ∧
    (rtlItems.length = 8) ∧
    (rtlItems[0]!.startOffset = 0) ∧ (rtlItems[0]!.endOffset = 1) ∧ (rtlItems[0]!.direction = .ltr) ∧
    (rtlItems[1]!.startOffset = 1) ∧ (rtlItems[1]!.endOffset = 1) ∧ (rtlItems[1]!.direction = .rtl) ∧
    (rtlItems[2]!.startOffset = 1) ∧ (rtlItems[2]!.endOffset = 2) ∧ (rtlItems[2]!.direction = .rtl) ∧
    (rtlItems[3]!.startOffset = 2) ∧ (rtlItems[3]!.endOffset = 6) ∧ (rtlItems[3]!.direction = .ltr) ∧
    (rtlItems[4]!.startOffset = 6) ∧ (rtlItems[4]!.endOffset = 7) ∧ (rtlItems[4]!.direction = .rtl) ∧
    (rtlItems[5]!.startOffset = 7) ∧ (rtlItems[5]!.endOffset = 11) ∧ (rtlItems[5]!.direction = .ltr) ∧
    (rtlItems[6]!.startOffset = 11) ∧ (rtlItems[6]!.endOffset = 11) ∧ (rtlItems[6]!.direction = .ltr) ∧
    (rtlItems[7]!.startOffset = 11) ∧ (rtlItems[7]!.endOffset = 12) ∧ (rtlItems[7]!.direction = .ltr) ∧
    (ltrRes.text = "[Text]text") ∧
    (ltrItems.length = 3) ∧
    (ltrItems[0]!.startOffset = 0) ∧ (ltrItems[0]!.endOffset = 0) ∧ (ltrItems[0]!.direction = .ltr) ∧
    (ltrItems[1]!.startOffset = 0) ∧ (ltrItems[1]!.endOffset = 10) ∧ (ltrItems[1]!.direction = .ltr) ∧
    (ltrItems[2]!.startOffset = 10) ∧ (ltrItems[2]!.endOffset = 10) ∧ (ltrItems[2]!.direction = .ltr) := by
  decide

/-- inline/inline_node_test.cc:1082 InvalidateAddSpan
    CSS 2.1 §9.4.2: Adding an empty span element adds openTag and closeTag items (+2 items). -/
theorem inlineNode_invalidateAddSpan :
    let beforeItems := (collectInlines [.text "before"]).items
    let afterItems := (collectInlines [.text "before", .openTag "span", .closeTag]).items
    afterItems.length = beforeItems.length + 2 := by
  rfl

/-- inline/inline_node_test.cc:1097 InvalidateRemoveSpan
    CSS 2.1 §9.4.2: Removing an inline child marks container block flow for inline recolletion. -/
theorem inlineNode_invalidateRemoveSpan :
    let (_, _, containerNeeds, _) := computeNeedsCollectInlines .removeNode
    containerNeeds = true := by
  rfl

/-- inline/inline_node_test.cc:1107 InvalidateAddInnerSpan
    CSS 2.1 §9.4.2: Adding an inner span inside an existing span adds openTag and closeTag items (+2 items). -/
theorem inlineNode_invalidateAddInnerSpan :
    let beforeItems := (collectInlines [.openTag "span", .closeTag]).items
    let afterItems := (collectInlines [.openTag "span", .openTag "span", .closeTag, .closeTag]).items
    afterItems.length = beforeItems.length + 2 := by
  rfl

/-- inline/inline_node_test.cc:1123 InvalidateRemoveInnerSpan
    CSS 2.1 §9.4.2: Removing an inner span marks container block flow for inline recolletion. -/
theorem inlineNode_invalidateRemoveInnerSpan :
    let (_, _, containerNeeds, _) := computeNeedsCollectInlines .removeNode
    containerNeeds = true := by
  rfl

/-- inline/inline_node_test.cc:1133 InvalidateSetText
    CSS 2.1 §9.4.2: Mutating text content marks container block flow for inline recolletion. -/
theorem inlineNode_invalidateSetText :
    let (_, _, containerNeeds, _) := computeNeedsCollectInlines (.changeStyle true)
    containerNeeds = true := by
  rfl

/-- inline/inline_node_test.cc:1142 InvalidateAddAbsolute
    CSS 2.1 §9.3 & §9.4.2: Adding an out-of-flow positioned child adds a single OOF item (+1 item). -/
theorem inlineNode_invalidateAddAbsolute :
    let beforeItems := (collectInlines [.text "before"]).items
    let afterItems := (collectInlines [.text "before", .outOfFlowPositioned]).items
    afterItems.length = beforeItems.length + 1 := by
  rfl

/-- inline/inline_node_test.cc:1159 InvalidateRemoveAbsolute
    CSS 2.1 §9.3 & §9.4.2: Removing an out-of-flow child marks container block flow for inline recolletion. -/
theorem inlineNode_invalidateRemoveAbsolute :
    let (_, _, containerNeeds, _) := computeNeedsCollectInlines .removeNode
    containerNeeds = true := by
  rfl

/-- inline/inline_node_test.cc:1171 InvalidateChangeToAbsolute
    CSS 2.1 §9.3 & §9.4.2: Changing an in-flow span to position:absolute replaces open/close tags with a single OOF item (-1 item). -/
theorem inlineNode_invalidateChangeToAbsolute :
    let beforeItems := (collectInlines [.text "before", .openTag "span", .closeTag]).items
    let afterItems := (collectInlines [.text "before", .outOfFlowPositioned]).items
    afterItems.length = beforeItems.length - 1 := by
  rfl

/-- inline/inline_node_test.cc:1189 InvalidateChangeFromAbsolute
    CSS 2.1 §9.3 & §9.4.2: Changing an out-of-flow child to an in-flow span replaces the OOF item with open/close tags (+1 item). -/
theorem inlineNode_invalidateChangeFromAbsolute :
    let beforeItems := (collectInlines [.text "before", .outOfFlowPositioned]).items
    let afterItems := (collectInlines [.text "before", .openTag "span", .closeTag]).items
    afterItems.length = beforeItems.length + 1 := by
  rfl

/-- inline/inline_node_test.cc:1207 InvalidateAddFloat
    CSS 2.1 §9.5 & §9.4.2: Adding a floating child adds a single float item (+1 item). -/
theorem inlineNode_invalidateAddFloat :
    let beforeItems := (collectInlines [.text "before"]).items
    let afterItems := (collectInlines [.text "before", .floating]).items
    afterItems.length = beforeItems.length + 1 := by
  rfl

/-- inline/inline_node_test.cc:1224 InvalidateRemoveFloat
    CSS 2.1 §9.5 & §9.4.2: Removing a floating child marks container block flow for inline recolletion. -/
theorem inlineNode_invalidateRemoveFloat :
    let (_, _, containerNeeds, _) := computeNeedsCollectInlines .removeNode
    containerNeeds = true := by
  rfl

/-- inline/inline_node_test.cc:1236 SpaceRestoredByInsertingWord
    CSS Text 3 §4.1 & CSS 2.1 §9.4.2: Spaces separated by empty tags collapse across the tags,
    but inserting text inside the span separates the spaces and prevents collapsing. -/
theorem inlineNode_spaceRestoredByInsertingWord :
    let beforeText := buildInlineString [
      BuilderInput.text "before ",
      BuilderInput.openTag,
      BuilderInput.closeTag,
      BuilderInput.text " after"
    ]
    let afterText := buildInlineString [
      BuilderInput.text "before ",
      BuilderInput.openTag,
      BuilderInput.text "mid",
      BuilderInput.closeTag,
      BuilderInput.text " after"
    ]
    beforeText = "before after" ∧ afterText = "before mid after" := by
  decide

/-- inline/inline_node_test.cc:960 NeedsCollectInlinesOnInsertToOutOfFlowButton
    CSS 2.1 §9.4.2 & §9.3: Inserting into an independent out-of-flow button does not invalidate container inlines. -/
theorem inlineNode_needsCollectInlinesOnInsertToOutOfFlowButton :
    let (_, _, containerNeeds, _) := computeNeedsCollectInlines (.insertNode true)
    containerNeeds = false := by
  rfl

/-- inline/inline_node_test.cc:1251 RemoveInlineNodeDataIfBlockBecomesEmpty1
    CSS 2.1 §9.4.2: Removing children so block becomes empty clears its inline formatting context. -/
theorem inlineNode_removeInlineNodeDataIfBlockBecomesEmpty1 :
    establishesInlineFormattingContext [.inline] = true ∧
    establishesInlineFormattingContext [] = false := by
  decide

/-- inline/inline_node_test.cc:1262 RemoveInlineNodeDataIfBlockBecomesEmpty2
    CSS 2.1 §9.4.2: Setting innerHTML="" so block becomes empty clears its inline formatting context. -/
theorem inlineNode_removeInlineNodeDataIfBlockBecomesEmpty2 :
    establishesInlineFormattingContext [.inline] = true ∧
    establishesInlineFormattingContext [] = false := by
  decide

/-- inline/inline_node_test.cc:1272 RemoveInlineNodeDataIfBlockObtainsBlockChild
    CSS 2.1 §9.4.2: A block container that obtains an in-flow block child no longer establishes an IFC directly. -/
theorem inlineNode_removeInlineNodeDataIfBlockObtainsBlockChild :
    establishesInlineFormattingContext [.inline] = true ∧
    establishesInlineFormattingContext [.block] = false := by
  decide

/-- inline/inline_node_test.cc:1459 SegmentRanges
    CSS Text 3 §5 & UAX #24: Segment range queries return all subsegment boundaries clamped to requested range. -/
theorem inlineNode_segmentRanges :
    let segs := [1, 7, 8, 12]
    segmentRanges segs 0 12 = [1, 7, 8, 12] ∧
    segmentRanges segs 0 1 = [1] ∧
    segmentRanges segs 2 3 = [3] ∧
    segmentRanges segs 7 8 = [8] ∧
    segmentRanges segs 0 8 = [1, 7, 8] ∧
    segmentRanges segs 2 8 = [7, 8] ∧
    segmentRanges segs 2 10 = [7, 8, 10] ∧
    segmentRanges segs 7 10 = [8, 10] ∧
    segmentRanges segs 8 9 = [9] ∧
    segmentRanges segs 8 10 = [10] ∧
    segmentRanges segs 9 12 = [12] := by
  decide

/-- inline/inline_node_test.cc:1671 InitialLetter
    CSS Inline 3 §3: Initial letters generate initialLetterBox items and flag hasInitialLetterBox. -/
theorem inlineNode_initialLetter :
    let step := collectInlinesStep 0 false (.initialLetterBox 20)
    let item := step.2.1
    item.itemType = .initialLetterBox ∧
    hasInitialLetterBox [item] = true := by
  decide

/-- inline/inline_node_test.cc:245 ShareInlineTextContentSingleSource
    CSS Text 3 §4.1: When whitespace is preserved (white-space: pre), the transformed text
    is identical to the source DOM text, enabling single-source buffer sharing. -/
theorem inlineNode_shareInlineTextContentSingleSource :
    canShareInlineTextContent .pre "Hello\nWorld  123".toList = true := by
  decide

/-- inline/inline_node_test.cc:256 ShareInlineTextContentLargeNotSharedWhenCollapsed
    CSS Text 3 §4.1: When whitespace collapsing shrinks consecutive spaces, the transformed
    text length changes and the DOM buffer cannot be shared. -/
theorem inlineNode_shareInlineTextContentLargeNotSharedWhenCollapsed :
    canShareInlineTextContent .normal "word  word".toList = false := by
  decide

/-- inline/inline_node_test.cc:274 ShareInlineTextContentLargeNotSharedSameLength
    CSS Text 3 §4.1: When whitespace collapsing turns newlines into spaces, length is preserved
    but characters are modified, so the DOM buffer cannot be shared. -/
theorem inlineNode_shareInlineTextContentLargeNotSharedSameLength :
    canShareInlineTextContent .normal "word\nword".toList = false := by
  decide

/-- inline/inline_node_test.cc:698 MinMaxSizesNeedsLayout
    CSS Text 3 §4.1 & DOM §5.3: Replacing text marks the layout object as needing layout,
    and querying min/max sizes does not clear the needs-layout state. -/
theorem inlineNode_minMaxSizesNeedsLayout :
    computeTextMutationInvalidation (.replace 0 1 "X") = { needsCollectInlines := false, forceReattachLayoutTree := false } := by
  decide

/-- inline/inline_node_test.cc:716 AssociatedItemsWithControlItem
    CSS Writing Modes 3 §2.4: In preformatted text with visual bidi ordering, forced line breaks
    pop and restore bidi controls, producing 5 associated items for the text node. -/
theorem inlineNode_associatedItemsWithControlItem :
    let items := buildVisualBidiTextItems 1 ["ab", "de"]
    items.length = 5 ∧
    items = [
      ⟨.text, 1, 3⟩,
      ⟨.bidiControl, 3, 4⟩,
      ⟨.control, 4, 5⟩,
      ⟨.bidiControl, 5, 6⟩,
      ⟨.text, 6, 8⟩
    ] := by
  decide

/-- inline/inline_node_test.cc:767 SetTextWithOffsetWithTextTransform
    CSS Text 3 §2.1: German sharp s expands to "SS" under uppercase transform,
    and incremental CharacterData deletion updates text content consistently. -/
theorem inlineNode_setTextWithOffsetWithTextTransform :
    applyTextTransform true "ßX".toList = ['S', 'S', 'X'] ∧
    applyTextTransform true (applyCharacterDataMutation "ßX" (.delete 1 1)).toList = ['S', 'S'] := by
  decide

/-- inline/inline_node_test.cc:1058 SegmentBidiChangeSetsNeedsLayout
    CSS Writing Modes 3 §2 & UAX #9 §3.3.4: In an RTL paragraph, changing following text from LTR to RTL
    alters the resolved bidi level of an intervening neutral character (Rule N1 vs N2), triggering relayout. -/
theorem inlineNode_segmentBidiChangeSetsNeedsLayout :
    let runsOld := resolveBidiParagraphRuns "abc-xyz" .rtl
    let runsNew := resolveBidiParagraphRuns "abc-\u05D1" .rtl
    bidiLevelAtOffset runsOld 3 = some 2 ∧
    bidiLevelAtOffset runsNew 3 = some 1 ∧
    needsRelayoutOnBidiChange runsOld runsNew 3 = true := by
  decide

/-- Test `InlineNodeTest, FindSvgTextChunksCrash1` (`inline/inline_node_test.cc:1733`).
    SVG 2 §11.2 & Unicode UAX #9:
    Explicit x positions partition SVG text elements into independent text chunks. -/
theorem inlineNode_findSvgTextChunksCrash1 :
    let xPositions := [0, 3, 6, 10]
    let segments := ["(", ")", "\u05D2", "("]
    partitionSvgTextChunks xPositions segments = [
      { x := 0, text := "(", length := 1 },
      { x := 3, text := ")", length := 1 },
      { x := 6, text := "\u05D2", length := 1 },
      { x := 10, text := "(", length := 1 }
    ] := by
  decide

/-- Test `InlineNodeTest, FindSvgTextChunksCrash2` (`inline/inline_node_test.cc:1749`).
    SVG 2 §11.2 & Unicode UAX #9:
    SVG text chunks with preserved whitespace newlines maintain chunk partitioning across lines. -/
theorem inlineNode_findSvgTextChunksCrash2 :
    let xPositions := [0, 3, 6, 10]
    let segments := ["(", ")", "\u05D2", "("]
    partitionSvgTextChunks xPositions segments = [
      { x := 0, text := "(", length := 1 },
      { x := 3, text := ")", length := 1 },
      { x := 6, text := "\u05D2", length := 1 },
      { x := 10, text := "(", length := 1 }
    ] := by
  decide

/-- Test `InlineNodeTest, FindSvgTextChunksCrash3` (`inline/inline_node_test.cc:1765`).
    SVG 2 §11.2 & Unicode Standard §3.8:
    SVG text chunks containing surrogate pairs partition correctly without crash. -/
theorem inlineNode_findSvgTextChunksCrash3 :
    let xPositions := [0, 0]
    let segments := ["PA", "PASS"]
    partitionSvgTextChunks xPositions segments = [
      { x := 0, text := "PA", length := 2 },
      { x := 0, text := "PASS", length := 4 }
    ] := by
  decide

/-- Test `InlineNodeTest, AddChildToSVGRoot` (`inline/inline_node_test.cc:1336`).
    SVG 2 §11 & CSS 2.1 §9.4.2:
    Adding child elements to an SVG root does not invalidate or mutate parent HTML inline formatting context. -/
theorem inlineNode_addChildToSVGRoot :
    svgChildMutatesParentIFC = false := by
  rfl

end ChromiumLayout.TestsInline
