/-
  docs/chromium-layout/tests/TestsInline_InlineNode.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/inline_node_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineShaping
import InlineTextCombine

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

end ChromiumLayout.TestsInline
