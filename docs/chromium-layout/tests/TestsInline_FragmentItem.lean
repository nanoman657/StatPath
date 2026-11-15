/-
  docs/chromium-layout/tests/TestsInline_FragmentItem.lean

  Formalized tests for CSS 2.1 §9.4.2, CSS Inline 3 §2, CSS Ruby 1 §3,
  and Blink FragmentItem / FragmentItems
  (`third_party/blink/renderer/core/layout/inline/fragment_item_test.cc`).
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test `FragmentItemTest.BasicText` (`inline/fragment_item_test.cc:126`).
    CSS 2.1 §9.4.2 & CSS Inline 3 §2:
    `<div style="width: 10ch; font-family: Ahem; font-size: 10px; line-height: 1">1234567 98765</div>`
    Wrapping text (70px + 10px space + 50px in 100px width) breaks into 2 lines through general layout:
    - line 1 at (0, 0) with fragment 0: isFirstForNode = true, isLastForNode = false;
    - line 2 at (0, 10) with fragment 1: isFirstForNode = false, isLastForNode = true. -/
theorem fragmentItem_basicText :
    let fh : FontHeight := { ascent := 10, descent := 0 }
    let w1 : InlineItem := .TextSeg 1 70 fh true false
    let sp : InlineItem := .TextSeg 1 10 fh true true
    let w2 : InlineItem := .TextSeg 1 50 fh true false
    let lines := breakLines 100 [w1, sp, w2]
    let (stacked, totalH) := stackLineBoxes fh 0 lines
    (lines.length = 2) ∧
    (totalH = 20) ∧
    (stacked.length = 2) ∧
    ((stacked.headD {}).bfcOffset.blockOffset = 0) ∧
    (((stacked.headD {}).items.headD {}).inlineSize = 70) ∧
    (isFirstFragmentForNode 0 = true) ∧
    (isLastFragmentForNode 0 stacked.length = false) ∧
    (((stacked.tailD []).headD {}).bfcOffset.blockOffset = 10) ∧
    ((((stacked.tailD []).headD {}).items.headD {}).inlineSize = 50) ∧
    (isFirstFragmentForNode 1 = false) ∧
    (isLastFragmentForNode 1 stacked.length = true) := by
  decide

/-- Test `FragmentItemTest.BasicInlineBox` (`inline/fragment_item_test.cc:235`).
    CSS 2.1 §9.4.2 & CSS Inline 3 §2:
    `<div id="container" style="width: 10ch">000 <span id="span1">1234 5678</span> 999 <span id="span2">12345678</span></div>`
    Lays out through general inline line breaking and stacking:
    - span1 wraps, producing two fragments: first at (40, 0), second at (0, 10);
    - span2 does not wrap, producing one fragment at (0, 20). -/
theorem fragmentItem_basicInlineBox :
    let fh : FontHeight := { ascent := 10, descent := 0 }
    let t0 : InlineItem := .TextSeg 0 30 fh true false
    let sp0 : InlineItem := .TextSeg 0 10 fh true true
    let s1_w1 : InlineItem := .TextSeg 1 40 fh true false
    let s1_sp : InlineItem := .TextSeg 1 10 fh true true
    let s1_w2 : InlineItem := .TextSeg 1 40 fh true false
    let t2 : InlineItem := .TextSeg 2 30 fh true false
    let sp2 : InlineItem := .TextSeg 2 10 fh true true
    let s2_w : InlineItem := .TextSeg 3 80 fh true false
    let lines := breakLines 100 [t0, sp0, s1_w1, s1_sp, s1_w2, t2, sp2, s2_w]
    let (stacked, _) := stackLineBoxes fh 0 lines
    let l0 := stacked.headD {}
    let l1 := (stacked.tailD []).headD {}
    let l2 := ((stacked.tailD []).tailD []).headD {}
    let s1_frag0 := l0.items.filter (fun it => it.itemId == 1) |>.headD {}
    let s1_frag1 := l1.items.filter (fun it => it.itemId == 1) |>.headD {}
    let s2_frag0 := l2.items.filter (fun it => it.itemId == 3) |>.headD {}
    (lines.length = 3) ∧
    -- span1 fragment 0 at (40, 0)
    (s1_frag0.inlineOffset = 40) ∧
    (l0.bfcOffset.blockOffset + s1_frag0.blockOffset = 0) ∧
    (s1_frag0.inlineSize = 40) ∧
    (isFirstFragmentForNode 0 = true) ∧
    (isLastFragmentForNode 0 2 = false) ∧
    -- span1 fragment 1 at (0, 10)
    (s1_frag1.inlineOffset = 0) ∧
    (l1.bfcOffset.blockOffset + s1_frag1.blockOffset = 10) ∧
    (s1_frag1.inlineSize = 40) ∧
    (isFirstFragmentForNode 1 = false) ∧
    (isLastFragmentForNode 1 2 = true) ∧
    -- span2 fragment 0 at (0, 20)
    (s2_frag0.inlineOffset = 0) ∧
    (l2.bfcOffset.blockOffset + s2_frag0.blockOffset = 20) ∧
    (s2_frag0.inlineSize = 80) ∧
    (isFirstFragmentForNode 0 = true) ∧
    (isLastFragmentForNode 0 1 = true) := by
  decide

/-- Test `FragmentItemTest.CulledInlineBox` (`inline/fragment_item_test.cc:291`).
    Culled span1 bounds unite its two fragments to Rect(0, 0, 80, 20). -/
theorem fragmentItem_culledInlineBox :
    let items : List FragmentItem := [
      { nodeId := 1, offset := { inlineOffset := 40, blockOffset := 0 }, size := { inlineSize := 40, blockSize := 10 } },
      { nodeId := 1, offset := { inlineOffset := 0, blockOffset := 10 }, size := { inlineSize := 40, blockSize := 10 } }
    ]
    culledInlineBoundingBox items 1 = { x := 0, y := 0, width := 80, height := 20 } := by
  decide

/-- Test `FragmentItemTest.CaretInlinePositionForOffset_TextFit` (`inline/fragment_item_test.cc:931`).
    text-fit: grow with used font-size 20px (avail 100, textLen 5) computes caret position 20 at offset 1. -/
theorem fragmentItem_caretInlinePositionForOffset_TextFit :
    caretInlinePositionForOffset 5 100 1 = 20 := by
  decide

/-- Test `FragmentItemTest.IsRubyAnnotationLine` (`inline/fragment_item_test.cc:952`).
    CSS Ruby 1 §3: Ruby container produces a base line (isRubyAnnotationLine = false)
    and an annotation line (isRubyAnnotationLine = true). -/
theorem fragmentItem_isRubyAnnotationLine :
    let lines := classifyRubyLineFragments true true
    (lines.length = 2) ∧
    (lines[0]! = (.line, false)) ∧
    (lines.any (fun (_, isAnn) => isAnn) = true) := by
  decide

/-- Test `FragmentItemsTest.IsContainerForCulledInline` (`inline/fragment_items_test.cc:46`).
    CSS Fragmentation 3 §2, CSS Inline 3 §2: Resolving container fragmentainers and first/last
    flags for culled inlines across multicolumn fragmentation. -/
theorem fragmentItems_isContainerForCulledInline :
    let culled1 := 1
    let culled2 := 2
    let container := 0
    let fragments : List (List Nat) := [
      [container],
      [container, culled1],
      [culled1],
      [culled1, culled2],
      [culled2],
      [culled2, container],
      [container]
    ]
    -- Fragment 0
    (isContainerForCulledInline fragments 0 culled1 = (false, false, false)) ∧
    (isContainerForCulledInline fragments 0 culled2 = (false, false, false)) ∧
    -- Fragment 1
    (isContainerForCulledInline fragments 1 culled1 = (true, true, false)) ∧
    (isContainerForCulledInline fragments 1 culled2 = (false, false, false)) ∧
    -- Fragment 2
    (isContainerForCulledInline fragments 2 culled1 = (true, false, false)) ∧
    (isContainerForCulledInline fragments 2 culled2 = (false, false, false)) ∧
    -- Fragment 3
    (isContainerForCulledInline fragments 3 culled1 = (true, false, true)) ∧
    (isContainerForCulledInline fragments 3 culled2 = (true, true, false)) ∧
    -- Fragment 4
    (isContainerForCulledInline fragments 4 culled1 = (false, false, false)) ∧
    (isContainerForCulledInline fragments 4 culled2 = (true, false, false)) ∧
    -- Fragment 5
    (isContainerForCulledInline fragments 5 culled1 = (false, false, false)) ∧
    (isContainerForCulledInline fragments 5 culled2 = (true, false, true)) ∧
    -- Fragment 6
    (isContainerForCulledInline fragments 6 culled1 = (false, false, false)) ∧
    (isContainerForCulledInline fragments 6 culled2 = (false, false, false)) := by
  decide

/-- Test `FragmentItemTest.RtlText` (`inline/fragment_item_test.cc:173`).
    CSS Writing Modes 3 §3.1 & UAX #9: Mixed-directional RTL text splits into visual runs;
    first-for-node and last-for-node sequence flags track the whole layout object. -/
theorem fragmentItem_rtlText :
    let visualRuns := bidiVisualFragmentRunsRtl [("11111", "."), ("22222", ".")]
    let spanFlags0 := deriveFragmentSequenceFlags 2 0
    let spanFlags1 := deriveFragmentSequenceFlags 2 1
    let textFlags0 := deriveFragmentSequenceFlags 4 0
    let textFlags1 := deriveFragmentSequenceFlags 4 1
    let textFlags2 := deriveFragmentSequenceFlags 4 2
    let textFlags3 := deriveFragmentSequenceFlags 4 3
    (visualRuns = [".", "11111", ".", "22222"]) ∧
    (spanFlags0 = (true, false)) ∧
    (spanFlags1 = (false, true)) ∧
    (textFlags0 = (true, false)) ∧
    (textFlags1 = (false, false)) ∧
    (textFlags2 = (false, false)) ∧
    (textFlags3 = (false, true)) := by
  decide

/-- Test `FragmentItemTest.StartOffsetInContainer` (`inline/fragment_item_test.cc:357`).
    CSS Text 3 §5.2: Soft hyphen line breaks generate hyphen items with start offsets in container. -/
theorem fragmentItem_startOffsetInContainer :
    let segmentLengths := [3, 3, 3]
    computeHyphenOffsetsInContainer segmentLengths = [4, 8, 12] := by
  decide

/-- Test `FragmentItemTest.EllipsizedAtomicInline` (`inline/fragment_item_test.cc:383`).
    CSS Overflow 3 §4.4: When atomic inline overflows container under text-overflow: ellipsis,
    it is marked as the last box item for the node. -/
theorem fragmentItem_ellipsizedAtomicInline :
    classifyEllipsizedAtomicInlineFragments 200 100 = some (.box, true) := by
  decide

/-- Test `FragmentItemsBuilderTest.MultipleLogicalLineItems` (`inline/fragment_items_builder_test.cc:23`).
    CSS 2.1 §9.4.2: FragmentItemsBuilder supports sequential line assembly, reordering, and filtering. -/
theorem fragmentItemsBuilder_multipleLogicalLineItems :
    let line1 := 101
    let line2 := 102
    -- Case 1: Sequential add
    let b1 := (({} : FragmentItemsBuilder).addLine line1).addLine line2
    -- Case 2: Reversed add
    let b2 := (({} : FragmentItemsBuilder).addLine line2).addLine line1
    -- Case 3: Filtered add (line 2 only)
    let b3 := ({} : FragmentItemsBuilder).addLine line2
    (b1.items = [line1, line2]) ∧
    (b2.items = [line2, line1]) ∧
    (b3.items = [line2]) := by
  decide

end ChromiumLayout.TestsInline
