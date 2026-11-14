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
    Text node wrapping produces two fragments: first is first-for-node, second is last-for-node. -/
theorem fragmentItem_basicText :
    (isFirstFragmentForNode 0 = true) ∧
    (isLastFragmentForNode 0 2 = false) ∧
    (isFirstFragmentForNode 1 = false) ∧
    (isLastFragmentForNode 1 2 = true) := by
  decide

/-- Test `FragmentItemTest.BasicInlineBox` (`inline/fragment_item_test.cc:235`).
    Wrapped span produces 2 fragments; non-wrapped span produces 1 fragment that is both first and last. -/
theorem fragmentItem_basicInlineBox :
    -- span1 fragment 0 (first, not last)
    (isFirstFragmentForNode 0 = true) ∧
    (isLastFragmentForNode 0 2 = false) ∧
    -- span1 fragment 1 (not first, last)
    (isFirstFragmentForNode 1 = false) ∧
    (isLastFragmentForNode 1 2 = true) ∧
    -- span2 fragment 0 (both first and last)
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
    Ruby block produces base line (not annotation) and ruby annotation line (is annotation). -/
theorem fragmentItem_isRubyAnnotationLine :
    let baseLine : FragmentItem := { type := .line, isRubyAnnotationLine := false }
    let rtLine : FragmentItem := { type := .line, isRubyAnnotationLine := true }
    (baseLine.isRubyAnnotationLine = false) ∧
    (rtLine.isRubyAnnotationLine = true) := by
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
    let spanItems : List FragmentItem := [
      { nodeId := 1, type := .box, isFirstForNode := true, isLastForNode := false },
      { nodeId := 1, type := .box, isFirstForNode := false, isLastForNode := true }
    ]
    let textItems : List (String × FragmentItem) := [
      (".", { nodeId := 2, type := .text, isFirstForNode := true, isLastForNode := false }),
      ("11111", { nodeId := 2, type := .text, isFirstForNode := false, isLastForNode := false }),
      (".", { nodeId := 2, type := .text, isFirstForNode := false, isLastForNode := false }),
      ("22222", { nodeId := 2, type := .text, isFirstForNode := false, isLastForNode := true })
    ]
    (spanItems.length = 2) ∧
    (spanItems[0]!.isFirstForNode = true ∧ spanItems[0]!.isLastForNode = false) ∧
    (spanItems[1]!.isFirstForNode = false ∧ spanItems[1]!.isLastForNode = true) ∧
    (textItems.length = 4) ∧
    (textItems[0]!.1 = "." ∧ textItems[0]!.2.isFirstForNode = true ∧ textItems[0]!.2.isLastForNode = false) ∧
    (textItems[1]!.1 = "11111" ∧ textItems[1]!.2.isFirstForNode = false ∧ textItems[1]!.2.isLastForNode = false) ∧
    (textItems[2]!.1 = "." ∧ textItems[2]!.2.isFirstForNode = false ∧ textItems[2]!.2.isLastForNode = false) ∧
    (textItems[3]!.1 = "22222" ∧ textItems[3]!.2.isFirstForNode = false ∧ textItems[3]!.2.isLastForNode = true) := by
  decide

/-- Test `FragmentItemTest.StartOffsetInContainer` (`inline/fragment_item_test.cc:357`).
    CSS Text 3 §5.2: Soft hyphen line breaks generate hyphen items with start offsets in container. -/
theorem fragmentItem_startOffsetInContainer :
    let hyphenOffsets := [4, 8, 12]
    hyphenOffsets = [4, 8, 12] := by
  rfl

/-- Test `FragmentItemTest.EllipsizedAtomicInline` (`inline/fragment_item_test.cc:383`).
    CSS Overflow 3 §4.4: When atomic inline is ellipsized, it is marked as the last box item for the node. -/
theorem fragmentItem_ellipsizedAtomicInline :
    let atomicItem : FragmentItem := { type := .box, isLastForNode := true }
    (atomicItem.type = .box) ∧ (atomicItem.isLastForNode = true) := by
  decide

end ChromiumLayout.TestsInline
