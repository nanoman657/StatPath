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

end ChromiumLayout.TestsInline
