/-
  docs/chromium-layout/tests/TestsInline_LineBreaker.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/line_breaker_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineShaping
import InlineBreakCandidate
import InlineTextCombine

namespace ChromiumLayout.TestsInline

open ChromiumLayout


/-! ### Test 1: FitWithEpsilon (line_breaker_test.cc:144) -/
theorem lineBreaker_fitWithEpsilon :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false

    let lines := breakLines 50 [mkWord 1 50]
    lines.length = 1 ∧ (lines.getD 0 {}).inlineSize = 50 := by
  decide

/-! ### Test 2: SingleNode (line_breaker_test.cc:171) -/
theorem lineBreaker_singleNode :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let mkSpace (id : Nat) (w : Nat := 10) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } true true

    let lineBreaker_singleNode_items : List InlineItem :=
      [ mkWord 1 30  -- "123"
      , mkSpace 2 10 -- " "
      , mkWord 3 30  -- "456"
      , mkSpace 4 10 -- " "
      , mkWord 5 30  -- "789"
      ]
    let lines80 := breakLines 80 lineBreaker_singleNode_items
    let lines60 := breakLines 60 lineBreaker_singleNode_items
    lines80.length = 2 ∧
    (lines80.getD 0 {}).inlineSize = 70 ∧
    (lines80.getD 1 {}).inlineSize = 30 ∧
    lines60.length = 3 ∧
    (lines60.getD 0 {}).inlineSize = 30 ∧
    (lines60.getD 1 {}).inlineSize = 30 ∧
    (lines60.getD 2 {}).inlineSize = 30 := by
  decide

/-! ### Test 8 & 9: OverflowTab and OverflowTabBreakWord (line_breaker_test.cc:301, 323) -/
theorem lineBreaker_overflowTab :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let mkSpace (id : Nat) (w : Nat := 10) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } true true

    let tabSeg := mkWord 1 110 false
    let sp := mkSpace 2 10
    let word2 := mkWord 3 30
    let lines := breakLines 100 [tabSeg, sp, word2]
    lines.length = 2 ∧
    (lines.getD 0 {}).inlineSize = 110 ∧
    (lines.getD 1 {}).inlineSize = 40 := by
  decide

/-! ### Test 10: OverflowAtomicInline (line_breaker_test.cc:346) -/
theorem lineBreaker_overflowAtomic :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let mkAtomic (id : Nat) (w : Nat) (h : Nat := 10) : InlineItem := .AtomicInline id { inlineSize := w, blockSize := h } BoxStrut.zero 8

    let lineBreaker_overflowAtomic_items : List InlineItem :=
      [ mkWord 1 50
      , mkAtomic 2 30 10
      , mkWord 3 30
      ]
    let lines80 := breakLines 80 lineBreaker_overflowAtomic_items
    let lines70 := breakLines 70 lineBreaker_overflowAtomic_items
    let lines40 := breakLines 40 lineBreaker_overflowAtomic_items
    let lines20 := breakLines 20 lineBreaker_overflowAtomic_items
    lines80.length = 2 ∧
    (lines80.getD 0 {}).inlineSize = 80 ∧
    (lines80.getD 1 {}).inlineSize = 30 ∧
    lines70.length = 2 ∧
    (lines70.getD 0 {}).inlineSize = 50 ∧
    (lines70.getD 1 {}).inlineSize = 60 ∧
    lines40.length = 3 ∧
    (lines40.getD 0 {}).inlineSize = 50 ∧
    (lines40.getD 1 {}).inlineSize = 30 ∧
    (lines40.getD 2 {}).inlineSize = 30 ∧
    lines20.length = 3 ∧
    (lines20.getD 0 {}).inlineSize = 50 ∧
    (lines20.getD 1 {}).inlineSize = 30 ∧
    (lines20.getD 2 {}).inlineSize = 30 := by
  decide

/-! ### Test 12: OverflowAfterSpacesAcrossElements (line_breaker_test.cc:423) -/
theorem lineBreaker_overflowAfterSpaces :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let mkSpace (id : Nat) (w : Nat := 10) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } true true

    let items := [mkWord 1 40, mkSpace 2 10, mkSpace 3 10, mkWord 4 10]
    let lines := breakLines 50 items
    lines.length = 2 ∧
    (lines.getD 0 {}).inlineSize = 40 ∧
    (lines.getD 1 {}).inlineSize = 10 := by
  decide

/-! ### Test 13: WrapLastWord (line_breaker_test.cc:447) -/
theorem lineBreaker_wrapLastWord :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let mkSpace (id : Nat) (w : Nat := 10) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } true true
    let mkOpen (id : Nat) (_mr : Nat := 0) : InlineItem := .OpenTag id 0 { ascent := 8, descent := 2 }
    let mkClose (id : Nat) (mr : Nat := 0) : InlineItem := .CloseTag id mr

    let lineBreaker_wrapLastWord_items : List InlineItem :=
      [ mkWord 1 30, mkSpace 2 10, mkWord 3 30, mkSpace 4 10, mkWord 5 30, mkSpace 6 10
      , mkOpen 7, mkWord 8 20, mkClose 9, mkSpace 10 10, mkWord 11 20
      ]
    let lines := breakLines 100 lineBreaker_wrapLastWord_items
    lines.length = 2 ∧
    (lines.getD 0 {}).inlineSize = 70 ∧
    (lines.getD 1 {}).inlineSize = 90 := by
  decide

/-! ### Test 14: WrapLetterSpacing (line_breaker_test.cc:466) -/
theorem lineBreaker_wrapLetterSpacing :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let mkSpace (id : Nat) (w : Nat := 10) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } true true

    let items := [mkWord 1 40, mkSpace 2 10, mkWord 3 20]
    let lines := breakLines 50 items
    lines.length = 2 ∧
    (lines.getD 0 {}).inlineSize = 40 ∧
    (lines.getD 1 {}).inlineSize = 20 := by
  decide

/-! ### Test 17: IdeographicTrailingSpaces (line_breaker_test.cc:548) -/
theorem lineBreaker_ideographicTrailingSpaces :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false

    let lines := breakLines 190 [mkWord 0 180, mkWord 1 20 false]
    lines.length = 2 ∧
    (lines.getD 0 {}).inlineSize = 180 ∧
    (lines.getD 1 {}).inlineSize = 20 := by
  decide

/-! ### Test 31: IdeographicSpaceBeforeEndBracket (line_breaker_test.cc:965) -/
theorem lineBreaker_ideographicBeforeBracket :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false

    let lines := breakLines 190 [mkWord 0 180, mkWord 2 10 false, mkWord 1 20 false]
    lines.length = 2 ∧
    (lines.getD 0 {}).inlineSize = 190 ∧
    (lines.getD 1 {}).inlineSize = 20 := by
  decide

/-! ### Test 32, 33, 34: BreakAt explicit breakpoints (line_breaker_test.cc:1002, 1044, 1079) -/
theorem lineBreaker_breakAt :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false
    let l1 := breakLines 800 [mkWord 1 10, .ForcedBreak 2, mkWord 3 40, .ForcedBreak 4, mkWord 5 10, .ForcedBreak 6, mkWord 7 30]
    l1.length = 4 ∧
    (l1.getD 0 {}).inlineSize = 10 ∧
    (l1.getD 1 {}).inlineSize = 40 ∧
    (l1.getD 2 {}).inlineSize = 10 ∧
    (l1.getD 3 {}).inlineSize = 30 := by
  decide

/-! ### Test 45: BidiControlEnterFlag (line_breaker_test.cc:1331) -/
/-- Test `LineBreakerTest, BidiControlEnterFlag` (`inline/line_breaker_test.cc:1331`).
    CSS 2.1 §10.8 & CSS Writing Modes 3 §3.2:
    `<div id="container" style="font: 10px/1 Ahem; width: 40px">xxx-<bdi>xx</bdi></div>`
    Single line of height 10px produced through breakLines and line box creation. -/
theorem lineBreaker_bidiControlEnter :
    let mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } cb false

    let strut : FontHeight := { ascent := 8, descent := 2 }
    let lines := breakLines 40 [mkWord 1 40]
    let (stacked, totalH) := stackLineBoxes strut 0 lines
    (lines.length = 1) ∧ (totalH = 10) ∧
    ((stacked.headD {}).bfcOffset.blockOffset = 0) := by
  decide

/-! ### Test 28: SplitTextIntoSegments (line_breaker_test.cc:887) -/
theorem lineBreaker_splitTextIntoSegments :
    let chars := ['A', 'V', Char.ofNat 0x1F197, '\u05E2', '\u05B4', '\u05D1', '\u05E8', '\u05B4', '\u05D9', '\u05EA']
    let lens := clusterUtf16Lengths chars
    (lens.length = 8) ∧
    (lens = [1, 1, 2, 2, 1, 2, 1, 1]) := by
  decide

/-! ### Test 18: WhitespaceState (line_breaker_test.cc:624) -/
/-- Test `WhitespaceStateTest, WhitespaceState` (`inline/line_breaker_test.cc:624`).
    Verifies trailing whitespace state across test configurations. -/
theorem lineBreaker_whitespaceState :
    (computeWhitespaceState .textEnd = .none) ∧
    (computeWhitespaceState (.softWrapBreak true) = .collapsed) ∧
    (computeWhitespaceState (.blockEndSpace true) = .none) ∧
    (computeWhitespaceState (.softWrapBreak false) = .preserved) ∧
    (computeWhitespaceState (.blockEndSpace false) = .preserved) ∧
    (computeWhitespaceState .emptyLine = .leading) ∧
    (computeWhitespaceState .atomicEnd = .none) := by
  decide

/-! ### Test 43: CanBreakInside (line_breaker_test.cc:1288) -/
/-- Test `CanBreakInsideTest, Data` (`inline/line_breaker_test.cc:1288`).
    Verifies CanBreakInside predicate across all 24 test configurations. -/
theorem lineBreaker_canBreakInside :
    (canBreakInside true [.text "a" false] = false) ∧
    (canBreakInside true [.text "a b" true] = true) ∧
    (canBreakInside false [.text "a b" true] = false) ∧
    (canBreakInside true [.text "a" false, .text "a b" true] = true) ∧
    (canBreakInside true [.text "a" false, .text " b" true] = true) ∧
    (canBreakInside true [.text "a " true, .text "b" false] = true) ∧
    (canBreakInside true [.text "a" false, .text " " true, .text "b" false] = true) ∧
    (canBreakInside true [.text "a" false, .text "b" false] = false) ∧
    (canBreakInside true [.outOfFlow] = false) ∧
    (canBreakInside true [.text "a" false, .outOfFlow] = false) ∧
    (canBreakInside true [.text "a" false, .outOfFlow, .text "b" false] = false) ∧
    (canBreakInside true [.text "a" false, .outOfFlow, .outOfFlow, .text "b" false] = false) ∧
    (canBreakInside true [.outOfFlow, .text "a b" true] = true) ∧
    (canBreakInside true [.text "a " true, .outOfFlow, .text "b" false] = true) ∧
    (canBreakInside true [.text "a" false, .outOfFlow, .text " b" true] = true) ∧
    (canBreakInside true [.text "a" false, .outOfFlow, .outOfFlow] = false) ∧
    (canBreakInside true [.text "ab c" true, .outOfFlow] = true) ∧
    (canBreakInside true [.text "ab" false, .outOfFlow, .outOfFlow, .outOfFlow] = false) ∧
    (canBreakInside true [.text "a" false, .outOfFlow, .text "b" false] = false) ∧
    (canBreakInside true [.text "a " true, .outOfFlow, .text "b" false] = true) ∧
    (canBreakInside true [.atomicInline] = false) ∧
    (canBreakInside true [.atomicInline, .atomicInline] = true) ∧
    (canBreakInside true [.text "a" false, .atomicInline] = true) ∧
    (canBreakInside true [.atomicInline, .text "a" false] = true) := by
  decide

/-! ### General Line Breaker Progress Law -/
theorem line_breaker_single_word_progress (avail : Nat) (w : Nat) (id : Nat) :
    let item : InlineItem := .TextSeg id w { ascent := 8, descent := 2 } true false
    let lines := breakLines avail [item]
    lines.length = 1 ∧ (lines.getD 0 {}).inlineSize = w := by
  dsimp [breakLines, breakLinesFuel, takeLine]
  exact ⟨rfl, rfl⟩

/-! ### Line Breaker Text Combine Tests (CSS Writing Modes 3 §5.1) -/

/-- LineBreakerTest.TextCombineCloseTag (`inline/line_breaker_test.cc:197`):
    LineBreaker does not care about white-space: pre inside text-combine;
    unbreakable sequence overflows on a single line. -/
theorem lineBreaker_textCombineCloseTag :
    let lines := breakLinesWithTextCombine "abc" "XYZ" "def" 30 10
    lines.length = 1 ∧ lines = ["abc\uFFFCdef"] := by
  decide

/-- LineBreakerTest.TextCombineBreak (`inline/line_breaker_test.cc:223`):
    Combined hyphen element provides a soft wrap opportunity after it,
    breaking the line into two lines. -/
theorem lineBreaker_textCombineBreak :
    let lines := breakLinesWithTextCombine "abc" "-" "def" 30 10
    lines.length = 2 ∧ lines = ["abc\uFFFC", "def"] := by
  decide

/-- LineBreakerTest.TextCombineNoBreak (`inline/line_breaker_test.cc:241`):
    Combined alphanumeric text has no break opportunities, overflowing on a single line. -/
theorem lineBreaker_textCombineNoBreak :
    let lines := breakLinesWithTextCombine "abc" "XYZ" "def" 30 10
    lines.length = 1 ∧ lines = ["abc\uFFFCdef"] := by
  decide

/-- LineBreakerTest.TextCombineNoBreakWithSpace (`inline/line_breaker_test.cc:258`):
    Space inside text-combine does not permit breaking inside;
    boundary between 'Z' and 'd' has no break opportunity. -/
theorem lineBreaker_textCombineNoBreakWithSpace :
    let lines := breakLinesWithTextCombine "abc" "X Z" "def" 30 10
    lines.length = 1 ∧ lines = ["abc\uFFFCdef"] := by
  decide

/-! ### Line Breaker Word Segmentation & Overflow Tests (CSS Text 3 §4, §5 & CSS 2.1 §9.5) -/

/-- LineBreakerTest.OverflowWord (`inline/line_breaker_test.cc:275`):
    First word overflows, space collapses at line start, second word is placed on next line. -/
theorem lineBreaker_overflowWord :
    let segs : List UnbreakableSegment :=
      [ { text := "12345", width := 50, followedBySpace := true }
      , { text := "678", width := 30, followedBySpace := false } ]
    let lines40 := breakSegmentLines 40 segs
    let lines20 := breakSegmentLines 20 segs
    lines40 = ["12345", "678"] ∧ lines20 = ["12345", "678"] := by
  decide

/-- LineBreakerTest.OverflowMargin (`inline/line_breaker_test.cc:387`):
    Word with trailing inline margin that overflows line breaks before the word. -/
theorem lineBreaker_overflowMargin :
    let segs : List UnbreakableSegment :=
      [ { text := "123", width := 30, followedBySpace := true }
      , { text := "456", width := 70, followedBySpace := true }
      , { text := "789", width := 30, followedBySpace := false } ]
    let lines80 := breakSegmentLines 80 segs
    let lines60 := breakSegmentLines 60 segs
    lines80 = ["123", "456", "789"] ∧ lines60 = ["123", "456", "789"] := by
  decide

/-- LineBreakerTest.BoundaryInWord (`inline/line_breaker_test.cc:486`):
    Element boundaries inside a word do not create break opportunities;
    words across boundary remain contiguous. -/
theorem lineBreaker_boundaryInWord :
    let segs : List UnbreakableSegment :=
      [ { text := "123", width := 30, followedBySpace := true }
      , { text := "456789", width := 60, followedBySpace := true }
      , { text := "abc", width := 30, followedBySpace := false } ]
    let lines80 := breakSegmentLines 80 segs
    let lines50 := breakSegmentLines 50 segs
    lines80 = ["123", "456789", "abc"] ∧ lines50 = ["123", "456789", "abc"] := by
  decide

/-- LineBreakerTest.BoundaryInFirstWord (`inline/line_breaker_test.cc:516`):
    First word split across element boundary cannot be broken. -/
theorem lineBreaker_boundaryInFirstWord :
    let segs : List UnbreakableSegment :=
      [ { text := "123456", width := 60, followedBySpace := true }
      , { text := "789", width := 30, followedBySpace := false } ]
    let lines80 := breakSegmentLines 80 segs
    let lines50 := breakSegmentLines 50 segs
    let lines20 := breakSegmentLines 20 segs
    lines80 = ["123456", "789"] ∧ lines50 = ["123456", "789"] ∧ lines20 = ["123456", "789"] := by
  decide

/-- LineBreakerTest.ForcedBreakFollowedByCloseTag (`inline/line_breaker_test.cc:789`):
    Forced break followed by close tags and collapsible whitespace at block end produces 1 line. -/
theorem lineBreaker_forcedBreakFollowedByCloseTag :
    let segs : List UnbreakableSegment :=
      [ { text := "line", width := 40, followedBySpace := false }
      , { text := "", width := 0, isForcedBreak := true }
      , { text := "", width := 0 } ]
    let lines := breakSegmentLines 100 segs
    lines.length = 1 ∧ lines = ["line"] := by
  decide

/-! ### Trailing Space Hanging Width Test (CSS Text 3 §4.1.2 & §5.4) -/

/-- TrailingSpaceWidthTest.TrailingSpaceWidth (`inline/line_breaker_test.cc:684`):
    Computes trailing space hanging width across 25 parameter configurations for pre and pre-wrap. -/
theorem lineBreaker_trailingSpaceWidth :
    -- white-space: pre (all 0)
    computeHangingSpaceWidth .pre false 0 1 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 0 3 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 1 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 1 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 3 none 50 = 0 ∧
    computeHangingSpaceWidth .pre false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .pre true 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .pre true 1 2 none 50 = 0 ∧
    -- white-space: pre-wrap
    computeHangingSpaceWidth .preWrap false 0 1 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 0 3 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 1 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 1 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 3 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap true 1 2 none 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 2 1 (some 4) 50 = 1 ∧
    computeHangingSpaceWidth .preWrap false 2 2 (some 4) 50 = 2 ∧
    computeHangingSpaceWidth .preWrap true 2 2 (some 4) 50 = 0 ∧
    computeHangingSpaceWidth .preWrap false 2 4 none 50 = 1 := by
  decide

end ChromiumLayout.TestsInline
