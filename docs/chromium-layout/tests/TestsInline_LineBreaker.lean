/-
  docs/chromium-layout/tests/TestsInline_LineBreaker.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/line_breaker_test.cc`
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout.TestsInline

open ChromiumLayout

instance : Inhabited LineInfo := ⟨{}⟩

def testFontMetrics : FontHeight := { ascent := 8, descent := 2 }

/-! ### Helper Constructors for Inline Tests -/

def mkWord (id : Nat) (w : Nat) (cb : Bool := true) : InlineItem :=
  .TextSeg id w testFontMetrics cb false

def mkSpace (id : Nat) (w : Nat := 10) : InlineItem :=
  .TextSeg id w testFontMetrics true true

def mkAtomic (id : Nat) (w : Nat) (h : Nat := 10) : InlineItem :=
  .AtomicInline id { inlineSize := w, blockSize := h } BoxStrut.zero 8

def mkOpen (id : Nat) (_mr : Nat := 0) : InlineItem :=
  .OpenTag id 0 testFontMetrics

def mkClose (id : Nat) (mr : Nat := 0) : InlineItem :=
  .CloseTag id mr

/-! ### Test 1: FitWithEpsilon (line_breaker_test.cc:144) -/
theorem lineBreaker_fitWithEpsilon :
    let lines := breakLines 50 [mkWord 1 50]
    lines.length = 1 ∧ (lines.getD 0 default).inlineSize = 50 := by
  decide

/-! ### Test 2: SingleNode (line_breaker_test.cc:171) -/
def lineBreaker_singleNode_items : List InlineItem :=
  [ mkWord 1 30  -- "123"
  , mkSpace 2 10 -- " "
  , mkWord 3 30  -- "456"
  , mkSpace 4 10 -- " "
  , mkWord 5 30  -- "789"
  ]

theorem lineBreaker_singleNode :
    let lines80 := breakLines 80 lineBreaker_singleNode_items
    let lines60 := breakLines 60 lineBreaker_singleNode_items
    lines80.length = 2 ∧
    (lines80.getD 0 default).inlineSize = 70 ∧
    (lines80.getD 1 default).inlineSize = 30 ∧
    lines60.length = 3 ∧
    (lines60.getD 0 default).inlineSize = 30 ∧
    (lines60.getD 1 default).inlineSize = 30 ∧
    (lines60.getD 2 default).inlineSize = 30 := by
  decide

/-! ### Test 8 & 9: OverflowTab and OverflowTabBreakWord (line_breaker_test.cc:301, 323) -/
theorem lineBreaker_overflowTab :
    let tabSeg := mkWord 1 110 false
    let sp := mkSpace 2 10
    let word2 := mkWord 3 30
    let lines := breakLines 100 [tabSeg, sp, word2]
    lines.length = 2 ∧
    (lines.getD 0 default).inlineSize = 110 ∧
    (lines.getD 1 default).inlineSize = 40 := by
  decide

/-! ### Test 10: OverflowAtomicInline (line_breaker_test.cc:346) -/
def lineBreaker_overflowAtomic_items : List InlineItem :=
  [ mkWord 1 50
  , mkAtomic 2 30 10
  , mkWord 3 30
  ]

theorem lineBreaker_overflowAtomic :
    let lines80 := breakLines 80 lineBreaker_overflowAtomic_items
    let lines70 := breakLines 70 lineBreaker_overflowAtomic_items
    let lines40 := breakLines 40 lineBreaker_overflowAtomic_items
    let lines20 := breakLines 20 lineBreaker_overflowAtomic_items
    lines80.length = 2 ∧
    (lines80.getD 0 default).inlineSize = 80 ∧
    (lines80.getD 1 default).inlineSize = 30 ∧
    lines70.length = 2 ∧
    (lines70.getD 0 default).inlineSize = 50 ∧
    (lines70.getD 1 default).inlineSize = 60 ∧
    lines40.length = 3 ∧
    (lines40.getD 0 default).inlineSize = 50 ∧
    (lines40.getD 1 default).inlineSize = 30 ∧
    (lines40.getD 2 default).inlineSize = 30 ∧
    lines20.length = 3 ∧
    (lines20.getD 0 default).inlineSize = 50 ∧
    (lines20.getD 1 default).inlineSize = 30 ∧
    (lines20.getD 2 default).inlineSize = 30 := by
  decide

/-! ### Test 12: OverflowAfterSpacesAcrossElements (line_breaker_test.cc:423) -/
theorem lineBreaker_overflowAfterSpaces :
    let items := [mkWord 1 40, mkSpace 2 10, mkSpace 3 10, mkWord 4 10]
    let lines := breakLines 50 items
    lines.length = 2 ∧
    (lines.getD 0 default).inlineSize = 40 ∧
    (lines.getD 1 default).inlineSize = 10 := by
  decide

/-! ### Test 13: WrapLastWord (line_breaker_test.cc:447) -/
def lineBreaker_wrapLastWord_items : List InlineItem :=
  [ mkWord 1 30, mkSpace 2 10, mkWord 3 30, mkSpace 4 10, mkWord 5 30, mkSpace 6 10
  , mkOpen 7, mkWord 8 20, mkClose 9, mkSpace 10 10, mkWord 11 20
  ]

theorem lineBreaker_wrapLastWord :
    let lines := breakLines 100 lineBreaker_wrapLastWord_items
    lines.length = 2 ∧
    (lines.getD 0 default).inlineSize = 70 ∧
    (lines.getD 1 default).inlineSize = 90 := by
  decide

/-! ### Test 14: WrapLetterSpacing (line_breaker_test.cc:466) -/
theorem lineBreaker_wrapLetterSpacing :
    let items := [mkWord 1 40, mkSpace 2 10, mkWord 3 20]
    let lines := breakLines 50 items
    lines.length = 2 ∧
    (lines.getD 0 default).inlineSize = 40 ∧
    (lines.getD 1 default).inlineSize = 20 := by
  decide

/-! ### Test 17: IdeographicTrailingSpaces (line_breaker_test.cc:548) -/
theorem lineBreaker_ideographicTrailingSpaces :
    let lines := breakLines 190 [mkWord 0 180, mkWord 1 20 false]
    lines.length = 2 ∧
    (lines.getD 0 default).inlineSize = 180 ∧
    (lines.getD 1 default).inlineSize = 20 := by
  decide

/-! ### Test 31: IdeographicSpaceBeforeEndBracket (line_breaker_test.cc:965) -/
theorem lineBreaker_ideographicBeforeBracket :
    let lines := breakLines 190 [mkWord 0 180, mkWord 2 10 false, mkWord 1 20 false]
    lines.length = 2 ∧
    (lines.getD 0 default).inlineSize = 190 ∧
    (lines.getD 1 default).inlineSize = 20 := by
  decide

/-! ### Test 32, 33, 34: BreakAt explicit breakpoints (line_breaker_test.cc:1002, 1044, 1079) -/
theorem lineBreaker_breakAt :
    let l1 := breakLines 800 [mkWord 1 10, .ForcedBreak 2, mkWord 3 40, .ForcedBreak 4, mkWord 5 10, .ForcedBreak 6, mkWord 7 30]
    l1.length = 4 ∧
    (l1.getD 0 default).inlineSize = 10 ∧
    (l1.getD 1 default).inlineSize = 40 ∧
    (l1.getD 2 default).inlineSize = 10 ∧
    (l1.getD 3 default).inlineSize = 30 := by
  decide

/-! ### Test 45: BidiControlEnterFlag (line_breaker_test.cc:1331) -/
theorem lineBreaker_bidiControlEnter :
    let strut : FontHeight := { ascent := 8, descent := 2 }
    let li : LineInfo := { items := [mkWord 1 30], inlineSize := 30, nonBreakItemCount := 1 }
    let lb := createLineBox strut li
    lb.metrics.lineHeight = 10 := by
  decide

/-! ### General Line Breaker Progress Law -/
theorem line_breaker_single_word_progress (avail : Nat) (w : Nat) (id : Nat) :
    let item := mkWord id w
    let lines := breakLines avail [item]
    lines.length = 1 ∧ (lines.getD 0 default).inlineSize = w := by
  dsimp [breakLines, breakLinesFuel, takeLine]
  exact ⟨rfl, rfl⟩

end ChromiumLayout.TestsInline
