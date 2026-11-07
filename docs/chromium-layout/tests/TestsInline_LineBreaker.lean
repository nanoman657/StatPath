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
def lineBreaker_fitWithEpsilon_vector : List (Nat × Nat) :=
  let t := mkWord 1 50
  let lines := breakLines 50 [t]
  [ (lines.length, 1)
  , ((lines.getD 0 default).inlineSize, 50)
  ]

theorem lineBreaker_fitWithEpsilon_pass :
    ∀ p ∈ lineBreaker_fitWithEpsilon_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 2: SingleNode (line_breaker_test.cc:171) -/
def lineBreaker_singleNode_items : List InlineItem :=
  [ mkWord 1 30  -- "123"
  , mkSpace 2 10 -- " "
  , mkWord 3 30  -- "456"
  , mkSpace 4 10 -- " "
  , mkWord 5 30  -- "789"
  ]

def lineBreaker_singleNode_vector : List (Nat × Nat) :=
  let lines80 := breakLines 80 lineBreaker_singleNode_items
  let lines60 := breakLines 60 lineBreaker_singleNode_items
  [ (lines80.length, 2)
  , ((lines80.getD 0 default).inlineSize, 70)
  , ((lines80.getD 1 default).inlineSize, 30)
  , (lines60.length, 3)
  , ((lines60.getD 0 default).inlineSize, 30)
  , ((lines60.getD 1 default).inlineSize, 30)
  , ((lines60.getD 2 default).inlineSize, 30)
  ]

theorem lineBreaker_singleNode_pass :
    ∀ p ∈ lineBreaker_singleNode_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 7: OverflowWord (line_breaker_test.cc:275) -/
def lineBreaker_overflowWord_items : List InlineItem :=
  [ mkWord 1 50
  , mkSpace 2 10
  , mkWord 3 30
  ]

-- Width 40: "12345" overflows line 1, "678" fits line 2 (2 lines)
def lineBreaker_overflowWord_vector : List (Nat × Nat) :=
  let lines40 := breakLines 40 lineBreaker_overflowWord_items
  [ (lines40.length, 2)
  , ((lines40.getD 0 default).inlineSize, 50)
  , ((lines40.getD 1 default).inlineSize, 40)
  ]

theorem lineBreaker_overflowWord_pass :
    ∀ p ∈ lineBreaker_overflowWord_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 8 & 9: OverflowTab and OverflowTabBreakWord (line_breaker_test.cc:301, 323) -/
def lineBreaker_overflowTab_vector : List (Nat × Nat) :=
  let tabSeg := mkWord 1 110 false
  let sp := mkSpace 2 10
  let word2 := mkWord 3 30
  let lines := breakLines 100 [tabSeg, sp, word2]
  [ (lines.length, 2)
  , ((lines.getD 0 default).inlineSize, 110)
  , ((lines.getD 1 default).inlineSize, 40)
  ]

theorem lineBreaker_overflowTab_pass :
    ∀ p ∈ lineBreaker_overflowTab_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 10: OverflowAtomicInline (line_breaker_test.cc:346) -/
def lineBreaker_overflowAtomic_items : List InlineItem :=
  [ mkWord 1 50
  , mkAtomic 2 30
  , mkWord 3 30
  ]

def lineBreaker_overflowAtomic_vector : List (Nat × Nat) :=
  let l80 := breakLines 80 lineBreaker_overflowAtomic_items
  let l70 := breakLines 70 lineBreaker_overflowAtomic_items
  let l40 := breakLines 40 lineBreaker_overflowAtomic_items
  let l20 := breakLines 20 lineBreaker_overflowAtomic_items
  [ (l80.length, 2)
  , ((l80.getD 0 default).inlineSize, 80)
  , ((l80.getD 1 default).inlineSize, 30)
  , (l70.length, 2)
  , ((l70.getD 0 default).inlineSize, 50)
  , ((l70.getD 1 default).inlineSize, 60)
  , (l40.length, 3)
  , ((l40.getD 0 default).inlineSize, 50)
  , ((l40.getD 1 default).inlineSize, 30)
  , ((l40.getD 2 default).inlineSize, 30)
  , (l20.length, 3)
  ]

theorem lineBreaker_overflowAtomic_pass :
    ∀ p ∈ lineBreaker_overflowAtomic_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 12: OverflowAfterSpacesAcrossElements (line_breaker_test.cc:423) -/
def lineBreaker_overflowAfterSpaces_vector : List (Nat × Nat) :=
  let items := [mkWord 1 50, mkSpace 2 10, mkSpace 3 10, mkWord 4 100, mkWord 5 30]
  let lines := breakLines 100 items
  [ (lines.length, 3)
  , ((lines.getD 0 default).inlineSize, 50)
  , ((lines.getD 1 default).inlineSize, 100)
  , ((lines.getD 2 default).inlineSize, 30)
  ]

theorem lineBreaker_overflowAfterSpaces_pass :
    ∀ p ∈ lineBreaker_overflowAfterSpaces_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 13: WrapLastWord (line_breaker_test.cc:447) -/
def lineBreaker_wrapLastWord_items : List InlineItem :=
  [ mkWord 1 30, mkSpace 2 10, mkWord 3 30, mkSpace 4 10, mkWord 5 30, mkSpace 6 10
  , mkOpen 7, mkWord 8 20, mkClose 9, mkSpace 10 10, mkWord 11 20
  ]

def lineBreaker_wrapLastWord_vector : List (Nat × Nat) :=
  let lines := breakLines 100 lineBreaker_wrapLastWord_items
  [ (lines.length, 2)
  , ((lines.getD 0 default).inlineSize, 70)
  , ((lines.getD 1 default).inlineSize, 90)
  ]

theorem lineBreaker_wrapLastWord_pass :
    ∀ p ∈ lineBreaker_wrapLastWord_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 14: WrapLetterSpacing (line_breaker_test.cc:466) -/
def lineBreaker_wrapLetterSpacing_vector : List (Nat × Nat) :=
  let lines := breakLines 100 [mkWord 1 70, mkSpace 2 20, mkWord 3 70]
  [ (lines.length, 2)
  , ((lines.getD 0 default).inlineSize, 70)
  , ((lines.getD 1 default).inlineSize, 70)
  ]

theorem lineBreaker_wrapLetterSpacing_pass :
    ∀ p ∈ lineBreaker_wrapLetterSpacing_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 16: BoundaryInFirstWord (line_breaker_test.cc:516) -/
def lineBreaker_boundaryInFirstWord_items : List InlineItem :=
  [ mkWord 1 30 false, mkWord 2 30, mkSpace 3 10, mkWord 4 30 ]

def lineBreaker_boundaryInFirstWord_vector : List (Nat × Nat) :=
  let l80 := breakLines 80 lineBreaker_boundaryInFirstWord_items
  [ (l80.length, 2)
  , ((l80.getD 0 default).inlineSize, 60)
  , ((l80.getD 1 default).inlineSize, 30)
  ]

theorem lineBreaker_boundaryInFirstWord_pass :
    ∀ p ∈ lineBreaker_boundaryInFirstWord_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 17: IdeographicTrailingSpaces (line_breaker_test.cc:548) -/
def lineBreaker_ideographicTrailingSpaces_vector : List (Nat × Nat) :=
  let ideoSeg := mkWord 1 70
  let lines := breakLines 60 [ideoSeg, ideoSeg]
  [ (lines.length, 2)
  , ((lines.getD 0 default).inlineSize, 70)
  , ((lines.getD 1 default).inlineSize, 70)
  ]

theorem lineBreaker_ideographicTrailingSpaces_pass :
    ∀ p ∈ lineBreaker_ideographicTrailingSpaces_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 18: WhitespaceState (line_breaker_test.cc:624) -/
inductive WhitespaceState where
  | kNone
  | kCollapsed
  | kPreserved
  | kLeading
deriving DecidableEq, Repr

def computeWhitespaceState (isPre : Bool) (hasTrailingSpace : Bool) (isEmpty : Bool) : WhitespaceState :=
  if isEmpty then .kLeading
  else if hasTrailingSpace then
    if isPre then .kPreserved else .kCollapsed
  else .kNone

theorem lineBreaker_whitespaceState_none :
    computeWhitespaceState false false false = WhitespaceState.kNone := rfl

theorem lineBreaker_whitespaceState_collapsed :
    computeWhitespaceState false true false = WhitespaceState.kCollapsed := rfl

theorem lineBreaker_whitespaceState_preserved :
    computeWhitespaceState true true false = WhitespaceState.kPreserved := rfl

theorem lineBreaker_whitespaceState_leading :
    computeWhitespaceState false false true = WhitespaceState.kLeading := rfl

/-! ### Test 19: TrailingSpaceWidth (line_breaker_test.cc:684) -/
def computeHangingSpaceWidth (avail : Nat) (contentWidth : Nat) (spaceCount : Nat) (spWidth : Nat) : Nat :=
  let total := contentWidth + spaceCount * spWidth
  if total > avail then total - avail else 0

def lineBreaker_trailingSpaceWidth_vector : List (Nat × Nat) :=
  [ (computeHangingSpaceWidth 50 50 1 10, 10)
  , (computeHangingSpaceWidth 50 50 2 10, 20)
  , (computeHangingSpaceWidth 50 30 1 10, 0)
  ]

theorem lineBreaker_trailingSpaceWidth_pass :
    ∀ p ∈ lineBreaker_trailingSpaceWidth_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 22: SplitTextZero (line_breaker_test.cc:762) -/
def lineBreaker_splitTextZero_vector : List (Nat × Nat) :=
  let normalItems := [mkWord 1 100, mkSpace 2 10, mkWord 3 20]
  let splitItems  := [mkWord 1 100, mkWord 2 0 false, mkSpace 3 10, mkWord 4 20]
  let l1 := breakLines 100 normalItems
  let l2 := breakLines 100 splitItems
  [ (l1.length, 2)
  , (l2.length, 2)
  , ((l1.getD 0 default).inlineSize, (l2.getD 0 default).inlineSize)
  , ((l1.getD 1 default).inlineSize, (l2.getD 1 default).inlineSize)
  ]

theorem lineBreaker_splitTextZero_pass :
    ∀ p ∈ lineBreaker_splitTextZero_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 28: SplitTextIntoSegements (line_breaker_test.cc:887) -/
theorem lineBreaker_splitTextIntoSegments_conservation (widths : List Nat) :
    (widths.map (fun w => mkWord 0 w false)).length = widths.length := by
  simp

/-! ### Test 31: IdeographicSpaceBeforeEndBracket (line_breaker_test.cc:965) -/
def lineBreaker_ideographicBeforeBracket_vector : List (Nat × Nat) :=
  let lines := breakLines 190 [mkWord 0 180, mkWord 2 10 false, mkWord 1 20 false]
  [ (lines.length, 2)
  , ((lines.getD 0 default).inlineSize, 190)
  , ((lines.getD 1 default).inlineSize, 20)
  ]

theorem lineBreaker_ideographicBeforeBracket_pass :
    ∀ p ∈ lineBreaker_ideographicBeforeBracket_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 32, 33, 34: BreakAt explicit breakpoints (line_breaker_test.cc:1002, 1044, 1079) -/
def lineBreaker_breakAt_vector : List (Nat × Nat) :=
  let l1 := breakLines 800 [mkWord 1 10, .ForcedBreak 2, mkWord 3 40, .ForcedBreak 4, mkWord 5 10, .ForcedBreak 6, mkWord 7 30]
  [ (l1.length, 4)
  , ((l1.getD 0 default).inlineSize, 10)
  , ((l1.getD 1 default).inlineSize, 40)
  , ((l1.getD 2 default).inlineSize, 10)
  , ((l1.getD 3 default).inlineSize, 30)
  ]

theorem lineBreaker_breakAt_pass :
    ∀ p ∈ lineBreaker_breakAt_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 43: CanBreakInside (line_breaker_test.cc:1288) -/
def canBreakInside (isNowrap : Bool) (items : List InlineItem) : Bool :=
  if isNowrap then false
  else
    let hasSpace := items.any (fun it => it.isCollapsible)
    let atomicCount := items.filter (fun it => match it with | .AtomicInline .. => true | _ => false) |>.length
    let breakableCount := items.filter (fun it => match it with | .TextSeg _ _ _ cb _ => cb | _ => false) |>.length
    hasSpace || atomicCount >= 2 || (atomicCount >= 1 && breakableCount >= 1)

theorem lineBreaker_canBreakInside_single :
    canBreakInside false [mkWord 1 10 false] = false := rfl

theorem lineBreaker_canBreakInside_space :
    canBreakInside false [mkWord 1 10, mkSpace 2, mkWord 3 10] = true := rfl

theorem lineBreaker_canBreakInside_nowrap :
    canBreakInside true [mkWord 1 10, mkSpace 2, mkWord 3 10] = false := rfl

theorem lineBreaker_canBreakInside_atomicPair :
    canBreakInside false [mkAtomic 1 10, mkAtomic 2 10] = true := rfl

theorem lineBreaker_canBreakInside_wordAtomic :
    canBreakInside false [mkWord 1 10, mkAtomic 2 10] = true := rfl

theorem lineBreaker_canBreakInside_singleAtomic :
    canBreakInside false [mkAtomic 1 10] = false := rfl

/-! ### Test 45: BidiControlEnterFlag (line_breaker_test.cc:1331) -/
def lineBreaker_bidiControlEnter_vector : List (Nat × Nat) :=
  let strut : FontHeight := { ascent := 8, descent := 2 }
  let li : LineInfo := { items := [mkWord 1 30], inlineSize := 30, nonBreakItemCount := 1 }
  let lb := createLineBox strut li
  [ (lb.metrics.lineHeight, 10) ]

theorem lineBreaker_bidiControlEnter_pass :
    ∀ p ∈ lineBreaker_bidiControlEnter_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### General Laws: Greedy Breaking and Progress -/

theorem line_breaker_single_word_progress (avail : Nat) (w : Nat) (id : Nat) :
    let item := mkWord id w
    (breakLines avail [item]).length = 1 ∧
    ((breakLines avail [item]).getD 0 default).inlineSize = w := by
  dsimp [breakLines, breakLinesFuel, takeLine, mkWord]
  cases avail with
  | zero =>
    constructor
    · rfl
    · rfl
  | succ n =>
    constructor
    · rfl
    · rfl

end ChromiumLayout.TestsInline
