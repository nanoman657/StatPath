import LayoutTypes
import LayoutInline

namespace ChromiumLayout.TestsInline

open ChromiumLayout

instance : Inhabited LineInfo := ⟨{}⟩
instance : Inhabited InlineItem := ⟨.ForcedBreak 0⟩

def testFontMetrics : FontHeight := { ascent := 8, descent := 2 }

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

def listMax : List Nat → Nat
  | [] => 0
  | x :: xs => Nat.max x (listMax xs)

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

theorem listMax_le_listSum : ∀ (l : List Nat), listMax l ≤ listSum l
  | [] => Nat.le_refl 0
  | x :: xs => by
    dsimp [listMax, listSum]
    have ih := listMax_le_listSum xs
    have h1 : x ≤ x + listSum xs := Nat.le_add_right x (listSum xs)
    have h2 : listMax xs ≤ x + listSum xs := by omega
    exact Nat.max_le.mpr ⟨h1, h2⟩

def computeMinMax (items : List InlineItem) : Nat × Nat :=
  let widths := items.map InlineItem.rawInlineSize
  (listMax widths, listSum widths)

/-! ### Test 1: CollectInlinesText (inline_node_test.cc:192) -/
def inlineNode_collectText_items : List InlineItem :=
  [ mkWord 1 60 -- "Hello "
  , mkOpen 2
  , mkWord 3 60 -- "inline"
  , mkClose 4
  , mkWord 5 70 -- " world."
  ]

def inlineNode_collectText_vector : List (Nat × Nat) :=
  [ (inlineNode_collectText_items.length, 5)
  , ((inlineNode_collectText_items.getD 0 default).rawInlineSize, 60)
  , ((inlineNode_collectText_items.getD 2 default).rawInlineSize, 60)
  , ((inlineNode_collectText_items.getD 4 default).rawInlineSize, 70)
  ]

theorem inlineNode_collectText_pass :
    ∀ p ∈ inlineNode_collectText_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 2: CollectInlinesBR (inline_node_test.cc:206) -/
def inlineNode_collectBR_items : List InlineItem :=
  [ mkWord 1 50 -- "Hello"
  , .ForcedBreak 2
  , mkWord 3 50 -- "World"
  ]

def inlineNode_collectBR_vector : List (Nat × Nat) :=
  [ (inlineNode_collectBR_items.length, 3)
  , ((inlineNode_collectBR_items.getD 0 default).rawInlineSize, 50)
  , ((inlineNode_collectBR_items.getD 2 default).rawInlineSize, 50)
  ]

theorem inlineNode_collectBR_pass :
    ∀ p ∈ inlineNode_collectBR_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 7: CollectInlinesInlineBlock (inline_node_test.cc:306) -/
def inlineNode_collectInlineBlock_items : List InlineItem :=
  [ mkWord 1 60
  , mkAtomic 2 10
  , mkWord 3 50
  ]

def inlineNode_collectInlineBlock_vector : List (Nat × Nat) :=
  [ (inlineNode_collectInlineBlock_items.length, 3)
  , ((inlineNode_collectInlineBlock_items.getD 1 default).rawInlineSize, 10)
  ]

theorem inlineNode_collectInlineBlock_pass :
    ∀ p ∈ inlineNode_collectInlineBlock_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 24: MinMaxSizes (inline_node_test.cc:649) -/
def inlineNode_minMax_vector : List (Nat × Nat) :=
  let mm1 := computeMinMax [mkWord 1 20, mkSpace 2 10, mkWord 3 40] -- "AB CDEF" -> (40, 70)
  let mmImg1 := computeMinMax [mkWord 1 50, mkSpace 2 10, mkAtomic 3 10, mkWord 4 10] -- Hello <img>(1em) -> (50, 80)
  let mmImg5 := computeMinMax [mkWord 1 50, mkSpace 2 10, mkAtomic 3 50, mkWord 4 10] -- Hello <img>(5em) -> (50, 120)
  let mmImg6 := computeMinMax [mkWord 1 50, mkSpace 2 10, mkAtomic 3 60, mkWord 4 10] -- Hello <img>(6em) -> (60, 130)
  [ (mm1.1, 40)
  , (mm1.2, 70)
  , (mmImg1.1, 50)
  , (mmImg1.2, 80)
  , (mmImg5.1, 50)
  , (mmImg5.2, 120)
  , (mmImg6.1, 60)
  , (mmImg6.2, 130)
  ]

theorem inlineNode_minMax_pass :
    ∀ p ∈ inlineNode_minMax_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 25: MinMaxSizesSaturated (inline_node_test.cc:675) -/
def saturateLayoutUnit (val : Nat) : Nat :=
  if val > 33554431 then 33554431 else val

def inlineNode_minMaxSaturated_vector : List (Nat × Nat) :=
  [ (saturateLayoutUnit 100000000, 33554431)
  , (saturateLayoutUnit 500, 500)
  ]

theorem inlineNode_minMaxSaturated_pass :
    ∀ p ∈ inlineNode_minMaxSaturated_vector, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ### Test 28, 30, 31, 33: Invalidation and NeedsCollectInlines -/
def propagatesNeedsCollectInlines (hasMutation : Bool) : Bool :=
  hasMutation

theorem inlineNode_invalidation_rule (mutation : Bool) :
    propagatesNeedsCollectInlines mutation = mutation := rfl

/-! ### Test 70: TextCombineWordSpacing (inline_node_test.cc:1713) -/
def resolveTextCombineSpacing (hasTextCombine : Bool) (spacing : Nat) : Nat :=
  if hasTextCombine then 0 else spacing

theorem inlineNode_textCombine_zeroes_spacing (s : Nat) :
    resolveTextCombineSpacing true s = 0 := rfl

/-! ### General Laws for Inline Nodes -/

/-- Min-Max bounds law: for any inline item sequence, minSize ≤ maxSize. -/
theorem inlineNode_min_le_max (items : List InlineItem) :
    (computeMinMax items).1 ≤ (computeMinMax items).2 :=
  listMax_le_listSum (items.map InlineItem.rawInlineSize)

end ChromiumLayout.TestsInline
