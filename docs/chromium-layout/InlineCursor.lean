/-
  docs/chromium-layout/InlineCursor.lean

  Formal model for Blink InlineCursor
  (`third_party/blink/renderer/core/layout/inline/inline_cursor.h`,
   `inline_cursor.cc`).

  Owns: CursorItem, cursor tree navigation (parent, child, line, leaf),
  and hit-testing monotonicity laws for LTR and RTL.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineCaret

namespace ChromiumLayout

/-! ## 1. Cursor Item Model -/

/-- An item visited by `InlineCursor` (`inline/inline_cursor.h:85-230`). -/
structure CursorItem where
  id : Nat := 0
  type : FragmentItemType := .text
  parentId : Option Nat := none
  lineIndex : Nat := 0
  bidiLevel : Nat := 0
  textOffset : Nat := 0
  textLength : Nat := 0
  isLeaf : Bool := true
  isLineBox : Bool := false
  deriving DecidableEq, Repr

/-- Clamped character count for hit testing. -/
def clampedHitCount (rel : Nat) (charWidth : Nat) (textLength : Nat) : Nat :=
  if charWidth == 0 then 0
  else Nat.min textLength (rel / charWidth)

theorem clampedHitCount_le_textLength (rel : Nat) (charWidth : Nat) (textLength : Nat) :
    clampedHitCount rel charWidth textLength ≤ textLength := by
  dsimp [clampedHitCount]
  split
  · omega
  · exact Nat.min_le_left _ _

theorem clampedHitCount_mono (charWidth : Nat) (textLength : Nat)
    (rel1 rel2 : Nat) (hLe : rel1 ≤ rel2) :
    clampedHitCount rel1 charWidth textLength ≤ clampedHitCount rel2 charWidth textLength := by
  dsimp [clampedHitCount]
  split
  · omega
  · have hDiv : rel1 / charWidth ≤ rel2 / charWidth := Nat.div_le_div_right hLe
    exact Nat.le_min.mpr ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) hDiv⟩

/-- Hit testing: map local coordinate to character offset within text run
    (`inline/inline_cursor.cc:1420-1550`, `PositionForPointInChild`).
    In LTR: charOffset = clampedHitCount(relX, charWidth, textLength).
    In RTL: charOffset = textLength - clampedHitCount(relX, charWidth, textLength). -/
def hitTestTextOffset (isRtl : Bool) (x : Int) (left : Int) (charWidth : Nat) (textLength : Nat) : Nat :=
  let relX := x - left
  if relX ≤ 0 then
    if isRtl then textLength else 0
  else
    let c := clampedHitCount relX.toNat charWidth textLength
    if isRtl then textLength - c else c

/-! ## 2. Hit Testing Monotonicity Laws -/

/-- In LTR mode, hit-testing character offset is monotonically non-decreasing with coordinate `x`. -/
theorem hitTest_ltr_monotonic (left : Int) (charWidth : Nat) (textLength : Nat) :
    ∀ (x1 x2 : Int), x1 ≤ x2 →
      hitTestTextOffset false x1 left charWidth textLength ≤
      hitTestTextOffset false x2 left charWidth textLength := by
  intro x1 x2 hLe
  dsimp [hitTestTextOffset]
  split
  · -- x1 - left <= 0
    split
    · omega
    · omega
  · -- x1 - left > 0
    split
    · -- x2 - left <= 0, impossible since x1 <= x2
      omega
    · -- x2 - left > 0
      have hRelLe : (x1 - left).toNat ≤ (x2 - left).toNat :=
        Int.toNat_le_toNat (by omega)
      exact clampedHitCount_mono charWidth textLength (x1 - left).toNat (x2 - left).toNat hRelLe

/-- In RTL mode, hit-testing character offset is monotonically non-increasing with coordinate `x`. -/
theorem hitTest_rtl_monotonic (left : Int) (charWidth : Nat) (textLength : Nat) :
    ∀ (x1 x2 : Int), x1 ≤ x2 →
      hitTestTextOffset true x2 left charWidth textLength ≤
      hitTestTextOffset true x1 left charWidth textLength := by
  intro x1 x2 hLe
  dsimp [hitTestTextOffset]
  split
  · -- x2 - left <= 0
    split
    · omega
    · omega
  · -- x2 - left > 0
    split
    · -- x1 - left <= 0
      have hBound := clampedHitCount_le_textLength (x2 - left).toNat charWidth textLength
      omega
    · -- x1 - left > 0
      have hRelLe : (x1 - left).toNat ≤ (x2 - left).toNat :=
        Int.toNat_le_toNat (by omega)
      have hCLe := clampedHitCount_mono charWidth textLength (x1 - left).toNat (x2 - left).toNat hRelLe
      omega

/-! ## 3. Cursor Tree Model & Navigation (CSS 2.1 §9.4.2, §9.5, §9.3, CSS Inline 3 §2, CSS Writing Modes 3 §3.2) -/

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2: A node in the pre-order flat fragment tree of an inline formatting context
    (`third_party/blink/renderer/core/layout/inline/inline_cursor.h:85-230`). -/
structure CursorNode where
  id : String := ""
  name : String := ""
  type : FragmentItemType := .text
  descendantsCount : Nat := 0
  lineIndex : Nat := 0
  isAtomic : Bool := false
  isLineBreak : Bool := false
  isEmptyLine : Bool := false
  isFloat : Bool := false
  isOutOfFlow : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Find parent index in pre-order flat tree: innermost ancestor whose descendants span over target. -/
def findParentAux (nodes : List CursorNode) (target : Nat) : Nat → Option Nat
  | 0 =>
    match nodes[0]? with
    | some n => if target ≤ n.descendantsCount then some 0 else none
    | none => none
  | k + 1 =>
    match nodes[k + 1]? with
    | some n =>
      if target ≤ (k + 1) + n.descendantsCount then some (k + 1)
      else findParentAux nodes target k
    | none => findParentAux nodes target k

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2: Move to parent box or line box. -/
def findParent (nodes : List CursorNode) : Nat → Option Nat
  | 0 => none
  | k + 1 => findParentAux nodes (k + 1) k

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2: Move to first child in pre-order traversal. -/
def findFirstChild (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nodes[idx]? with
  | some n =>
    if n.descendantsCount > 0 ∧ ¬n.isAtomic ∧ idx + 1 < nodes.length then
      some (idx + 1)
    else none
  | none => none

/-- Backward search for last direct child among descendants. -/
def findLastChildAux (nodes : List CursorNode) (parentIdx : Nat) : Nat → Option Nat
  | 0 => none
  | count + 1 =>
    let candidate := parentIdx + count + 1
    if findParent nodes candidate == some parentIdx then
      some candidate
    else
      findLastChildAux nodes parentIdx count

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2: Move to last direct child of current container box. -/
def findLastChild (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nodes[idx]? with
  | some n =>
    if n.descendantsCount > 0 ∧ ¬n.isAtomic then
      findLastChildAux nodes idx n.descendantsCount
    else none
  | none => none

/-- Repeatedly descend through first children until leaf. -/
def firstLogicalLeafAux (nodes : List CursorNode) : Nat → Nat → Nat
  | 0, cur => cur
  | fuel + 1, cur =>
    match findFirstChild nodes cur with
    | some child => firstLogicalLeafAux nodes fuel child
    | none => cur

/-- Repeatedly descend through last children until leaf. -/
def lastLogicalLeafAux (nodes : List CursorNode) : Nat → Nat → Nat
  | 0, cur => cur
  | fuel + 1, cur =>
    match findLastChild nodes cur with
    | some child => lastLogicalLeafAux nodes fuel child
    | none => cur

/-- CSS Writing Modes 3 §3.2: First logical leaf in reading order.
    In LTR: leftmost leaf (descend through first children).
    In RTL: rightmost leaf (descend through last children). -/
def firstLogicalLeaf (nodes : List CursorNode) (root : Nat) (isRtl : Bool) : Nat :=
  if isRtl then lastLogicalLeafAux nodes nodes.length root
  else firstLogicalLeafAux nodes nodes.length root

/-- CSS Writing Modes 3 §3.2: Last logical leaf in reading order.
    In LTR: rightmost leaf (descend through last children).
    In RTL: leftmost leaf (descend through first children). -/
def lastLogicalLeaf (nodes : List CursorNode) (root : Nat) (isRtl : Bool) : Nat :=
  if isRtl then firstLogicalLeafAux nodes nodes.length root
  else lastLogicalLeafAux nodes nodes.length root

def findContainingLineAux (nodes : List CursorNode) : Nat → Option Nat
  | 0 =>
    match nodes[0]? with
    | some n => if n.type == .line ∨ n.name == "#linebox" then some 0 else none
    | none => none
  | k + 1 =>
    match nodes[k + 1]? with
    | some n =>
      if n.type == .line ∨ n.name == "#linebox" then some (k + 1)
      else findContainingLineAux nodes k
    | none => findContainingLineAux nodes k

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2: Containing line box of an inline fragment. -/
def findContainingLine (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  findContainingLineAux nodes idx

/-- Blink InlineCursor::MoveToNextSkippingChildren. -/
def nextSkippingChildren (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nodes[idx]? with
  | some n =>
    let nextIdx := idx + 1 + n.descendantsCount
    if nextIdx < nodes.length then some nextIdx else none
  | none => none

/-- CSS 2.1 §9.4.2: Move to next line box. -/
def findNextLine (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nextSkippingChildren nodes idx with
  | some nextIdx =>
    if nextIdx < nodes.length then
      match nodes[nextIdx]? with
      | some n => if n.type == .line ∨ n.name == "#linebox" then some nextIdx else none
      | none => none
    else none
  | none => none

/-- CSS Inline 3 §2 & Blink InlineCursorPosition::IsInlineLeaf. -/
def isInlineLeaf (n : CursorNode) (ignoreLineBreak : Bool := false) : Bool :=
  if n.isLineBreak then ¬ignoreLineBreak
  else (n.type == .text ∨ n.isAtomic) ∧
       (n.descendantsCount == 0 ∨ n.isAtomic) ∧
       n.type != .line ∧ n.name != "#linebox"

/-- Collect all inline leaf debug strings visited by MoveToNextInlineLeaf. -/
def collectInlineLeaves (nodes : List CursorNode) (ignoreLineBreak : Bool := false) : List String :=
  let firstLine := match nodes[0]? with
    | some n => if n.type == .line ∨ n.name == "#linebox" then [n.name] else []
    | none => []
  let leaves := nodes.filter (fun n => isInlineLeaf n ignoreLineBreak) |>.map CursorNode.name
  firstLine ++ leaves

/-- Collect ancestor element IDs walking up via findParent. -/
def collectAncestorIds (nodes : List CursorNode) (startIdx : Nat) : List String :=
  let rec loop (cur : Nat) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match findParent nodes cur with
      | some p =>
        match nodes[p]? with
        | some parentNode =>
          let rest := loop p fuel
          if parentNode.id != "" then parentNode.id :: rest else rest
        | none => []
      | none => []
  loop startIdx nodes.length

/-- CSS 2.1 §9.4.2, §9.5, §9.3: Filter in-flow inline items for culled inline box,
    excluding floating and out-of-flow positioned elements. -/
def culledInFlowItems (items : List CursorNode) : List CursorNode :=
  items.filter (fun n => ¬n.isFloat ∧ ¬n.isOutOfFlow)

def culledInFlowNames (items : List CursorNode) : List String :=
  (culledInFlowItems items).map CursorNode.name

/-- Pre-order DFS traversal of cursor items. -/
def collectPreOrder (nodes : List CursorNode) : List String :=
  nodes.map CursorNode.name

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: Move to next inline leaf on the same line box.
    If current node is a container box, skips its descendants and moves to the first leaf in following siblings on the same line.
    If current node is a leaf, moves to next leaf on the same line. -/
def nextInlineLeafOnLine (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nodes[idx]? with
  | some cur =>
    let startIdx :=
      if cur.descendantsCount > 0 ∧ ¬cur.isAtomic then
        idx + 1 + cur.descendantsCount
      else
        idx + 1
    let rec findNext (k : Nat) (fuel : Nat) : Option Nat :=
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match nodes[k]? with
        | some n =>
          if n.lineIndex == cur.lineIndex then
            if isInlineLeaf n then some k
            else findNext (k + 1) fuel
          else none
        | none => none
    findNext startIdx nodes.length
  | none => none

/-- Collect leaf names on line using nextInlineLeafOnLine. -/
def collectInlineLeavesOnLine (nodes : List CursorNode) (startIdx : Nat) : List String :=
  let rec loop (cur : Nat) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match nodes[cur]? with
      | some n =>
        let name := n.name
        match nextInlineLeafOnLine nodes cur with
        | some nextIdx => name :: loop nextIdx fuel
        | none => [name]
      | none => []
  loop startIdx nodes.length

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: Move to previous inline leaf on the same line box.
    If current node is a container box, looks backward among previous siblings/leaves on the same line. -/
def previousInlineLeafOnLine (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nodes[idx]? with
  | some cur =>
    let rec findPrev : Nat → Option Nat
      | 0 => none
      | k + 1 =>
        match nodes[k]? with
        | some n =>
          if n.lineIndex == cur.lineIndex then
            if isInlineLeaf n then some k
            else findPrev k
          else none
        | none => none
    findPrev idx
  | none => none

/-- Collect leaf names backward on line using previousInlineLeafOnLine. -/
def collectPreviousInlineLeavesOnLine (nodes : List CursorNode) (startIdx : Nat) : List String :=
  let rec loop (cur : Nat) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match nodes[cur]? with
      | some n =>
        let name := n.name
        match previousInlineLeafOnLine nodes cur with
        | some prevIdx => name :: loop prevIdx fuel
        | none => [name]
      | none => []
  loop startIdx nodes.length

/-- CSS 2.1 §9.4.2: Move to previous item in pre-order traversal. -/
def previousCursor (idx : Nat) : Option Nat :=
  if idx > 0 then some (idx - 1) else none

/-- Collect backward pre-order traversal names. -/
def collectPrevious (nodes : List CursorNode) (startIdx : Nat) : List String :=
  let rec loop (cur : Nat) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match nodes[cur]? with
      | some n =>
        let name := n.name
        match previousCursor cur with
        | some prevIdx => name :: loop prevIdx fuel
        | none => [name]
      | none => []
  loop startIdx nodes.length

/-- CSS Inline 3 §2: Move to previous inline leaf in IFC traversal. -/
def previousInlineLeaf (nodes : List CursorNode) (idx : Nat) (ignoreLineBreak : Bool := false) : Option Nat :=
  let rec findPrev : Nat → Option Nat
    | 0 => none
    | k + 1 =>
      match nodes[k]? with
      | some n =>
        if isInlineLeaf n ignoreLineBreak then some k
        else findPrev k
      | none => none
  findPrev idx

/-- Collect backward inline leaf names. -/
def collectPreviousInlineLeaves (nodes : List CursorNode) (startIdx : Nat) (ignoreLineBreak : Bool := false) : List String :=
  let rec loop (cur : Nat) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match nodes[cur]? with
      | some n =>
        let name := n.name
        match previousInlineLeaf nodes cur ignoreLineBreak with
        | some prevIdx => name :: loop prevIdx fuel
        | none => [name]
      | none => []
  loop startIdx nodes.length

/-- CSS 2.1 §9.4.2: Move to previous line box. -/
def findPreviousLine (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  let rec findPrev : Nat → Option Nat
    | 0 => none
    | k + 1 =>
      match nodes[k]? with
      | some n =>
        if n.type == .line ∨ n.name == "#linebox" then some k
        else findPrev k
      | none => none
  findPrev idx

/-- CSS 2.1 §9.4.2: Find next direct sibling in fragment tree (skipping children of current node). -/
def nextSibling (nodes : List CursorNode) (idx : Nat) : Option Nat :=
  match nextSkippingChildren nodes idx with
  | some nextIdx =>
    if findParent nodes nextIdx == findParent nodes idx then some nextIdx
    else none
  | none => none

/-- Collect names of siblings starting from current node. -/
def collectSiblings (nodes : List CursorNode) (startIdx : Nat) : List String :=
  let rec loop (cur : Nat) (fuel : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match nodes[cur]? with
      | some n =>
        let name := n.name
        match nextSibling nodes cur with
        | some nextIdx => name :: loop nextIdx fuel
        | none => [name]
      | none => []
  loop startIdx nodes.length

/-- CSS Inline 3 §2: Items strictly descending from a given container in the fragment tree. -/
def descendantNodes (nodes : List CursorNode) (idx : Nat) : List CursorNode :=
  match nodes[idx]? with
  | some n =>
    if n.descendantsCount > 0 ∧ ¬n.isAtomic then
      nodes.take (idx + 1 + n.descendantsCount) |>.drop (idx + 1)
    else []
  | none => []

def descendantNames (nodes : List CursorNode) (idx : Nat) : List String :=
  (descendantNodes nodes idx).map CursorNode.name

/-- Collect items with matching object identifier (fragments of the same LayoutObject). -/
def itemsForLayoutObject (nodes : List CursorNode) (objId : String) : List String :=
  nodes.filter (fun n => n.id == objId) |>.map CursorNode.name

/-! ## 4. Cursor Tree Navigation Laws -/

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2: The parent of the first child of any node with descendants is the node itself. -/
theorem findParent_of_first_child (nodes : List CursorNode) (i : Nat) (n : CursorNode)
    (hNode : nodes[i]? = some n) (hDesc : n.descendantsCount > 0) :
    findParent nodes (i + 1) = some i := by
  dsimp [findParent]
  cases i with
  | zero =>
    dsimp [findParentAux]
    rw [hNode]
    have : 1 ≤ n.descendantsCount := by omega
    simp [this]
  | succ k =>
    dsimp [findParentAux]
    rw [hNode]
    have : k + 1 + 1 ≤ (k + 1) + n.descendantsCount := by omega
    simp [this]

/-- Blink MoveToNextSkippingChildren strictly advances past current index. -/
theorem nextSkippingChildren_strictly_advances (i : Nat) (descendantsCount : Nat) :
    i < i + 1 + descendantsCount := by
  omega

/-- CSS 2.1 §9.5, §9.3: Culled in-flow item filtering excludes all floats and out-of-flow elements. -/
theorem culledInFlowItems_excludes_floats_and_oof (items : List CursorNode) (n : CursorNode)
    (hMem : n ∈ culledInFlowItems items) :
    n.isFloat = false ∧ n.isOutOfFlow = false := by
  have h := (List.mem_filter.mp hMem).2
  simp only [Bool.not_eq_true] at h
  exact of_decide_eq_true h

/-- CSS 2.1 §9.2.2: Atomic inlines (inline-block, replaced elements) have no in-flow children in the inline formatting context. -/
theorem atomic_inline_has_no_children (nodes : List CursorNode) (idx : Nat) (n : CursorNode)
    (hNode : nodes[idx]? = some n) (hAtomic : n.isAtomic = true) :
    findFirstChild nodes idx = none := by
  dsimp [findFirstChild]
  rw [hNode]
  simp [hAtomic]

/-- CSS Inline 3 §2: A leaf fragment (0 descendants) has no descendant items. -/
theorem descendantNodes_empty_of_leaf (nodes : List CursorNode) (idx : Nat) (n : CursorNode)
    (hNode : nodes[idx]? = some n) (hDesc : n.descendantsCount = 0) :
    descendantNodes nodes idx = [] := by
  dsimp [descendantNodes]
  rw [hNode]
  simp [hDesc]

/-- CSS 2.1 §9.4.2: MoveToPrevious strictly decreases index in pre-order traversal. -/
theorem previousCursor_strictly_decreases (idx : Nat) (hPos : idx > 0) :
    ∃ prev, previousCursor idx = some prev ∧ prev < idx := by
  dsimp [previousCursor]
  simp [hPos]
  omega

/-- CSS 2.1 §9.4.2: Next sibling shares the same parent fragment in the formatting context tree. -/
theorem nextSibling_preserves_parent (nodes : List CursorNode) (idx nextIdx : Nat)
    (hSib : nextSibling nodes idx = some nextIdx) :
    findParent nodes nextIdx = findParent nodes idx := by
  dsimp [nextSibling] at hSib
  split at hSib
  · rename_i hNext
    split at hSib
    · rename_i hEq
      injection hSib with hId
      subst hId
      simp only [beq_iff_eq] at hEq
      exact hEq
    · contradiction
  · contradiction

/-- CSS 2.1 §9.3 & §9.5: When all elements are out-of-flow positioned, the inline flow has no in-flow items. -/
theorem empty_out_of_flow_no_inflow (items : List CursorNode)
    (hOOF : ∀ n ∈ items, n.isOutOfFlow = true) :
    culledInFlowItems items = [] := by
  dsimp [culledInFlowItems]
  rw [List.filter_eq_nil_iff]
  intro n hn
  have := hOOF n hn
  simp [this]

/-- CSS Writing Modes 3 §3.1, CSS 2.1 §9.4.2:
    Visual inline offset to character index with boundary snapping. -/
def visualInlineOffsetToCharIndex (coord : Int) (glyphSize : Int) (charCount : Nat) : Nat :=
  if coord ≤ glyphSize / 2 then 0
  else
    let idx := (coord - glyphSize / 2 + glyphSize - 1) / glyphSize
    min charCount idx.toNat

/-- CSS Writing Modes 3 §3.1, CSS 2.1 §9.4.2:
    Map a physical point within an inline text fragment to a DOM text position and affinity. -/
def positionForPointInChild (isVertical : Bool) (isRtl : Bool) (fragmentOffset point : Int × Int)
    (inlineSize : Int) (charCount : Nat) : Nat × TextAffinity :=
  let coord := if isVertical then point.2 - fragmentOffset.2 else point.1 - fragmentOffset.1
  let glyphSize := if charCount > 0 then inlineSize / (charCount : Int) else inlineSize
  let ltrOffset := visualInlineOffsetToCharIndex coord glyphSize charCount
  let finalOffset := if isRtl then charCount - ltrOffset else ltrOffset
  let affinity : TextAffinity := if finalOffset == charCount then .upstream else .downstream
  (finalOffset, affinity)

/-- CSS Writing Modes 3 §3.1, CSS 2.1 §9.4.2:
    A point at or before the visual start of an LTR fragment always maps to character offset 0. -/
theorem positionForPointInChild_ltr_start (isVertical : Bool) (fragmentOffset point : Int × Int)
    (inlineSize : Int) (charCount : Nat)
    (hCoord : (if isVertical then point.2 - fragmentOffset.2 else point.1 - fragmentOffset.1) ≤
      (if charCount > 0 then inlineSize / (charCount : Int) else inlineSize) / 2) :
    (positionForPointInChild isVertical false fragmentOffset point inlineSize charCount).1 = 0 := by
  dsimp [positionForPointInChild, visualInlineOffsetToCharIndex]
  simp [hCoord]

end ChromiumLayout
