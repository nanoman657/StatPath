/-
  docs/chromium-layout/InlineFragmentItem.lean

  Formal model for Blink FragmentItem and FragmentItems
  (`third_party/blink/renderer/core/layout/inline/fragment_item.h`,
   `fragment_items.h`, `fragment_items_builder.h`).

  Owns: FragmentItem, FragmentItems representation, culled inline box bounds,
  ink overflow union laws, and fragmentainer distribution.
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout

/-! ## 1. Fragment Item Model -/

inductive FragmentItemType where
  | line
  | text
  | generatedText
  | box
  deriving DecidableEq, Repr

/-- Physical rectangle (`platform/geometry/physical_rect.h`). -/
structure PhysicalRect where
  x : Nat := 0
  y : Nat := 0
  width : Nat := 0
  height : Nat := 0
  deriving DecidableEq, Repr

/-- Rectangle union (`PhysicalRect::Unite`). -/
def PhysicalRect.union (r1 r2 : PhysicalRect) : PhysicalRect :=
  if r1.width == 0 && r1.height == 0 then r2
  else if r2.width == 0 && r2.height == 0 then r1
  else
    let minX := Nat.min r1.x r2.x
    let minY := Nat.min r1.y r2.y
    let maxX := Nat.max (r1.x + r1.width) (r2.x + r2.width)
    let maxY := Nat.max (r1.y + r1.height) (r2.y + r2.height)
    { x := minX, y := minY, width := maxX - minX, height := maxY - minY }

/-- Rectangle enclosure: `r2` is contained in `r1` (`r1.encloses r2`). -/
def PhysicalRect.encloses (r1 r2 : PhysicalRect) : Prop :=
  r1.x ≤ r2.x ∧
  r1.y ≤ r2.y ∧
  r2.x + r2.width ≤ r1.x + r1.width ∧
  r2.y + r2.height ≤ r1.y + r1.height

/-- A fragment item in the inline formatting context
    (`inline/fragment_item.h:74-320`). -/
structure FragmentItem where
  type : FragmentItemType := .text
  nodeId : Nat := 0
  offset : LogicalOffset := {}
  size : LogicalSize := {}
  inkOverflow : PhysicalRect := {}
  isFirstForNode : Bool := false
  isLastForNode : Bool := false
  isRubyAnnotationLine : Bool := false
  startOffsetInContainer : Option Nat := none
  deriving DecidableEq, Repr

/-- Compute bounding box for a culled inline from its descendant items
    (`inline/fragment_item.cc:754-780`, `CulledInlineBox`). -/
def culledInlineBoundingBox (items : List FragmentItem) (targetNodeId : Nat) : PhysicalRect :=
  let matching := items.filter (fun it => it.nodeId == targetNodeId)
  matching.foldl
    (fun acc it => acc.union { x := it.offset.inlineOffset
                             , y := it.offset.blockOffset
                             , width := it.size.inlineSize
                             , height := it.size.blockSize })
    {}

/-- Caret inline position with `text-fit: grow`
    (`inline/fragment_item_test.cc:931`, `CaretInlinePositionForOffset_TextFit`). -/
def caretInlinePositionForOffset (textLen : Nat) (availWidth : Nat) (offset : Nat) : Nat :=
  if textLen == 0 then 0
  else (availWidth / textLen) * offset

/-! ## 2. General Laws for Fragment Items -/

/-- Union of non-empty rectangles encloses the left rectangle. -/
theorem physicalRect_union_encloses_left (r1 r2 : PhysicalRect)
    (h1 : r1.width ≠ 0 ∨ r1.height ≠ 0) :
    (r1.union r2).encloses r1 := by
  dsimp [PhysicalRect.union]
  have hZero : ¬ (r1.width == 0 && r1.height == 0) := by
    intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h1 with hw | hh
    · exact hw h.1
    · exact hh h.2
  simp [hZero]
  split
  · -- r2 is empty
    dsimp [PhysicalRect.encloses]
    omega
  · -- both non-empty
    dsimp [PhysicalRect.encloses]
    let minX := Nat.min r1.x r2.x
    let minY := Nat.min r1.y r2.y
    let maxX := Nat.max (r1.x + r1.width) (r2.x + r2.width)
    let maxY := Nat.max (r1.y + r1.height) (r2.y + r2.height)
    have hMinXLe : minX ≤ r1.x := Nat.min_le_left _ _
    have hXLe : r1.x ≤ r1.x + r1.width := Nat.le_add_right _ _
    have hMaxXGe : r1.x + r1.width ≤ maxX := Nat.le_max_left _ _
    have hMinXLeMax : minX ≤ maxX := by omega
    have hMinYLe : minY ≤ r1.y := Nat.min_le_left _ _
    have hYLe : r1.y ≤ r1.y + r1.height := Nat.le_add_right _ _
    have hMaxYGe : r1.y + r1.height ≤ maxY := Nat.le_max_left _ _
    have hMinYLeMax : minY ≤ maxY := by omega
    refine ⟨hMinXLe, hMinYLe, ?_, ?_⟩
    · rw [Nat.add_sub_of_le hMinXLeMax]
      exact hMaxXGe
    · rw [Nat.add_sub_of_le hMinYLeMax]
      exact hMaxYGe

/-- Union of non-empty rectangles encloses the right rectangle. -/
theorem physicalRect_union_encloses_right (r1 r2 : PhysicalRect)
    (h2 : r2.width ≠ 0 ∨ r2.height ≠ 0) :
    (r1.union r2).encloses r2 := by
  dsimp [PhysicalRect.union]
  split
  · -- r1 is empty
    dsimp [PhysicalRect.encloses]
    omega
  · split
    · -- r2 is empty, contradiction
      rename_i _ h2Empty
      simp only [Bool.and_eq_true, beq_iff_eq] at h2Empty
      rcases h2 with hw | hh
      · exact False.elim (hw h2Empty.1)
      · exact False.elim (hh h2Empty.2)
    · -- both non-empty
      dsimp [PhysicalRect.encloses]
      let minX := Nat.min r1.x r2.x
      let minY := Nat.min r1.y r2.y
      let maxX := Nat.max (r1.x + r1.width) (r2.x + r2.width)
      let maxY := Nat.max (r1.y + r1.height) (r2.y + r2.height)
      have hMinXLe : minX ≤ r2.x := Nat.min_le_right _ _
      have hXLe : r2.x ≤ r2.x + r2.width := Nat.le_add_right _ _
      have hMaxXGe : r2.x + r2.width ≤ maxX := Nat.le_max_right _ _
      have hMinXLeMax : minX ≤ maxX := by omega
      have hMinYLe : minY ≤ r2.y := Nat.min_le_right _ _
      have hYLe : r2.y ≤ r2.y + r2.height := Nat.le_add_right _ _
      have hMaxYGe : r2.y + r2.height ≤ maxY := Nat.le_max_right _ _
      have hMinYLeMax : minY ≤ maxY := by omega
      refine ⟨hMinXLe, hMinYLe, ?_, ?_⟩
      · rw [Nat.add_sub_of_le hMinXLeMax]
        exact hMaxXGe
      · rw [Nat.add_sub_of_le hMinYLeMax]
        exact hMaxYGe

end ChromiumLayout
