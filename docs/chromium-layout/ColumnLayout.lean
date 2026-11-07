/-
  ColumnLayout.lean: multi-column layout algorithm (CSS Multi-column Layout Level 1),
  written from column_layout_algorithm_test.cc (pin 36c121be). Owned by the block lane (Column*).
-/
import ColumnWidth

namespace ChromiumLayout
namespace ColumnLayout

open ColumnWidth

/-- Child sizing in multicol: a fixed pixel size, a percentage of column width, or auto. -/
inductive Len where
  | px (n : Nat)
  | pct (p : Nat)
  | auto
  deriving Inhabited, DecidableEq, Repr

/-- Resolve a child inline size against the used column inline size. -/
def resolveLen (colW : Nat) : Len → Nat
  | .px n => n
  | .pct p => colW * p / 100
  | .auto => colW

/-- A child block inside a multicol container. -/
structure ColChild where
  id : Nat := 0
  width : Len := .auto
  height : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Multicolumn container specification. -/
structure Multicol where
  cols : Nat
  gap : Nat
  width : Nat
  height : Nat
  children : List ColChild := []
  deriving Inhabited, DecidableEq, Repr

/-- Fragment of a child inside a column fragmentainer. -/
structure ChildSlice where
  id : Nat := 0
  relX : Nat := 0
  relY : Nat := 0
  w : Nat := 0
  h : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- A column fragmentainer. -/
structure ColFrag where
  colIdx : Nat := 0
  relX : Nat := 0
  relY : Nat := 0
  w : Nat := 0
  h : Nat := 0
  slices : List ChildSlice := []
  deriving Inhabited, DecidableEq, Repr

/-- Result of multicolumn layout. -/
structure MulticolResult where
  w : Nat := 0
  h : Nat := 0
  colWidth : Nat := 0
  columns : List ColFrag := []
  deriving Inhabited, DecidableEq, Repr

/-- Column stride: inline distance from start of one column to start of the next. -/
def colStride (colWidth gap : Nat) : Nat :=
  colWidth + gap

/-- Inline offset of the k-th column fragmentainer. -/
def columnInlineOffset (k : Nat) (colWidth gap : Nat) : Nat :=
  k * colStride colWidth gap

/-- Total content block size. -/
def totalContentHeight (children : List ColChild) : Nat :=
  children.foldl (fun acc c => acc + c.height) 0

/-- Number of column fragmentainers created for `column-fill: auto`. -/
def actualColumnCount (fragH : Nat) (contentH : Nat) : Nat :=
  if fragH = 0 then
    if contentH = 0 then 1 else contentH
  else
    Nat.max 1 ((contentH + fragH - 1) / fragH)

/-- Slice a list of sequential in-flow children into column fragmentainer k. -/
def sliceChildren (k : Nat) (fragH : Nat) (colW : Nat) (children : List ColChild) : List ChildSlice :=
  if fragH = 0 then
    let rec findChildAt (chs : List ColChild) (accum : Nat) : List ChildSlice :=
      match chs with
      | [] => []
      | c :: cs =>
          if k >= accum && k < accum + c.height then
            [⟨c.id, 0, 0, resolveLen colW c.width, 1⟩]
          else
            findChildAt cs (accum + c.height)
    findChildAt children 0
  else
    let colStart := k * fragH
    let colEnd := (k + 1) * fragH
    let rec sliceAt (chs : List ColChild) (curY : Nat) : List ChildSlice :=
      match chs with
      | [] => []
      | c :: cs =>
          let nextY := curY + c.height
          let cWidth := resolveLen colW c.width
          if c.height = 0 then
            let inCol := (curY >= colStart && curY < colEnd) ||
                         (curY = colEnd && k + 1 = actualColumnCount fragH curY)
            let rest := sliceAt cs nextY
            if inCol then
              ⟨c.id, 0, curY - colStart, cWidth, 0⟩ :: rest
            else
              rest
          else
            let overlapStart := Nat.max curY colStart
            let overlapEnd := Nat.min nextY colEnd
            let rest := sliceAt cs nextY
            if overlapStart < overlapEnd then
              let sliceH := overlapEnd - overlapStart
              let sliceY := overlapStart - colStart
              ⟨c.id, 0, sliceY, cWidth, sliceH⟩ :: rest
            else
              rest
    sliceAt children 0

/-- Multicolumn layout algorithm for `column-fill: auto`. -/
def layoutMulticol (mc : Multicol) : MulticolResult :=
  let colW := usedWidth mc.cols 0 mc.gap mc.width
  let contentH := totalContentHeight mc.children
  let numCols := actualColumnCount mc.height contentH
  let cols := (List.range numCols).map (fun k =>
    let x := columnInlineOffset k colW mc.gap
    let y := 0
    let slices := sliceChildren k mc.height colW mc.children
    ⟨k, x, y, colW, mc.height, slices⟩)
  ⟨mc.width, mc.height, colW, cols⟩

/-- Column stride is strictly positive when column width is positive. -/
theorem colStride_pos (colWidth gap : Nat) (h : 0 < colWidth) :
    0 < colStride colWidth gap := by
  unfold colStride
  omega

/-- Column offset advances by stride for each subsequent column. -/
theorem columnInlineOffset_step (k colWidth gap : Nat) :
    columnInlineOffset (k + 1) colWidth gap = columnInlineOffset k colWidth gap + colStride colWidth gap := by
  unfold columnInlineOffset
  rw [Nat.add_mul]
  rw [Nat.one_mul]

/-- Columns do not overlap when gap is non-negative and column width is positive. -/
theorem columns_non_overlapping (k colWidth gap : Nat) :
    columnInlineOffset k colWidth gap + colWidth ≤ columnInlineOffset (k + 1) colWidth gap := by
  rw [columnInlineOffset_step]
  unfold colStride
  omega

/-- Multicolumn container always generates at least one column fragmentainer. -/
theorem actualColumnCount_at_least_one (fragH contentH : Nat) :
    1 ≤ actualColumnCount fragH contentH := by
  unfold actualColumnCount
  split
  · split <;> omega
  · apply Nat.le_max_left

end ColumnLayout
end ChromiumLayout
