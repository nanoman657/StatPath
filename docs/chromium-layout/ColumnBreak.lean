/-
  ColumnBreak.lean: nested boxes with `break-inside` inside a multicol container, written from
  CSS Fragmentation Level 3 (§3.2 break-inside, §5.3 splitting boxes) and checked against
  column_layout_algorithm_test.cc. Owned by the block lane (Column*).
-/
import ColumnLayout

namespace ChromiumLayout
namespace ColumnLayout

/-- A margin-free block tree: a leaf of fixed height or a box of stacked children.
    CSS 2.1 §9.4.1 normal flow; CSS Fragmentation Level 3 §3.2 (`break-inside`). -/
inductive BNode where
  | leaf (w : Len) (h : Nat) (bi : BreakInside := .auto)
  | box (w : Len) (bi : BreakInside) (kids : List BNode)
  deriving Inhabited, Repr

/-- A fragment of a node inside column `col`; `y` is the offset from the column top, `kids` are the
    child fragments in the same column. CSS Fragmentation Level 3 §5.3 Splitting Boxes. -/
structure NFrag where
  col : Nat
  y : Nat
  w : Nat
  h : Nat
  kids : List NFrag
  deriving Inhabited, Repr

/-- Whether a block should be pushed to the start of the next column fragmentainer.
    CSS Fragmentation Level 3 §3.2. -/
def shouldPush (y fragH : Nat) (avoids : Bool) (h : Nat) : Bool :=
  y > 0 && (y ≥ fragH || (avoids && y + h > fragH))

/-- Unfragmented block size of a node. CSS 2.1 §10.6.3 auto height. -/
def nodeHeight : Nat → BNode → Nat
  | 0, _ => 0
  | _ + 1, .leaf _ h _ => h
  | f + 1, .box _ _ ks => (ks.map (nodeHeight f)).sum

/-- Lay out a node starting in column `c` at offset `y`. A node that avoids breaks inside and does
    not fit in the rest of the column moves to the top of the next column, even when it is too tall
    for it (CSS Fragmentation Level 3 §3.2); a box that breaks fills the rest of each column it
    leaves (§5.3). Returns the fragments, the end column and the end offset. -/
def layoutNode (fragH colW : Nat) : Nat → BNode → Nat → Nat → List NFrag × Nat × Nat
  | 0, _, c, y => ([], c, y)
  | _ + 1, .leaf w h bi, c, y =>
    let push := shouldPush y fragH bi.avoidsColumn h
    let c0 := if push then c + 1 else c
    let y0 := if push then 0 else y
    let rw := resolveLen colW w
    let r := placeChildSlices fragH rw (h + 1) 0 h c0 y0
    (r.1.map (fun s => ⟨s.colIdx, s.relY, s.w, s.h, []⟩), r.2.1, r.2.2)
  | f + 1, .box w bi ks, c, y =>
    let push := shouldPush y fragH bi.avoidsColumn ((ks.map (nodeHeight f)).sum)
    let c0 := if push then c + 1 else c
    let y0 := if push then 0 else y
    let rw := resolveLen colW w
    let r := ks.foldl (fun (acc : List NFrag × Nat × Nat) k =>
      let q := layoutNode fragH colW f k acc.2.1 acc.2.2
      (acc.1 ++ q.1, q.2.1, q.2.2)) ([], c0, y0)
    let pieces := (List.range (r.2.1 - c0 + 1)).filterMap (fun i =>
      let colIdx := c0 + i
      let colKids := r.1.filter (fun k => k.col = colIdx)
      if colKids.isEmpty then none
      else
        let a := if i = 0 then y0 else 0
        let b := if colIdx = r.2.1 then r.2.2 else fragH
        some ⟨colIdx, a, rw, b - a, colKids⟩)
    (pieces, r.2.1, r.2.2)

/-- Lay out a sequence of block nodes across column fragmentainers.
    CSS Fragmentation Level 3 §5.3. -/
def layoutNodes (fragH colW : Nat) (f : Nat) (nodes : List BNode) : List NFrag :=
  (nodes.foldl (fun (acc : List NFrag × Nat × Nat) n =>
    let r := layoutNode fragH colW f n acc.2.1 acc.2.2
    (acc.1 ++ r.1, r.2.1, r.2.2)) ([], 0, 0)).1

/-- Law: A leaf that avoids column breaks and does not fit in the remaining space
    is pushed to the start of the next column.
    CSS Fragmentation Level 3 §3.2 & §5.3. -/
theorem avoid_leaf_next_col (fragH colW f c y h : Nat) (w : Len) (bi : BreakInside)
    (hy : 0 < y) (_hyf : y < fragH) (ha : bi.avoidsColumn = true) (hf : fragH < y + h) (hh : 0 < h) :
    let (frags, _, _) := layoutNode fragH colW (f + 1) (.leaf w h bi) c y
    ∃ s rest, frags = s :: rest ∧ s.col = c + 1 ∧ s.y = 0 := by
  dsimp [layoutNode]
  have hp : shouldPush y fragH bi.avoidsColumn h = true := by
    dsimp [shouldPush]; simp [ha]; omega
  rw [hp]
  dsimp [placeChildSlices]
  split
  · omega
  · split
    · refine ⟨_, _, rfl, rfl, rfl⟩
    · refine ⟨_, _, rfl, rfl, rfl⟩

end ColumnLayout
end ChromiumLayout
