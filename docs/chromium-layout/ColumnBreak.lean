/-
  ColumnBreak.lean: nested boxes with `break-inside`, explicit block size, and floats inside
  a multicol container, written from CSS 2.1 §9.5 (floats), §9.5.1 (Rule 6 float ordering),
  §10.6.2 (fixed height), §11.1 (overflow), CSS Multicol 1 §4, and CSS Fragmentation Level 3
  (§3.2 break-inside, §5.2 margins at breaks, §5.3 splitting boxes) and checked against
  column_layout_algorithm_test.cc. Owned by the block lane (Column*).
-/
import ColumnLayout

namespace ChromiumLayout
namespace ColumnLayout

/-- Float type for boxes in multicol: none, left, or right. CSS 2.1 §9.5.1. -/
inductive FloatType where
  | none
  | left
  | right
  deriving Inhabited, DecidableEq, Repr

/-- A block tree: a leaf of fixed height or a box of stacked children with optional
    specified height and float type.
    CSS 2.1 §9.4.1 normal flow, §9.5 floats, §10.6.2 fixed height;
    CSS Fragmentation Level 3 §3.2 (`break-inside`), §5.3. -/
inductive BNode where
  | leaf (w : Len) (h : Nat) (bi : BreakInside := .auto) (fl : FloatType := .none) (marginTop : Nat := 0)
  | box (w : Len) (bi : BreakInside) (kids : List BNode) (optH : Option Nat := none) (fl : FloatType := .none) (marginTop : Nat := 0)
  deriving Inhabited, Repr

/-- A fragment of a node inside column `col`; `x` and `y` are the offset from the column top-left,
    `kids` are the child fragments in the same column.
    CSS 2.1 §9.5, CSS Fragmentation Level 3 §5.3 Splitting Boxes. -/
structure NFrag where
  col : Nat
  x : Nat := 0
  y : Nat
  w : Nat
  h : Nat
  kids : List NFrag
  deriving Inhabited, Repr

/-- Whether a block should be pushed to the start of the next column fragmentainer.
    CSS Fragmentation Level 3 §3.2. -/
def shouldPush (y fragH : Nat) (avoids : Bool) (h : Nat) : Bool :=
  y > 0 && (y ≥ fragH || (avoids && y + h > fragH))

/-- Unfragmented block size of a node. CSS 2.1 §10.6.2 fixed height, §10.6.3 auto height. -/
def nodeHeight : Nat → BNode → Nat
  | 0, _ => 0
  | _ + 1, .leaf _ h _ _ _ => h
  | f + 1, .box _ _ ks optH _ _ =>
    match optH with
    | some h => h
    | none => (ks.map (nodeHeight f)).sum

/-- Whether any part of a node avoids breaking inside. CSS Fragmentation Level 3 §3.2. -/
def nodeAvoids : Nat → BNode → Bool
  | 0, _ => false
  | _ + 1, .leaf _ _ bi _ _ => bi.avoidsColumn
  | f + 1, .box _ bi ks _ _ _ => bi.avoidsColumn || ks.any (nodeAvoids f)

/-- Float direction and top margin of a node. CSS 2.1 §8.3, §9.5.1. -/
def nodeProps : BNode → FloatType × Nat
  | .leaf _ _ _ fl m => (fl, m)
  | .box _ _ _ _ fl m => (fl, m)

/-- Lay out an in-flow node starting in column `c` at offset `y`.
    CSS 2.1 §10.6.2 (fixed height), §11.1 (overflow), CSS Fragmentation Level 3 §3.2 & §5.3. -/
def layoutNode (fragH colW : Nat) : Nat → BNode → Nat → Nat → List NFrag × Nat × Nat
  | 0, _, c, y => ([], c, y)
  | _ + 1, .leaf w h bi _ _, c, y =>
    let push := shouldPush y fragH bi.avoidsColumn h
    let c0 := if push then c + 1 else c
    let y0 := if push then 0 else y
    let rw := resolveLen colW w
    let r := placeChildSlices fragH rw (h + 1) 0 h c0 y0
    (r.1.map (fun s => ⟨s.colIdx, 0, s.relY, s.w, s.h, []⟩), r.2.1, r.2.2)
  | f + 1, .box w bi ks optH _ _, c, y =>
    let hBox := match optH with | some h => h | none => (ks.map (nodeHeight f)).sum
    let push := shouldPush y fragH bi.avoidsColumn hBox
    let c0 := if push then c + 1 else c
    let y0 := if push then 0 else y
    let rw := resolveLen colW w
    let r := ks.foldl (fun (acc : List NFrag × Nat × Nat) k =>
      let q := layoutNode fragH colW f k acc.2.1 acc.2.2
      (acc.1 ++ q.1, q.2.1, q.2.2)) ([], c0, y0)
    let (endC, endY) := match optH with
      | none => (r.2.1, r.2.2)
      | some h =>
        if y0 + h ≤ fragH then (c0, y0 + h)
        else
          let rem := h - (fragH - y0)
          (c0 + 1 + rem / fragH, rem % fragH)
    let maxCol := match optH with
      | none => r.2.1
      | some _ => max (if endY > 0 then endC else endC - 1) r.2.1
    let numCols := if maxCol ≥ c0 then maxCol - c0 + 1 else 0
    let pieces := (List.range numCols).filterMap (fun i =>
      let colIdx := c0 + i
      let colKids := r.1.filter (fun k => k.col = colIdx)
      let boxFragY := if colIdx = c0 then y0 else 0
      match optH with
      | none =>
        if colKids.isEmpty then none
        else
          let b := if colIdx = r.2.1 then r.2.2 else fragH
          let colKidsRel := colKids.map (fun k => { k with y := k.y - boxFragY })
          some ⟨colIdx, 0, boxFragY, rw, b - boxFragY, colKidsRel⟩
      | some h =>
        let consumedBefore := if colIdx = c0 then 0 else (fragH - y0) + (colIdx - c0 - 1) * fragH
        let availInCol := if colIdx = c0 then fragH - y0 else fragH
        let remH := if h > consumedBefore then h - consumedBefore else 0
        let boxFragH := min availInCol remH
        if boxFragH = 0 && colKids.isEmpty then none
        else
          let colKidsRel := colKids.map (fun k => { k with y := k.y - boxFragY })
          some ⟨colIdx, 0, boxFragY, rw, boxFragH, colKidsRel⟩)
    (pieces, endC, endY)

/-- Float state in a column: placed left and right floats (x, y, w, h). CSS 2.1 §9.5. -/
structure ColFloats where
  lefts : List (Nat × Nat × Nat × Nat) := []
  rights : List (Nat × Nat × Nat × Nat) := []
  deriving Inhabited, Repr

/-- Active left float width at vertical position y. CSS 2.1 §9.5.1. -/
def leftWidthAt (cf : ColFloats) (y : Nat) : Nat :=
  cf.lefts.foldl (fun mw (fx, fy, fw, fh) => if fy ≤ y && y < fy + fh then max mw (fx + fw) else mw) 0

/-- Active right float width at vertical position y. CSS 2.1 §9.5.1. -/
def rightWidthAt (colW : Nat) (cf : ColFloats) (y : Nat) : Nat :=
  cf.rights.foldl (fun mw (fx, fy, _, fh) => if fy ≤ y && y < fy + fh then max mw (colW - fx) else mw) 0

/-- Horizontal position of a float in a column. CSS 2.1 §9.5.1. -/
def floatX (colW : Nat) (cf : ColFloats) (fl : FloatType) (w y : Nat) : Nat :=
  match fl with
  | .left => leftWidthAt cf y
  | .right => colW - rightWidthAt colW cf y - w
  | .none => 0

/-- Record a placed float slice in column float state. CSS 2.1 §9.5.1. -/
def addFloat (cf : ColFloats) (fl : FloatType) (x y w h : Nat) : ColFloats :=
  match fl with
  | .left => { cf with lefts := (x, y, w, h) :: cf.lefts }
  | .right => { cf with rights := (x, y, w, h) :: cf.rights }
  | .none => cf

/-- Set the column float state at a specific column index. -/
def padSet (l : List ColFloats) (idx : Nat) (val : ColFloats) : List ColFloats :=
  match idx, l with
  | 0, _ :: rest => val :: rest
  | 0, [] => [val]
  | n + 1, x :: rest => x :: padSet rest n val
  | n + 1, [] => {} :: padSet [] n val

/-- Place slices of a fragmented float across columns.
    CSS 2.1 §9.5.1, CSS Fragmentation Level 3 §5.2, §5.3. -/
def placeFloatSlices (fragH colW : Nat) (fl : FloatType) (w mTop : Nat) :
    Nat → Nat → Nat → Nat → Bool → List NFrag → List ColFloats → List NFrag × List ColFloats
  | 0, _, _, _, _, acc, cfl => (acc.reverse, cfl)
  | fuel + 1, remH, curCol, curY, isFirst, acc, cfl =>
    if remH = 0 then (acc.reverse, cfl)
    else
      let cf := cfl.getD curCol {}
      let y0 := if isFirst then curY + mTop else 0
      let avail := if y0 < fragH then fragH - y0 else 0
      let sliceH := min avail remH
      let placeX := floatX colW cf fl w y0
      let frag : NFrag := ⟨curCol, placeX, y0, w, sliceH, []⟩
      let nextCfl := padSet cfl curCol (addFloat cf fl placeX y0 w sliceH)
      placeFloatSlices fragH colW fl w mTop fuel (remH - sliceH) (curCol + 1) 0 false (frag :: acc) nextCfl

/-- Lay out a sequence of block nodes and floats across column fragmentainers.
    CSS 2.1 §9.5, §9.5.1 Rule 6; CSS Multicol 1 §4; CSS Fragmentation Level 3 §3.2, §5.2, §5.3. -/
def layoutNodes (fragH colW : Nat) (f : Nat) (nodes : List BNode) : List NFrag :=
  let rec loop (nodes : List BNode) (c y floatCol : Nat) (cfloats : List ColFloats)
               (acc : List NFrag) : List NFrag :=
    match nodes with
    | [] => acc
    | n :: rest =>
      let (fl, mTop) := nodeProps n
      match fl with
      | .none =>
        let (nFrags, endC, endY) := layoutNode fragH colW f n c y
        loop rest endC endY (max floatCol endC) cfloats (acc ++ nFrags)
      | _ =>
        let h := nodeHeight f n
        let avoids := nodeAvoids f n
        let rw := resolveLen colW (match n with | .leaf w _ _ _ _ => w | .box w _ _ _ _ _ => w)
        let fc0 := max c floatCol
        let fy0 := if fc0 = c then y else 0
        let avail0 := if fy0 + mTop < fragH then fragH - (fy0 + mTop) else 0
        let mustPush := avoids && (avail0 < h)
        let (fc, fy) := if mustPush then (fc0 + 1, 0) else (fc0, fy0)
        match n with
        | .leaf _ _ _ _ _ =>
          let (frags, nextCfl) := placeFloatSlices fragH colW fl rw mTop (h + 1) h fc fy true [] cfloats
          loop rest c y fc nextCfl (acc ++ frags)
        | .box _ _ ks optH _ _ =>
          let (nFrags, endC, _) := layoutNode fragH colW f (.box (.px rw) .auto ks optH) fc (fy + mTop)
          let cf := cfloats.getD fc {}
          let placeX := floatX colW cf fl rw (fy + mTop)
          let fragsWithX := nFrags.map (fun fr => if fr.col = fc then { fr with x := placeX } else fr)
          let nextCfl := padSet cfloats fc (addFloat cf fl placeX (fy + mTop) rw h)
          loop rest c y (max fc endC) nextCfl (acc ++ fragsWithX)
  let allFrags := loop nodes 0 0 0 [] []
  let maxCol := (allFrags.map (·.col)).foldl max 0
  (List.range (maxCol + 1)).flatMap (fun colIdx => allFrags.filter (·.col = colIdx))

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

/-- Law: A box with specified height `h` fitting within the column fragmentainer (`y + h ≤ fragH`)
    always advances the parent layout cursor to `(c, y + h)`, regardless of its children.
    CSS 2.1 §10.6.2 & §11.1 (overflow does not affect in-flow progression). -/
theorem box_fit_end_pos (fragH colW f c y h : Nat) (w : Len) (bi : BreakInside) (ks : List BNode)
    (h_fit : y + h ≤ fragH) (h_pos : 0 < h) :
    let (_, endC, endY) := layoutNode fragH colW (f + 1) (.box w bi ks (some h)) c y
    endC = c ∧ endY = y + h := by
  dsimp [layoutNode]
  have hp : shouldPush y fragH bi.avoidsColumn h = false := by
    dsimp [shouldPush]
    have : ¬(y ≥ fragH) := by omega
    have : ¬(bi.avoidsColumn && y + h > fragH) := by
      intro hc; cases bi.avoidsColumn <;> simp at hc <;> omega
    simp [*]
  rw [hp]
  dsimp
  have : y + h ≤ fragH := h_fit
  simp [this]

/-- Law: A right float placed in an empty column aligns with the column's right edge.
    CSS 2.1 §9.5.1. -/
theorem right_float_aligns_right (colW w y : Nat) (hw : w ≤ colW) :
    floatX colW {} .right w y + w = colW := by
  dsimp [floatX, rightWidthAt]
  omega

end ColumnLayout
end ChromiumLayout
