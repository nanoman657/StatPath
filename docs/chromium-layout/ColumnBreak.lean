/-
  ColumnBreak.lean: nested boxes with `break-inside`, explicit block size, forced breaks,
  and floats inside a multicol container, written from CSS 2.1 §9.5 (floats),
  §9.5.1 (Rule 6 float ordering), §10.6.2 (fixed height), §11.1 (overflow), CSS Multicol 1 §4,
  and CSS Fragmentation Level 3 (§3.1 forced breaks, §3.2 break-inside, §3.3 suppression at start
  of fragmentainer, §5.2 margins at breaks, §5.3 splitting boxes) and checked against
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
    specified height, float type, top margin, and forced breaks.
    CSS 2.1 §9.4.1 normal flow, §9.5 floats, §10.6.2 fixed height;
    CSS Fragmentation Level 3 §3.1 forced breaks, §3.2 (`break-inside`),
    §5.2 margin truncation/preservation at breaks, §5.3 splitting boxes. -/
inductive BNode where
  | leaf (w : Len) (h : Nat) (bi : BreakInside := .auto) (fl : FloatType := .none)
         (marginTop : Nat := 0) (breakBefore : Bool := false) (breakAfter : Bool := false)
         (isNewFc : Bool := false)
  | box (w : Len) (bi : BreakInside) (kids : List BNode) (optH : Option Nat := none)
        (fl : FloatType := .none) (marginTop : Nat := 0) (breakBefore : Bool := false) (breakAfter : Bool := false)
        (border : Nat := 0) (padding : Nat := 0) (isNewFc : Bool := false)
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

/-- Unfragmented block size of a node. CSS 2.1 §8.1 (border/padding), §10.6.2 (fixed height), §10.6.3 (auto height). -/
def nodeHeight : Nat → BNode → Nat
  | 0, _ => 0
  | _ + 1, .leaf _ h .. => h
  | f + 1, .box _ _ ks optH _ _ _ _ border padding .. =>
    let bp := border + padding
    match optH with
    | some h => h + 2 * bp
    | none => (ks.map (nodeHeight f)).sum + 2 * bp

/-- Whether any part of a node avoids breaking inside. CSS Fragmentation Level 3 §3.2. -/
def nodeAvoids : Nat → BNode → Bool
  | 0, _ => false
  | _ + 1, .leaf _ _ bi .. => bi.avoidsColumn
  | f + 1, .box _ bi ks .. => bi.avoidsColumn || ks.any (nodeAvoids f)

/-- Margin top of a node. CSS 2.1 §8.3. -/
def nodeMarginTop : BNode → Nat
  | .leaf _ _ _ _ m .. => m
  | .box _ _ _ _ _ m .. => m

/-- Float direction of a node. CSS 2.1 §9.5.1. -/
def nodeFloat : BNode → FloatType
  | .leaf _ _ _ fl .. => fl
  | .box _ _ _ _ fl .. => fl

/-- Whether a node has forced break-before. CSS Fragmentation Level 3 §3.1. -/
def nodeBreakBefore : BNode → Bool
  | .leaf _ _ _ _ _ bB .. => bB
  | .box _ _ _ _ _ _ bB .. => bB

/-- Whether a node has forced break-after. CSS Fragmentation Level 3 §3.1. -/
def nodeBreakAfter : BNode → Bool
  | .leaf _ _ _ _ _ _ bA .. => bA
  | .box _ _ _ _ _ _ _ bA .. => bA

/-- Whether a node establishes a new formatting context root. CSS 2.1 §9.5. -/
def nodeIsNewFc : BNode → Bool
  | .leaf _ _ _ _ _ _ _ isNewFc => isNewFc
  | .box _ _ _ _ _ _ _ _ _ _ isNewFc => isNewFc

/-- Float direction and top margin of a node. CSS 2.1 §8.3, §9.5.1. -/
def nodeProps (n : BNode) : FloatType × Nat :=
  (nodeFloat n, nodeMarginTop n)

/-- Calculate starting column and y offset for a node in fragmentainer.
    CSS Fragmentation Level 3 §3.1, §3.3, §5.2. -/
def nodeStart (fragH : Nat) (c y : Nat) (bB : Bool) (avoids : Bool) (mTop h : Nat) : Nat × Nat :=
  if bB && y > 0 then
    -- CSS Fragmentation Level 3 §3.1 forced break, §5.2 margin preserved
    (c + 1, mTop)
  else
    let yEff := y + mTop
    if y > 0 && (yEff ≥ fragH || (avoids && yEff + h > fragH)) then
      -- CSS Fragmentation Level 3 §3.2 unforced break, §5.2 margin truncated to zero
      (c + 1, 0)
    else
      (c, yEff)

/-- Apply break-after if requested. CSS Fragmentation Level 3 §3.1. -/
def applyBreakAfter (bA : Bool) (c y : Nat) : Nat × Nat :=
  if bA && y > 0 then (c + 1, 0) else (c, y)

/-- Lay out an in-flow node starting in column `c` at offset `y`.
    CSS 2.1 §8.1 (box dimensions), §8.5 (borders), §10.6.2 (fixed height), §11.1 (overflow);
    CSS Fragmentation Level 3 §3.1 (forced breaks), §3.2 & §5.3 (splitting boxes),
    §5.2 (margins at breaks), §5.4 (box-decoration-break: slice). -/
def layoutNode (fragH colW : Nat) : Nat → BNode → Nat → Nat → List NFrag × Nat × Nat
  | 0, _, c, y => ([], c, y)
  | _ + 1, .leaf w h bi _ mTop bB bA .., c, y =>
    let (c0, y0) := nodeStart fragH c y bB bi.avoidsColumn mTop h
    let rw := resolveLen colW w
    let r := placeChildSlices fragH rw (h + 1) 0 h c0 y0
    let (finalC, finalY) := applyBreakAfter bA r.2.1 r.2.2
    (r.1.map (fun s => ⟨s.colIdx, 0, s.relY, s.w, s.h, []⟩), finalC, finalY)
  | f + 1, .box w bi ks optH _ mTop bB bA border padding .., c, y =>
    let bp := border + padding
    let hBox := match optH with | some h => h + 2 * bp | none => (ks.map (nodeHeight f)).sum + 2 * bp
    let avoids := bi.avoidsColumn || ks.any (nodeAvoids f)
    let (c0, y0) := nodeStart fragH c y bB avoids mTop hBox
    let rw := resolveLen colW w
    let innerW := if rw ≥ 2 * bp then rw - 2 * bp else 0
    let r := ks.foldl (fun (acc : List NFrag × Nat × Nat) k =>
      let q := layoutNode fragH innerW f k acc.2.1 acc.2.2
      (acc.1 ++ q.1, q.2.1, q.2.2)) ([], c0, y0 + bp)
    let (endC, endY) := match optH with
      | none =>
        if ks.isEmpty then (c0, y0 + 2 * bp)
        else if r.2.2 + bp ≤ fragH then (r.2.1, r.2.2 + bp)
        else (r.2.1 + 1, bp)
      | some h =>
        let totalH := h + 2 * bp
        if y0 + totalH ≤ fragH then (c0, y0 + totalH)
        else
          let rem := totalH - (fragH - y0)
          (c0 + 1 + rem / fragH, rem % fragH)
    let maxCol := match optH with
      | none => max (if endY > 0 then endC else if endC > 0 then endC - 1 else 0) (max c0 r.2.1)
      | some _ => max (if endY > 0 then endC else if endC > 0 then endC - 1 else 0) (max c0 r.2.1)
    let numCols := if maxCol ≥ c0 then maxCol - c0 + 1 else 0
    let pieces := (List.range numCols).filterMap (fun i =>
      let colIdx := c0 + i
      let colKids := r.1.filter (fun k => k.col = colIdx)
      let boxFragY := if colIdx = c0 then y0 else 0
      let colKidsRel := colKids.map (fun k => { k with x := k.x + bp, y := k.y - boxFragY })
      match optH with
      | none =>
        let boxFragH := if colIdx = endC then endY - boxFragY else if colIdx < endC then fragH - boxFragY else 0
        if boxFragH = 0 && colKids.isEmpty then none
        else some ⟨colIdx, 0, boxFragY, rw, boxFragH, colKidsRel⟩
      | some h =>
        let totalH := h + 2 * bp
        let consumedBefore := if colIdx = c0 then 0 else (fragH - y0) + (colIdx - c0 - 1) * fragH
        let availInCol := if colIdx = c0 then fragH - y0 else fragH
        let remH := if totalH > consumedBefore then totalH - consumedBefore else 0
        let boxFragH := min availInCol remH
        if boxFragH = 0 && colKids.isEmpty then none
        else some ⟨colIdx, 0, boxFragY, rw, boxFragH, colKidsRel⟩)
    let (finalC, finalY) := applyBreakAfter bA endC endY
    (pieces, finalC, finalY)

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

/-- Place slices of a fragmented box float across columns and update float state.
    CSS 2.1 §9.5, §9.5.1; CSS Fragmentation Level 3 §5.3. -/
def placeBoxFloatFrags (colW : Nat) (fl : FloatType) (frags : List NFrag) (cfloats : List ColFloats) :
    List NFrag × List ColFloats :=
  frags.foldl (fun (acc : List NFrag × List ColFloats) fr =>
    let cf := acc.2.getD fr.col {}
    let px := floatX colW cf fl fr.w fr.y
    let frWithX := { fr with x := px }
    let nextCf := addFloat cf fl px fr.y fr.w fr.h
    (acc.1 ++ [frWithX], padSet acc.2 fr.col nextCf)) ([], cfloats)

/-- Clear an element establishing a new formatting context below floats if it does not fit beside them.
    CSS 2.1 §9.5. -/
def clearFloats (colW : Nat) (cf : ColFloats) (isNewFc : Bool) (w y mTop : Nat) : Nat × Nat :=
  if isNewFc then
    let y0 := y + mTop
    let lw := leftWidthAt cf y0
    let rw := rightWidthAt colW cf y0
    let availW := if colW ≥ lw + rw then colW - lw - rw else 0
    if w > availW then
      let fb := (cf.lefts ++ cf.rights).foldl (fun mb (_, fy, _, fh) => max mb (fy + fh)) 0
      (max y0 fb, 0)
    else
      (y, mTop)
  else
    (y, mTop)

/-- Lay out a sequence of block nodes and floats across column fragmentainers.
    CSS 2.1 §9.5 (floats and clearance), §9.5.1 Rule 6; CSS Multicol 1 §4; CSS Fragmentation Level 3
    §3.1 (forced breaks), §3.2 (avoidance), §5.2 (margin preservation/truncation), §5.3. -/
def layoutNodes (fragH colW : Nat) (f : Nat) (nodes : List BNode) : List NFrag :=
  let rec loop (nodes : List BNode) (c y floatCol : Nat) (cfloats : List ColFloats)
               (acc : List NFrag) : List NFrag :=
    match nodes with
    | [] => acc
    | n :: rest =>
      let fl := nodeFloat n
      let mTop := nodeMarginTop n
      let bB := nodeBreakBefore n
      let bA := nodeBreakAfter n
      match fl with
      | .none =>
        let isNewFc := nodeIsNewFc n
        let rw := resolveLen colW (match n with | .leaf w .. => w | .box w .. => w)
        let cf := cfloats.getD c {}
        let (adjY, adjMTop) := clearFloats colW cf isNewFc rw y mTop
        let nWithAdjMargin := match n with
          | .leaf w h bi fl _ bB bA isNewFc => .leaf w h bi fl adjMTop bB bA isNewFc
          | .box w bi ks optH fl _ bB bA b p isNewFc => .box w bi ks optH fl adjMTop bB bA b p isNewFc
        let (nFrags, endC, endY) := layoutNode fragH colW f nWithAdjMargin c adjY
        loop rest endC endY (max floatCol endC) cfloats (acc ++ nFrags)
      | _ =>
        let h := nodeHeight f n
        let avoids := nodeAvoids f n
        let rw := resolveLen colW (match n with | .leaf w .. => w | .box w .. => w)
        let fc0 := max c floatCol
        let fy0 := if fc0 = c then y else 0
        let avail0 := if fy0 + mTop < fragH then fragH - (fy0 + mTop) else 0
        let mustPush := (bB && fy0 > 0) || (avoids && avail0 < h)
        let (fc, fy) := if mustPush then (fc0 + 1, 0) else (fc0, fy0)
        match n with
        | .leaf .. =>
          let (frags, nextCfl) := placeFloatSlices fragH colW fl rw mTop (h + 1) h fc fy true [] cfloats
          let (finalC, _) := applyBreakAfter bA fc fy
          loop rest c y finalC nextCfl (acc ++ frags)
        | .box _ _ ks optH _ _ _ _ border padding .. =>
          let (nFrags, _, _) := layoutNode fragH colW f (.box (.px rw) .auto ks optH .none 0 false false border padding) fc (fy + mTop)
          let (fragsWithX, nextCfl) := placeBoxFloatFrags colW fl nFrags cfloats
          let (finalC, _) := applyBreakAfter bA fc 0
          loop rest c y finalC nextCfl (acc ++ fragsWithX)
  let allFrags := loop nodes 0 0 0 [] []
  let maxCol := (allFrags.map (·.col)).foldl max 0
  (List.range (maxCol + 1)).flatMap (fun colIdx => allFrags.filter (·.col = colIdx))

/-- Law: An in-flow leaf with `break-before: column` not at the start of a column
    (`y > 0`) is pushed to the start of the next column (`c + 1`).
    CSS Fragmentation Level 3 §3.1 & §3.3. -/
theorem forced_break_col (fragH colW f c y h : Nat) (w : Len) (bi : BreakInside)
    (hy : 0 < y) (hh : 0 < h) :
    let (frags, _, _) := layoutNode fragH colW (f + 1) (.leaf w h bi .none 0 true false) c y
    ∃ s rest, frags = s :: rest ∧ s.col = c + 1 ∧ s.y = 0 := by
  dsimp [layoutNode]
  have hp : nodeStart fragH c y true bi.avoidsColumn 0 h = (c + 1, 0) := by
    dsimp [nodeStart]; simp [hy]
  rw [hp]
  dsimp [placeChildSlices]
  split
  · omega
  · split
    · refine ⟨_, _, rfl, rfl, rfl⟩
    · refine ⟨_, _, rfl, rfl, rfl⟩

/-- Law: A leaf that avoids column breaks and does not fit in the remaining space
    is pushed to the start of the next column.
    CSS Fragmentation Level 3 §3.2 & §5.3. -/
theorem avoid_leaf_next_col (fragH colW f c y h : Nat) (w : Len) (bi : BreakInside)
    (hy : 0 < y) (_hyf : y < fragH) (ha : bi.avoidsColumn = true) (hf : fragH < y + h) (hh : 0 < h) :
    let (frags, _, _) := layoutNode fragH colW (f + 1) (.leaf w h bi) c y
    ∃ s rest, frags = s :: rest ∧ s.col = c + 1 ∧ s.y = 0 := by
  dsimp [layoutNode]
  have hp : nodeStart fragH c y false bi.avoidsColumn 0 h = (c + 1, 0) := by
    dsimp [nodeStart]; simp [hy, ha, hf]
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
  have hp : nodeStart fragH c y false (bi.avoidsColumn || ks.any (nodeAvoids f)) 0 h = (c, y) := by
    dsimp [nodeStart]
    have h1 : decide (y ≥ fragH) = false := by simp; omega
    have h2 : decide (y + h > fragH) = false := by simp; omega
    simp [h1, h2]
  have hpc : (nodeStart fragH c y false (bi.avoidsColumn || ks.any (nodeAvoids f)) 0 h).fst = c := by rw [hp]
  have hpy : (nodeStart fragH c y false (bi.avoidsColumn || ks.any (nodeAvoids f)) 0 h).snd = y := by rw [hp]
  have hle : y + h ≤ fragH := h_fit
  simp [hpc, hpy, hle, applyBreakAfter]

/-- Law: Under default `box-decoration-break: slice`, a box with border `b`
    that fits within the fragmentainer has total block size `h + 2 * b`.
    CSS 2.1 §8.1 & CSS Fragmentation Level 3 §5.4. -/
theorem box_border_size (fragH colW f c y h b : Nat) (w : Len) (bi : BreakInside) (ks : List BNode)
    (h_fit : y + h + 2 * b ≤ fragH) (h_pos : 0 < h) :
    let (_, endC, endY) := layoutNode fragH colW (f + 1) (.box w bi ks (some h) .none 0 false false b 0) c y
    endC = c ∧ endY = y + h + 2 * b := by
  dsimp [layoutNode]
  have hp : nodeStart fragH c y false (bi.avoidsColumn || ks.any (nodeAvoids f)) 0 (h + 2 * b) = (c, y) := by
    dsimp [nodeStart]
    have h1 : decide (y ≥ fragH) = false := by simp; omega
    have h2 : decide (y + (h + 2 * b) > fragH) = false := by simp; omega
    simp [h1, h2]
  have hpc : (nodeStart fragH c y false (bi.avoidsColumn || ks.any (nodeAvoids f)) 0 (h + 2 * b)).fst = c := by rw [hp]
  have hpy : (nodeStart fragH c y false (bi.avoidsColumn || ks.any (nodeAvoids f)) 0 (h + 2 * b)).snd = y := by rw [hp]
  have hle : y + (h + 2 * b) ≤ fragH := by omega
  simp [hpc, hpy, hle, applyBreakAfter]
  omega

/-- Law: A right float placed in an empty column aligns with the column's right edge.
    CSS 2.1 §9.5.1. -/
theorem right_float_aligns_right (colW w y : Nat) (hw : w ≤ colW) :
    floatX colW {} .right w y + w = colW := by
  dsimp [floatX, rightWidthAt]
  omega

/-- Law: An element establishing a new block formatting context overlapping floats of height fh
    (y + mTop < fh) whose width exceeds available width is cleared to at least the float bottom.
    CSS 2.1 §9.5. -/
theorem new_fc_clears_float (colW lw fh y mTop w : Nat)
    (h_pos : y + mTop < fh) (h_w : colW - lw < w) (h_lw : lw ≤ colW) :
    let cf : ColFloats := { lefts := [(0, 0, lw, fh)], rights := [] }
    let (clearY, _) := clearFloats colW cf true w y mTop
    fh ≤ clearY := by
  dsimp [clearFloats, leftWidthAt, rightWidthAt]
  have h1 : y + mTop < fh := h_pos
  have h2 : lw ≤ colW := h_lw
  have h3 : colW - lw < w := h_w
  simp [h1, h2, h3]
  omega

end ColumnLayout
end ChromiumLayout
