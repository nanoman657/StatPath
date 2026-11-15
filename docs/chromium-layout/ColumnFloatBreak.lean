import LayoutTypes
import LayoutBlock
import ColumnLayout
import ColumnNested

/-!
# Multi-Column Float Fragmentation, Editable Intrinsic Size, OOF Spanners, and Nested Offsets

Formalizes CSS Multi-column Layout Level 1 (§3.4, §5, §6) and CSS Fragmentation
Module Level 3 (§3.1, §3.3, §5.1).
-/

namespace ColumnFloatBreak

/-- CSS Multicol 1 §3.4: empty `contenteditable` multicol has balanced height `lh`,
    slicing any float `(fw, fh)` across `cols` columns without increasing `lh`. -/
def layoutEditableMulticol (w cols gap lh fw fh : Nat) :=
  let cw := (w - (cols - 1) * gap) / cols
  let n := if fh == 0 then 1 else cols
  ((w, lh), (List.range n).map fun i =>
    (i * (cw + gap), 0, cw, lh,
     if fh > i * lh then [(0, 0, fw, min lh (fh - i * lh))] else []))

theorem editableMulticol_height (w cols gap lh fw fh : Nat) :
    (layoutEditableMulticol w cols gap lh fw fh).1.2 = lh := rfl

/-- Slice a left float `(fw, fh)` starting at `(col, y)` across columns of height `colH`. -/
def sliceFloat (colH : Nat) : Nat → Nat → Nat → Nat → Nat → List (Nat × Nat × Nat × Nat × Nat)
  | 0, _, _, _, _ => []
  | _ + 1, _, _, _, 0 => []
  | fuel + 1, col, y, fw, rem =>
    let take := min rem (colH - y)
    (col, 0, y, fw, take) ::
      (if rem <= colH - y then [] else sliceFloat colH fuel (col + 1) 0 fw (rem - take))

/-- Inline indent at `(col, y)` from placed float slices `(c, fx, fy, fw, fh)`. -/
def floatIndentAt (slices : List (Nat × Nat × Nat × Nat × Nat)) (col y : Nat) : Nat :=
  slices.foldl (fun acc (c, _, fy, fw, fh) =>
    if c == col && fy <= y && y < fy + fh then acc + fw else acc) 0

theorem floatIndentAt_nil (col y : Nat) : floatIndentAt [] col y = 0 := rfl

inductive InlineOrFloat | line (lh : Nat) | leftFloat (fw fh : Nat)

/-- CSS Multicol 1 §5, CSS 2.1 §9.5: layout lines and left floats across columns of height `colH`. -/
def layoutLinesAndFloats (colH startCol : Nat) (items : List InlineOrFloat) :=
  let rec go : List InlineOrFloat → Nat → Nat → List (Nat × Nat × Nat × Nat × Nat) →
      List (Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat × Nat)
    | [], _, _, flts => ([], flts)
    | .line lh :: tl, col, y, flts =>
      let (c, y') := if y + lh <= colH then (col, y) else (col + 1, 0)
      let (ls, fs) := go tl c (y' + lh) flts
      ((c, floatIndentAt flts c y', y') :: ls, fs)
    | .leftFloat fw fh :: tl, col, y, flts =>
      let x0 := floatIndentAt flts col y
      let raw := sliceFloat colH (fh + 1) col y fw fh
      let placed := raw.map fun (c, _, fy, w, h) =>
        (c, if c == col then x0 else floatIndentAt flts c fy, fy, w, h)
      go tl col y (flts ++ placed)
  go items startCol 0 []

/-- CSS Fragmentation 3 §3.3: lines kept in column 0 under `orphans` and `widows`. -/
def linesInFirstColumn (avail0 lh total orphans widows : Nat) : Nat :=
  let fit := avail0 / lh
  if total <= fit then total
  else if fit < orphans then 0
  else
    let c0 := total - max (total - fit) (min total widows)
    if c0 < orphans then 0 else c0

theorem linesInFirstColumn_lt_orphans (avail0 lh total orphans widows : Nat)
    (h1 : ¬ total <= avail0 / lh) (h2 : avail0 / lh < orphans) :
    linesInFirstColumn avail0 lh total orphans widows = 0 := by
  simp [linesInFirstColumn, h1, h2]

/-- CSS Fragmentation 3 §3.3: layout a block with `total` lines and a float moved by
    `orphans` or `widows`. -/
def layoutBlockWithMovedFloat (colH prevH total lh orphans widows fltIdx fw fh : Nat) :=
  let c0 := linesInFirstColumn (colH - prevH) lh total orphans widows
  let c1 := total - c0
  let pre := fltIdx - c0
  let items1 := (List.replicate pre (.line lh)) ++ [.leftFloat fw fh] ++
    (List.replicate (c1 - pre) (.line lh))
  (c0, layoutLinesAndFloats colH 1 items1)

/-- CSS Fragmentation 3 §3.1: forced break on single in-flow child propagates to wrapper. -/
def layoutWrapperForcedBreak (cw gap colH : Nat) (ws : List (Option (Nat × Nat) × Nat)) :=
  ws.zipIdx.map fun ((flt, h), i) =>
    let kids := match flt with | none => [(0, 0, cw, h)] | some (fw, fh) => [(0, 0, fw, fh), (0, 0, cw, h)]
    (i * (cw + gap), 0, cw, min colH h, kids)

/-- CSS Multicol 1 §3.4: negative block-start margin in balanced multicol. -/
def layoutBalancedNegativeMargin (w cols gap cw ch negM : Nat) :=
  let colW := (w - (cols - 1) * gap) / cols
  let bh := ch - negM
  ((w, bh), (0, 0, colW, bh), (0, -(Int.ofNat negM), cw, ch))

theorem balancedNegativeMargin_le_childH (w cols gap cw ch negM : Nat) :
    (layoutBalancedNegativeMargin w cols gap cw ch negM).1.2 <= ch := by
  simp [layoutBalancedNegativeMargin]

/-- CSS Positioned Layout 3: relpos slices across columns while single-col abspos stays in col 0. -/
def layoutRelWithSingleColAbspos (cw gap colH rw rh aw ah : Nat) :=
  ((ChromiumLayout.ColumnNested.sliceOne colH (rh + 1) rh 0).1).zipIdx.map fun ((_, sh), i) =>
    (i * (cw + gap), 0, cw, sh,
     if i == 0 then [(0, 0, rw, sh), (0, 0, aw, ah)] else [(0, 0, rw, sh)])

/-- CSS Overflow 3 §3.1: multicol visual ink overflow. -/
def multicolInkOverflow (cw gap ch : Nat) (exts : List (Nat × Nat)) : Nat × Nat × Nat × Nat :=
  let n := exts.length
  let bw := if n == 0 then 0 else n * cw + (n - 1) * gap
  let (mw, mh) := exts.zipIdx.foldl (fun (aw, ah) ((w, h), i) =>
    (max aw (i * (cw + gap) + w), max ah h)) (bw, ch)
  (0, 0, mw, mh)

/-- CSS Fragmentation 3 §3.1: `OffsetFromOwnerLayoutBox` in nested multicol. -/
def nestedOffsetFromOwnerLayoutBox
    (ocw ogap oh ospacer icw igap ih ispacer th : Nat) : List (Int × Int) :=
  let ocol0 := ospacer / oh
  let oy0 := ospacer % oh
  let h0 := oh - oy0
  let ox := fun c => c * (ocw + ogap)
  let ix := fun c => c * (icw + igap)
  let cols : List (Int × Int × Nat) :=
    [(Int.ofNat (ox ocol0 + ix 0), Int.ofNat oy0, h0),
     (Int.ofNat (ox ocol0 + ix 1), Int.ofNat oy0, h0),
     (Int.ofNat (ox (ocol0 + 1) + ix 0), 0, min (ih - h0) oh),
     (Int.ofNat (ox (ocol0 + 1) + ix 1), 0, min (ih - h0) oh)]
  let rec place : List (Int × Int × Nat) → Nat → Nat → List (Int × Int)
    | [], _, _ => []
    | (cx, cy, ch) :: rest, sp, rem =>
      if rem == 0 then []
      else if sp >= ch then place rest (sp - ch) rem
      else (cx, cy + Int.ofNat sp) :: place rest 0 (rem - min rem (ch - sp))
  match place cols ispacer th with
  | [] => []
  | (x0, y0) :: tl => (0, 0) :: tl.map fun (x, y) => (x - x0, y - y0)

/-- CSS Multicol 1 §6 & CSS Positioned Layout 3: OOF placed after spanner(s) inside a
    relpos container in a multicol of height `mh` fragments across the remaining
    column height `mh - inflowH / 2` after the spanner (`PositionedFragmentationAndColumnSpanners`,
    `PositionedFragmentationWithNestedSpanner`). -/
def layoutOofAfterSpanner (w gap mh rw inflowH aw ah : Nat) :=
  let cw := (w - gap) / 2
  let yAfter := inflowH / 2
  let remH := mh - yAfter
  let pre := if inflowH == 0 then [(0, 0, cw, 0), (0, 0, w, 0)]
    else [(0, 0, cw, 0), (0, 0, w, 0), (0, 0, cw, yAfter), (cw + gap, 0, cw, yAfter), (0, yAfter, w, 0)]
  let post := [(0, yAfter, cw, remH, [(0, 0, rw, 0), (0, 0, aw, min ah remH)]),
               (cw + gap, yAfter, cw, remH, [(0, 0, aw, ah - min ah remH)])]
  (pre, post)

/-- CSS Multicol 1 §6: abspos inside a column spanner bubbles up to the outer relpos
    containing block outside the multicol, using either explicit `top` or the spanner's
    block-end `inflowH / 2 + spMargin + spH` as static position (`AbsposInSpanner`,
    `AbsposInSpannerStaticPos`). -/
def layoutAbsposInSpanner (w gap mh inflowH spMargin spH aw ah : Nat) (absTop : Option Nat) :=
  let cw := (w - gap) / 2
  let bh := inflowH / 2
  let spY := bh + spMargin
  let endY := spY + spH
  let oofY := absTop.getD endY
  ([(0, 0, cw, bh), (cw + gap, 0, cw, bh), (0, spY, w, spH), (0, endY, cw, mh - endY)],
   (0, oofY, aw, ah))

/-- CSS Multicol 1 §6: OOF inside a relpos preceding `numSpanners` empty spanners balances
    column height to `colH = min mh ((max inflowH (absTop + ah)) / 2)` and creates
    `(max inflowH (absTop + ah)) / colH` columns before the spanners. -/
def layoutOofBeforeSpanners (w gap mh inflowH absTop aw ah numSpanners : Nat) :=
  let cw := (w - gap) / 2
  let totalH := max inflowH (absTop + ah)
  let colH := min mh (totalH / 2)
  let nCols := totalH / colH
  let cols := (List.range nCols).map fun i =>
    let y0 := i * colH
    let y1 := (i + 1) * colH
    let s0 := max absTop y0
    let s1 := min (absTop + ah) y1
    let oof := if s1 > s0 then [(0, s0 - y0, aw, s1 - s0)] else []
    (i * (cw + gap), 0, cw, colH, oof)
  let spanners := List.replicate numSpanners (0, colH, w, 0)
  (cols, spanners)

/-- CSS Positioned Layout 3: auto-height OOF with `bottom: 0` inside relpos of height `rh`
    in multicol of height `colH` starts at `rh - sum childH` and slices children across columns. -/
def layoutAutoHeightBottomOof (cw gap colH rw rh aw : Nat) (kids : List (Nat × Nat)) :=
  let ah := kids.foldl (fun acc (_, h) => acc + h) 0
  let top0 := rh - ah
  let s0 := colH - top0
  let s1 := ah - s0
  [(0, 0, cw, colH, [(0, 0, rw, colH), (0, top0, aw, s0)]),
   (cw + gap, 0, cw, colH, [(0, 0, rw, rh - colH), (0, 0, aw, s1)])]

/-- CSS Fragmentation 3 §3.1: fragmentainer break tokens `(seq, consumed, childTokens, causedBySpanner)`
    around a column spanner when an OOF of height `oofH` and in-flow content of height
    `inflowBefore` precede the spanner and `inflowAfter` follows it. -/
def fragmentainerBreakTokensWithSpanner (colH inflowBefore oofH inflowAfter : Nat) :=
  let nBefore := (max inflowBefore oofH) / colH
  let pre := (List.range nBefore).map fun i =>
    let consumed := (i + 1) * colH
    (i, consumed, 1, decide (inflowBefore <= consumed))
  let postH := inflowAfter / 2
  (pre, true, [(nBefore, nBefore * colH + postH, 1, false)], false)

/-- CSS Fragmentation 3 §3.1: for `numCols` columns of height `colH` and OOF boxes
    `(top, h)`, every column `c < numCols - 1` has a break token whose child-token count
    is the number of OOFs spanning across `(c + 1) * colH`, and the last column has `none`. -/
def oofFragmentainerBreakTokens (numCols colH : Nat) (oofs : List (Nat × Nat)) : List (Option Nat) :=
  (List.range numCols).map fun c =>
    if c + 1 == numCols then none
    else
      let edge := (c + 1) * colH
      some (oofs.filter (fun (t, h) => t < edge && t + h > edge)).length

theorem oofFragmentainerBreakTokens_length (numCols colH : Nat) (oofs : List (Nat × Nat)) :
    (oofFragmentainerBreakTokens numCols colH oofs).length = numCols := by
  simp [oofFragmentainerBreakTokens]

end ColumnFloatBreak
