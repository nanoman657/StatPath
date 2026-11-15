import ColumnLayout
/-
  ColumnNested.lean: Nested multi-column fragmentation (CSS Multi-column Layout Level 1 §3.4, §4,
  §6; CSS Fragmentation Level 3 §3.1, §5.1). Models an inner multicol container fragmented across
  outer multicol fragmentainers, with optional leading sibling, padding, block-start border/spanner
  chrome, and either unbreakable or sliceable in-flow children. Owned by the block lane.
-/
namespace ChromiumLayout
namespace ColumnNested

/-- Inner column inline size inside an outer column of width `outerColW` with horizontal padding
    `pad`. CSS Multi-column Layout 1 §3.4. -/
def innerColWidth (outerColW pad innerCols innerGap : Nat) : Nat :=
  (outerColW - 2 * pad - (innerCols - 1) * innerGap) / innerCols

/-- Law: `innerCols` inner columns never exceed the available content inline size after padding and
    gaps. CSS Multi-column Layout 1 §3.4. -/
theorem inner_cols_fit_outer (outerColW pad innerCols innerGap : Nat) :
    innerCols * innerColWidth outerColW pad innerCols innerGap ≤
      outerColW - 2 * pad - (innerCols - 1) * innerGap := by
  unfold innerColWidth
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

/-- Group `items` into chunks of size `cap`, producing inner column fragments
    `(cx, cy, cw, colH, childRects)`. -/
def packInnerCols (pad cy cw gap colH itemH cap : Nat) :
    Nat → Nat → List Nat → List (Nat × Nat × Nat × Nat × List (Nat × Nat × Nat × Nat))
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, j, rem =>
    let takeN := max 1 cap
    let grp := rem.take takeN
    let kids := grp.zipIdx.map fun (w, i) => (0, i * itemH, w, itemH)
    (pad + j * (cw + gap), cy, cw, colH, kids) ::
      packInnerCols pad cy cw gap colH itemH cap fuel (j + 1) (rem.drop takeN)

/-- Fragment an inner multicol container containing unbreakable items `items` (each of block size
    `itemH`) across outer columns of block size `outerH` and inline size `outerColW`.
    Returns `(y, outerColW, boxH, innerColFrags)` for each outer column.
    CSS Multi-column Layout 1 §4, CSS Fragmentation 3 §3.1. -/
def layoutNestedItems (outerH outerColW innerCols innerGap pad itemH leadH : Nat)
    (innerH : Option Nat) (items : List Nat) :
    List (Nat × Nat × Nat × List (Nat × Nat × Nat × Nat × List (Nat × Nat × Nat × Nat))) :=
  let cw := innerColWidth outerColW pad innerCols innerGap
  let rec go : Nat → Bool → Option Nat → List Nat →
      List (Nat × Nat × Nat × List (Nat × Nat × Nat × Nat × List (Nat × Nat × Nat × Nat)))
    | 0, _, _, _ => []
    | fuel + 1, isFirst, remBox, remItems =>
      if remBox == some 0 && remItems.isEmpty then []
      else if remBox == none && !isFirst && remItems.isEmpty then []
      else
        let y0 := if isFirst then leadH else 0
        let avail := outerH - y0
        let topPad := if isFirst then pad else 0
        let cap0 := (avail - topPad) / itemH
        let boxH := match remBox with
          | some r => min r avail
          | none =>
            if (remItems.drop (innerCols * cap0)).isEmpty then
              topPad + min cap0 remItems.length * itemH
            else avail
        let remBox' := remBox.map (· - boxH)
        let botPad := if remBox' == some 0 then pad else 0
        let colH := if remBox.isSome then boxH - topPad - botPad else avail - topPad
        let cap := colH / itemH
        let (here, rest) :=
          if remBox' == some 0 then (remItems, [])
          else (remItems.take (innerCols * cap), remItems.drop (innerCols * cap))
        let cols :=
          if isFirst && here.isEmpty then [(pad, topPad, cw, colH, [])]
          else packInnerCols pad topPad cw innerGap colH itemH cap here.length 0 here
        (y0, outerColW, boxH, cols) :: go fuel false remBox' rest
  go (items.length + 4) true (innerH.map (· + 2 * pad)) items

/-- Fragment a 2-column inner multicol of inline size `outerColW` and gap `innerGap` with
    block-start chrome `topChrome` (padding-top, border-top, or spanner) and a sliceable child
    `(childW, childH)` across outer columns of height `outerH` after leading height `leadH`.
    CSS Multi-column Layout 1 §4, §6; CSS Fragmentation 3 §3.1. -/
def layoutNestedBlock (outerH outerColW innerGap leadH topChrome : Nat)
    (innerH : Option Nat) (childW childH : Nat) :
    List (Nat × Nat × Nat × List (Nat × Nat × Nat × Nat × (Nat × Nat × Nat × Nat))) :=
  let cw := innerColWidth outerColW 0 2 innerGap
  let cx1 := cw + innerGap
  if innerH.isNone && childH == 0 then
    [(leadH, outerColW, 0, [(0, 0, cw, 0, (0, 0, childW, 0))])]
  else
    let colH0 := if leadH < outerH then outerH - topChrome else 0
    let c0 :=
      if leadH == outerH then []
      else if colH0 == 0 then [(leadH, outerColW, outerH - leadH, [])]
      else
        [(leadH, outerColW, outerH - leadH,
          [(0, topChrome, cw, colH0, (0, 0, childW, colH0)),
           (cx1, topChrome, cw, colH0, (0, 0, childW, colH0))])]
    let remChild := childH - 2 * colH0
    let colH1 := match innerH with
      | some h => h - colH0
      | none => (remChild + 1) / 2
    let s0 := min remChild colH1
    let s1 := remChild - s0
    c0 ++ [(0, outerColW, colH1,
            [(0, 0, cw, colH1, (0, 0, childW, s0)),
             (cx1, 0, cw, colH1, (0, 0, childW, s1))])]

/-- Slice a single block of height `rem` starting at offset `cy` inside columns of height `colH`,
    returning `(sliceSizes, nextCy, extraColsStarted)`. CSS Fragmentation 3 §3.1. -/
def sliceOne (colH : Nat) : Nat → Nat → Nat → List (Nat × Nat) × Nat
  | 0, _, cy => ([], cy)
  | _ + 1, 0, cy => ([], cy)
  | fuel + 1, rem, cy =>
    let s := min rem (colH - cy)
    let rem' := rem - s
    let cy' := if cy + s == colH then 0 else cy + s
    let (rest, finalCy) := sliceOne colH fuel rem' cy'
    ((0, s) :: rest, finalCy)

/-- Slice a sequence of children `(w, h)` across inner columns of height `colH`. -/
def sliceStream (colH : Nat) (kids : List (Nat × Nat)) : List (List (Nat × Nat)) :=
  let rec go (cy : Nat) : List (Nat × Nat) → List (List (Nat × Nat))
    | [] => []
    | (w, h) :: rest =>
      let (slices, cy') := sliceOne colH (h + 2) h cy
      (slices.map fun (_, s) => (w, s)) :: go cy' rest
  go 0 kids

/-- `HasSeenAllChildren` on each break token of a fragmented IFC of block size `boxH` containing
    `numLines` lines of height `lineH` in fragmentainers of height `colH`.
    CSS Fragmentation 3 §3.1. -/
def ifcBreakTokensHasSeenAll (colH boxH lineH numLines : Nat) : List Bool :=
  let numFrags := (boxH + colH - 1) / colH
  let linesPerCol := colH / lineH
  (List.range (numFrags - 1)).map fun k => decide ((k + 1) * linesPerCol ≥ numLines)

end ColumnNested
end ChromiumLayout
