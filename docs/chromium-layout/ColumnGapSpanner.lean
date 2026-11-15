/-
  ColumnGapSpanner.lean: Multi-column gap decoration geometry (cross gaps, row-wrap main gaps,
  and start/end spanner main gaps), invalid spanners inside nested BFCs, wrapper margin/border
  splitting before spanners, and spanner fragmentation across outer multi-column containers.
  Spec: CSS Gap Decorations Module Level 1 §3 (Gap Geometry, Cross Gaps, Main Gaps),
  CSS Multi-column Layout Module Level 1 §6 (Spanning Columns), and
  CSS Multi-column Layout Module Level 2 (`column-height`, `column-wrap`).
-/

namespace ChromiumLayout
namespace ColumnGapSpanner

/-- Classification of a multi-column main (row) gap for gap decorations.
    CSS Gap Decorations 1 §3. -/
inductive MainGapKind where
  | none
  | startSpanner
  | endSpanner
  deriving DecidableEq, Repr

/-- Segment of a multi-column container: either a column flow segment of total stacked
    block size `totalH` or a `column-span: all` spanner of block size `h`. -/
inductive Seg where
  | cols (totalH : Nat)
  | spanner (h : Nat)
  deriving DecidableEq, Repr

/-- Cross-gap `(inlineOffset, blockOffset)` midpoints between `numCols` columns of width
    `colW` separated by `colGap`, inside a container with border `border`.
    CSS Gap Decorations 1 §3.2.
    Required by `GapDecorationBasic`, `GapDecorationContentEndPastContainer`,
    `GapDecorationColumnWrapOneColumn`, `GapDecorationColumnWrapBasic`,
    `GapDecorationColumnWrapAndSpanner`, `GapDecorationTwoSpanners`. -/
def crossGaps (border colW colGap numCols : Nat) : List (Nat × Nat) :=
  (List.range (numCols - 1)).map fun i =>
    (border + (i + 1) * colW + i * colGap + colGap / 2, border)

/-- Content inline bounds `(inlineStart, inlineEnd)` for multi-column gap geometry:
    extends past `border + width` when overflow columns create cross gaps beyond the
    container inline end. CSS Gap Decorations 1 §3.3.
    Required by `GapDecorationBasic`, `GapDecorationContentEndPastContainer`. -/
def contentInlineBounds (border width colW colGap numCols : Nat) : Nat × Nat :=
  let gs := crossGaps border colW colGap numCols
  let lastGap := match gs.getLast? with
    | some (g, _) => g
    | none => 0
  (border, max (border + width) lastGap)

/-- Helper to consume a column segment of total stacked height `remTotal` across wrapping
    rows of height `colH` (or unconstrained when `colH == 0`) with `numCols` columns per row. -/
def consumeCols (fuel border colH rowGap numCols y remTotal : Nat)
    (gaps : List (Nat × MainGapKind)) : List (Nat × MainGapKind) × Nat :=
  match fuel with
  | 0 => (gaps, y)
  | fuel' + 1 =>
    if remTotal == 0 then (gaps, y)
    else if colH == 0 then
      let balH := (remTotal + numCols - 1) / numCols
      (gaps, y + balH)
    else
      let stride := colH + rowGap
      let offInRow := (y - border) % stride
      let remRowH := colH - offInRow
      let cap := numCols * remRowH
      if remTotal ≤ cap then
        let usedH := (remTotal + numCols - 1) / numCols
        (gaps, y + usedH)
      else
        let rowEnd := y + remRowH
        let gaps' := gaps ++ [(rowEnd + rowGap / 2, .none)]
        consumeCols fuel' border colH rowGap numCols (rowEnd + rowGap) (remTotal - cap) gaps'

/-- Accumulate main gaps `(blockOffset, kind)` and final content block end across a sequence
    of column segments and spanners. CSS Gap Decorations 1 §3.1–§3.3, CSS Multicol 2.
    Required by `GapDecorationBasic`, `GapDecorationContentEndPastContainer`,
    `GapDecorationColumnWrapOneColumn`, `GapDecorationColumnWrapBasic`,
    `GapDecorationColumnWrapAndSpanner`, `GapDecorationTwoSpanners`. -/
def accumulateMainGaps (border colH rowGap numCols : Nat) (segs : List Seg) :
    List (Nat × MainGapKind) × Nat :=
  let rec go (y : Nat) (gaps : List (Nat × MainGapKind)) :
      List Seg → List (Nat × MainGapKind) × Nat
    | [] => (gaps, y)
    | .cols totalH :: rest =>
      let (gaps', y') := consumeCols (totalH + 1) border colH rowGap numCols y totalH gaps
      go y' gaps' rest
    | .spanner h :: rest =>
      let (gaps1, y1) :=
        if colH > 0 then
          let stride := colH + rowGap
          let offInRow := (y - border) % stride
          let remRowH := colH - offInRow
          if offInRow > 0 && remRowH < h then
            let rowEnd := y + remRowH
            (gaps ++ [(rowEnd + rowGap / 2, .none)], rowEnd + rowGap)
          else (gaps, y)
        else (gaps, y)
      let gaps2 := gaps1 ++ [(y1, .startSpanner)]
      let y2 := y1 + h
      let gaps3 := if rest.isEmpty then gaps2 else gaps2 ++ [(y2, .endSpanner)]
      go y2 gaps3 rest
  go border [] segs

/-- Layout a multi-column child wrapper with `marginTop` and `borderTop` containing a
    `column-span: all` spanner of `(spanW, spanH)` followed by a child of `(childW, childH)`.
    Returns `(containerH, preColRect, preWrapRect, spannerRect, postColYs, postChildH)`.
    CSS Multicol 1 §6.
    Required by `MarginAndBorderTopWithSpanner`. -/
def layoutMarginBorderWithSpanner (colW gap nCols wrapW marginTop borderTop
    spanW spanH childH : Nat) :
    Nat × (Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) ×
      (Nat × Nat × Nat × Nat) × List (Nat × Nat × Nat × Nat) :=
  let preH := marginTop + borderTop
  let postH := (childH + nCols - 1) / nCols
  let postY := preH + spanH
  let postCols := (List.range nCols).map fun i => (i * (colW + gap), postY, colW, postH)
  (postY + postH,
   (0, 0, colW, preH),
   (0, marginTop, wrapW, borderTop),
   (0, preH, spanW, spanH),
   postCols)

/-- Layout invalid `column-span: all` descendants inside a float of width `floatW` and a
    `display: flow-root` BFC sibling, each of block size `boxH`, across `nCols` columns.
    Because `column-span: all` only applies to in-flow descendants in the multicol's own BFC,
    both are fragmented as normal column content alongside each other. CSS Multicol 1 §6.1.
    Required by `InvalidSpanners`. -/
def layoutInvalidSpannersInBfc (colW gap nCols border floatW boxH : Nat) :
    (Nat × Nat) × List ((Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat)) :=
  let colH := boxH / nCols
  let totalW := nCols * colW + (nCols - 1) * gap + 2 * border
  let totalH := colH + 2 * border
  let cols := (List.range nCols).map fun i =>
    ((border + i * (colW + gap), border, colW, colH),
     (0, 0, floatW, colH),
     (floatW, 0, colW - floatW, colH))
  ((totalW, totalH), cols)

/-- Fragment a nested multicol `.inner` (with fixed height `innerH`, padding `pad`, 2 inner
    columns, a pre-spanner balanced row of height `preRowH`, an inner spanner of total height
    `spanH`, and a post-spanner balanced row) across outer columns of height `outerH` after
    a leading outer block of height `leadH`.
    Returns `(spanSlices, postInnerColYAndH, trailingOuterSliceH)`.
    CSS Multicol 1 §6, CSS Fragmentation 3 §3.1.
    Required by `BreakInsideSpanner`, `BreakInsideSpannerTwice`,
    `BreakInsideSpannerWithContent`. -/
def fragmentInnerSpanner (outerH leadH innerH pad preRowH spanH : Nat)
    (clipPostByInnerEnd : Bool := false) :
    List Nat × (Nat × Nat) × Nat :=
  let rem0 := outerH - leadH
  let preUsed := pad + preRowH
  let s0 := min spanH (rem0 - preUsed)
  let remSpan1 := spanH - s0
  if remSpan1 ≤ outerH then
    let postY := remSpan1
    let rawPostH := outerH - postY
    let postH := if clipPostByInnerEnd then rawPostH - pad else rawPostH
    let totalBoxH := innerH + 2 * pad
    let trailH := totalBoxH - rem0 - outerH
    ([s0, remSpan1], (postY, postH), trailH)
  else
    let s1 := outerH
    let s2 := remSpan1 - s1
    let postY := s2
    let postH := outerH - postY
    let totalBoxH := innerH + 2 * pad
    let trailH := totalBoxH - rem0 - 2 * outerH
    ([s0, s1, s2], (postY, postH), trailH)

/-- Law: a multi-column container with `numCols ≥ 1` has `numCols - 1` cross gaps
    (CSS Gap Decorations 1 §3.2). -/
theorem crossGaps_length (border colW colGap numCols : Nat) :
    (crossGaps border colW colGap numCols).length = numCols - 1 := by
  simp [crossGaps]

/-- Law: `contentInlineBounds` always has `inlineEnd ≥ border + width`
    (CSS Gap Decorations 1 §3.3). -/
theorem contentInlineEnd_ge_box (border width colW colGap numCols : Nat) :
    (contentInlineBounds border width colW colGap numCols).2 ≥ border + width := by
  simp [contentInlineBounds]
  omega

end ColumnGapSpanner
end ChromiumLayout
