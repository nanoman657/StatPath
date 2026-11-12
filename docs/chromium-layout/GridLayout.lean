/-
  GridLayout.lean: CSS Grid Layout Level 1 algorithm,
  written from grid_layout_algorithm_test.cc and grid_track_collection_test.cc.
  Owned by the block lane (Grid*).
-/

namespace ChromiumLayout
namespace GridLayout

/-- Track sizing and gap specification for a 2D CSS grid container. -/
structure GridSpec where
  columns : List Nat := []
  rows : List Nat := []
  colGap : Nat := 0
  rowGap : Nat := 0
  width : Option Nat := none
  height : Option Nat := none
  deriving Inhabited, DecidableEq, Repr

/-- Item specification inside a CSS grid container. -/
structure GridItem where
  id : Nat := 0
  col : Option Nat := none
  row : Option Nat := none
  colSpan : Nat := 1
  rowSpan : Nat := 1
  w : Option Nat := none
  h : Option Nat := none
  deriving Inhabited, DecidableEq, Repr

/-- Placed grid item with resolved cell coordinates and physical dimensions. -/
structure PlacedGridItem where
  id : Nat := 0
  col : Nat := 0
  row : Nat := 0
  colSpan : Nat := 1
  rowSpan : Nat := 1
  x : Nat := 0
  y : Nat := 0
  w : Nat := 0
  h : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Auto-placement algorithm in row-major order (CSS Grid §8.5). -/
def autoPlaceItems (numCols : Nat) (items : List GridItem) : List PlacedGridItem :=
  let rec place (curCol curRow : Nat) (rem : List GridItem) : List PlacedGridItem :=
    match rem with
    | [] => []
    | it :: rest =>
        let (targetCol, targetRow, nextCol, nextRow) :=
          match it.col, it.row with
          | some c, some r => (c, r, curCol, curRow)
          | some c, none =>
              let r := if c < curCol then curRow + 1 else curRow
              let nc := if c + 1 >= numCols then 0 else c + 1
              let nr := if c + 1 >= numCols then r + 1 else r
              (c, r, nc, nr)
          | none, some r =>
              let c := if r > curRow then 0 else curCol
              let nc := if c + 1 >= numCols then 0 else c + 1
              let nr := if c + 1 >= numCols then r + 1 else r
              (c, r, nc, nr)
          | none, none =>
              let c := curCol
              let r := curRow
              let nc := if c + 1 >= numCols then 0 else c + 1
              let nr := if c + 1 >= numCols then r + 1 else r
              (c, r, nc, nr)
        let placed : PlacedGridItem := {
          id := it.id,
          col := targetCol,
          row := targetRow,
          colSpan := it.colSpan,
          rowSpan := it.rowSpan,
          w := it.w.getD 0,
          h := it.h.getD 0
        }
        placed :: place nextCol nextRow rest
  place 0 0 items

/-- Calculate offset of track `idx` accounting for preceding track sizes and gaps. -/
def trackOffset (gap : Nat) (tracks : List Nat) (idx : Nat) : Nat :=
  let rec loop (i : Nat) (offset : Nat) (rem : List Nat) : Nat :=
    match rem with
    | [] => offset
    | t :: rest =>
        if i = idx then offset
        else loop (i + 1) (offset + t + gap) rest
  loop 0 0 tracks

/-- Calculate total spanned size across `span` consecutive tracks including inner gaps. -/
def trackSpanSize (gap : Nat) (tracks : List Nat) (startIdx span : Nat) : Nat :=
  let rec loop (i : Nat) (rem : List Nat) (accum : Nat) (count : Nat) : Nat :=
    match rem with
    | [] => accum
    | t :: rest =>
        if i < startIdx then loop (i + 1) rest accum count
        else if count < span then
          let addGap := if count = 0 then 0 else gap
          loop (i + 1) rest (accum + t + addGap) (count + 1)
        else accum
  loop 0 tracks 0 0

/-- Result of 2D grid container layout. -/
structure GridResult where
  w : Nat := 0
  h : Nat := 0
  items : List PlacedGridItem := []
  deriving Inhabited, DecidableEq, Repr

/-- 2D Grid Layout Algorithm (CSS Grid Layout Level 1). -/
def layoutGrid (spec : GridSpec) (items : List GridItem) : GridResult :=
  let numCols := spec.columns.length
  let placed := autoPlaceItems numCols items
  let finalItems := placed.map (fun it =>
    let x := trackOffset spec.colGap spec.columns it.col
    let y := trackOffset spec.rowGap spec.rows it.row
    let cellW := trackSpanSize spec.colGap spec.columns it.col it.colSpan
    let cellH := trackSpanSize spec.rowGap spec.rows it.row it.rowSpan
    let w := if it.w > 0 then it.w else cellW
    let h := if it.h > 0 then it.h else cellH
    { it with x := x, y := y, w := w, h := h })
  let contentW :=
    match spec.columns with
    | [] => 0
    | _ => spec.columns.foldl (·+·) 0 + (spec.columns.length - 1) * spec.colGap
  let contentH :=
    match spec.rows with
    | [] => 0
    | _ => spec.rows.foldl (·+·) 0 + (spec.rows.length - 1) * spec.rowGap
  let finalW := spec.width.getD contentW
  let finalH := spec.height.getD contentH
  ⟨finalW, finalH, finalItems⟩

/-- Helper loop for range index mapping. -/
def rangeIndexLoop (idx accum line : Nat) : List Nat → Nat
  | [] => idx
  | count :: rest =>
      if line < accum + count then idx
      else rangeIndexLoop (idx + 1) (accum + count) line rest

/-- Find which range index contains the given grid line index (`GridTrackCollection`). -/
def rangeIndexFromGridLine (rangeCounts : List Nat) (line : Nat) : Nat :=
  rangeIndexLoop 0 0 line rangeCounts

/-- Grid range descriptor with starting grid line and track count. -/
structure GridRange where
  startLine : Nat
  trackCount : Nat
  deriving Inhabited, DecidableEq, Repr

/-- Build grid ranges from repeater definitions (`GridRangeBuilder`). -/
def buildGridRanges (repeaters : List (Nat × Nat)) : List GridRange :=
  let rec loop (curLine : Nat) (rem : List (Nat × Nat)) : List GridRange :=
    match rem with
    | [] => []
    | (trackSize, repeatCount) :: rest =>
        let count := trackSize * repeatCount
        ⟨curLine, count⟩ :: loop (curLine + count) rest
  loop 0 repeaters

/-- Adding gap strictly increases inter-track distance when gap is positive. -/
theorem grid_gap_positive (t gap : Nat) (h : 0 < gap) :
    t < t + gap := by
  omega

/-- Grid line 0 is in range 0 when the first range has positive track count. -/
theorem range_index_first_track (c : Nat) (rest : List Nat) (h : 0 < c) :
    rangeIndexFromGridLine (c :: rest) 0 = 0 := by
  dsimp [rangeIndexFromGridLine, rangeIndexLoop]
  split
  · rfl
  · rename_i h_not
    omega

/-- Track offset of index 0 is always 0. -/
theorem track_offset_zero (gap : Nat) (tracks : List Nat) :
    trackOffset gap tracks 0 = 0 := by
  dsimp [trackOffset]
  cases tracks <;> rfl

/-- A track sizing function (CSS Grid 1 §7.2): a keyword, a fixed length, a percentage, a flexible
    length, or fit-content(percentage). -/
inductive TrackSz where
  | auto
  | minContent
  | maxContent
  | fixed (px : Nat)
  | pct (p : Nat)
  | fr (q : Nat)
  | fitContent (p : Nat)
  deriving DecidableEq, Repr

/-- A track definition: one track sizing function, or `minmax(lo, hi)` (CSS Grid 1 §7.2.2). -/
inductive TrackDef where
  | single (s : TrackSz)
  | minmax (lo hi : TrackSz)
  deriving DecidableEq, Repr

/-- Minimum of a track after normalization (CSS Grid 1 §7.2.2): a percentage resolves only against a
    definite content size and is `auto` otherwise, and a flexible minimum is `auto`. -/
def normMin (definite : Bool) : TrackSz → TrackSz
  | .pct p => if definite then .pct p else .auto
  | .fr _ => .auto
  | s => s

/-- Maximum of a track after normalization: a percentage as for `normMin`; fit-content(p) stays a
    fit-content in a definite container and is `max-content` in an indefinite one. -/
def normMax (definite : Bool) : TrackSz → TrackSz
  | .pct p => if definite then .pct p else .auto
  | .fitContent p => if definite then .fitContent p else .maxContent
  | s => s

/-- Normalized (min, max) of a track definition. A single fit-content(p) has minimum `p` in a
    definite container and `auto` otherwise. This is the rule the set constructor applies. -/
def normalizeTrack (definite : Bool) : TrackDef → TrackSz × TrackSz
  | .single (.fitContent p) => (normMin definite (.pct p), normMax definite (.fitContent p))
  | .single s => (normMin definite s, normMax definite s)
  | .minmax lo hi => (normMin definite lo, normMax definite hi)

/-- Law: in an indefinite container no normalized track keeps a percentage. -/
theorem normalizeTrack_indefinite_no_pct (t : TrackDef) (p : Nat) :
    (normalizeTrack false t).1 ≠ .pct p ∧ (normalizeTrack false t).2 ≠ .pct p := by
  cases t with
  | single s => cases s <;> simp [normalizeTrack, normMin, normMax]
  | minmax lo hi => cases lo <;> cases hi <;> simp [normalizeTrack, normMin, normMax]

/-- An explicit repeater (CSS Grid 2 §7.2): `tracks` tracks per repetition, repeated `reps` times.
    An auto-fit repeater takes the auto repetition count instead, and it collapses (CSS Grid 2
    §7.2.3.2) when no grid item is placed in it. -/
structure RepeaterSpec where
  tracks : Nat
  reps : Nat := 1
  autoFit : Bool := false
  hasItems : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- Explicit ranges from a starting grid line, each paired with whether it is collapsed. -/
def rangesFrom (autoReps : Nat) : Nat → List RepeaterSpec → List (GridRange × Bool)
  | _, [] => []
  | curLine, r :: rest =>
      let reps := if r.autoFit then autoReps else r.reps
      let count := r.tracks * reps
      (⟨curLine, count⟩, r.autoFit && !r.hasItems) :: rangesFrom autoReps (curLine + count) rest

/-- Explicit ranges from the start of the grid, with auto-fit collapse (`GridRangeBuilder`). -/
def buildGridRangesAuto (autoReps : Nat) (repeaters : List RepeaterSpec) : List (GridRange × Bool) :=
  rangesFrom autoReps 0 repeaters

/-- Law: a range is collapsed exactly when its repeater is auto-fit and has no placed item. -/
theorem collapsed_iff_autofit_empty (autoReps : Nat) (rs : List RepeaterSpec) (curLine : Nat) :
    (rangesFrom autoReps curLine rs).map (·.2) = rs.map (fun r => r.autoFit && !r.hasItems) := by
  induction rs generalizing curLine with
  | nil => rfl
  | cons r rest ih => simp [rangesFrom, ih]

/-- Midpoint of gap `g` along one axis, between track `g` and track `g + 1`. The gutter starts at
    the end of track `g` and is `gap` wide; the midpoint is `gap / 2` into it. Centring the rule in
    the gutter is the convention the gap-geometry tests check; the spec text does not state it. -/
def gapMidpoint (gap : Nat) (tracks : List Nat) (g : Nat) : Nat :=
  trackOffset gap tracks g + tracks.getD g 0 + gap / 2

/-- Content size along one axis: the track sizes plus the `length - 1` gaps between them. -/
def gridContentSize (gap : Nat) (tracks : List Nat) : Nat :=
  tracks.foldl (· + ·) 0 + (tracks.length - 1) * gap

/-- A placed item as half-open track ranges on each axis (`lo` inclusive, `hi` exclusive). -/
structure GapItem where
  rowLo : Nat
  rowHi : Nat
  colLo : Nat
  colHi : Nat

/-- Law: a gap midpoint lies at or after the end of its leading track. -/
theorem gapMidpoint_ge_track_end (gap : Nat) (tracks : List Nat) (g : Nat) :
    trackOffset gap tracks g + tracks.getD g 0 ≤ gapMidpoint gap tracks g := by
  unfold gapMidpoint
  omega

/-- A gap decoration object exists only when the container sets a gap rule and there is a gap to
    decorate, i.e. at least two tracks. The rule flag is an input; the Blink `GapGeometry` object
    itself is not modelled. Each conjunct is checked by one negative row (`nullptr` results). -/
def gapGeometryPresent (hasRule : Bool) (tracks : List Nat) : Bool :=
  hasRule && decide (2 ≤ tracks.length)

/-- Size of each of `n` auto tracks, all with zero base size, after stretching. With
    `align-content: normal` the free space left in a box of size `box` after the `n - 1` gaps is
    divided equally among the auto tracks (CSS Grid Layout 1, stretch auto tracks). -/
def stretchedAutoSize (box gap n : Nat) : Nat :=
  if n = 0 then 0 else (box - (n - 1) * gap) / n

/-- Law: the stretched auto tracks never exceed the box. -/
theorem stretchedAutoSize_total_le (box gap n : Nat) :
    stretchedAutoSize box gap n * n ≤ box := by
  unfold stretchedAutoSize
  split
  · simp
  · exact Nat.le_trans (Nat.div_mul_le_self _ _) (Nat.sub_le _ _)

end GridLayout
end ChromiumLayout
