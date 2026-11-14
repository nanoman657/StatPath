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

/-- Resolve gap percentage against container dimension. CSS Box Alignment 3 §8, CSS Grid 1 §10.1. -/
def resolveGapPercent (pct : Nat) (containerDim : Option Nat) : Nat :=
  match containerDim with
  | some d => d * pct / 100
  | none => 0

/-- Resolve gap percentage in LayoutUnit (64ths px). CSS Box Alignment 3 §8, CSS Grid 1 §10.1. -/
def resolveGapPercentLU (pct : Nat) (containerDim : Option Nat) : Nat :=
  match containerDim with
  | some d => d * pct * 64 / 100
  | none => 0

/-- Grid range descriptor with starting grid line, track count, and collapsed flag. CSS Grid 1 §7.2.3. -/
structure GridRange where
  startLine : Nat
  trackCount : Nat
  isCollapsed : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- Grid repeater descriptor (track size, repeat count, and whether collapsed). CSS Grid 1 §7.2.3. -/
structure GridRepeater where
  trackSize : Nat
  repeatCount : Nat
  isCollapsed : Bool := false
  deriving Inhabited, DecidableEq, Repr

instance : Coe (Nat × Nat) GridRepeater where
  coe p := ⟨p.1, p.2, false⟩

/-- Build grid ranges from repeater definitions (`GridRangeBuilder`). CSS Grid 1 §7.2.3. -/
def buildGridRanges (repeaters : List GridRepeater) : List GridRange :=
  let rec loop (curLine : Nat) (rem : List GridRepeater) : List GridRange :=
    match rem with
    | [] => []
    | rep :: rest =>
        let count := rep.trackSize * rep.repeatCount
        ⟨curLine, count, rep.isCollapsed⟩ :: loop (curLine + count) rest
  loop 0 repeaters

/-- Track size type for CSS Grid Level 1 §7.2.5. -/
inductive GridTrackSizeType where
  | auto
  | fixed (px : Nat)
  | percent (pct : Nat)
  | minContent
  | maxContent
  | flex (fr : Nat)
  | fitContent (limit : Nat)
  deriving Inhabited, DecidableEq, Repr

/-- A resolved grid track size pair: (minTrackSize, maxTrackSize). CSS Grid 1 §7.2.5. -/
structure NormalizedTrackSize where
  minType : GridTrackSizeType
  maxType : GridTrackSizeType
  deriving Inhabited, DecidableEq, Repr

/-- Normalize track size definition for definite vs indefinite container. CSS Grid 1 §7.2.5. -/
def normalizeTrackSize (minType maxType : GridTrackSizeType) (isIndefinite : Bool) : NormalizedTrackSize :=
  let normMin :=
    match minType with
    | .flex _ => .auto
    | .percent _ => if isIndefinite then .auto else minType
    | _ => minType
  let normMax :=
    match maxType with
    | .percent _ => if isIndefinite then .auto else maxType
    | .fitContent _ => if isIndefinite then .maxContent else maxType
    | _ => maxType
  ⟨normMin, normMax⟩

/-- Law: First grid range starts at line 0.
    CSS Grid Layout Level 1 §7.2.3. -/
theorem grid_ranges_start_zero (rep : GridRepeater) (rest : List GridRepeater) :
    (buildGridRanges (rep :: rest)).head?.map (·.startLine) = some 0 := by
  rfl

/-- Law: A flex factor is never a track minimum in normalized track sizes.
    CSS Grid Layout Level 1 §7.2.5. -/
theorem normalize_no_flex_min (minT maxT : GridTrackSizeType) (isIndefinite : Bool) :
    match (normalizeTrackSize minT maxT isIndefinite).minType with
    | .flex _ => False
    | _ => True := by
  dsimp [normalizeTrackSize]
  cases minT <;> (try cases isIndefinite) <;> trivial

/-- Law: Percentage gap resolves to 0 when container dimension is indefinite.
    CSS Box Alignment Level 3 §8, CSS Grid 1 §10.1. -/
theorem resolve_gap_none (pct : Nat) :
    resolveGapPercent pct none = 0 := by
  rfl

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

/-- A refined grid range with start grid line, track count, collapsed, and implicit flags.
    CSS Grid Layout Level 1 §7.2.3, §7.6. -/
structure TrackRange where
  startLine : Nat
  trackCount : Nat
  isCollapsed : Bool := false
  isImplicit : Bool := false
  hasFlexible : Bool := false
  hasIntrinsic : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- Ensure track coverage over [startLine, startLine + count) given range list.
    Returns the start and end range indices (0-based, inclusive) that cover the interval.
    CSS Grid Layout Level 1 §7.6. -/
def coverageRangeIndices (ranges : List TrackRange) (startLine count : Nat) : Option (Nat × Nat) :=
  let endLine := startLine + count
  let rec loop (idx : Nat) (rem : List TrackRange) (startIdx endIdx : Option Nat) : Option (Nat × Nat) :=
    match rem with
    | [] =>
        match startIdx, endIdx with
        | some s, some e => some (s, e)
        | some s, none => some (s, idx - 1)
        | _, _ => none
    | r :: rest =>
        let rEnd := r.startLine + r.trackCount
        let overlaps := r.startLine < endLine && rEnd > startLine
        let newStart := if overlaps && startIdx.isNone then some idx else startIdx
        let newEnd := if overlaps then some idx else endIdx
        loop (idx + 1) rest newStart newEnd
  loop 0 ranges none none

/-- Whether a track size is flexible (fr unit). CSS Grid Layout Level 1 §11.4. -/
def isFlexibleTrack : GridTrackSizeType → Bool
  | .flex _ => true
  | _ => false

/-- Whether a track size is intrinsic (min-content, max-content, auto, fit-content, flex).
    CSS Grid Layout Level 1 §11.4. -/
def isIntrinsicTrack : GridTrackSizeType → Bool
  | .minContent | .maxContent | .auto | .fitContent _ | .flex _ => true
  | _ => false

/-- Law: An empty range list has no coverage indices.
    CSS Grid Layout Level 1 §7.6. -/
theorem coverage_indices_empty (s c : Nat) :
    coverageRangeIndices [] s c = none := by
  rfl

/-- Law: Fixed track size is neither flexible nor intrinsic.
    CSS Grid Layout Level 1 §11.4. -/
theorem fixed_track_not_flexible (px : Nat) :
    isFlexibleTrack (.fixed px) = false ∧ isIntrinsicTrack (.fixed px) = false := by
  exact ⟨rfl, rfl⟩

/-- Law: Flex track size is always flexible.
    CSS Grid Layout Level 1 §11.4. -/
theorem flex_track_is_flexible (fr : Nat) :
    isFlexibleTrack (.flex fr) = true := by
  rfl

/-- Law: Min-content track size is intrinsic.
    CSS Grid Layout Level 1 §11.4. -/
theorem min_content_is_intrinsic :
    isIntrinsicTrack .minContent = true := by
  rfl

end GridLayout
end ChromiumLayout
