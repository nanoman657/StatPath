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

/-- A repeater descriptor with track count, collapsed, and property flags.
    CSS Grid Layout Level 1 §7.2.3. -/
structure TrackRepeater where
  trackCount : Nat
  isCollapsed : Bool := false
  hasFlexible : Bool := false
  hasIntrinsic : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- Build base track ranges from track repeaters.
    CSS Grid Layout Level 1 §7.2.3. -/
def buildTrackRanges (repeaters : List TrackRepeater) : List TrackRange :=
  let rec loop (curLine : Nat) (rem : List TrackRepeater) : List TrackRange :=
    match rem with
    | [] => []
    | rep :: rest =>
        ⟨curLine, rep.trackCount, rep.isCollapsed, false, rep.hasFlexible, rep.hasIntrinsic⟩ ::
          loop (curLine + rep.trackCount) rest
  loop 0 repeaters

/-- Build track ranges from set counts with running sum start lines.
    CSS Grid Layout Level 1 §7.2.3. -/
def buildTrackRangesFromSetCounts (setCounts : List Nat) : List TrackRange :=
  let rec loop (curLine : Nat) (rem : List Nat) : List TrackRange :=
    match rem with
    | [] => []
    | count :: rest =>
        ⟨curLine, count, false, false, false, false⟩ :: loop (curLine + count) rest
  loop 0 setCounts

/-- Split a track range at a line boundary if the line falls strictly within the range.
    CSS Grid Layout Level 1 §7.2.3, §7.6. -/
def splitRangeAt (line : Nat) (r : TrackRange) : List TrackRange :=
  let rEnd := r.startLine + r.trackCount
  if line > r.startLine && line < rEnd then
    [ { r with trackCount := line - r.startLine },
      { r with startLine := line, trackCount := rEnd - line } ]
  else
    [r]

/-- Split track ranges at a line boundary. CSS Grid Layout Level 1 §7.6. -/
def splitRangesAt (line : Nat) (ranges : List TrackRange) : List TrackRange :=
  ranges.flatMap (splitRangeAt line)

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

/-- Ensure track coverage over [startLine, startLine + count) by splitting ranges at
    coverage boundaries and appending implicit ranges when exceeding explicit bounds.
    Returns (updatedRanges, startRangeIndex, endRangeIndex).
    CSS Grid Layout Level 1 §7.2.3, §7.6. -/
def ensureTrackCoverage (ranges : List TrackRange) (startLine count : Nat)
    (isImplicitFlex : Bool := false) (isImplicitIntrinsic : Bool := false) : List TrackRange × Nat × Nat :=
  let endLine := startLine + count
  let split1 := splitRangesAt startLine ranges
  let split2 := splitRangesAt endLine split1
  let lastEnd := match split2.getLast? with
    | some r => r.startLine + r.trackCount
    | none => 0
  let uncollapsed := split2.map (fun r =>
    let rEnd := r.startLine + r.trackCount
    if r.startLine < endLine && rEnd > startLine then
      { r with isCollapsed := false }
    else r)
  let finalRanges :=
    if startLine > lastEnd then
      uncollapsed ++ [
        ⟨lastEnd, startLine - lastEnd, false, true, isImplicitFlex, isImplicitIntrinsic⟩,
        ⟨startLine, count, false, true, isImplicitFlex, isImplicitIntrinsic⟩
      ]
    else if endLine > lastEnd then
      uncollapsed ++ [⟨lastEnd, endLine - lastEnd, false, true, isImplicitFlex, isImplicitIntrinsic⟩]
    else
      uncollapsed
  let (sIdx, eIdx) := match coverageRangeIndices finalRanges startLine count with
    | some p => p
    | none => (0, 0)
  (finalRanges, sIdx, eIdx)

/-- Whether a track size is flexible (fr unit). CSS Grid Layout Level 1 §11.4. -/
def isFlexibleTrack : GridTrackSizeType → Bool
  | .flex _ => true
  | _ => false

/-- Whether a track size is intrinsic (min-content, max-content, auto, fit-content, flex).
    CSS Grid Layout Level 1 §11.4. -/
def isIntrinsicTrack : GridTrackSizeType → Bool
  | .minContent | .maxContent | .auto | .fitContent _ | .flex _ => true
  | _ => false

/-- Law: Empty track repeaters produce no track ranges.
    CSS Grid Layout Level 1 §7.2.3. -/
theorem build_track_ranges_empty :
    buildTrackRanges [] = [] := by
  rfl

/-- Law: Empty set counts produce no track ranges.
    CSS Grid Layout Level 1 §7.2.3. -/
theorem build_set_counts_empty :
    buildTrackRangesFromSetCounts [] = [] := by
  rfl

/-- Law: Splitting an empty range list at any line yields empty ranges.
    CSS Grid Layout Level 1 §7.6. -/
theorem split_ranges_empty (line : Nat) :
    splitRangesAt line [] = [] := by
  rfl

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

/-! ## Grid Gap Geometry (CSS Gap Decorations Level 1 §3.2, §3.3, CSS Box Alignment 3 §8) -/

/-- Compute the midpoints of the gaps between consecutive tracks.
    CSS Gap Decorations Level 1 §3.2, CSS Box Alignment 3 §8. -/
def computeGridGapMidpoints (gap : Nat) (tracks : List Nat) : List Nat :=
  let rec loop (offset : Nat) (rem : List Nat) : List Nat :=
    match rem with
    | [] | [_] => []
    | t1 :: t2 :: rest =>
        (offset + t1 + gap / 2) :: loop (offset + t1 + gap) (t2 :: rest)
  loop 0 tracks

/-- Total size spanning all tracks and intervening gaps.
    CSS Grid Layout Level 1 §10.1, CSS Box Alignment 3 §8. -/
def gridTotalSpan (gap : Nat) (tracks : List Nat) : Nat :=
  match tracks with
  | [] => 0
  | _ => tracks.foldl (·+·) 0 + (tracks.length - 1) * gap

/-- Grid gap geometry structure holding gap dimensions, midpoints, and content bounds.
    CSS Gap Decorations Level 1 §3.2, §3.3, CSS Box Alignment 3 §8. -/
structure GridGapGeometry where
  inlineGap : Nat
  blockGap : Nat
  mainGaps : List Nat
  crossGaps : List Nat
  contentInlineStart : Nat := 0
  contentInlineEnd : Nat
  contentBlockStart : Nat := 0
  contentBlockEnd : Nat
  deriving Inhabited, DecidableEq, Repr

/-- Compute the 2D gap geometry for a CSS grid container.
    CSS Gap Decorations Level 1 §3.2, §3.3, CSS Box Alignment 3 §8. -/
def computeGridGapGeometry (colGap rowGap : Nat) (colTracks rowTracks : List Nat) : GridGapGeometry :=
  let mainGaps := computeGridGapMidpoints rowGap rowTracks
  let crossGaps := computeGridGapMidpoints colGap colTracks
  let inlineEnd := gridTotalSpan colGap colTracks
  let blockEnd := gridTotalSpan rowGap rowTracks
  { inlineGap := colGap, blockGap := rowGap,
    mainGaps := mainGaps, crossGaps := crossGaps,
    contentInlineEnd := inlineEnd, contentBlockEnd := blockEnd }

/-! ## Grid Gap Geometry Laws (CSS Gap Decorations Level 1 §3.2, §3.3, CSS Box Alignment 3 §8) -/

/-- Law: Empty track list produces no gap midpoints.
    CSS Gap Decorations Level 1 §3.2. -/
theorem compute_grid_gap_midpoints_empty (gap : Nat) :
    computeGridGapMidpoints gap [] = [] := rfl

/-- Law: Single track produces no gap midpoints.
    CSS Gap Decorations Level 1 §3.2. -/
theorem compute_grid_gap_midpoints_single (gap t : Nat) :
    computeGridGapMidpoints gap [t] = [] := rfl

/-- Law: Empty track list has 0 total span.
    CSS Grid Layout Level 1 §10.1. -/
theorem grid_total_span_empty (gap : Nat) :
    gridTotalSpan gap [] = 0 := rfl

/-- Law: Single track has total span equal to its track size.
    CSS Grid Layout Level 1 §10.1. -/
theorem grid_total_span_single (gap t : Nat) :
    gridTotalSpan gap [t] = t := by
  dsimp [gridTotalSpan]
  omega

/-- Law: Two tracks produce a single gap midpoint at first track size plus half the gap.
    CSS Gap Decorations Level 1 §3.2. -/
theorem compute_grid_gap_midpoints_two (gap t1 t2 : Nat) :
    computeGridGapMidpoints gap [t1, t2] = [t1 + gap / 2] := by
  dsimp [computeGridGapMidpoints, computeGridGapMidpoints.loop]
  rw [Nat.zero_add]

/-! ## Gap Segment State Ranges (CSS Gap Decorations Level 1 §3.2, §3.3) -/

/-- Gap segment state representing whether a gap segment between two tracks is blocked by a spanning item
    or adjacent to empty cells. CSS Gap Decorations Level 1 §3.2, §3.3. -/
inductive GapSegmentStatus where
  | none
  | blocked
  | emptyBefore
  | emptyAfter
  | emptyBoth
  deriving Inhabited, DecidableEq, Repr

/-- Coalesced segment state range [start, end) along a gap. CSS Gap Decorations Level 1 §3.2. -/
structure GapSegmentRange where
  start : Nat
  «end» : Nat
  status : GapSegmentStatus
  deriving Inhabited, DecidableEq, Repr

/-- Compute the gap status between two adjacent cells.
    CSS Gap Decorations Level 1 §3.2, §3.3. -/
def cellPairGapStatus (c1 c2 : Option Nat) : GapSegmentStatus :=
  match c1, c2 with
  | some id1, some id2 => if id1 == id2 then .blocked else .none
  | none, none => .emptyBoth
  | none, some _ => .emptyBefore
  | some _, none => .emptyAfter

/-- Coalesce consecutive track segment statuses into disjoint ranges [start, end). -/
def coalesceGapRanges (statuses : List GapSegmentStatus) : List GapSegmentRange :=
  let rec loop (idx : Nat) (curStatus : GapSegmentStatus) (startIdx : Nat) (rem : List GapSegmentStatus) : List GapSegmentRange :=
    match rem with
    | [] =>
        if curStatus != .none then [⟨startIdx, idx, curStatus⟩] else []
    | st :: rest =>
        if st == curStatus then
          loop (idx + 1) curStatus startIdx rest
        else
          let pfx := if curStatus != .none then [⟨startIdx, idx, curStatus⟩] else []
          pfx ++ loop (idx + 1) st idx rest
  match statuses with
  | [] => []
  | st :: rest => loop 1 st 0 rest

/-- Compute the segment status list along a column gap (cross gap) between colIdx and colIdx + 1. -/
def columnGapStatuses (colIdx : Nat) (grid : List (List (Option Nat))) : List GapSegmentStatus :=
  grid.map (fun row =>
    let c1 := row.getD colIdx none
    let c2 := row.getD (colIdx + 1) none
    cellPairGapStatus c1 c2)

/-- Compute the segment status list along a row gap (main gap) between rowIdx and rowIdx + 1. -/
def rowGapStatuses (rowIdx : Nat) (numCols : Nat) (grid : List (List (Option Nat))) : List GapSegmentStatus :=
  let r1 := grid.getD rowIdx []
  let r2 := grid.getD (rowIdx + 1) []
  (List.range numCols).map (fun c =>
    let c1 := r1.getD c none
    let c2 := r2.getD c none
    cellPairGapStatus c1 c2)

/-- Coalesced ranges along a column gap (cross gap). CSS Gap Decorations Level 1 §3.2. -/
def crossGapRanges (colIdx : Nat) (grid : List (List (Option Nat))) : List GapSegmentRange :=
  coalesceGapRanges (columnGapStatuses colIdx grid)

/-- Coalesced ranges along a row gap (main gap). CSS Gap Decorations Level 1 §3.2. -/
def mainGapRanges (rowIdx : Nat) (numCols : Nat) (grid : List (List (Option Nat))) : List GapSegmentRange :=
  coalesceGapRanges (rowGapStatuses rowIdx numCols grid)

/-! ## Gap Segment State Range Laws (CSS Gap Decorations Level 1 §3.2, §3.3) -/

/-- Law: Adjacent cells occupied by the same item ID are blocked across the intervening gap.
    CSS Gap Decorations Level 1 §3.2. -/
theorem cell_pair_status_same_item (id : Nat) :
    cellPairGapStatus (some id) (some id) = .blocked := by
  dsimp [cellPairGapStatus]
  simp

/-- Law: Two empty adjacent cells produce emptyBoth status.
    CSS Gap Decorations Level 1 §3.2. -/
theorem cell_pair_status_both_none :
    cellPairGapStatus none none = .emptyBoth := rfl

/-- Law: Empty cell before occupied cell produces emptyBefore status.
    CSS Gap Decorations Level 1 §3.2. -/
theorem cell_pair_status_empty_before (id : Nat) :
    cellPairGapStatus none (some id) = .emptyBefore := rfl

/-- Law: Occupied cell before empty cell produces emptyAfter status.
    CSS Gap Decorations Level 1 §3.2. -/
theorem cell_pair_status_empty_after (id : Nat) :
    cellPairGapStatus (some id) none = .emptyAfter := rfl

/-- Law: Empty status list produces no segment ranges.
    CSS Gap Decorations Level 1 §3.2. -/
theorem coalesce_gap_ranges_empty :
    coalesceGapRanges [] = [] := rfl

/-- Law: Single none status produces no segment ranges.
    CSS Gap Decorations Level 1 §3.2. -/
theorem coalesce_gap_ranges_single_none :
    coalesceGapRanges [.none] = [] := rfl

/-- Law: Single blocked status produces a range from 0 to 1.
    CSS Gap Decorations Level 1 §3.2. -/
theorem coalesce_gap_ranges_single_blocked :
    coalesceGapRanges [.blocked] = [⟨0, 1, .blocked⟩] := rfl

/-- Sum of track sizes within a span [startIdx, endIdx) in a track collection.
    CSS Grid Layout Module Level 1 §11.5. -/
def sumTrackSizes (tracks : List Nat) (startIdx endIdx : Nat) : Nat :=
  (tracks.take endIdx).drop startIdx |>.foldl (·+·) 0

/-- Available space for a grid item spanning a range of tracks [startLine, endLine] (1-indexed grid lines)
    separated by gaps of size `gap`.
    CSS Grid Layout Module Level 1 §11.5 (Calculate the Available Grid Space),
    §11.6 (Track Sizing Algorithm). -/
def itemAvailableTrackSize (tracks : List Nat) (gap : Nat) (startLine endLine : Nat) : Nat :=
  if endLine ≤ startLine then 0
  else
    let startIdx := startLine - 1
    let endIdx := endLine - 1
    let span := endIdx - startIdx
    let totalTrack := sumTrackSizes tracks startIdx endIdx
    let totalGap := if span > 1 then (span - 1) * gap else 0
    totalTrack + totalGap

/-- Law: An invalid track span (endLine ≤ startLine) yields 0 available space.
    CSS Grid Layout Module Level 1 §11.5. -/
theorem item_available_size_invalid_span (tracks : List Nat) (gap startLine endLine : Nat)
    (h : endLine ≤ startLine) :
    itemAvailableTrackSize tracks gap startLine endLine = 0 := by
  dsimp [itemAvailableTrackSize]
  split
  · rfl
  · omega

/-- Law: An empty track collection yields 0 sum of track sizes.
    CSS Grid Layout Module Level 1 §11.5. -/
theorem sum_track_sizes_empty (startIdx endIdx : Nat) :
    sumTrackSizes [] startIdx endIdx = 0 := by
  dsimp [sumTrackSizes]
  simp

/-- Law: A grid item spanning a single track receives exactly the size of that track
    with no gap space added.
    CSS Grid Layout Module Level 1 §11.5. -/
theorem item_available_size_single_track (tracks : List Nat) (gap : Nat) (line : Nat) (h : line > 0) :
    itemAvailableTrackSize tracks gap line (line + 1) = sumTrackSizes tracks (line - 1) line := by
  unfold itemAvailableTrackSize
  split
  · omega
  · have hend : line + 1 - 1 = line := by omega
    have hdiff : line - (line - 1) = 1 := by omega
    simp [hend, hdiff]

/-- Law: A grid item spanning two adjacent tracks receives the sum of both track sizes
    plus exactly one gap.
    CSS Grid Layout Module Level 1 §11.5. -/
theorem item_available_size_two_tracks (tracks : List Nat) (gap : Nat) (line : Nat) (h : line > 0) :
    itemAvailableTrackSize tracks gap line (line + 2) = sumTrackSizes tracks (line - 1) (line + 1) + gap := by
  unfold itemAvailableTrackSize
  split
  · omega
  · have hend : line + 2 - 1 = line + 1 := by omega
    have hdiff : line + 1 - (line - 1) = 2 := by omega
    simp [hend, hdiff]

end GridLayout
end ChromiumLayout
