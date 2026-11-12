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

/-- Grid ranges from `(trackSize, repeatCount)` repeaters with no auto-fit repeater
    (`GridRangeBuilder`): `buildGridRangesAuto` with zero auto repetitions and no auto-fit repeater. -/
def buildGridRanges (repeaters : List (Nat × Nat)) : List GridRange :=
  (buildGridRangesAuto 0 (repeaters.map fun p => ({ tracks := p.1, reps := p.2 } : RepeaterSpec))).map (·.1)

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

/-! ### Intrinsic track sizing

Resolution of intrinsic track sizes for one axis, as the grid track sizing algorithm applies it
(shared with grid-lanes lanes): items are processed in groups of equal span size (CSS Grid 2
`#algo-spanning-items`), each group in five contribution steps. An item's extra space is shared
among the sets it spans (`#extra-space`); the planned increases of a step are applied once the
group is done. Then free space is maximized (`#algo-grow-tracks`) and auto tracks are stretched
(`#algo-stretch`). Sizes are whole pixels; the remainder of a division is dropped. Percentage,
flexible and fit-content tracks are not modelled: `trackBounds` returns `none` for them. Item
min-content and max-content contributions are inputs supplied by the test. -/

/-- Sizing function of one side (minimum or maximum) of a normalized track. -/
inductive IntrinsicSz where
  | fixed (px : Nat)
  | auto
  | minContent
  | maxContent
  deriving DecidableEq, Repr

/-- Converts a normalized track side; `none` for percentage, flexible and fit-content lengths. -/
def toIntrinsic : TrackSz → Option IntrinsicSz
  | .fixed px => some (.fixed px)
  | .auto => some .auto
  | .minContent => some .minContent
  | .maxContent => some .maxContent
  | _ => none

/-- Normalized (minimum, maximum) of a track definition in a definite container. -/
def trackBounds (t : TrackDef) : Option (IntrinsicSz × IntrinsicSz) :=
  let p := normalizeTrack true t
  match toIntrinsic p.1, toIntrinsic p.2 with
  | some lo, some hi => some (lo, hi)
  | _, _ => none

/-- A grid item: the first track it spans, its span, and its min-content and max-content
    contributions in pixels. -/
structure IntrinsicItem where
  start : Nat
  span : Nat
  minContent : Nat
  maxContent : Nat

/-- A track set during resolution: its sizing functions, base size, growth limit (`none` is
    infinite), whether its growth limit became finite in the last intrinsic maximum step and is
    therefore infinitely growable for the next step, and the planned increase of the current step
    (`none` when the step did not accommodate an item). -/
structure IntrinsicSet where
  lo : IntrinsicSz
  hi : IntrinsicSz
  base : Nat
  growth : Option Nat
  infGrowable : Bool
  planned : Option Nat

/-- The contribution steps of one span-size group, in the order they are applied. -/
inductive IntrinsicStep where
  | intrinsicMin
  | contentMin
  | maxContentMin
  | intrinsicMax
  | maxContentMax

/-- Minimum steps grow base sizes; maximum steps grow growth limits. -/
def IntrinsicStep.isMin : IntrinsicStep → Bool
  | .intrinsicMin | .contentMin | .maxContentMin => true
  | .intrinsicMax | .maxContentMax => false

/-- Intrinsic (min-content, max-content or auto) sizing function. -/
def isIntrinsic : IntrinsicSz → Bool
  | .fixed _ => false
  | _ => true

/-- Min-content or max-content minimum. -/
def hasContentMin : IntrinsicSz → Bool
  | .minContent | .maxContent => true
  | _ => false

/-- Max-content minimum. -/
def hasMaxContentMin : IntrinsicSz → Bool
  | .maxContent => true
  | _ => false

/-- Max-content or auto maximum. -/
def hasMaxContentOrAutoMax : IntrinsicSz → Bool
  | .maxContent | .auto => true
  | _ => false

/-- Whether a set takes part in a step (it accommodates the item). -/
def stepApplies : IntrinsicStep → IntrinsicSet → Bool
  | .intrinsicMin, s => isIntrinsic s.lo
  | .contentMin, s => hasContentMin s.lo
  | .maxContentMin, s => hasMaxContentMin s.lo
  | .intrinsicMax, s => isIntrinsic s.hi
  | .maxContentMax, s => hasMaxContentOrAutoMax s.hi

/-- Whether a step may grow a set beyond its limit once the within-limit share is used up. -/
def stepGrowsBeyond : IntrinsicStep → IntrinsicSet → Bool
  | .intrinsicMin, s => isIntrinsic s.hi
  | .contentMin, s => isIntrinsic s.hi
  | .maxContentMin, s => hasMaxContentOrAutoMax s.hi
  | _, _ => false

/-- Contribution of an item to a step: max-content for the max-content steps, else min-content. -/
def stepContribution : IntrinsicStep → IntrinsicItem → Nat
  | .maxContentMin, it => it.maxContent
  | .maxContentMax, it => it.maxContent
  | _, it => it.minContent

/-- Size a step increases: the base size for minimum steps, the definite growth limit for maximum
    steps. -/
def stepAffected (st : IntrinsicStep) (s : IntrinsicSet) : Nat :=
  if st.isMin then s.base else s.growth.getD s.base

/-- Growth potential of a set in a step; `none` is infinite. For minimum steps this is the growth
    limit minus the base; for maximum steps it is infinite when the growth limit is infinite or
    infinitely growable, and zero otherwise. -/
def stepPotential (st : IntrinsicStep) (s : IntrinsicSet) : Option Nat :=
  if st.isMin then s.growth.map (· - s.base)
  else match s.growth with
    | none => none
    | some _ => if s.infGrowable then none else some 0

/-- Ascending order of growth potentials, infinite last. -/
def potLe : Option Nat → Option Nat → Bool
  | none, none => true
  | none, some _ => false
  | some _, none => true
  | some a, some b => Nat.ble a b

/-- Insertion of a (track, potential) pair into a list sorted by potential. -/
def insertByPot (x : Nat × Option Nat) : List (Nat × Option Nat) → List (Nat × Option Nat)
  | [] => [x]
  | y :: ys => if potLe x.2 y.2 then x :: y :: ys else y :: insertByPot x ys

/-- Sorts (track, potential) pairs by potential. -/
def sortByPot : List (Nat × Option Nat) → List (Nat × Option Nat)
  | [] => []
  | x :: xs => insertByPot x (sortByPot xs)

/-- Equal distribution of `rem` pixels over sets in ascending potential order: each set takes the
    smaller of its potential and an equal share of the space still left (CSS Grid 2
    `#extra-space`). -/
def fillSorted : Nat → List (Nat × Option Nat) → List (Nat × Nat)
  | _, [] => []
  | rem, (i, p) :: rest =>
    let share := rem / (rest.length + 1)
    let give := match p with
      | none => share
      | some q => Nat.min q share
    (i, give) :: fillSorted (rem - give) rest

/-- Placeholder for an index outside the track list; it takes part in no step. -/
def dummySet : IntrinsicSet := ⟨.auto, .auto, 0, none, false, none⟩

/-- Shares of one item's extra space among the sets it spans in a step, as (track, increase)
    pairs. The shares are computed against the sets before the step. An item with no extra space,
    or no set taking part, produces no pairs. Space left after the within-limit shares goes equally
    to the sets allowed to grow beyond their limits (all taking-part sets when there are none). -/
def itemShares (st : IntrinsicStep) (sets : List IntrinsicSet) (it : IntrinsicItem) :
    List (Nat × Nat) :=
  let idxs := (List.range it.span).map (fun k => it.start + k)
  let getS := fun (i : Nat) => sets.getD i dummySet
  let spanned := idxs.foldl (fun acc i => acc + stepAffected st (getS i)) 0
  let extra := stepContribution st it - spanned
  let applied := idxs.filter (fun i => stepApplies st (getS i))
  if extra == 0 || applied.isEmpty then []
  else
    let within := fillSorted extra (sortByPot (applied.map (fun i => (i, stepPotential st (getS i)))))
    let leftover := extra - (within.map (·.2)).foldl (· + ·) 0
    let beyond := match applied.filter (fun i => stepGrowsBeyond st (getS i)) with
      | [] => applied
      | b => b
    let beyondShare := leftover / beyond.length
    applied.map (fun i =>
      (i, (within.lookup i).getD 0 + (if beyond.contains i then beyondShare else 0)))

/-- Grows a set by its planned increase: a base size for minimum steps; for maximum steps, the
    growth limit becomes the definite growth limit plus the increase, and the set is infinitely
    growable when its growth limit was infinite. -/
def growSet (st : IntrinsicStep) (s : IntrinsicSet) (p : Nat) : IntrinsicSet :=
  if st.isMin then { s with base := s.base + p, infGrowable := false, planned := none }
  else { s with infGrowable := s.growth.isNone,
                growth := some (s.growth.getD s.base + p), planned := none }

/-- One contribution step over a group of items. The shares of all items are computed against the
    sets as they were before the step; each set's planned increase is the largest share it
    received, and the planned increases are applied after the whole group. -/
def groupStep (st : IntrinsicStep) (items : List IntrinsicItem) (sets : List IntrinsicSet) :
    List IntrinsicSet :=
  let ups := items.flatMap (itemShares st sets)
  (List.range sets.length).map (fun i =>
    let s := sets.getD i dummySet
    match (ups.filter (fun u => u.1 == i)).map (·.2) with
    | [] => s
    | v :: vs => growSet st s (vs.foldl max v))

/-- Resolves the items of one span size: the five steps, in order. -/
def resolveSpan (items : List IntrinsicItem) (sets : List IntrinsicSet) (span : Nat) :
    List IntrinsicSet :=
  let group := items.filter (fun it => it.span == span)
  [IntrinsicStep.intrinsicMin, .contentMin, .maxContentMin, .intrinsicMax, .maxContentMax].foldl
    (fun acc st => groupStep st group acc) sets

/-- Resolves intrinsic track sizes for span sizes `1 .. maxSpan`, in increasing span order. -/
def resolveIntrinsic (items : List IntrinsicItem) (maxSpan : Nat) (sets : List IntrinsicSet) :
    List IntrinsicSet :=
  (List.range maxSpan).foldl (fun acc k => resolveSpan items acc (k + 1)) sets

/-- Initial set of a track: base size from a fixed minimum (else zero), growth limit from a fixed
    maximum (else infinite). -/
def initSet (lo hi : IntrinsicSz) : IntrinsicSet :=
  { lo := lo, hi := hi,
    base := (match lo with | .fixed px => px | _ => 0),
    growth := (match hi with | .fixed px => some px | _ => none),
    infGrowable := false, planned := none }

/-- Sum of the base sizes. -/
def sumBase (sets : List IntrinsicSet) : Nat :=
  sets.foldl (fun acc s => acc + s.base) 0

/-- Maximize tracks (CSS Grid 2 `#algo-grow-tracks`): infinite growth limits become base sizes,
    then the free space left in the container is shared equally up to the growth limits. -/
def maximizeSets (container : Nat) (sets0 : List IntrinsicSet) : List IntrinsicSet :=
  let sets := sets0.map (fun s => { s with growth := some (s.growth.getD s.base) })
  let free := container - sumBase sets
  let pots := (List.range sets.length).map (fun i =>
    let s := sets.getD i dummySet
    (i, some (s.growth.getD s.base - s.base)))
  let shares := fillSorted free (sortByPot pots)
  (List.range sets.length).map (fun i =>
    let s := sets.getD i dummySet
    { s with base := s.base + (shares.lookup i).getD 0 })

/-- Stretch auto tracks (CSS Grid 2 `#algo-stretch`): the free space left after the base sizes is
    shared equally among the tracks whose maximum is `auto`. -/
def stretchSets (container : Nat) (sets : List IntrinsicSet) : List Nat :=
  let free := container - sumBase sets
  let autos := (sets.filter (fun s => s.hi == IntrinsicSz.auto)).length
  let share := if autos == 0 then 0 else free / autos
  sets.map (fun s => if s.hi == IntrinsicSz.auto then s.base + share else s.base)

/-- Intrinsic track sizes of one axis: the base sizes after resolution, maximization and
    stretching. `none` when a track is percentage, flexible or fit-content sized. -/
def intrinsicTrackSizes (container : Nat) (tracks : List TrackDef) (items : List IntrinsicItem) :
    Option (List Nat) := do
  let bounds ← tracks.mapM trackBounds
  let sets := bounds.map (fun b => initSet b.1 b.2)
  let resolved := resolveIntrinsic items tracks.length sets
  return stretchSets container (maximizeSets container resolved)

end GridLayout
end ChromiumLayout
