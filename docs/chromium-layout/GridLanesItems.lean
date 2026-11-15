/-
  GridLanesItems.lean: Grid-lanes item span resolution, item group collection (with
  major/minor baseline groups), implicit/explicit track range splitting, fit-tolerance
  (`GetFirstEligibleLine`) auto-placement, and `fill-reverse` / `track-reverse` placement.
  Spec: CSS Grid Layout Module Level 1 §7.2–§8.3, CSS Box Alignment Module Level 3 §4.1 & §9,
  and CSS Grid Layout Module Level 3 (Grid Lanes / Masonry layout).
-/

namespace ChromiumLayout
namespace GridLanesItems

/-- 1-based CSS grid line placement specification in the grid-lanes axis.
    CSS Grid 1 §8.3. -/
inductive SpanSpec where
  | auto (span : Nat)
  | startSpan (start1 span : Nat)
  | startEnd (start1 end1 : Nat)
  | endSpan (end1 span : Nat)
  deriving DecidableEq, Repr

/-- Resolve a `SpanSpec` to `(definiteZeroBasedSpan, spanLen, isAutoPlaced)`.
    Required by `ConstructGridLanesItems`, `GridLanesAutoPlacedItems`,
    `CollectGridLanesItemGroups`. -/
def resolveSpan (s : SpanSpec) : Option (Nat × Nat) × Nat × Bool :=
  match s with
  | .auto n => (none, n, true)
  | .startSpan st n => (some (st - 1, st - 1 + n), n, false)
  | .startEnd st en => (some (st - 1, en - 1), en - st, false)
  | .endSpan en n => (some (en - 1 - n, en - 1), n, false)

/-- Group `grid-lanes` items `(spanSpec, optIsFirstBaseline)` by their resolved span and
    baseline group (`none` = non-baseline, `some true` = major/first baseline,
    `some false` = minor/last baseline), returning `(definiteSpan, spanLen, baselineGroup, itemCount)`
    in order of first appearance. CSS Grid 3, CSS Box Alignment 3 §9.
    Required by `CollectGridLanesItemGroups`, `CollectGridLanesItemGroupsWithBaseline`. -/
def collectItemGroups (items : List (SpanSpec × Option Bool)) :
    List (Option (Nat × Nat) × Nat × Option Bool × Nat) :=
  items.foldl (fun acc (sp, bl) =>
    let (defSpan, len, _) := resolveSpan sp
    if acc.any (fun (d, l, b, _) => d == defSpan && l == len && b == bl) then
      acc.map (fun (d, l, b, c) =>
        if d == defSpan && l == len && b == bl then (d, l, b, c + 1) else (d, l, b, c))
    else
      acc ++ [(defSpan, len, bl, 1)]) []

/-- Build track ranges `(startLine, trackCount)` from `preImplicit` tracks before explicit
    line 1, explicit template segment track counts `templateCounts`, an interior split at
    0-based line `splitLine`, and an implicit extension ending at 0-based line `postEnd`.
    CSS Grid 1 §7.2, §7.5.
    Required by `BuildRanges`. -/
def buildTrackRanges (preImplicit : Nat) (templateCounts : List Nat)
    (splitLine postEnd : Nat) : List (Nat × Nat) :=
  let init : List (Nat × Nat) := if preImplicit > 0 then [(0, preImplicit)] else []
  let (explicitRanges, endExplicit) := templateCounts.foldl (fun (acc, cur) cnt =>
    let next := cur + cnt
    if cur < splitLine && splitLine < next then
      (acc ++ [(cur, splitLine - cur), (splitLine, next - splitLine)], next)
    else
      (acc ++ [(cur, cnt)], next)) (init, preImplicit)
  if postEnd > endExplicit then
    explicitRanges ++ [(endExplicit, postEnd - endExplicit)]
  else
    explicitRanges

/-- Maximum running position across `spanSize` consecutive tracks starting at `startTrack`. -/
def windowMax (pos : List Nat) (startTrack spanSize : Nat) : Nat :=
  ((pos.drop startTrack).take spanSize).foldl max 0

/-- Find the first eligible track span `((startLine, endLine), maxPos)` of width `spanSize`
    starting at or after `cursor` (wrapping around to `0` if none is eligible at or after
    `cursor`) within `tieThreshold` of the global minimum window position.
    CSS Grid 3 (`item-tolerance` / `fit-tolerance`).
    Required by `GetFirstEligibleLine`. -/
def firstEligibleLine (pos : List Nat) (tieThreshold spanSize cursor : Nat) :
    (Nat × Nat) × Nat :=
  let count := pos.length + 1 - spanSize
  let windows := (List.range count).map fun i => (i, windowMax pos i spanSize)
  let minPos := windows.foldl (fun m (_, w) => min m w) (windowMax pos 0 spanSize)
  let eligible := windows.filter fun (_, w) => w ≤ minPos + tieThreshold
  let chosen := match eligible.find? (fun (i, _) => i ≥ cursor) with
    | some p => p
    | none => eligible.headD (0, 0)
  ((chosen.1, chosen.1 + spanSize), chosen.2)

/-- Compute the `(inlineOffset, blockOffset)` of an item under `fill-reverse` in a container
    with track size `trackSz` and effective stacking-axis size `containerStackSz`.
    Reflected items stack from `containerStackSz - stackStart - itemSz`; items with default
    `start` alignment (`isAlignEnd = false`) shift by `-remSpace` toward the start of their
    opening. CSS Grid 3 (`grid-lanes-direction: fill-reverse`).
    Required by `PopulateColumnFillAndTrackReverseBreakTokenData`,
    `PopulateRowFillAndTrackReverseBreakTokenData`,
    `PopulateIndefiniteFillReverseBreakTokenData`. -/
def placeFillReverse (isRow : Bool) (trackSz containerStackSz startTrack spanTracks gridSz : Nat)
    (isGridEnd : Bool) (stackStart itemSz remSpace : Nat) (isAlignEnd : Bool) : Nat × Nat :=
  let areaSz := spanTracks * trackSz
  let gPos := startTrack * trackSz + (if isGridEnd then areaSz - gridSz else 0)
  let sPos := containerStackSz - stackStart - itemSz - (if isAlignEnd then 0 else remSpace)
  if isRow then (sPos, gPos) else (gPos, sPos)

/-- Column `fill-reverse` reverses stored per-lane item order for block fragmentation,
    while row `fill-reverse` acts on the inline axis and preserves per-lane item order.
    Required by `PopulateColumnFillAndTrackReverseBreakTokenData`,
    `PopulateRowFillAndTrackReverseBreakTokenData`,
    `PopulateIndefiniteFillReverseBreakTokenData`. -/
def orderForFillReverse (isRow : Bool) (xs : List α) : List α :=
  if isRow then xs else xs.reverse

/-- Law: a non-subgrid `grid-lanes` item is marked `is_auto_placed` iff its resolved span
    in the grid axis is indefinite (`none`). CSS Grid 3. -/
theorem resolveSpan_autoPlaced_iff (s : SpanSpec) :
    (resolveSpan s).2.2 = (resolveSpan s).1.isNone := by
  cases s <;> rfl

/-- Law: under `fill-reverse`, an `end`-aligned item stays at its reflected position
    `containerStackSz - stackStart - itemSz` regardless of remaining space in the opening. -/
theorem placeFillReverse_end_pos (trackSz containerSz startTrack spanTracks gridSz : Nat)
    (isGridEnd : Bool) (stackStart itemSz rem : Nat) :
    (placeFillReverse false trackSz containerSz startTrack spanTracks gridSz isGridEnd
      stackStart itemSz rem true).2 = containerSz - stackStart - itemSz := by
  simp [placeFillReverse]

end GridLanesItems
end ChromiumLayout
