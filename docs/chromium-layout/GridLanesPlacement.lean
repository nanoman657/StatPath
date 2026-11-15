/-
  GridLanesPlacement.lean: Per-lane item placement, grid-axis and stacking-axis alignment,
  auto-sized stretch opening resolution, content alignment, dense packing into openings
  above spanners, and fragmented break-token data sharing for `display: grid-lanes`.
  Spec: CSS Grid Layout Module Level 3 (Grid Lanes / Masonry layout) and
  CSS Box Alignment Module Level 3 §5 (Self-Alignment) & §6 (Content-Distribution).
-/

namespace ChromiumLayout
namespace GridLanesPlacement

/-- Self-alignment or content-distribution keyword. CSS Box Alignment 3 §5–§6. -/
inductive Align where
  | start
  | center
  | end
  | stretch
  deriving DecidableEq, Repr

/-- Alignment offset within an available range `avail` for an item of size `sz`.
    CSS Box Alignment 3 §5.
    Required by `PopulateGridAxisAlignedBreakTokenData`,
    `PopulateRowGridAxisAlignedBreakTokenData`,
    `PopulateStackingAxisAlignedBreakTokenData`,
    `PopulateContentAlignedBreakTokenData`. -/
def alignOffset (a : Align) (avail sz : Nat) : Nat :=
  match a with
  | .start | .stretch => 0
  | .center => (avail - sz) / 2
  | .end => avail - sz

/-- Persisted `StretchSizeInStackingAxis` for fragmented layout: `some openingSz` iff
    the item has `stretch` alignment and no explicit size in the stacking axis.
    Required by `PopulateStackingAxisAlignedBreakTokenData`,
    `PopulateExplicitStackingAxisStretchBreakTokenData`,
    `PopulateRowStackingAxisStretchSpaceBreakTokenData`,
    `PopulateStackingAxisStretchSpannerSpaceBreakTokenData`,
    `PopulateLastStackingAxisAlignedBreakTokenData`. -/
def stretchSize (a : Align) (explicitStackSz : Bool) (openingSz : Nat) : Option Nat :=
  if a == .stretch && !explicitStackSz then some openingSz else none

/-- Logical `(inlineOffset, blockOffset)` and `StretchSizeInStackingAxis` for an item
    spanning `[startTrack, startTrack + spanTracks)` in a `grid-lanes` container with
    track size `trackSz`. When `isRow` is false (`column` lanes), the grid axis is inline
    and the stacking axis is block; when `isRow` is true (`row` lanes), the grid axis is
    block and the stacking axis is inline.
    Required by `PopulateGridLanesBreakTokenData`, `PopulateRowGridLanesBreakTokenData`,
    `PopulateGridAxisAlignedBreakTokenData`, `PopulateRowGridAxisAlignedBreakTokenData`,
    `PopulateStackingAxisAlignedBreakTokenData`,
    `PopulateRowStackingAxisAlignedBreakTokenData`,
    `PopulateExplicitStackingAxisStretchBreakTokenData`,
    `PopulateRowExplicitStackingAxisStretchBreakTokenData`,
    `PopulateRowStackingAxisStretchSpaceBreakTokenData`,
    `PopulateStackingAxisStretchSpannerSpaceBreakTokenData`,
    `PopulateRowStackingAxisStretchSpannerSpaceBreakTokenData`,
    `PopulateLastStackingAxisAlignedBreakTokenData`,
    `PopulateRowLastStackingAxisAlignedBreakTokenData`,
    `PopulateStackingAxisAlignedSpannerBreakTokenData`,
    `PopulateRowStackingAxisAlignedSpannerBreakTokenData`,
    `PopulateContentAlignedBreakTokenData`,
    `PopulateRowContentAlignedBreakTokenData`. -/
def placeAligned (isRow : Bool) (trackSz startTrack spanTracks gridSz : Nat) (gridAlign : Align)
    (stackStart openingSz stackSz : Nat) (stackAlign : Align) (explicitStackSz : Bool := true)
    (contentShift : Nat := 0) : (Nat × Nat) × Option Nat :=
  let areaSz := spanTracks * trackSz
  let effGridSz := if gridSz == 0 then areaSz else gridSz
  let gPos := startTrack * trackSz + alignOffset gridAlign areaSz effGridSz
  let sPos := stackStart + alignOffset stackAlign openingSz stackSz + contentShift
  let offset := if isRow then (sPos, gPos) else (gPos, sPos)
  (offset, stretchSize stackAlign explicitStackSz openingSz)

/-- Stacking-axis shift from `align-content` / `justify-content` on a `grid-lanes`
    container of size `containerSz` with total content extent `contentSz`.
    Required by `PopulateContentAlignedBreakTokenData`,
    `PopulateRowContentAlignedBreakTokenData`. -/
def contentShift (a : Align) (containerSz contentSz : Nat) : Nat :=
  alignOffset a containerSz contentSz

/-- Whether a lane entry at `lane` for an item spanning `[startTrack, startTrack + span)`
    is marked `is_item_start` (true only for the first spanned lane).
    Required by `PopulateGridLanesBreakTokenData`, `PopulateDensePackedBreakTokenData`,
    `PopulateDensePackedSpannerBreakTokenData`,
    `PopulateDenseSpannerWithDifferentParentsPerLane`. -/
def isItemStart (startTrack lane : Nat) : Bool :=
  lane == startTrack

/-- Place a dense-packed item (or spanner) of size `stackSz` and alignment `stackAlign`
    into an opening `[openStart, openEnd)` starting at `startTrack` in a column `grid-lanes`
    container with track width `trackSz`, returning `(inlineOffset, blockOffset, isStartFirst, isStartCont)`.
    Required by `PopulateDensePackedBreakTokenData`,
    `PopulateDensePackedSpannerBreakTokenData`,
    `PopulateDenseSpannerWithDifferentParentsPerLane`,
    `PopulateDenseItemAboveDenseSpannerUsesParentSpanner`. -/
def placeDenseInOpening (trackSz startTrack openStart openEnd stackSz : Nat)
    (stackAlign : Align := .start) : (Nat × Nat) × Bool × Bool :=
  let (off, _) := placeAligned false trackSz startTrack 1 0 .start
    openStart (openEnd - openStart) stackSz stackAlign true 0
  (off, isItemStart startTrack startTrack, isItemStart startTrack (startTrack + 1))

/-- Count direct `item_data` entries per lane for a list of `(startTrack, spanTracks, isPackedBelowSpannerPerLane)`
    items across `numTracks` lanes. An item adds a direct entry in lane `l` iff `l` is in
    `[startTrack, startTrack + spanTracks)` and is not nested under a parent spanner in `l`. -/
def directLaneCounts (numTracks : Nat)
    (items : List (Nat × Nat × List Bool)) : List Nat :=
  (List.range numTracks).map fun l =>
    items.countP fun (s, span, nestedFlags) =>
      s ≤ l && l < s + span && !(nestedFlags.getD (l - s) false)

/-- Fragmentation break-token state across two fragments of height `fragH` when a spanner
    of block size `spannerH` and bottom margin `marginEnd` is followed in a lane by an
    item of height `nextItemH`: returns `(totalBlockSize, marginBlockEnd, unfinishedFrag0, unfinishedFrag1)`.
    Required by `SharePlacementDataAcrossFragments`. -/
def sharePlacementAcrossFragments (fragH spannerH marginEnd nextItemH : Nat) :
    Nat × Nat × Bool × Bool :=
  let endPos := spannerH + marginEnd + nextItemH
  (spannerH, marginEnd, endPos > fragH, endPos > 2 * fragH)

/-- Fragmentation spanner expansion state across two fragments when a spanner initially
    estimated at `estH` fragments into two parts `part1` and `part2`: returns
    `(totalBlockSize, adjustFrag0, adjustFrag1)`.
    Required by `ShareExpansionDataAcrossFragments`. -/
def shareExpansionAcrossFragments (estH part1 part2 : Nat) : Nat × Nat × Nat :=
  let total := part1 + part2
  (total, 0, total - estH)

/-- Law: for any alignment mode, an item of size `sz ≤ avail` has `alignOffset a avail sz + sz ≤ avail`
    (CSS Box Alignment 3 §5). -/
theorem alignOffset_le_avail (a : Align) (avail sz : Nat) (h : sz ≤ avail) :
    alignOffset a avail sz + sz ≤ avail := by
  cases a <;> simp [alignOffset] <;> omega

/-- Law: an explicitly sized item never persists a `StretchSizeInStackingAxis`, even when
    its alignment is `stretch` (CSS Grid 3). -/
theorem stretchSize_none_of_explicit (a : Align) (openingSz : Nat) :
    stretchSize a true openingSz = none := by
  simp [stretchSize]

end GridLanesPlacement
end ChromiumLayout
