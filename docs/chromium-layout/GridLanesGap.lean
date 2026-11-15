import GridLayout
/-
  GridLanesGap.lean: gap decoration geometry of a grid-lanes container along its grid axis,
  written from grid_lanes/grid_lanes_layout_algorithm_test.cc (GapGeometry* tests).
  Spec: CSS Gap Decorations 1 §3.2 (gap rules sit at the midpoint of each gap between tracks);
  gap decorations exist only if a gap rule is set and there are at least two tracks
  (CSS Gap Decorations 1 §3.1). Reuses `GridLayout.computeGridGapMidpoints`.
-/
namespace ChromiumLayout
namespace GridLanesGap
open GridLayout

/-- Grid-axis gaps of a grid-lanes container: midpoint offsets in the border box (border added),
    content start and content end along the grid axis. `none` without a rule or with fewer than
    two tracks. -/
def gridAxisGaps (border gap : Nat) (hasRule : Bool) (tracks : List Nat) :
    Option (List Nat × Nat × Nat) :=
  if hasRule && 2 ≤ tracks.length then
    some ((computeGridGapMidpoints gap tracks).map (border + ·), border, border + gridTotalSpan gap tracks)
  else none

/-- Start offset of the track grid along the grid axis under `justify-content`/`align-content: center`
    (CSS Box Alignment 3 §5.3): `border + (size - 2 * border - gridTotalSpan gap tracks) / 2`. -/
def centerStart (border size gap : Nat) (tracks : List Nat) : Nat :=
  border + (size - 2 * border - gridTotalSpan gap tracks) / 2

/-- Along the stacking axis the content extent spans from `border` to the maximum of the content-box
    end (`size - border`) and any overflowing lane content (`border + contentSpan`).
    CSS Gap Decorations 1 §3.3. -/
def stackContent (border size : Nat) (contentSpan : Nat := 0) : Nat × Nat :=
  (border, max (size - border) (border + contentSpan))

/-- Law: no gap rule means no gap geometry (`GapGeometryRequiresGapRule`). -/
theorem gridAxisGaps_no_rule (b g : Nat) (ts : List Nat) : gridAxisGaps b g false ts = none := by
  simp [gridAxisGaps]

/-- Law: fewer than two tracks means no gap geometry (`GapGeometrySingleTrack`). -/
theorem gridAxisGaps_single (b g : Nat) (r : Bool) (t : Nat) : gridAxisGaps b g r [t] = none := by
  simp [gridAxisGaps]

/-- Law: stacking-axis content end is at least the content-box end (`size - border`), and extends
    further when lane items overflow (CSS Gap Decorations 1 §3.3). -/
theorem stackContent_ge_box (b sz span : Nat) : sz - b ≤ (stackContent b sz span).2 :=
  Nat.le_max_left (sz - b) (b + span)

end GridLanesGap
end ChromiumLayout
