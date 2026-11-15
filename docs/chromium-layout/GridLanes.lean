import GridTrackSizing
/-
  GridLanes.lean: grid-lanes (masonry) auto-repeat expansion and auto-fit collapsing along the
  grid axis, written from grid_lanes/grid_lanes_layout_algorithm_test.cc (ColumnAutoFit*/RowAutoFit*).
  Spec: CSS Grid Layout 1 §7.2.3.2 (auto-fill and auto-fit repetitions; floor track size to 1px to
  avoid division by zero; auto-fit collapses empty tracks) and CSS Grid Layout 3 §repeat-auto-fit,
  §masonry-intrinsic-repeat (auto-placed virtual items are only added to auto-fit tracks up to the
  total span count of auto-placed items; intrinsic auto-repeats use the item contribution from a
  first sizing pass). The grid axis is columns for `grid-lanes-direction: column` and rows for `row`.
-/
namespace ChromiumLayout
namespace GridLanes
open GridTrackSizing

/-- One template segment: `n` fixed tracks of `size`, or an `auto-fit` repeat of fixed `size` or
    `auto` (with item contribution `size` from the first sizing pass). CSS Grid 1 §7.2.3.2,
    CSS Grid 3 §masonry-intrinsic-repeat. -/
inductive Rep where
  | fixed (n size : Nat)
  | autoFit (size : Nat)
  | autoFitAuto (size : Nat)

/-- Expanded tracks as `(sizingFn, itemContribution, isAutoFit)`. Auto-fit repeats as often as fits
    in the space left by fixed tracks (flooring track size to at least 1px, at least 1 repetition).
    CSS Grid 1 §7.2.3.2. -/
def expand (W : Nat) (reps : List Rep) : List (Sz × Nat × Bool) :=
  let fixedTotal := (reps.map fun | .fixed n s => n * s | _ => 0).sum
  let repCount (s : Nat) := max 1 ((W - fixedTotal) / max 1 s)
  reps.flatMap fun
    | .fixed n s => List.replicate n (.px s, s, false)
    | .autoFit s => List.replicate (repCount s) (.px s, s, true)
    | .autoFitAuto s => List.replicate (repCount s) (.auto, s, true)

/-- Track sizes after auto-fit collapsing (CSS Grid 1 §7.2.3.2, CSS Grid 3 §repeat-auto-fit):
    an auto-fit track at 0-based index `i` is kept iff `i` is less than the number of auto-placed
    items (`none`) or an item is explicitly placed at 1-based line `i + 1` (`some (i + 1)`). -/
def laneSizes (W : Nat) (reps : List Rep) (items : List (Option Nat)) : List Nat :=
  let autoCount := items.countP Option.isNone
  let kept := (expand W reps).zipIdx.filterMap fun (t, i) =>
    if !t.2.2 || i < autoCount || items.contains (some (i + 1)) then some (t.1, t.2.1) else none
  sizes W (kept.map fun (sz, _) => ⟨sz, sz, 1⟩)
    (kept.zipIdx.map fun ((_, c), j) => { s := j, e := j + 1, minC := c, maxC := c })

/-- Law: a fixed repeater `repeat(n, s)` always expands to `n` tracks (CSS Grid 1 §7.2.3). -/
theorem expand_fixed_length (W n s : Nat) : (expand W [.fixed n s]).length = n := by
  simp [expand]

end GridLanes
end ChromiumLayout
