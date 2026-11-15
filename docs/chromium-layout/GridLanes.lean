import GridTrackSizing
/-
  GridLanes.lean: grid-lanes (masonry) lane placement and auto-fit collapsing along the grid axis,
  written from grid_lanes/grid_lanes_layout_algorithm_test.cc (ColumnAutoFit*/RowAutoFit* tests).
  Spec: CSS Grid Layout 1 §7.2.3.2 (auto-fill and auto-fit repetitions; auto-fit collapses empty
  tracks) and CSS Grid Layout 3 (grid-lanes) item placement: an auto-placed item goes to the lane
  with the smallest running position, ties to the earliest lane. The grid axis is columns for
  `grid-lanes-direction: column` and rows for `row`; both are the same model with the axes swapped.
  Not modelled: the tie threshold, spanning items, gaps, `auto`-sized repeat() tracks.
-/
namespace ChromiumLayout
namespace GridLanes
open GridTrackSizing

/-- One template segment: `n` fixed tracks of `size`, or an auto-fit repeat of `size`. -/
inductive Rep where
  | fixed (n size : Nat)
  | autoFit (size : Nat)

/-- Expanded tracks as (size, collapsible). Auto-fit repeats as often as fits in the space left by
    the other tracks, at least once. CSS Grid 1 §7.2.3.2. -/
def expand (W : Nat) (reps : List Rep) : List (Nat × Bool) :=
  let fixedTotal := (reps.map fun | .fixed n s => n * s | .autoFit _ => 0).sum
  reps.flatMap fun
    | .fixed n s => List.replicate n (s, false)
    | .autoFit s => List.replicate (max 1 ((W - fixedTotal) / s)) (s, true)

/-- Index of the first smallest running position. -/
def minPos : List Nat → Nat
  | [] => 0
  | [_] => 0
  | p :: ps => let j := minPos ps; if p ≤ ps.getD j 0 then 0 else j + 1

/-- Law: an auto-placed item lands in a lane whose running position is minimal. -/
theorem minPos_le : ∀ (ps : List Nat) (i : Nat), i < ps.length → ps.getD (minPos ps) 0 ≤ ps.getD i 0
  | [], i, h => by simp at h
  | [p], i, h => by
      have : i = 0 := by simp at h; omega
      subst this; simp [minPos]
  | p :: q :: ps, i, h => by
      have ih := minPos_le (q :: ps)
      simp only [minPos]
      split
      · rename_i hc
        cases i with
        | zero => simp only [List.getD_cons_zero]; exact Nat.le_refl _
        | succ i =>
          simp only [List.getD_cons_zero, List.getD_cons_succ]
          exact Nat.le_trans hc (ih i (by simp at h ⊢; omega))
      · rename_i hc
        cases i with
        | zero => simp only [List.getD_cons_zero, List.getD_cons_succ]; omega
        | succ i =>
          simp only [List.getD_cons_succ]
          exact ih i (by simp at h ⊢; omega)

/-- Place items in order over `n` lanes; an item is (explicit 1-based lane, stacking size). Returns
    the lane of each item and the running positions. -/
def place (n : Nat) (items : List (Option Nat × Nat)) : List Nat :=
  (items.foldl (fun (acc : List Nat × List Nat) (it : Option Nat × Nat) =>
    let lane := match it.1 with | some l => l - 1 | none => minPos acc.2
    (acc.1 ++ [lane], acc.2.mapIdx fun i p => if i == lane then p + it.2 else p)) ([], List.replicate n 0)).1

/-- Track sizes after placement: auto-fit lanes without items collapse (§7.2.3.2); the rest are
    sized by the grid track sizing algorithm. -/
def laneSizes (W : Nat) (reps : List Rep) (items : List (Option Nat × Nat)) : List Nat :=
  let tracks := expand W reps
  let used := place tracks.length items
  let kept := (tracks.zipIdx.filter fun (t, i) => !t.2 || used.contains i).map fun (t, _) => t.1
  sizes W (kept.map fun s => ⟨.px s, .px s, 1⟩)

end GridLanes
end ChromiumLayout
