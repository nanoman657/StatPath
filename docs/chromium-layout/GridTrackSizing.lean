/-
  GridTrackSizing.lean: the grid track sizing algorithm for one axis, written from
  grid_lanes/grid_lanes_layout_algorithm_test.cc (track size tests).
  Spec: CSS Grid Layout 1 §11 (specs/css-grid-1.txt): §11.4 initialize, §11.5 resolve intrinsic
  sizes, §11.6 maximize, §11.7 expand flexible, §11.8 stretch auto tracks. CSS Grid 3 (grid-lanes)
  uses the same algorithm in its grid axis.
  Simplifications, all marked where they occur: tracks are sets of `n` repeated tracks with the
  same definition (intrinsic tracks have n = 1); the "infinitely growable" flag, fit-content(),
  flexible items and baseline shims are not modelled; space is shared with natural-number division.
  Item contributions (min-content, max-content, minimum) are inputs: text measurement belongs to
  the inline lane.
-/
namespace ChromiumLayout
namespace GridTrackSizing

/-- Track sizing function. CSS Grid 1 §7.2.1. -/
inductive Sz where
  | px (n : Nat) | pct (n : Nat) | fr (n : Nat) | minC | maxC | auto
  deriving DecidableEq, Repr

/-- A set of `n` repeated tracks `minmax(lo, hi)`. -/
structure TS where
  lo : Sz
  hi : Sz
  n : Nat := 1

/-- Grid item over track sets `[s, e)` with its minimum, min-content and max-content
    contributions. CSS Grid 1 §11.5. -/
structure It where
  s : Nat
  e : Nat
  mn : Nat := 0
  minC : Nat
  maxC : Nat

/-- Track state: (base size, growth limit); `none` is infinity. -/
abbrev St := List (Nat × Option Nat)

/-- Fixed sizing function resolved against the container size `W`. CSS Grid 1 §11.4. -/
def fixedLen (W : Nat) : Sz → Option Nat
  | .px n => some n
  | .pct p => some (p * W / 100)
  | _ => none

/-- Intrinsic sizing function (min-content, max-content, auto). CSS Grid 1 §11.5. -/
def isIntr : Sz → Bool
  | .minC | .maxC | .auto => true
  | _ => false

/-- §11.4 initialize track sizes: fixed minimum is the base size, intrinsic minimum is 0; fixed
    maximum is the growth limit, otherwise infinity; the growth limit is at least the base size. -/
def init (W : Nat) (ts : List TS) : St :=
  ts.map fun t =>
    let b := t.n * (fixedLen W t.lo).getD 0
    (b, (fixedLen W t.hi).map fun g => max (t.n * g) b)

/-- §11.5.1 distribute extra space equally: the tracks of `it` selected by `sel` share what is
    missing between `c` and the current sum (of growth limits if `useGl`, else base sizes).
    Limits and freezing are not modelled (they do not occur in the tests). -/
def grow (ts : List TS) (it : It) (sel : TS → Bool) (useGl : Bool) (c : Nat) (st : St) : St :=
  let cur := fun (x : Nat × Option Nat) => if useGl then x.2.getD x.1 else x.1
  let total := ((st.drop it.s).take (it.e - it.s)).foldl (fun a x => a + cur x) 0
  let share := (c - total) / (((ts.drop it.s).take (it.e - it.s)).countP sel)
  (st.zip ts).mapIdx fun i (x, t) =>
    if it.s ≤ i && i < it.e && sel t then
      (if useGl then (x.1, some (cur x + share)) else (x.1 + share, x.2))
    else x

/-- Raise growth limits that fell below the base size. -/
def fixLimits (st : St) : St := st.map fun x => (x.1, x.2.map (max x.1))

/-- §11.5 one item: intrinsic minimums, content-based minimums, max-content minimums, then
    intrinsic and max-content maximums. -/
def itemStep (ts : List TS) (st : St) (it : It) : St :=
  let st := grow ts it (fun t => isIntr t.lo) false it.mn st
  let st := grow ts it (fun t => t.lo == .minC || t.lo == .maxC) false it.minC st
  let st := fixLimits (grow ts it (fun t => t.lo == .maxC) false it.maxC st)
  let st := grow ts it (fun t => isIntr t.hi) true it.minC st
  grow ts it (fun t => t.hi == .maxC || t.hi == .auto) true it.maxC st

/-- §11.5: items by increasing span, then infinite growth limits become the base size. -/
def resolveIntrinsic (ts : List TS) (items : List It) (st : St) : St :=
  let st := (List.range (ts.length + 1)).foldl
    (fun st k => (items.filter (fun it => it.e - it.s == k)).foldl (itemStep ts) st) st
  fixLimits (st.map fun x => (x.1, some (x.2.getD x.1)))

/-- §11.6 maximize tracks: share free space equally, freezing tracks at their growth limit
    (repeated at most `fuel` times). -/
def maximize : Nat → Nat → St → St
  | 0, _, st => st
  | f + 1, free, st =>
    let cap := fun (x : Nat × Option Nat) => (x.2.getD x.1) - x.1
    let share := free / (st.filter (fun x => 0 < cap x)).length
    let st' := st.map fun x => if 0 < cap x then (x.1 + min share (cap x), x.2) else x
    maximize f (free - ((st'.map (·.1)).sum - (st.map (·.1)).sum)) st'

/-- §11.7 expand flexible tracks: the fr size is the space left by the other tracks divided by
    the sum of flex factors (at least 1); a flexible track is at least its base size. -/
def expandFlex (W : Nat) (ts : List TS) (st : St) : St :=
  let w := fun (t : TS) => match t.hi with | .fr k => t.n * k | _ => 0
  let used := ((st.zip ts).map fun (x, t) => if w t == 0 then x.1 else 0).sum
  let f := (W - used) / max 1 (ts.map w).sum
  (st.zip ts).map fun (x, t) => if w t == 0 then x else (max x.1 (w t * f), x.2)

/-- §11.8 stretch auto tracks: leftover space is shared by tracks with an `auto` maximum. -/
def stretch (W : Nat) (ts : List TS) (st : St) : St :=
  let share := (W - (st.map (·.1)).sum) / (ts.filter (fun t => t.hi == .auto)).length
  (st.zip ts).map fun (x, t) => if t.hi == .auto then (x.1 + share, x.2) else x

/-- Track set sizes (§11.3): initialize, resolve intrinsic, maximize, expand flexible, stretch. -/
def sizes (W : Nat) (ts : List TS) (items : List It := []) : List Nat :=
  let st := resolveIntrinsic ts items (init W ts)
  let free := W - (st.map (·.1)).sum
  ((stretch W ts (expandFlex W ts (maximize ts.length free st))).map (·.1))

/-- Law: a percentage track never exceeds the container for percentages up to 100. -/
theorem fixedLen_pct_le (W p : Nat) (h : p ≤ 100) : fixedLen W (.pct p) = some (p * W / 100) ∧
    p * W / 100 ≤ W := by
  refine ⟨rfl, ?_⟩
  exact Nat.div_le_of_le_mul (Nat.mul_le_mul_right W (by omega) |> fun h => by simpa [Nat.mul_comm] using h)

end GridTrackSizing
end ChromiumLayout
