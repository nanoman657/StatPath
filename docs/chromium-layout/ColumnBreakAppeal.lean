import ColumnLayout
/-
  ColumnBreakAppeal.lean: CSS Fragmentation Level 3 §3.1–§3.3, §4.1–§4.4 break-appeal resolution
  for `break-before: avoid`, `break-after: avoid`, `break-inside: avoid`, `orphans`/`widows`,
  forced breaks, and monolithic replaced elements in multi-column layout.
  Written from CSS Fragmentation 3 §4.4 (Unforced Breaks: Rule 1 forced breaks, Rule 2 break-before/
  break-after avoidance, Rule 3 orphans/widows, Rule 4 break-inside avoidance) and checked against
  column_layout_algorithm_test.cc (AvoidBreakBetween*, TallReplacedContent). Owned by the block lane.
-/
namespace ChromiumLayout
namespace ColumnBreakAppeal

/-- A placed fragment `(y, w, h, children)` inside a column (with `x = 0`). -/
abbrev Frag := Nat × Nat × Nat × List (Nat × Nat × Nat)

/-- An in-flow item in a multicol container:
    - `leaf w h avoidBefore avoidAfter forceAfter monolithic`
    - `box w kids avoidBefore avoidAfter avoidInside orphans widows`
      where each child in `kids` is `(w, h, avoidBefore)`.
    CSS Fragmentation 3 §3.1–§3.3. -/
inductive Entry where
  | leaf (w h : Nat) (avoidBefore : Bool := false) (avoidAfter : Bool := false)
         (forceAfter : Bool := false) (monolithic : Bool := false)
  | box (w : Nat) (kids : List (Nat × Nat × Bool)) (avoidBefore : Bool := false)
        (avoidAfter : Bool := false) (avoidInside : Bool := false)
        (orphans : Nat := 1) (widows : Nat := 1)
  deriving DecidableEq, Repr

/-- Break appeal at a boundary between two sibling entries (CSS Fragmentation 3 §4.4 Rule 2):
    0 if either side avoids the break, 3 otherwise. -/
def edgeAppeal (prevAvoidAfter curAvoidBefore : Bool) : Nat :=
  if prevAvoidAfter || curAvoidBefore then 0 else 3

/-- Break appeal before child index `j` (`0 < j < n`) inside a box (CSS Fragmentation 3 §4.4
    Rules 2–4): 0 if `break-before: avoid`, 1 if container has `break-inside: avoid`,
    2 if `j < orphans` or `n - j < widows`, and 3 otherwise. -/
def insideAppeal (avoidBefore avoidInside : Bool) (orphans widows j n : Nat) : Nat :=
  if avoidBefore then 0
  else if avoidInside then 1
  else if j < orphans || n - j < widows then 2
  else 3

/-- Atomic unit in the flattened flow: `(entryIdx, w, h, forceAfter, monolithic, appealBefore)`. -/
abbrev UnitItem := Nat × Nat × Nat × Bool × Bool × Nat

/-- Flatten entries into atomic units with boundary appeals. -/
def flattenEntries (entries : List Entry) : List UnitItem :=
  let rec loop : Nat → Bool → List Entry → List UnitItem
    | _, _, [] => []
    | idx, prevAvoidA, .leaf w h avB avA forceA mono :: rest =>
      let app := if idx == 0 then 0 else edgeAppeal prevAvoidA avB
      (idx, w, h, forceA, mono, app) :: loop (idx + 1) avA rest
    | idx, prevAvoidA, .box _ ks avB avA avIn orph wid :: rest =>
      let n := ks.length
      let units := ks.zipIdx.map fun ((kw, kh, kAvB), j) =>
        let app :=
          if j == 0 then (if idx == 0 then 0 else edgeAppeal prevAvoidA (avB || kAvB))
          else insideAppeal kAvB avIn orph wid j n
        (idx, kw, kh, false, false, app)
      units ++ loop (idx + 1) avA rest
  loop 0 false entries

/-- Build column fragments from the per-unit slices `(entryIdx, w, h)` in a column. -/
def buildColFrags (fragH : Nat) (isCol0 : Bool) (entries : List Entry)
    (slices otherSlices : List (Nat × Nat × Nat)) : List Frag :=
  let rec go (idx y : Nat) : List Entry → List Frag
    | [] => []
    | e :: rest =>
      let my := slices.filter (fun (i, _, _) => i == idx)
      match my with
      | [] => go (idx + 1) y rest
      | (_, w0, h0) :: _ =>
        match e with
        | .leaf .. => (y, w0, h0, []) :: go (idx + 1) (y + h0) rest
        | .box bw .. =>
          let (_, kidsRev) := my.foldl (fun (cy, acc) (_, kw, kh) =>
            (cy + kh, (cy, kw, kh) :: acc)) (0, [])
          let kidsH := (my.map (·.2.2)).sum
          let splitNext := isCol0 && otherSlices.any (fun (i, _, _) => i == idx)
          let boxH := if splitNext then fragH - y else kidsH
          (y, bw, boxH, kidsRev.reverse) :: go (idx + 1) (y + boxH) rest
  go 0 0 entries

/-- Slice units across the column boundary at `fragH` when no positive-appeal breakpoint exists. -/
def sliceAtFragH (fragH : Nat) : Nat → List UnitItem → List (Nat × Nat × Nat) × List (Nat × Nat × Nat)
  | _, [] => ([], [])
  | y, (idx, w, h, _, mono, _) :: rest =>
    if y + h ≤ fragH then
      let (c0, c1) := sliceAtFragH fragH (y + h) rest
      ((idx, w, h) :: c0, c1)
    else if y < fragH then
      if mono then
        ([(idx, w, h)], rest.map fun (i, uw, uh, _, _, _) => (i, uw, uh))
      else
        let h0 := fragH - y
        ([(idx, w, h0)], (idx, w, h - h0) :: rest.map fun (i, uw, uh, _, _, _) => (i, uw, uh))
    else
      ([], (idx, w, h) :: rest.map fun (i, uw, uh, _, _, _) => (i, uw, uh))

/-- Lay out `entries` across two columns of block size `fragH`, returning `(col0, col1)`.
    CSS Fragmentation 3 §4.1–§4.4. -/
def layoutAppeal (fragH : Nat) (entries : List Entry) : List Frag × List Frag :=
  let units := flattenEntries entries
  let toSlice (u : UnitItem) : Nat × Nat × Nat := (u.1, u.2.1, u.2.2.1)
  let totalH := (units.map (·.2.2.1)).sum
  let forcedIdx := units.findIdx? (fun u => u.2.2.2.1)
  let (s0, s1) :=
    match forcedIdx with
    | some fi => ((units.take (fi + 1)).map toSlice, (units.drop (fi + 1)).map toSlice)
    | none =>
      if totalH ≤ fragH then (units.map toSlice, [])
      else
        let cands := (List.range units.length).drop 1
        let best : Nat × Nat := cands.foldl (fun (bestA, bestK) k =>
          let prefH := ((units.take k).map (·.2.2.1)).sum
          let app := match units[k]? with | some u => u.2.2.2.2.2 | none => 0
          if prefH ≤ fragH && app > 0 && app ≥ bestA then (app, k) else (bestA, bestK)) (0, 0)
        if best.1 > 0 then
          ((units.take best.2).map toSlice, (units.drop best.2).map toSlice)
        else
          sliceAtFragH fragH 0 units
  (buildColFrags fragH true entries s0 s1, buildColFrags fragH false entries s1 s0)

/-- Law: `break-before: avoid` or `break-after: avoid` strictly dominates `orphans`/`widows`
    violations (`edgeAppeal` / `insideAppeal` with `avoidBefore` is 0, whereas without `avoidBefore`
    and `avoidInside` it is at least 2). CSS Fragmentation 3 §4.4 Rules 2–3. -/
theorem avoid_before_dominates_orphans (avoidIn : Bool) (orphans widows j n : Nat) :
    insideAppeal true avoidIn orphans widows j n < insideAppeal false false orphans widows j n := by
  simp only [insideAppeal, Bool.false_eq_true, ↓reduceIte]
  split <;> omega

/-- Whether a Class C breakpoint exists between a wrapper block's block-start edge and its
    first in-flow child when preceded by a float of block size `floatH`. If the wrapper itself
    clears the float (`clearOnW = true`), the float is above the wrapper; otherwise the child
    is pushed down by `floatH`, creating a positive gap beyond the wrapper's border `bW` and
    the child's collapsed top margin `mC` iff `bW + mC < floatH`.
    CSS Fragmentation 3 §4.1, CSS 2.1 §9.5.2. -/
def hasClassCBreakpoint (clearOnW : Bool) (bW mC floatH : Nat) : Bool :=
  !clearOnW && decide (bW + mC < floatH)

/-- Law: when the wrapper's top border plus its child's collapsed top margin reaches or exceeds
    the float's block size (`floatH ≤ bW + mC`), no clearance gap is introduced, so no Class C
    breakpoint exists before the child. CSS Fragmentation 3 §4.1, CSS 2.1 §9.5.2. -/
theorem no_class_c_when_margin_clears_float (clearOnW : Bool) (bW mC floatH : Nat)
    (h : floatH ≤ bW + mC) :
    hasClassCBreakpoint clearOnW bW mC floatH = false := by
  have hnot : ¬ (bW + mC < floatH) := Nat.not_lt.mpr h
  simp [hasClassCBreakpoint, hnot]

/-- Lay out a two-column fragment pair `(col0Rects, col1WrapperAndChild)` for a leading block
    `(50, h0)`, a float `(floatW, floatH)`, and a wrapper block of content width `wW` and border
    `bW` containing an unbreakable child `(wC, hC)` with collapsed top margin `mC`.
    CSS Fragmentation 3 §4.1. -/
def layoutClassC (fragH h0 floatW floatH wW bW mC wC hC : Nat) (clearOnW : Bool) :
    List (Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat × Nat × Nat) :=
  let bw := wW + 2 * bW
  if hasClassCBreakpoint clearOnW bW mC floatH then
    ([(0, 0, 50, h0), (0, h0, floatW, floatH), (0, h0, bw, fragH - h0)],
     (bw, hC + bW, bW, 0, wC, hC))
  else
    ([(0, 0, 50, h0), (0, h0, floatW, floatH)],
     (bw, mC + hC + 2 * bW, bW, bW + mC, wC, hC))

/-- Adjoining block-start margin after a fragmentation break: retained after a forced break,
    truncated to zero after an unforced break (CSS Fragmentation 3 §5.2). -/
def marginAfterBreak (forced : Bool) (m : Nat) : Nat :=
  if forced then m else 0

end ColumnBreakAppeal
end ChromiumLayout
