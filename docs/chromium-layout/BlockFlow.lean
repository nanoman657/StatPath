/-
  BlockFlow.lean: signed-margin block-flow model, written from the Blink layout unit tests
  (block_layout_algorithm_test.cc and friends), not from the C++.

  Module owned by the "block" lane (new `Block*.lean` module). It does not edit
  `LayoutTypes.lean`; it reuses `MarginStrut` from it and adds what the tests need and the
  base model lacks: signed margins, nested collapse-through, auto margins, percentage and
  shrink-to-fit widths.

  Coordinates are absolute (root border-box top-left = (0, 0)); the tests' child offsets are
  differences (`Frag.relY`, `Frag.relX`). Lengths are whole pixels (`Int`/`Nat`).

  Not modelled (rows depending on them are `blocked` in MANIFEST-Block.md): floats, clear,
  writing modes, text/inline content, fragmentation, caching.
-/
import LayoutTypes

namespace ChromiumLayout

namespace MarginStrut

/-- A signed margin as a strut (needed by every test with a negative margin, e.g.
    `ZeroBlockSizeAboveEdge`, `NewFcFirstChildIsZeroBlockSize`, `CollapsingMarginsCase2WithFloats`). -/
def ofInt (m : Int) : MarginStrut :=
  if 0 ≤ m then { pos := m.toNat, neg := 0 } else { pos := 0, neg := (-m).toNat }

/-- Signed collapsed value `pos - neg` (CSS 2.1 §8.3.1: max positive plus min negative);
    required by every vector that places a box at a collapsed margin. -/
def signedSum (s : MarginStrut) : Int := (s.pos : Int) - (s.neg : Int)

end MarginStrut

namespace BlockFlow

/-- CSS `width`: `auto`, a pixel length or a percentage (`PercentageResolutionSize`, `AutoMargin`,
    `ShrinkToFit`). -/
inductive Len where
  | auto
  | px (n : Nat)
  | pct (n : Nat)

/-- Horizontal margin: `auto` or a signed pixel length (`AutoMargin`). -/
inductive MLen where
  | auto
  | px (n : Int)

/-- An in-flow block box as the tests' HTML describes it (content-box sizing, as the tests use).
    `newBfc` stands for `display: flow-root`/`overflow: hidden`/`contain: paint`. -/
structure BF where
  id : Nat := 0
  width : Len := .auto
  height : Option Nat := none
  mt : Int := 0
  mb : Int := 0
  ml : MLen := .px 0
  mr : MLen := .px 0
  pt : Nat := 0
  pb : Nat := 0
  pl : Nat := 0
  pr : Nat := 0
  bt : Nat := 0
  bb : Nat := 0
  bl : Nat := 0
  br : Nat := 0
  newBfc : Bool := false
  /-- A left float (CSS 2.1 §9.5). Floats are leaf boxes here: they are placed at the flow position
      without consuming it and never collapse margins (`CollapsingMarginsCase2WithFloats`). -/
  isFloat : Bool := false
  children : List BF := []

/-- Border-box fragment in absolute coordinates (`PhysicalBoxFragment` size and offset,
    `FragmentChildIterator::NextChild`). -/
structure Frag where
  id : Nat := 0
  x : Int := 0
  y : Int := 0
  w : Nat := 0
  h : Int := 0
  kids : List Frag := []

namespace Frag

/-- The `i`-th child fragment (default fragment when absent). -/
def kid (f : Frag) (i : Nat) : Frag := f.kids.getD i {}

/-- Child block offset relative to its parent (`PhysicalFragmentLink::Offset().top`). -/
def relY (p c : Frag) : Int := c.y - p.y

/-- Child inline offset relative to its parent (`PhysicalFragmentLink::Offset().left`). -/
def relX (p c : Frag) : Int := c.x - p.x

end Frag

namespace BF

def hpad (b : BF) : Nat := b.pl + b.pr + b.bl + b.br

/-- Border or padding at the block start, or a new BFC: the top margin does not collapse with
    the first child (`CollapsingMarginsCase4`). -/
def hasStartEdge (b : BF) : Bool := b.newBfc || b.bt + b.pt > 0

/-- Border or padding at the block end, a definite height, or a new BFC: the bottom margin does not
    collapse with the last child (`CollapsingMarginsCase3`). -/
def hasEndEdge (b : BF) : Bool := b.newBfc || b.bb + b.pb > 0 || b.height.isSome

end BF

/-- A box is empty (its margins collapse through it) when it has no edges, no definite height and
    only empty children (`CollapsingMarginsCase2WithFloats`, `ZeroBlockSizeAboveEdge`).
    Fuel `d` bounds the tree depth. -/
def isEmpty : Nat → BF → Bool
  | 0, _ => false
  | d + 1, b => !b.hasStartEdge && !b.hasEndEdge && b.children.all (fun c => c.isFloat || isEmpty d c)

/-- All margins of an empty subtree collapse into one strut (`NewFcFirstChildIsZeroBlockSize`). -/
def allMargins : Nat → BF → MarginStrut
  | 0, b => MarginStrut.append (MarginStrut.ofInt b.mt) (MarginStrut.ofInt b.mb)
  | d + 1, b =>
      b.children.foldl (fun s c => if c.isFloat then s else MarginStrut.append s (allMargins d c))
        (MarginStrut.append (MarginStrut.ofInt b.mt) (MarginStrut.ofInt b.mb))

/-- The strut at the moment a non-empty box's border-box top is resolved: the box's top margin
    collapses with the first non-empty descendant's through empty siblings, unless an edge
    intervenes (`CollapsingMarginsCase3/4`, `LayoutBlockChildren`). -/
def firstResolve : Nat → BF → MarginStrut → MarginStrut
  | 0, b, s => MarginStrut.append s (MarginStrut.ofInt b.mt)
  | d + 1, b, s =>
      let s1 := MarginStrut.append s (MarginStrut.ofInt b.mt)
      if b.hasStartEdge then s1
      else
        (b.children.foldl
          (fun (st : MarginStrut × Bool) c =>
            if st.2 || c.isFloat then st
            else if isEmpty (d + 1) c then (MarginStrut.append st.1 (allMargins d c), false)
            else (firstResolve d c st.1, true))
          (s1, false)).1

/-- Used content width: pixel, percentage of the containing block's content width, or stretch to
    the available inline size (`FixedSize`, `PercentageResolutionSize`, `LayoutBlockChildren`). -/
def contentWidth (A : Nat) (b : BF) : Nat :=
  match b.width with
  | .px n => n
  | .pct p => A * p / 100
  | .auto =>
      let ml : Int := match b.ml with | .auto => 0 | .px n => n
      let mr : Int := match b.mr with | .auto => 0 | .px n => n
      ((A : Int) - ml - mr - b.hpad).toNat

/-- Used margins after auto resolution (CSS 2.1 §10.3.3; `AutoMargin`). -/
def usedMargins (A : Nat) (b : BF) : Int × Int :=
  let rem : Int := (A : Int) - ((contentWidth A b + b.hpad : Nat) : Int)
  match b.ml, b.mr with
  | .auto, .auto =>
      if rem ≤ 0 then (0, rem) else (rem / 2, rem - rem / 2)
  | .auto, .px r => (rem - r, r)
  | .px l, .auto => (l, rem - l)
  | .px l, .px r => (l, r)

/-- A left float laid out at the current flow position: its top is the incoming strut resolved
    against `pos`, but the flow position and strut are not changed (CSS 2.1 §9.5.1). A float is a
    leaf here; its content is not modelled. -/
def layoutFloat (A : Nat) (x0 pos : Int) (s : MarginStrut) (b : BF) : Frag :=
  let vert : Int := (b.pt : Int) + (b.pb : Int) + (b.bt : Int) + (b.bb : Int)
  { id := b.id, x := x0 + (usedMargins A b).1, y := pos + s.signedSum,
    w := contentWidth A b + b.hpad,
    h := (match b.height with | some H => (H : Int) | none => 0) + vert }

/-- Lay out one block box in absolute coordinates. `A`: containing block content width;
    `x0`: containing block content-left; `pos`: block position the incoming strut `s` hangs from.
    Returns the fragment, the new flow position (border-box bottom, or `pos` for an empty box) and
    the outgoing strut. Fuel `d` bounds the tree depth. -/
def layoutBox : Nat → Nat → Int → Int → MarginStrut → BF → Frag × Int × MarginStrut
  | 0, _, x0, pos, s, b => ({ id := b.id, x := x0, y := pos }, pos, s)
  | d + 1, A, x0, pos, s, b =>
      let cw := contentWidth A b
      let x := x0 + (usedMargins A b).1
      if isEmpty (d + 1) b then
        let y := pos + (MarginStrut.append s (MarginStrut.ofInt b.mt)).signedSum
        -- Children of an empty box are materialised at the box's resolved position with a fresh
        -- strut (an approximation; the tests only read their widths).
        let cx : Int := x + (b.bl : Int) + (b.pl : Int)
        let kids := (b.children.foldl
          (fun (st : List Frag × Int × MarginStrut) c =>
            let res := if c.isFloat then (layoutFloat cw cx st.2.1 st.2.2 c, st.2.1, st.2.2)
                       else layoutBox d cw cx st.2.1 st.2.2 c
            (res.1 :: st.1, res.2.1, res.2.2))
          ([], y, MarginStrut.empty)).1.reverse
        ({ id := b.id, x := x, y := y, w := cw + b.hpad, h := 0, kids := kids },
         pos, MarginStrut.append s (allMargins d b))
      else
        let y := pos + (firstResolve (d + 1) b s).signedSum
        let inner : Int × MarginStrut :=
          if b.hasStartEdge then (y + (b.bt : Int) + (b.pt : Int), MarginStrut.empty)
          else (pos, MarginStrut.append s (MarginStrut.ofInt b.mt))
        let cx : Int := x + (b.bl : Int) + (b.pl : Int)
        let r := b.children.foldl
          (fun (st : List Frag × Int × MarginStrut × Bool) c =>
            if c.isFloat then
              (layoutFloat cw cx st.2.1 st.2.2.1 c :: st.1, st.2.1, st.2.2.1, st.2.2.2)
            else
              let res := layoutBox d cw cx st.2.1 st.2.2.1 c
              (res.1 :: st.1, res.2.1, res.2.2, st.2.2.2 || !isEmpty (d + 1) c))
          ([], inner.1, inner.2, false)
        let pos' := r.2.1
        let s' := r.2.2.1
        let resolved := r.2.2.2
        let icb : Int :=
          if resolved then (if b.hasEndEdge then pos' + s'.signedSum else pos')
          else y + (b.bt : Int) + (b.pt : Int)
        let yb : Int :=
          match b.height with
          | some H => y + (b.bt : Int) + (b.pt : Int) + (H : Int) + (b.pb : Int) + (b.bb : Int)
          | none => icb + (b.pb : Int) + (b.bb : Int)
        let endS :=
          if b.hasEndEdge then MarginStrut.ofInt b.mb
          else MarginStrut.append s' (MarginStrut.ofInt b.mb)
        ({ id := b.id, x := x, y := y, w := cw + b.hpad, h := yb - y, kids := r.1.reverse },
         yb, endS)

/-- Tree depth bound used by all vectors. -/
def fuel : Nat := 12

/-- Lay out a root box (a new formatting context at the origin with available width `A`). -/
def layoutRoot (A : Nat) (b : BF) : Frag :=
  (layoutBox fuel A 0 0 MarginStrut.empty b).1

/-- The viewport-rooted `html > body` chain used by the tests that read `GetHtmlPhysicalFragment()`:
    viewport width 800, `html` a new BFC, `body` with the UA `margin: 8px`. -/
def htmlBody (bodyChildren : List BF) : BF :=
  { id := 0, newBfc := true,
    children := [{ id := 1, mt := 8, mb := 8, ml := .px 8, mr := .px 8, children := bodyChildren }] }

/-- Max-content inline size of a block: definite width, or the widest child plus its margins
    (`ComputeMinMaxContent`). -/
def maxContent : Nat → BF → Nat
  | 0, b => b.hpad
  | d + 1, b =>
      match b.width with
      | .px n => n + b.hpad
      | _ =>
          b.hpad + b.children.foldl (fun m c =>
            let ml : Int := match c.ml with | .auto => 0 | .px n => n
            let mr : Int := match c.mr with | .auto => 0 | .px n => n
            max m ((((maxContent d c : Nat) : Int) + ml + mr).toNat)) 0

/-- Shrink-to-fit inline size: `min(max(min-content, available), max-content)`
    (`ShrinkToFit`); for plain blocks min-content = max-content. -/
def shrinkToFit (avail minC maxC : Nat) : Nat := min (max minC avail) maxC

/-- Shrink-to-fit always lies within [minC, maxC] whenever minC ≤ maxC
    (generalises `MinMaxSizesTest.ShrinkToFit`). -/
theorem shrinkToFit_bounds (avail minC maxC : Nat) (h : minC ≤ maxC) :
    minC ≤ shrinkToFit avail minC maxC ∧ shrinkToFit avail minC maxC ≤ maxC := by
  unfold shrinkToFit
  omega

/-! ## General laws -/

/-- CSS 2.1 §8.3.1 for two adjoining margins: the collapsed value is the larger positive margin
    plus the smaller (most negative) margin, counting absent sides as 0. Generalises the pairwise
    "max(a, b)" comments in `CollapsingMarginsCase3/4` and the negative cases of
    `ZeroBlockSizeAboveEdge`. -/
theorem collapse_pair (a b : Int) :
    (MarginStrut.append (MarginStrut.ofInt a) (MarginStrut.ofInt b)).signedSum
      = max (max a b) 0 + min (min a b) 0 := by
  unfold MarginStrut.append MarginStrut.ofInt MarginStrut.signedSum
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b <;>
    simp only [ha, hb, ite_true, ite_false, Nat.max_def] <;>
    simp only [Int.max_def, Int.min_def] <;>
    split <;> split <;> split <;> split <;>
    omega

/-- Adding a margin to a strut never moves the collapsed value outside the envelope of the
    strut's value and the margin's (collapsing only max-es positives and min-es negatives):
    the positive part is monotone. -/
theorem append_pos_ge (s t : MarginStrut) : s.pos ≤ (MarginStrut.append s t).pos := by
  unfold MarginStrut.append; simp only [Nat.max_def]; split <;> omega

/-- An empty box is transparent to the flow position (`ZeroBlockSizeAboveEdge`: the box after an
    empty box starts from the same position). -/
theorem empty_box_keeps_pos (d A : Nat) (x0 pos : Int) (s : MarginStrut) (b : BF)
    (h : isEmpty (d + 1) b = true) :
    (layoutBox (d + 1) A x0 pos s b).2.1 = pos := by
  simp [layoutBox, h]

/-- A non-empty box with a start edge is placed at the incoming strut collapsed with its own top
    margin (`CollapsingMarginsCase4`, with padding: `220 = 20 + 200`). -/
theorem start_edge_top (d A : Nat) (x0 pos : Int) (s : MarginStrut) (b : BF)
    (hne : isEmpty (d + 1) b = false) (he : b.hasStartEdge = true) :
    (layoutBox (d + 1) A x0 pos s b).1.y
      = pos + (MarginStrut.append s (MarginStrut.ofInt b.mt)).signedSum := by
  have h1 : firstResolve (d + 1) b s = MarginStrut.append s (MarginStrut.ofInt b.mt) := by
    simp [firstResolve, he]
  simp [layoutBox, hne, h1]

/-- Horizontal constraint of CSS 2.1 §10.3.3 for an `auto`-width box with definite margins:
    margin-left + border-box width + margin-right fills the containing block exactly when it
    fits (`LayoutBlockChildren`, `FixedSize`, `AutoMargin`). -/
theorem auto_width_fills (A : Nat) (b : BF) (l r : Int)
    (hw : b.width = .auto) (hl : b.ml = .px l) (hr : b.mr = .px r)
    (hfit : l + r + (b.hpad : Int) ≤ (A : Int)) :
    l + ((contentWidth A b + b.hpad : Nat) : Int) + r = (A : Int) := by
  simp only [contentWidth, hw, hl, hr]
  omega

end BlockFlow
end ChromiumLayout
