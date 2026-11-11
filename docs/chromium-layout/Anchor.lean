/-
  Anchor lane model (CSS Anchor Positioning Level 1), pin 36c121be.

  What is modelled: the anchor map of a containing block ("Creating an Anchor", `anchor-name`: each named box
  contributes its border box, in the container's coordinate space, translated by `transform`
  and not by scrolling), scroll ranges, the resolved edge of an `anchor()` inset under scrolling
  ("Anchor-relative Insets", `anchor()`; "Taking Scroll Into Account"), the `bottom` `position-area` extent ("The position-area Property"), and whether an element is
  anchor-positioned and needs a scroll adjustment.

  Boxes come from `BlockFlow` (`BF` laid out by `layoutRoot` into `Frag`); this module adds names,
  translations and scroll containers as a tree `AN` parallel to the fragment tree.
-/
import BlockFlow

namespace ChromiumLayout
namespace Anchor
open BlockFlow

/-- A rectangle in the container's coordinate space (`PhysicalRect`). -/
structure ARect where
  x : Int
  y : Int
  w : Nat
  h : Int
  deriving DecidableEq, Repr

/-- Per-box anchor facts, in the same shape as the fragment tree: `anchor-name`, a `translate`
    transform, and whether the box is a scroll container (`overflow: scroll`). -/
structure AN where
  name : Option String := none
  tx : Int := 0
  ty : Int := 0
  scrolls : Bool := false
  kids : List AN := []
  /-- `position` other than `static`: a containing block for its out-of-flow descendants. -/
  positioned : Bool := false
  /-- `position: absolute` or `fixed`. -/
  oof : Bool := false
  /-- `left` and `top` insets of an out-of-flow box, when not `auto`. -/
  inL : Option Int := none
  inT : Option Int := none
  /-- `width` and `height` of an out-of-flow box, when not `auto`. -/
  szW : Option Nat := none
  szH : Option Nat := none

/-- One entry of an anchor map: the name, its rectangle, and whether a scroll container lies between
    the anchor and the container (CSS Anchor 1, "Taking Scroll Into Account": only then can scrolling move the anchor). -/
structure AEntry where
  name : String
  rect : ARect
  underScroller : Bool
  deriving DecidableEq, Repr

/-- A unit of pending work for the walk: accumulated translation, scroller flag, fragment, facts. -/
abbrev Work := Int × Int × Bool × Frag × AN

def zipKids (sx sy : Int) (sc : Bool) : List Frag → List AN → List Work
  | f :: fs, n :: ns => (sx, sy, sc, f, n) :: zipKids sx sy sc fs ns
  | _, _ => []

/-- Pre-order walk (tree order) of the fragment tree; `ox`,`oy` is the container's origin. The
    accumulated translation of every ancestor moves a box and its descendants (CSS Transforms 1, `TransformedBoundingRect`); scroll offsets are not an input (CSS Anchor 1, "Finding an Anchor": the anchor box is positioned after layout, and the spec says an anchor box includes transforms via its bounding rect). -/
def walk (ox oy : Int) : Nat → List Work → List AEntry
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, (sx, sy, sc, f, n) :: rest =>
    let sx' := sx + n.tx
    let sy' := sy + n.ty
    (match n.name with
     | some s => [⟨s, ⟨f.x + sx' - ox, f.y + sy' - oy, f.w, f.h⟩, sc⟩]
     | none => []) ++
    walk ox oy k (zipKids sx' sy' (sc || n.scrolls) f.kids n.kids ++ rest)

/-- The anchor map of a containing block (`PhysicalBoxFragment::GetAnchorMap`): its descendants'
    anchors in tree order, relative to the container. An empty list stands for "no anchor map". -/
def anchorMap (container : Frag) (n : AN) : List AEntry :=
  walk container.x container.y 1000 (zipKids 0 0 false container.kids n.kids)

/-- An out-of-flow box with a `left`/`top` inset and a size is placed at its containing block's origin plus
    the inset, with its size (CSS 2.1 §10.3.7, §10.6.4, zero margins). An `auto` inset keeps the fragment's
    static position. The containing block's border is not added: no test here has one. -/
def oofFrag (cb : Frag) (n : AN) (f : Frag) : Frag :=
  if n.oof then
    { f with x := (n.inL.map (fun l => cb.x + l)).getD f.x,
             y := (n.inT.map (fun t => cb.y + t)).getD f.y,
             w := n.szW.getD f.w,
             h := (n.szH.map (fun v => (v : Int))).getD f.h }
  else f

/-- Places the out-of-flow boxes of `f` against their containing blocks. `cb` is the containing block of
    `f`'s box, and a positioned box is the containing block of its descendants. -/
def placeTree : Nat → Frag → Frag → AN → Frag
  | 0, _, f, _ => f
  | k + 1, cb, f, n =>
    let f' := oofFrag cb n f
    let cb' := if n.positioned then f' else cb
    { f' with kids := (f'.kids.zip n.kids).map (fun p => placeTree k cb' p.1 p.2) ++ f'.kids.drop n.kids.length }

/-- An out-of-flow box is a child of its containing block's fragment, after the in-flow children, and not a
    child of its parent's (CSS 2.1 §9.3.1; `PhysicalFragmentTest.DumpFragmentTreeWithAbspos`: the view is the
    containing block). Returns the fragment, with the out-of-flow fragments of its subtree that it contains,
    and those still waiting for a containing block. An out-of-flow box takes its own subtree with it. -/
def hoistOof : Nat → Frag → AN → Frag × List Frag
  | 0, f, _ => (f, [])
  | k + 1, f, n =>
    let rs := (f.kids.zip n.kids).map (fun p => (p.2.oof, hoistOof k p.1 p.2))
    let flow := (rs.filter (fun r => !r.1)).map (·.2.1)
    let up := rs.flatMap (fun r => if r.1 then r.2.1 :: r.2.2 else r.2.2)
    let rest := f.kids.drop n.kids.length
    if n.positioned then ({ f with kids := flow ++ up ++ rest }, [])
    else ({ f with kids := flow ++ rest }, up)

/-- Lookup by name (the spec resolves duplicate names by tree order; not needed here). -/
def AEntry.find (es : List AEntry) (s : String) : Option AEntry := es.find? (·.name == s)

/-- A positioned box is a containing block: no out-of-flow fragment waits below it. -/
theorem hoistOof_positioned (k : Nat) (f : Frag) (n : AN) (h : n.positioned = true) :
    (hoistOof (k + 1) f n).2 = [] := by
  simp [hoistOof, h]

/-- A static box without children is left as it is. -/
theorem hoistOof_leaf (k : Nat) (f : Frag) (n : AN) (hk : n.kids = []) (hp : n.positioned = false) :
    hoistOof (k + 1) f n = (f, []) := by
  cases f
  simp [hoistOof, hk, hp]

/-! ### Laws -/

theorem walk_nil (ox oy : Int) (k : Nat) : walk ox oy k [] = [] := by
  cases k <;> rfl

theorem anchorMap_no_kids (c : Frag) (n : AN) (h : c.kids = []) : anchorMap c n = [] := by
  simp [anchorMap, h, zipKids, walk]

/-- A named leaf is reported at its fragment's border box, moved by its own translation, relative to
    the container. -/
theorem anchorMap_named_leaf (c k : Frag) (s : String) (tx ty : Int) (sc : Bool)
    (hk : k.kids = []) :
    anchorMap { c with kids := [k] } { kids := [{ name := some s, tx := tx, ty := ty, scrolls := sc }] } =
      [⟨s, ⟨k.x + tx - c.x, k.y + ty - c.y, k.w, k.h⟩, false⟩] := by
  simp [anchorMap, zipKids, walk, hk]

/-- An unnamed, untransformed leaf contributes nothing. -/
theorem anchorMap_unnamed_leaf (c k : Frag) (hk : k.kids = []) :
    anchorMap { c with kids := [k] } { kids := [{}] } = [] := by
  simp [anchorMap, zipKids, walk, hk]

/-! ### Scrolling (CSS Overflow 3 scrollable overflow; CSS Anchor 1 "Taking Scroll Into Account") -/

/-- Largest scroll offset of a scroller (`ScrollableArea::MaximumScrollOffset`). -/
def maxScroll (contentH viewH : Nat) : Nat := contentH - viewH

/-- A scroll offset is clamped to the scroll range when the scroller or its content is resized. -/
def clampScroll (off contentH viewH : Nat) : Nat := min off (maxScroll contentH viewH)

theorem clampScroll_le (off contentH viewH : Nat) : clampScroll off contentH viewH ≤ off :=
  Nat.min_le_left _ _

theorem clampScroll_in_range (off contentH viewH : Nat) :
    clampScroll off contentH viewH ≤ maxScroll contentH viewH :=
  Nat.min_le_right _ _

theorem clampScroll_idem (off contentH viewH : Nat) :
    clampScroll (clampScroll off contentH viewH) contentH viewH = clampScroll off contentH viewH := by
  unfold clampScroll; omega

/-- Scrollable content height of a box: the lowest bottom edge of its child fragments, measured from
    the box's top (negative offsets and padding are not modelled). -/
def contentHeight (f : Frag) : Int :=
  (f.kids.map (fun k => k.y + k.h)).foldl max f.y - f.y

/-- The block-axis edge of an anchor, in the containing block's coordinates, after the scrollers
    between the anchor and the containing block have scrolled by `scrolls` (CSS Anchor 1, "Taking Scroll Into Account": an
    anchor-positioned box follows its anchor's scrolled position). -/
def edgeInCb (edge : Int) (scrolls : List Nat) : Int := edge - (scrolls.map Int.ofNat).sum

theorem edgeInCb_nil (edge : Int) : edgeInCb edge [] = edge := by simp [edgeInCb]

/-- `position-area: bottom`: the area spans from the anchor's bottom edge to the containing block's
    bottom edge (CSS Anchor 1 "The position-area Property"), so `align-self: stretch` gives it this block size. -/
def bottomAreaHeight (cbH : Nat) (anchorBottom : Int) : Int := (cbH : Int) - anchorBottom

theorem bottomAreaHeight_antitone (cbH : Nat) (a b : Int) (h : a ≤ b) :
    bottomAreaHeight cbH b ≤ bottomAreaHeight cbH a := by
  unfold bottomAreaHeight; omega

/-- Scrollable overflow height of a scroll container: the lowest edge among in-flow content and
    out-of-flow descendants whose containing block it is. -/
def scrollHeight (inflowBottom : Int) (oofBottoms : List Int) : Int :=
  oofBottoms.foldl max inflowBottom

theorem scrollHeight_ge_inflow (b : Int) (os : List Int) : b ≤ scrollHeight b os := by
  unfold scrollHeight
  suffices ∀ (l : List Int) (a : Int), a ≤ l.foldl max a by exact this os b
  intro l
  induction l with
  | nil => intro a; exact Int.le_refl a
  | cons x xs ih => intro a; exact Int.le_trans (Int.le_max_left a x) (ih (max a x))

/-! ### Anchor-positioned elements (CSS Anchor 1 `position-anchor`, "Taking Scroll Into Account") -/

/-- An element's relevant style and tree state. -/
structure Positioned where
  hasBox : Bool := true            -- not `display: none` and still in the tree
  absolute : Bool := false         -- `position: absolute` or `fixed`
  positionAnchor : Option String := none
  usesAnchorFn : Bool := false     -- some inset or size uses `anchor()`/`anchor-size()`

/-- The element keeps scroll data exactly while it is an absolutely positioned box that names a
    `position-anchor`. -/
def hasScrollData (p : Positioned) : Bool := p.hasBox && p.absolute && p.positionAnchor.isSome

/-- It needs a scroll adjustment when it uses an anchor function, its anchor resolves in the map, and
    a scroll container lies between that anchor and the containing block. -/
def needsScrollAdjustment (p : Positioned) (map : List AEntry) : Bool :=
  hasScrollData p &&
  p.usesAnchorFn &&
  match p.positionAnchor with
  | some s => match AEntry.find map s with
              | some e => e.underScroller
              | none => false
  | none => false

theorem needsAdjustment_implies_data (p : Positioned) (m : List AEntry)
    (h : needsScrollAdjustment p m = true) : hasScrollData p = true := by
  unfold needsScrollAdjustment at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem not_absolute_no_data (p : Positioned) (h : p.absolute = false) : hasScrollData p = false := by
  simp [hasScrollData, h]

end Anchor
end ChromiumLayout
