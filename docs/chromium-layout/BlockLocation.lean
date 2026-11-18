/-
  BlockLocation.lean: LocationContainer, derived from element display kinds.
  Written from CSS 2.1 §9.2 (box generation: `display:inline` generates no box of
  its own for its in-flow children, so their positions are relative to the nearest
  enclosing box) and SVG 2 (foreignObject element) (x/y are in the SVG user space,
  not in the parent box's writing-mode frame).
  Required by layout_box_test.cc:356 (LocationContainer), :435 (LocationContainerOfSVG).
  Owned by the block lane (Block*).
-/
namespace ChromiumLayout
namespace BlockLocation

/-- Display kind of an element, as far as box generation is concerned.
    CSS 2.1 §9.2.1, §17 (table model), SVG 2 foreignObject. -/
inductive Disp where
  | block | inline | table | tbody | row | cell | replaced | svgRoot | foreignObject
  deriving DecidableEq

/-- Only `inline` elements generate no `LayoutBox`. CSS 2.1 §9.2.2. -/
def generatesBox (d : Disp) : Bool := d != .inline

/-- `LocationContainer` of an element of kind `self`, given its ancestors
    (innermost first): the distance to the nearest ancestor that generates a box.
    A foreignObject has none: its x/y are in SVG user space (SVG 2 foreignObject).
    Needed by layout_box_test.cc:356, :435. -/
def locationContainer (self : Disp) (anc : List Disp) : Option Nat :=
  if self == .foreignObject then none
  else anc.findIdx? generatesBox

/-- Law (CSS 2.1 §9.2.2): any number `n` of inline ancestors are skipped; the
    container is the first box-generating ancestor, `n` steps out. -/
theorem locationContainer_skips_inlines (self : Disp) (h : self ≠ .foreignObject)
    (n : Nat) (b : Disp) (hb : b ≠ .inline) (rest : List Disp) :
    locationContainer self (List.replicate n .inline ++ b :: rest) = some n := by
  have hs : (self == .foreignObject) = false := by simpa using h
  have hg : generatesBox b = true := by simpa [generatesBox] using hb
  have : (List.replicate n Disp.inline ++ b :: rest).findIdx? generatesBox = some n := by
    induction n with
    | zero => simp [List.findIdx?_cons, hg]
    | succ k ih => simp [List.replicate_succ, List.findIdx?_cons, generatesBox, ih]
  simp [locationContainer, hs, this]

/-- Law (SVG 2): a foreignObject never has a location container. -/
theorem foreignObject_no_container (anc : List Disp) :
    locationContainer .foreignObject anc = none := by
  simp [locationContainer]

end BlockLocation
end ChromiumLayout
