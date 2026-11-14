/-
  OutOfFlowAnchor.lean: CSS Anchor Positioning Level 1 algorithms,
  written from CSS Anchor Positioning Module Level 1 §3 (Declaring Anchors),
  §4 (The anchor() function) and checked against anchor_evaluator_impl_test.cc.
  Owned by the block lane (OutOfFlow*).
-/

namespace ChromiumLayout
namespace OutOfFlowAnchor

/-- Anchor side: top, bottom, left, right, center. CSS Anchor Positioning 1 §4.1. -/
inductive AnchorSide where
  | top
  | bottom
  | left
  | right
  | center
  deriving Inhabited, DecidableEq, Repr

/-- Physical rect (x, y, w, h) of an anchor target. -/
structure AnchorRect where
  x : Nat := 0
  y : Nat := 0
  w : Nat := 0
  h : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- An anchor declaration with an identifier name and its physical geometry. CSS Anchor Positioning 1 §3.1. -/
structure AnchorEntry where
  name : String
  rect : AnchorRect
  deriving Inhabited, DecidableEq, Repr

/-- Anchor map inside a containing block. CSS Anchor Positioning 1 §3.1. -/
def AnchorMap := List AnchorEntry

/-- Find an anchor's rect by name in the anchor map. CSS Anchor Positioning 1 §3.1. -/
def lookupAnchor (map : AnchorMap) (name : String) : Option AnchorRect :=
  match map.find? (fun e => e.name == name) with
  | some entry => some entry.rect
  | none => none

/-- Evaluate an anchor side reference to a physical coordinate. CSS Anchor Positioning 1 §4.1. -/
def evaluateAnchorSide (side : AnchorSide) (r : AnchorRect) : Nat :=
  match side with
  | .top => r.y
  | .bottom => r.y + r.h
  | .left => r.x
  | .right => r.x + r.w
  | .center => r.x + r.w / 2

/-- Evaluate an anchor query given an anchor map, anchor name, and side. CSS Anchor Positioning 1 §4.1. -/
def evaluateAnchor (map : AnchorMap) (name : String) (side : AnchorSide) : Option Nat :=
  (lookupAnchor map name).map (evaluateAnchorSide side)

/-- Law: Top edge of an anchor is always at or before bottom edge.
    CSS Anchor Positioning 1 §4.1. -/
theorem anchor_top_le_bottom (r : AnchorRect) :
    evaluateAnchorSide .top r ≤ evaluateAnchorSide .bottom r := by
  dsimp [evaluateAnchorSide]
  omega

/-- Law: Left edge of an anchor is always at or before right edge.
    CSS Anchor Positioning 1 §4.1. -/
theorem anchor_left_le_right (r : AnchorRect) :
    evaluateAnchorSide .left r ≤ evaluateAnchorSide .right r := by
  dsimp [evaluateAnchorSide]
  omega

/-- Law: Lookup in an empty anchor map always yields none.
    CSS Anchor Positioning 1 §3.1. -/
theorem anchor_lookup_empty (name : String) :
    lookupAnchor [] name = none := by
  rfl

/-- Apply CSS translation transform to an anchor rectangle.
    CSS Transforms 1 §2, CSS Anchor Positioning 1 §3.1. -/
def transformAnchor (r : AnchorRect) (dx dy : Nat) : AnchorRect :=
  ⟨r.x + dx, r.y + dy, r.w, r.h⟩

/-- Scroll position invariance: scrolling a scroll container does not shift anchor geometry
    in the anchor map relative to the scroll container's content box.
    CSS Anchor Positioning 1 §3.1. -/
def scrollAnchor (r : AnchorRect) (_scrollX _scrollY : Nat) : AnchorRect :=
  r

/-- Whether a fragment or frame view has a running anchor transform animation.
    CSS Anchor Positioning 1 §3.1. -/
def hasRunningAnchorTransformAnimation (isAnimating : Bool := false) : Bool :=
  isAnimating

/-- Law: Transform preserves anchor width and height.
    CSS Transforms 1 §2. -/
theorem transform_preserves_size (r : AnchorRect) (dx dy : Nat) :
    (transformAnchor r dx dy).w = r.w ∧ (transformAnchor r dx dy).h = r.h := by
  dsimp [transformAnchor]
  exact ⟨rfl, rfl⟩

/-- Law: Transform shifts x and y by dx and dy.
    CSS Transforms 1 §2. -/
theorem transform_shifts_pos (r : AnchorRect) (dx dy : Nat) :
    (transformAnchor r dx dy).x = r.x + dx ∧ (transformAnchor r dx dy).y = r.y + dy := by
  dsimp [transformAnchor]
  exact ⟨rfl, rfl⟩

/-- Law: Anchor geometry in anchor map is invariant under scroll offset.
    CSS Anchor Positioning 1 §3.1. -/
theorem scroll_invariant (r : AnchorRect) (sx sy : Nat) :
    scrollAnchor r sx sy = r := by
  rfl

/-- Law: Identity translation leaves anchor rectangle unchanged.
    CSS Transforms 1 §2. -/
theorem transform_zero_id (r : AnchorRect) :
    transformAnchor r 0 0 = r := by
  cases r
  rfl

/-- Law: In the absence of active animations, hasRunningAnchorTransformAnimation is false.
    CSS Anchor Positioning 1 §3.1. -/
theorem no_running_anchor_transform_animation :
    hasRunningAnchorTransformAnimation false = false := by
  rfl

end OutOfFlowAnchor
end ChromiumLayout
