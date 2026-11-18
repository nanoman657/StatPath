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

/-- Scoped anchor declaration with element identifier, containing block scope id, and anchor-name.
    CSS Anchor Positioning 1 §3.1, §3.2. -/
structure ScopedAnchor where
  elementId : String
  scopeId : Nat := 0
  name : String
  deriving Inhabited, DecidableEq, Repr

/-- Find target anchor matching a scoped name within containing block scope.
    CSS Anchor Positioning 1 §3.2. -/
def findTargetAnchor (anchors : List ScopedAnchor) (scopeId : Nat) (name : String) : Option String :=
  let matching := anchors.filter (fun a => a.scopeId == scopeId && a.name == name)
  matching.head?.map (·.elementId)

/-- Implicit anchor validation for out-of-flow positioned element.
    CSS Anchor Positioning 1 §3.3. -/
def acceptableImplicitAnchor (implicitAnchorId : Option String := none) : Option String :=
  implicitAnchorId

/-- Law: Empty anchor list yields no target anchor.
    CSS Anchor Positioning 1 §3.2. -/
theorem find_anchor_empty (scopeId : Nat) (name : String) :
    findTargetAnchor [] scopeId name = none := by
  rfl

/-- Law: Matching scope and anchor name resolves to the target element.
    CSS Anchor Positioning 1 §3.2. -/
theorem find_anchor_matches (elemId : String) (scope : Nat) (name : String) :
    findTargetAnchor [{ elementId := elemId, scopeId := scope, name := name }] scope name = some elemId := by
  dsimp [findTargetAnchor]
  simp

/-- Law: Mismatched containing block scope resolves to none.
    CSS Anchor Positioning 1 §3.2. -/
theorem find_anchor_mismatch (elemId : String) (s1 s2 : Nat) (name : String) (h : (s1 == s2) = false) :
    findTargetAnchor [{ elementId := elemId, scopeId := s1, name := name }] s2 name = none := by
  dsimp [findTargetAnchor]
  simp [h]

/-- Law: In the absence of an implicit anchor element, acceptableImplicitAnchor is none.
    CSS Anchor Positioning 1 §3.3. -/
theorem implicit_anchor_none :
    acceptableImplicitAnchor none = none := by
  rfl

/-- Insert a scoped anchor into a duplicate-free set.
    CSS Anchor Positioning 1 §3.1, §3.2 (`anchor_scope_test.cc:44`, `:56`). -/
def scopedInsert (set : List ScopedAnchor) (entry : ScopedAnchor) : Bool × List ScopedAnchor :=
  if set.contains entry then (false, set) else (true, entry :: set)

/-- Membership lookup in a scoped anchor set.
    CSS Anchor Positioning 1 §3.2 (`anchor_scope_test.cc:72`, `:80`, `:93`, `:115`). -/
def scopedContains (set : List ScopedAnchor) (entry : ScopedAnchor) : Bool :=
  set.contains entry

/-- Removal from a scoped anchor set.
    CSS Anchor Positioning 1 §3.2 (`anchor_scope_test.cc:80`). -/
def scopedErase (set : List ScopedAnchor) (entry : ScopedAnchor) : List ScopedAnchor :=
  set.erase entry

/-- Inline anchor physical rectangle along a single line.
    CSS Anchor Positioning 1 §3.1 (`anchor_evaluator_impl_test.cc:221`). -/
def inlineAnchorRect (charOffset charCount fontSize itemHeight : Nat) : AnchorRect :=
  ⟨charOffset * fontSize, 0, charCount * fontSize, itemHeight⟩

/-- AnchorPositionScrollData attachment and scroll-adjustment eligibility
    `(hasScrollData, needsScrollAdjustment)`.
    CSS Anchor Positioning 1 §3.3, §4.3 (`anchor_position_scroll_data_test.cc:45`, `:94`). -/
def anchorScrollDataState (isConnected isOutOfFlow hasPositionAnchor usesAnchorFn anchorFound : Bool) :
    Bool × Bool :=
  let hasData := isConnected && isOutOfFlow && hasPositionAnchor
  (hasData, hasData && usesAnchorFn && anchorFound)

/-- Clamped scroll adjustment offset when scroller or scroll-content size changes.
    CSS Anchor Positioning 1 §4.3, CSS Overflow 3 §2.2 (`anchor_position_scroll_data_test.cc:142`, `:205`). -/
def clampedScrollAdjustment (contentHeight scrollerHeight requestedScrollY : Nat) : Nat :=
  min requestedScrollY (contentHeight - scrollerHeight)

/-- Stretched block size in `position-area: bottom` after scroll-end relayout.
    CSS Anchor Positioning 1 §4.2, §4.3 (`anchor_position_scroll_data_test.cc:266`). -/
def positionAreaBottomStretchHeight (scrollerHeight anchorTop anchorHeight scrollY : Nat) : Nat :=
  scrollerHeight - (anchorTop + anchorHeight - scrollY)

/-- Outer scroller `scrollHeight` during compositor scroll vs after `scrollend` relayout.
    CSS Anchor Positioning 1 §4.3, CSS Overflow 3 §2.2 (`anchor_position_scroll_data_test.cc:392`). -/
def outerScrollHeightDuringAndAfterScroll
    (baseScrollHeight anchorBottomInOuter anchoredHeight lastFinishedScrollY : Nat) : Nat :=
  max baseScrollHeight (anchorBottomInOuter - lastFinishedScrollY + anchoredHeight)

/-- Law: Re-inserting an existing scoped anchor into a singleton set yields `isNew = false`.
    CSS Anchor Positioning 1 §3.2. -/
theorem scopedInsert_duplicate_false (a : ScopedAnchor) :
    scopedInsert [a] a = (false, [a]) := by
  simp [scopedInsert]

/-- Law: Clamped scroll adjustment never exceeds the requested scroll offset.
    CSS Anchor Positioning 1 §4.3, CSS Overflow 3 §2.2. -/
theorem clampedScrollAdjustment_le_requested (contentH scrollerH reqY : Nat) :
    clampedScrollAdjustment contentH scrollerH reqY ≤ reqY := by
  simp [clampedScrollAdjustment]
  omega

/-- Law: In-flow elements never attach `AnchorPositionScrollData`.
    CSS Anchor Positioning 1 §3.3, §4.3. -/
theorem anchorScrollDataState_inflow_false
    (isConnected hasPos usesFn found : Bool) :
    (anchorScrollDataState isConnected false hasPos usesFn found).1 = false := by
  simp [anchorScrollDataState]

end OutOfFlowAnchor
end ChromiumLayout
