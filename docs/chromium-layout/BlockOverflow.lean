/-
  BlockOverflow.lean: CSS Overflow and Containment layout rules (CSS Overflow 3 §3, §4, CSS Containment 2 §3.3).
  Formalizes overflow clipping, scroll container establishment, overflow-clip-margin expansion,
  and paint containment formatting context creation. Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockOverflow

/-- CSS `overflow` keyword values. CSS Overflow Module Level 3 §3.1. -/
inductive OverflowValue where
  | visible
  | hidden
  | clip
  | scroll
  | auto
  deriving DecidableEq, Repr, Inhabited

/-- Axis-aligned 2D integer rectangle. -/
structure Rect where
  x : Nat := 0
  y : Nat := 0
  w : Nat := 0
  h : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Whether an element establishes a scroll container.
    CSS Overflow Module Level 3 §3 Scroll Containers.
    `clip` does not create a scroll container; `hidden`, `scroll`, and `auto` do. -/
def isScrollContainer (ox oy : OverflowValue) : Bool :=
  (ox == .scroll || ox == .auto || ox == .hidden) ||
  (oy == .scroll || oy == .auto || oy == .hidden)

/-- Whether overflow is clipped along an axis.
    CSS Overflow Module Level 3 §3.1, CSS Containment Level 2 §3.3. -/
def clipsAxis (v : OverflowValue) (containPaint : Bool) : Bool :=
  containPaint || v == .clip || v == .hidden || v == .scroll

/-- Whether an element creates a new formatting context.
    CSS 2.1 §9.4.1, CSS Containment Level 2 §3.3. -/
def createsNewFormattingContext (ox oy : OverflowValue) (containPaint : Bool) : Bool :=
  containPaint || ox != .visible || oy != .visible

/-- Whether an element can act as a containing block for fixed-position objects.
    CSS Containment Level 2 §3.3 Paint Containment. -/
def canContainFixedPositionObjects (containPaint : Bool) : Bool :=
  containPaint

/-- CSS Containment keyword values. CSS Containment Module Level 2 §3. -/
inductive Containment where
  | none
  | strict
  | content
  | paint
  | layout
  | size
  | style
  deriving DecidableEq, Repr, Inhabited

/-- Whether containment establishes a containing block for fixed-position descendants.
    CSS Containment Module Level 2 §3.2, §3.3, §3.5.
    `strict`, `content`, `paint`, and `layout` act as containing block for fixed-pos.
    `style` and `size` do not. -/
def isFixedPosContainingBlock (c : Containment) : Bool :=
  c == .strict || c == .content || c == .paint || c == .layout

/-- Inner clipping rect for form controls with symmetric border.
    CSS Overflow Module Level 3 §3.1, HTML §4.10. -/
def controlInnerClipRect (w h border : Nat) : Rect :=
  ⟨border, border, w - 2 * border, h - 2 * border⟩

/-- Visual overflow dimension along a single axis given parent size, child overflow size,
    clip margin, and whether the axis is clipped.
    CSS Overflow Module Level 3 §3.1, §4, CSS Containment Level 2 §3.3. -/
def visualOverflowAxis (parentSize childSize clipMargin : Nat) (isClipped : Bool) : Nat :=
  if isClipped then
    Nat.max parentSize (Nat.min childSize (parentSize + clipMargin))
  else
    Nat.max parentSize childSize

/-- Visual overflow rect of a box given its border-box size, child overflow size,
    overflow properties, paint containment, and overflow-clip-margin.
    CSS Overflow Module Level 3 §3.1, §4, CSS Containment Level 2 §3.3. -/
def visualOverflowRect (parentW parentH childW childH clipMargin : Nat)
    (ox oy : OverflowValue) (containPaint : Bool) : Rect :=
  let clipX := clipsAxis ox containPaint
  let clipY := clipsAxis oy containPaint
  let vw := visualOverflowAxis parentW childW clipMargin clipX
  let vh := visualOverflowAxis parentH childH clipMargin clipY
  ⟨0, 0, vw, vh⟩

/-- Law: An unclipped axis allows visual overflow to expand to the child size.
    CSS Overflow Module Level 3 §3.1. -/
theorem visual_overflow_unclipped_ge_child (pw cw m : Nat) :
    visualOverflowAxis pw cw m false ≥ cw := by
  dsimp [visualOverflowAxis]
  exact Nat.le_max_right pw cw

/-- Law: A clipped axis bounds visual overflow within the element's box plus clip margin.
    CSS Overflow Module Level 3 §3.1, §4. -/
theorem visual_overflow_clipped_le_bound (pw cw m : Nat) :
    visualOverflowAxis pw cw m true ≤ pw + m := by
  dsimp [visualOverflowAxis]
  exact Nat.max_le.2 ⟨Nat.le_add_right pw m, Nat.min_le_right cw (pw + m)⟩

/-- Law: Paint containment always clips overflow along both axes.
    CSS Containment Module Level 2 §3.3. -/
theorem contain_paint_clips_both (ox oy : OverflowValue) :
    clipsAxis ox true = true ∧ clipsAxis oy true = true := by
  dsimp [clipsAxis]
  exact ⟨rfl, rfl⟩

/-- Law: Paint containment always establishes an independent formatting context.
    CSS Containment Module Level 2 §3.3. -/
theorem contain_paint_creates_nfc (ox oy : OverflowValue) :
    createsNewFormattingContext ox oy true = true := by
  dsimp [createsNewFormattingContext]
  rfl

/-- Law: Strict containment establishes a containing block for fixed-position elements.
    CSS Containment Module Level 2 §3.5. -/
theorem contain_strict_fixed_pos : isFixedPosContainingBlock .strict = true := by
  rfl

/-- Law: Style containment never establishes a containing block for fixed-position elements.
    CSS Containment Module Level 2 §3.4. -/
theorem contain_style_not_fixed_pos : isFixedPosContainingBlock .style = false := by
  rfl

/-- Law: Control inner clip rect width and height plus borders reconstruct outer dimensions.
    CSS Overflow Module Level 3 §3.1. -/
theorem control_clip_rect_bounds (w h b : Nat) (hw : 2 * b ≤ w) (hh : 2 * b ≤ h) :
    (controlInnerClipRect w h b).w + 2 * b = w ∧ (controlInnerClipRect w h b).h + 2 * b = h := by
  dsimp [controlInnerClipRect]
  omega

end BlockOverflow
end ChromiumLayout
