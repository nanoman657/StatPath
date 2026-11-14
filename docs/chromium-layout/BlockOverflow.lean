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

/-- 2D integer physical rectangle with signed offset and size.
    CSS Box Model §4, CSS Overflow 3 §2.1. -/
structure PhysicalRect where
  x : Int := 0
  y : Int := 0
  w : Int := 0
  h : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Strut or edge insets/outsets along four edges: top, right, bottom, left.
    CSS Box Model §4. -/
structure BoxEdges where
  top : Int := 0
  right : Int := 0
  bottom : Int := 0
  left : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Expand physical rect edges outward by top, right, bottom, left amounts.
    CSS Box Model §4, CSS Overflow 3 §2.1. -/
def expandEdges (r : PhysicalRect) (e : BoxEdges) : PhysicalRect :=
  ⟨r.x - e.left, r.y - e.top, r.w + e.left + e.right, r.h + e.top + e.bottom⟩

/-- Uniform edge expansion (e.g. outline width or blur filter extent on all sides).
    CSS Basic User Interface 3 §7.1, CSS 2.1 §18.4. -/
def uniformEdges (amt : Int) : BoxEdges :=
  ⟨amt, amt, amt, amt⟩

/-- Self visual overflow rect of a box given its border box rect and outline width.
    CSS Basic User Interface 3 §7.1, CSS 2.1 §18.4.
    An outline expands the visual overflow rectangle by the outline width on all 4 sides. -/
def outlineVisualOverflow (borderBox : PhysicalRect) (outlineWidth : Int) : PhysicalRect :=
  expandEdges borderBox (uniformEdges outlineWidth)

/-- Mask clipping of visual overflow rect.
    CSS Masking 1 §3.
    A mask clips visual overflow to the mask box (border box expanded by mask-box-image outsets). -/
def maskVisualOverflow (borderBox : PhysicalRect) (outset : BoxEdges) : PhysicalRect :=
  expandEdges borderBox outset

/-- Box shadow visual overflow rect from border box. When shadow is none/initial, returns border box.
    CSS Backgrounds and Borders 3 §7.1. -/
def shadowVisualOverflow (borderBox : PhysicalRect) (hasShadow : Bool) (shadowOutset : BoxEdges) : PhysicalRect :=
  if hasShadow then expandEdges borderBox shadowOutset else borderBox

/-- Filter blur outset extent (3 * blur-radius * zoom).
    CSS Filter Effects 1 §5. -/
def filterBlurOutset (radius zoom : Int) : Int :=
  3 * radius * zoom

/-- Filtered visual overflow rect given unfiltered visual overflow and blur filter parameters.
    CSS Filter Effects 1 §5. -/
def filterVisualOverflow (unfiltered : PhysicalRect) (radius zoom : Int) : PhysicalRect :=
  expandEdges unfiltered (uniformEdges (filterBlurOutset radius zoom))

/-- Table border box rect from content box rect and outer collapsed border half-widths.
    CSS 2.1 §17.6, §17.6.2.
    Half of the outer collapsed border widths extend outside the table grid / content edge. -/
def tableCollapsedBorderBox (contentBox : PhysicalRect) (topHalf rightHalf bottomHalf leftHalf : Int) : PhysicalRect :=
  expandEdges contentBox ⟨topHalf, rightHalf, bottomHalf, leftHalf⟩

/-- Law: Outline expands width and height monotonically for any non-negative outline width.
    CSS Basic User Interface 3 §7.1. -/
theorem outline_expands_size (r : PhysicalRect) (w : Int) (hw : w ≥ 0) :
    (outlineVisualOverflow r w).w ≥ r.w ∧ (outlineVisualOverflow r w).h ≥ r.h := by
  dsimp [outlineVisualOverflow, expandEdges, uniformEdges]
  omega

/-- Law: Outline shifts top-left origin outward for any non-negative outline width.
    CSS Basic User Interface 3 §7.1. -/
theorem outline_shifts_origin (r : PhysicalRect) (w : Int) (hw : w ≥ 0) :
    (outlineVisualOverflow r w).x ≤ r.x ∧ (outlineVisualOverflow r w).y ≤ r.y := by
  dsimp [outlineVisualOverflow, expandEdges, uniformEdges]
  omega

/-- Law: Removing box-shadow (initial/none) resets visual overflow back to border box.
    CSS Backgrounds and Borders 3 §7.1. -/
theorem shadow_initial_clears (bb : PhysicalRect) (outset : BoxEdges) :
    shadowVisualOverflow bb false outset = bb := by
  rfl

/-- Law: A mask with zero outsets clips visual overflow exactly to the border box.
    CSS Masking 1 §3. -/
theorem mask_zero_outset_eq_border_box (bb : PhysicalRect) :
    maskVisualOverflow bb ⟨0, 0, 0, 0⟩ = bb := by
  cases bb
  dsimp [maskVisualOverflow, expandEdges]
  simp

/-- Law: Collapsed border box dimensions are bounded below by content box dimensions.
    CSS 2.1 §17.6. -/
theorem table_border_box_ge_content (cb : PhysicalRect) (t r b l : Int)
    (ht : t ≥ 0) (hr : r ≥ 0) (hb : b ≥ 0) (hl : l ≥ 0) :
    (tableCollapsedBorderBox cb t r b l).w ≥ cb.w ∧
    (tableCollapsedBorderBox cb t r b l).h ≥ cb.h := by
  dsimp [tableCollapsedBorderBox, expandEdges]
  omega

/-- Law: Filter blur outset is non-negative for non-negative radius and zoom.
    CSS Filter Effects 1 §5. -/
theorem filter_blur_outset_nonneg (r z : Int) (hr : r ≥ 0) (hz : z ≥ 0) :
    filterBlurOutset r z ≥ 0 := by
  dsimp [filterBlurOutset]
  have h3 : (3 : Int) ≥ 0 := by decide
  have h3r : 3 * r ≥ 0 := Int.mul_nonneg h3 hr
  exact Int.mul_nonneg h3r hz

/-- Whether an element scrolls overflow.
    CSS Overflow Module Level 3 §3. -/
def scrollsOverflow (o : OverflowValue) : Bool :=
  o == .auto || o == .scroll

/-- Whether an element is user-scrollable.
    CSS Overflow Module Level 3 §3.
    An element is user-scrollable if it scrolls overflow and content exceeds container size. -/
def isUserScrollable (o : OverflowValue) (containerSize contentSize : Nat) : Bool :=
  scrollsOverflow o && contentSize > containerSize

/-- Whether an element is fixed to the view (viewport).
    CSS Positioned Layout 3 §2.2, CSS Transforms 1 §2.
    A fixed-position element is fixed to the view unless an ancestor has a transform
    (which establishes a containing block for fixed-position descendants). -/
def isFixedToView (isFixed : Bool) (hasTransformAncestor : Bool) : Bool :=
  isFixed && !hasTransformAncestor

/-- Minimum inline size for empty form controls (select, file input, marquee).
    CSS Box Model 3 §4, CSS Sizing 3 §5.1. -/
def controlMinContentInlineSize (border : Nat) : Nat :=
  2 * border

/-- Union of parent border box rect and child visual overflow rect.
    CSS Overflow 3 §2.1. -/
def visualOverflowWithChild (parent : PhysicalRect) (child : PhysicalRect) : PhysicalRect :=
  let minX := min parent.x child.x
  let minY := min parent.y child.y
  let maxX := max (parent.x + parent.w) (child.x + child.w)
  let maxY := max (parent.y + parent.h) (child.y + child.h)
  ⟨minX, minY, maxX - minX, maxY - minY⟩

/-- Law: Hidden overflow never scrolls overflow.
    CSS Overflow Module Level 3 §3. -/
theorem scrolls_overflow_hidden : scrollsOverflow .hidden = false := rfl

/-- Law: Auto overflow scrolls overflow.
    CSS Overflow Module Level 3 §3. -/
theorem scrolls_overflow_auto : scrollsOverflow .auto = true := rfl

/-- Law: An element is user-scrollable only if content strictly exceeds container size.
    CSS Overflow Module Level 3 §3. -/
theorem user_scrollable_implies_overflow (o : OverflowValue) (sz c : Nat)
    (h : isUserScrollable o sz c = true) : c > sz := by
  dsimp [isUserScrollable] at h
  cases hsc : scrollsOverflow o <;> simp [hsc] at h
  exact h

/-- Law: Transform on ancestor prevents an element from being fixed to view.
    CSS Transforms 1 §2, CSS Positioned Layout 3 §2.2. -/
theorem transform_cb_not_fixed_to_view (isFixed : Bool) :
    isFixedToView isFixed true = false := by
  dsimp [isFixedToView]
  cases isFixed <;> rfl

/-- Law: Without transform ancestor, fixed-to-view corresponds to fixed positioning.
    CSS Positioned Layout 3 §2.2. -/
theorem fixed_to_view_no_transform (isFixed : Bool) :
    isFixedToView isFixed false = isFixed := by
  dsimp [isFixedToView]
  cases isFixed <;> rfl

/-- Law: Form control minimum inline size equals twice the border.
    CSS Box Model 3 §4, CSS Sizing 3 §5.1. -/
theorem control_min_size_eq (b : Nat) :
    controlMinContentInlineSize b = 2 * b := rfl

/-- Law: Child visual overflow expansion never moves the parent origin rightward or downward.
    CSS Overflow 3 §2.1. -/
theorem child_visual_overflow_origin (p c : PhysicalRect) :
    (visualOverflowWithChild p c).x ≤ p.x ∧ (visualOverflowWithChild p c).y ≤ p.y := by
  dsimp [visualOverflowWithChild]
  omega

end BlockOverflow
end ChromiumLayout
