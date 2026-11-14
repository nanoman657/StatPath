/-
  BlockScroll.lean: scrollbar gutter effect on children's inline size and child physical
  location under container scrollbars and writing modes.
  Written from CSS 2.1 §8.1 (Box dimensions), §9.2 (Controlling display type),
  §9.4.3 (Relative positioning), §9.5.1 (Floats), §10.1 (Containing block),
  §10.3.7 / §10.6.4 (Absolute positioning), §11.1 (Overflow),
  and CSS Writing Modes Level 3 §6.4 (Abstract-to-Physical Mappings), §7.3.
  Checked against layout_block_test.cc (`WidthAvailableToChildrenChanged`) and
  layout_box_test.cc (`LocationOf*ChildWithContainerScrollbars*`).
  Owned by the block lane.
-/
import BlockFlow
import BlockFragmentation
import BlockWritingMode

namespace ChromiumLayout
namespace BlockScroll

open BlockWritingMode

/-- A box with `overflow-y:auto` shows a vertical scrollbar exactly when its content is taller than
    its content box (layout_block_test.cc:28 `WidthAvailableToChildrenChanged`: 6 x 20px items in a
    100px box). -/
def needsVerticalScrollbar (overflowAuto : Bool) (boxH contentH : Nat) : Bool :=
  overflowAuto && decide (boxH < contentH)

/-- Inline size available to block children: the box's content width minus the scrollbar gutter
    when a vertical scrollbar is shown (layout_block_test.cc:28). `sb` is the platform's
    scrollbar width; the test only compares against `ComputeScrollbars().HorizontalSum()`. -/
def childInlineSize (boxW sb : Nat) (overflowAuto : Bool) (boxH contentH : Nat) : Nat :=
  if needsVerticalScrollbar overflowAuto boxH contentH then boxW - sb else boxW

/-- Text direction: left-to-right or right-to-left.
    CSS Writing Modes Level 3 §3.1, CSS 2.1 §9.2. -/
inductive Direction where
  | ltr
  | rtl
  deriving DecidableEq, Repr

/-- Container scrollbars geometry: vertical and horizontal scrollbar dimensions.
    CSS 2.1 §11.1, CSS Writing Modes Level 3 §7.3. -/
structure ContainerScrollbars where
  vWidth : Nat := 0
  hHeight : Nat := 0
  deriving DecidableEq, Repr

/-- Container box geometry: writing mode, direction, border, padding, content size, and scrollbars.
    CSS 2.1 §8.1, §10.1, §11.1, CSS Writing Modes Level 3 §6.4. -/
structure ContainerBox where
  wm : WritingMode := .horizontalTb
  dir : Direction := .ltr
  border : Phys
  padding : Phys
  contentWidth : Nat
  contentHeight : Nat
  scrollbars : ContainerScrollbars := {}
  deriving DecidableEq, Repr

/-- Total border box width. CSS 2.1 §8.1. -/
def totalWidth (c : ContainerBox) : Nat :=
  c.border.left + c.padding.left + c.contentWidth + c.padding.right + c.border.right

/-- Total border box height. CSS 2.1 §8.1. -/
def totalHeight (c : ContainerBox) : Nat :=
  c.border.top + c.padding.top + c.contentHeight + c.padding.bottom + c.border.bottom

/-- Left offset of container's padding box due to scrollbars.
    In horizontal-tb RTL, vertical scrollbar is placed on the left edge.
    CSS Writing Modes Level 3 §7.3, CSS 2.1 §11.1. -/
def scrollbarLeft (c : ContainerBox) : Nat :=
  match c.wm, c.dir with
  | .horizontalTb, .rtl => c.scrollbars.vWidth
  | _, _ => 0

/-- Top-left origin (x, y) of the containing block for absolute children (padding box).
    CSS 2.1 §10.1. -/
def paddingBoxOrigin (c : ContainerBox) : Nat × Nat :=
  (c.border.left + scrollbarLeft c, c.border.top)

/-- Location of an absolute positioned child with explicit top and left insets.
    CSS 2.1 §10.1, §10.3.7, §10.6.4. -/
def absoluteChildLocation (c : ContainerBox) (left top : Nat) : Nat × Nat :=
  let (ox, oy) := paddingBoxOrigin c
  (ox + left, oy + top)

/-- Location of an absolute positioned child with auto top and left (static position).
    CSS 2.1 §10.3.7, §10.6.4, CSS Writing Modes Level 3 §6.4. -/
def absoluteAutoLocation (c : ContainerBox) (childW childH : Nat) : Nat × Nat :=
  let x := match c.wm, c.dir with
    | .horizontalTb, .ltr => c.border.left + c.padding.left
    | .verticalLr, .ltr => c.border.left + c.padding.left
    | .verticalRl, .ltr => totalWidth c - (c.border.right + c.padding.right + c.scrollbars.vWidth) - childW
    | .horizontalTb, .rtl => totalWidth c - (c.border.right + c.padding.right) - childW
    | .verticalLr, .rtl => c.border.left + c.padding.left
    | .verticalRl, .rtl => totalWidth c - (c.border.right + c.padding.right + c.scrollbars.vWidth) - childW
  let y := match c.wm, c.dir with
    | .verticalLr, .rtl => totalHeight c - (c.border.bottom + c.padding.bottom + c.scrollbars.hHeight) - childH
    | .verticalRl, .rtl => totalHeight c - (c.border.bottom + c.padding.bottom + c.scrollbars.hHeight) - childH
    | _, _ => c.border.top + c.padding.top
  (x, y)

/-- Location of an in-flow child with preceding sibling block offset.
    CSS 2.1 §9.2, CSS Writing Modes Level 3 §6.4. -/
def inFlowChildLocation (c : ContainerBox) (childW childH : Nat) (offsetW offsetH : Nat) : Nat × Nat :=
  let (baseX, baseY) := absoluteAutoLocation c childW childH
  match c.wm with
  | .horizontalTb => (baseX, baseY + offsetH)
  | .verticalLr => (baseX + offsetW, baseY)
  | .verticalRl => (baseX - offsetW, baseY)

/-- Location of a relative positioned child: in-flow position shifted by relative insets.
    CSS 2.1 §9.4.3. -/
def relativeChildLocation (c : ContainerBox) (childW childH : Nat) (offsetW offsetH : Nat)
    (relLeft relTop : Nat) : Nat × Nat :=
  let (ix, iy) := inFlowChildLocation c childW childH offsetW offsetH
  (ix + relLeft, iy + relTop)

/-- Location of a float: left child.
    In horizontal-tb RTL, floats to the left edge of the content box after scrollbar.
    CSS 2.1 §9.5.1, CSS Writing Modes Level 3 §6.4. -/
def floatLeftChildLocation (c : ContainerBox) (childW childH : Nat) : Nat × Nat :=
  match c.wm, c.dir with
  | .horizontalTb, .rtl => (c.border.left + scrollbarLeft c + c.padding.left, c.border.top + c.padding.top)
  | _, _ => absoluteAutoLocation c childW childH

/-- Law: Absolute child location shifts padding box origin by left and top insets.
    CSS 2.1 §10.1. -/
theorem abs_loc_eq_origin_add (c : ContainerBox) (l t : Nat) :
    absoluteChildLocation c l t = (c.border.left + scrollbarLeft c + l, c.border.top + t) := by
  dsimp [absoluteChildLocation, paddingBoxOrigin]

/-- Law: Non-RTL horizontal mode has zero scrollbar left offset.
    CSS 2.1 §11.1. -/
theorem scrollbar_left_zero (c : ContainerBox) (h : c.dir = .ltr) :
    scrollbarLeft c = 0 := by
  dsimp [scrollbarLeft]
  rw [h]
  cases c.wm <;> rfl

/-- Law: Relative child location shifts in-flow location by relative offsets.
    CSS 2.1 §9.4.3. -/
theorem rel_loc_eq_inflow_add (c : ContainerBox) (cw ch ow oh rl rt : Nat) :
    relativeChildLocation c cw ch ow oh rl rt =
    let (ix, iy) := inFlowChildLocation c cw ch ow oh
    (ix + rl, iy + rt) := by
  rfl

end BlockScroll

namespace BlockFlow
export BlockScroll (needsVerticalScrollbar childInlineSize)
end BlockFlow

end ChromiumLayout
