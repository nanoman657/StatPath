/-
  BlockScroll.lean: scrollbar gutter effect on children's inline size, written from
  layout_block_test.cc (`WidthAvailableToChildrenChanged`). Owned by the block lane.
-/
import BlockFlow
import BlockFragmentation

namespace ChromiumLayout
namespace BlockFlow

/-- A scrollable box shows a scrollbar along one axis exactly when its content is larger than its
    box on that axis. The rule compares the two sizes on the same axis only; a scrollbar on the
    other axis that shrinks the box is not modelled. -/
def needsScrollbarAlong (overflowAuto : Bool) (boxSize contentSize : Nat) : Bool :=
  overflowAuto && decide (boxSize < contentSize)

/-- Width a `scrollbar-gutter` reserves on one inline edge (CSS Overflow 3). Overlay scrollbars
    take no space. A classic scrollbar of width `sb` is reserved by `stable` even when nothing
    overflows, and by `auto` only while a scrollbar is shown. -/
def gutterEdge (overlay stable scrollbarShown : Bool) (sb : Nat) : Nat :=
  if overlay || !(stable || scrollbarShown) then 0 else sb

/-- The reserved (inline-start, inline-end) pair. `both-edges` also reserves the inline-start
    edge; otherwise only the inline-end edge is reserved. -/
def gutterInlineEdges (overlay stable bothEdges scrollbarShown : Bool) (sb : Nat) : Nat × Nat :=
  let edge := gutterEdge overlay stable scrollbarShown sb
  ((if bothEdges then edge else 0), edge)

/-- Physical (left, right, top, bottom) reservation of an inline (start, end) pair. The inline
    axis is horizontal in horizontal-tb, where inline-start is left and inline-end is right, and
    vertical in vertical-rl, where inline-start is top and inline-end is bottom. -/
def physicalGutter (vertical : Bool) (edges : Nat × Nat) : Nat × Nat × Nat × Nat :=
  if vertical then (0, 0, edges.1, edges.2) else (edges.1, edges.2, 0, 0)

/-- Padding-box size along the inline axis, from the border-box size and the reserved pair. -/
def paddingInline (boxSize : Nat) (edges : Nat × Nat) : Nat :=
  boxSize - edges.1 - edges.2

end BlockFlow
end ChromiumLayout
