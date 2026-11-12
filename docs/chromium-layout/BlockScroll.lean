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

/-- A box with `overflow-y:auto` shows a vertical scrollbar exactly when its content is taller than
    its content box (layout_block_test.cc:28 `WidthAvailableToChildrenChanged`: 6 x 20px items in a
    100px box). -/
def needsVerticalScrollbar (overflowAuto : Bool) (boxH contentH : Nat) : Bool :=
  needsScrollbarAlong overflowAuto boxH contentH

/-- Inline size available to block children: the box's content width minus the scrollbar gutter
    when a vertical scrollbar is shown (layout_block_test.cc:28). `sb` is the platform's
    scrollbar width; the test only compares against `ComputeScrollbars().HorizontalSum()`. -/
def childInlineSize (boxW sb : Nat) (overflowAuto : Bool) (boxH contentH : Nat) : Nat :=
  if needsVerticalScrollbar overflowAuto boxH contentH then boxW - sb else boxW

end BlockFlow
end ChromiumLayout
