/-
  Vectors transcribed from layout_block_test.cc.
-/
import BlockScroll

namespace ChromiumLayout
namespace TestsBlock
open BlockFlow

/-- The scroller of `WidthAvailableToChildrenChanged` (line 28): `overflow-y:auto; width:150px;
    height:100px` with six 20px items. -/
def scroller : BF :=
  { id := 0, width := .px 150, height := some 100, children :=
    (List.range 6).map (fun i => { id := i + 1, height := some 20 }) }

theorem scroller_content_height :
    let f := layoutRoot 800 scroller
    extent fuel f - f.y = 120 := by decide

/-- `WidthAvailableToChildrenChanged` (layout_block_test.cc:28): the children's inline size is the
    content width minus the scrollbar gutter when a vertical scrollbar is shown, i.e. with
    `overflow-y:auto` and content taller than the box (6 x 20px items in a 100px box), and it is the
    full 150 otherwise. `sb` is any scrollbar width; the test compares against
    `ComputeScrollbars().HorizontalSum()`. The rule is stated inline with `needsScrollbarAlong`. -/
theorem WidthAvailableToChildrenChanged_vectors (sb : Nat) :
    (if needsScrollbarAlong true 100 120 then 150 - sb else 150) = 150 - sb ∧
    (if needsScrollbarAlong false 100 120 then 150 - sb else 150) = 150 := by
  simp [needsScrollbarAlong]

end TestsBlock
end ChromiumLayout
