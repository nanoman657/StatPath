/-
  Vectors transcribed from layout_block_test.cc.
-/
import BlockScroll
import OutOfFlowCB

namespace ChromiumLayout
namespace TestsBlock
open BlockFlow OutOfFlowCB

/-- The scroller of `WidthAvailableToChildrenChanged` (line 28): `overflow-y:auto; width:150px;
    height:100px` with six 20px items. -/
def scroller : BF :=
  { id := 0, width := .px 150, height := some 100, children :=
    (List.range 6).map (fun i => { id := i + 1, height := some 20 }) }

theorem scroller_content_height :
    let f := layoutRoot 800 scroller
    extent fuel f - f.y = 120 := by decide

/-- `WidthAvailableToChildrenChanged`: with overflow the item is `150 - scrollbar` wide
    (any scrollbar width `sb`), without `overflow-y:auto` it is 150. -/
theorem WidthAvailableToChildrenChanged_vectors (sb : Nat) :
    childInlineSize 150 sb true 100 120 = 150 - sb ∧
    childInlineSize 150 sb false 100 120 = 150 := by
  simp [childInlineSize, needsVerticalScrollbar]

/-- `ContainmentStyleChange` (line 101): `#target{contain:strict}` is the containing block of the
    `position:fixed` box (ancestors nearest first: div, div, target, ...); with `contain:style`
    the containing block is the viewport. -/
theorem ContainmentStyleChange_vectors :
    fixedContainingBlock [false, false, true, false, false] = some 2 ∧
    fixedContainingBlock [false, false, false, false, false] = none := by decide

end TestsBlock
end ChromiumLayout
