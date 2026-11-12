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

/-- `WidthAvailableToChildrenChanged`: with overflow the item is `150 - scrollbar` wide
    (any scrollbar width `sb`), without `overflow-y:auto` it is 150. -/
theorem WidthAvailableToChildrenChanged_vectors (sb : Nat) :
    childInlineSize 150 sb true 100 120 = 150 - sb ∧
    childInlineSize 150 sb false 100 120 = 150 := by
  simp [childInlineSize, needsVerticalScrollbar, needsScrollbarAlong]

end TestsBlock
end ChromiumLayout
