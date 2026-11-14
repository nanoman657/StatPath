/-
  Vectors transcribed from layout_block_test.cc.
-/
import BlockOverflow
import BlockScroll

namespace ChromiumLayout
namespace TestsBlock
open BlockFlow BlockOverflow

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

-- layout_block_test.cc:101: ContainmentStyleChange
-- CSS Containment Module Level 2 §3.4, §3.5.
-- contain: strict creates a containing block for fixed-position objects (HasOutOfFlowFragmentChild = true);
-- contain: style does not (HasOutOfFlowFragmentChild = false, delegated to LayoutView).
theorem ContainmentStyleChange_vectors :
    isFixedPosContainingBlock .strict = true ∧
    isFixedPosContainingBlock .style = false := by
  decide

-- layout_block_test.cc:73: NestedInlineVisualOverflow
-- CSS Overflow 3 §2.1. Child image with negative margin creates visual overflow beyond 0x0 block.
theorem NestedInlineVisualOverflow_vectors :
    visualOverflowWithChild ⟨0, 0, 0, 0⟩ ⟨-15, 0, 40, 40⟩ = ⟨-15, 0, 40, 40⟩ := by
  decide

-- layout_block_test.cc:86: NestedInlineVisualOverflowVerticalRL
-- CSS Overflow 3 §2.1, CSS Writing Modes 3 §6.4. Visual overflow in vertical-rl with negative right margin.
theorem NestedInlineVisualOverflowVerticalRL_vectors :
    visualOverflowWithChild ⟨0, 0, 0, 0⟩ ⟨-25, 0, 40, 40⟩ = ⟨-25, 0, 40, 40⟩ := by
  decide

end TestsBlock
end ChromiumLayout
