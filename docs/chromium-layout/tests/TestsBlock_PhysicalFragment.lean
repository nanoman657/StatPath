import BlockFlow
import BlockSticky

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow BlockSticky

-- physical_fragment_test.cc:84: StickyFragmentPropagationTest.StickyAxisEnabled
-- Single-axis scroll container (overflow-y: scroll; overflow-x: clip) consumes vertical sticky
-- and marks horizontal sticky pending. Ancestor scroller (overflow: scroll) consumes pending horizontal.
-- CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3.
theorem StickyAxisEnabled_vectors :
    let innerItems : List StickyItem := [
      ⟨"sticky-y", .vertical⟩,
      ⟨"sticky-x", .horizontal⟩,
      ⟨"sticky-both", .both⟩
    ]
    let innerDescendants := resolveStickyDescendants .vertical innerItems
    let outerItems := propagatePendingSticky innerDescendants
    let outerDescendants := resolveStickyDescendants .both outerItems
    -- inner checks:
    innerDescendants.length = 3 ∧
    innerDescendants[0]!.axes = ⟨.vertical, .none⟩ ∧
    innerDescendants[1]!.axes = ⟨.none, .horizontal⟩ ∧
    innerDescendants[2]!.axes = ⟨.vertical, .horizontal⟩ ∧
    -- outer checks:
    outerDescendants.length = 2 ∧
    outerDescendants[0]!.axes = ⟨.horizontal, .none⟩ ∧
    outerDescendants[1]!.axes = ⟨.horizontal, .none⟩ := by
  decide

-- physical_fragment_test.cc:134: DumpFragmentTreeBasic
-- Input: HTML/body with <div id="block"></div>
def basicDoc : BF := htmlBody [{ id := 2 }]

theorem DumpFragmentTreeBasic_vectors :
    let f := layoutRoot 800 basicDoc
    let body := f.kid 0
    let block := body.kid 0
    body.w = 784 ∧ body.h = 0 ∧
    block.w = 784 ∧ block.h = 0 ∧
    f.relX body = 8 ∧ f.relY body = 8 ∧
    body.relX block = 0 ∧ body.relY block = 0 := by
  decide

end TestsBlock
end ChromiumLayout
