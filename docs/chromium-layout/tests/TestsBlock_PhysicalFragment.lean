import BlockFlow

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow

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
