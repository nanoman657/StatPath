import BlockFlow

namespace TestsBlock

open ChromiumLayout.BlockFlow

-- min_max_size_test.cc:13: ShrinkToFit
theorem ShrinkToFit_vectors :
    shrinkToFit 300 100 200 = 200 ∧
    shrinkToFit 200 100 300 = 200 ∧
    shrinkToFit 100 200 300 = 200 := by
  decide

end TestsBlock
