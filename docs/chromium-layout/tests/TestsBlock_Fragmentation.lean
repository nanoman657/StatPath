import BlockFlow
import BlockFragmentation
import ColumnWidth

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow ColumnWidth

-- fragmentation_test.cc:25: MultipleFragments
-- Multicolumn with columns: 3; width: 620px; column-gap: 10px; height: 100px;
-- outer1 (150px) contains inner1 (250px) and inner2 (10px). outer2 is 90px.
def mf_col_width : Nat := usedWidth 3 0 10 620

theorem MultipleFragments_vectors :
    mf_col_width = 200 ∧
    -- outer1 slices: 100, 50, 0
    sliceSize 100 0 150 0 = 100 ∧
    sliceSize 100 0 150 1 = 50 ∧
    sliceSize 100 0 150 2 = 0 ∧
    -- inner1 slices: 100, 100, 50
    sliceSize 100 0 250 0 = 100 ∧
    sliceSize 100 0 250 1 = 100 ∧
    sliceSize 100 0 250 2 = 50 ∧
    -- inner2 slices: 0 in col 0 and 1, 10 in col 2 (starts at 250)
    sliceSize 100 250 10 0 = 0 ∧
    sliceSize 100 250 10 1 = 0 ∧
    sliceSize 100 250 10 2 = 10 ∧
    -- outer2 slices: 0 in col 0, 50 in col 1, 40 in col 2 (starts at 150)
    sliceSize 100 150 90 0 = 0 ∧
    sliceSize 100 150 90 1 = 50 ∧
    sliceSize 100 150 90 2 = 40 := by
  decide

-- fragmentation_test.cc:345: ConsumedBlockSizeOverflowInflow
def cbs_tree : BF :=
  { id := 0, height := some 150, children := [
    { id := 1, height := some 333 }
  ] }

theorem ConsumedBlockSizeOverflowInflow_vectors :
    let f := layoutRoot 1000 cbs_tree
    hasBreakToken 100 f 0 = true ∧ consumedBlockSize 100 0 = 100 ∧
    hasBreakToken 100 f 1 = true ∧ consumedBlockSize 100 1 = 200 ∧
    hasBreakToken 100 f 2 = true ∧ consumedBlockSize 100 2 = 300 ∧
    hasBreakToken 100 f 3 = false := by
  decide

end TestsBlock
end ChromiumLayout
