import BlockFlow
import BlockFragmentation
import ColumnWidth

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow ColumnWidth

-- layout_box_test.cc:2069: StitchedBlockSize
-- Multicolumn with column block size 100px.
-- outer (90px), middle (100px), inner (350px).
-- Stitched block size equals the unfragmented border-box block size.
theorem StitchedBlockSize_vectors :
    sliceTotal 100 0 90 1 = 90 ∧
    sliceTotal 100 0 100 1 = 100 ∧
    sliceTotal 100 0 350 4 = 350 := by
  decide

-- layout_box_test.cc:2105: StitchedSizeWithOverflow
-- Multicolumn with inline size 300px, 3 columns, gap 0: column width is 100px.
-- Stitched sizes are (100, 90), (100, 100), (100, 350).
theorem StitchedSizeWithOverflow_vectors :
    let w := usedWidth 3 0 0 300
    (w, sliceTotal 100 0 90 1) = (100, 90) ∧
    (w, sliceTotal 100 0 100 1) = (100, 100) ∧
    (w, sliceTotal 100 0 350 4) = (100, 350) := by
  decide

end TestsBlock
end ChromiumLayout
