import BlockFlow
import BlockFragmentation
import BlockWritingMode
import ColumnWidth

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow BlockWritingMode ColumnWidth

-- layout_box_test.cc:2045: ContentBoxFragmentedVlr
-- In vertical-lr, block-size maps to physical width and inline-size to physical height.
-- CSS Writing Modes Level 3 §6.4, CSS 2.1 §8.1.
theorem ContentBoxFragmentedVlr_vectors :
    let border : Phys := ⟨1, 2, 3, 4⟩
    let padding : Phys := ⟨5, 10, 15, 20⟩
    physicalContentBox .verticalLr border padding 50 200 = (24, 6, 200, 50) := by
  decide

-- layout_box_test.cc:2057: ContentBoxFragmentedVrl
-- In vertical-rl, block-size maps to physical width and inline-size to physical height.
-- CSS Writing Modes Level 3 §6.4, CSS 2.1 §8.1.
theorem ContentBoxFragmentedVrl_vectors :
    let border : Phys := ⟨1, 2, 3, 4⟩
    let padding : Phys := ⟨5, 10, 15, 20⟩
    physicalContentBox .verticalRl border padding 50 200 = (24, 6, 200, 50) := by
  decide

-- layout_box_test.cc:2069: StitchedBlockSize
-- Multicolumn with column block size 100px.
-- outer (90px), middle (100px), inner (350px).
-- Stitched block size equals the unfragmented border-box block size.
theorem StitchedBlockSize_vectors :
    sliceTotal 100 0 90 1 = 90 ∧
    sliceTotal 100 0 100 1 = 100 ∧
    sliceTotal 100 0 350 4 = 350 := by
  decide

-- layout_box_test.cc:2087: StitchedBlockSizeVrl
-- Multicolumn with column block size 100px in vertical-rl writing mode.
-- Stitched block size is invariant under writing mode.
-- CSS Writing Modes Level 3 §6.1, CSS Fragmentation 3 §2.
theorem StitchedBlockSizeVrl_vectors :
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

-- layout_box_test.cc:2143: StitchedSizeAfterRelayout
-- In multicolumn with column width 100px (300px / 3 columns), content requires ceil(height / F) slices
-- and stitched size equals (colWidth, unfragmented height).
-- CSS Fragmentation Level 3 §2.
theorem StitchedSizeAfterRelayout_vectors :
    let F := 100
    let colW := usedWidth 3 0 0 300
    -- height 250px -> 3 fragments, stitched size (100, 250)
    sliceCount F 250 = 3 ∧ (colW, sliceTotal F 0 250 3) = (100, 250) ∧
    -- height 50px -> 1 fragment, stitched size (100, 50)
    sliceCount F 50 = 1 ∧ (colW, sliceTotal F 0 50 1) = (100, 50) ∧
    -- height 150px -> 2 fragments, stitched size (100, 150)
    sliceCount F 150 = 2 ∧ (colW, sliceTotal F 0 150 2) = (100, 150) := by
  decide

end TestsBlock
end ChromiumLayout
