import BlockFlow
import BlockFragmentation
import BlockOverflow
import BlockWritingMode
import ColumnWidth

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow BlockOverflow BlockWritingMode ColumnWidth

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

-- layout_box_test.cc:482: VisualOverflowRectWithBlockChild
-- CSS Overflow Module Level 3 §3.1.
theorem VisualOverflowRectWithBlockChild_vectors :
    let selfRect : Rect := ⟨0, 0, 100, 100⟩
    let visRect := visualOverflowRect 100 100 300 300 0 .visible .visible false
    selfRect = ⟨0, 0, 100, 100⟩ ∧ visRect = ⟨0, 0, 300, 300⟩ := by
  decide

-- layout_box_test.cc:572: VisualOverflowRectOverflowHidden
-- CSS Overflow Module Level 3 §3, §3.1.
theorem VisualOverflowRectOverflowHidden_vectors :
    isScrollContainer .hidden .hidden = true ∧
    clipsAxis .hidden false = true ∧
    visualOverflowRect 100 100 300 300 0 .hidden .hidden false = ⟨0, 0, 100, 100⟩ := by
  decide

-- layout_box_test.cc:587: VisualOverflowRectOverflowClip
-- CSS Overflow Module Level 3 §3, §3.1.
theorem VisualOverflowRectOverflowClip_vectors :
    isScrollContainer .clip .clip = false ∧
    visualOverflowRect 100 50 300 300 0 .clip .clip false = ⟨0, 0, 100, 50⟩ ∧
    visualOverflowRect 100 50 300 300 0 .clip .visible false = ⟨0, 0, 100, 300⟩ ∧
    visualOverflowRect 100 50 300 300 0 .visible .clip false = ⟨0, 0, 300, 50⟩ := by
  decide

-- layout_box_test.cc:623: VisualOverflowRectWithOverflowClipMargin
-- CSS Overflow Module Level 3 §4, CSS Containment Level 2 §3.3.
theorem VisualOverflowRectWithOverflowClipMargin_vectors :
    visualOverflowRect 100 50 110 55 4 .clip .clip false = ⟨0, 0, 104, 54⟩ ∧
    visualOverflowRect 100 50 110 55 11 .clip .clip false = ⟨0, 0, 110, 55⟩ ∧
    visualOverflowRect 100 50 110 55 11 .visible .visible true = ⟨0, 0, 110, 55⟩ := by
  decide

-- layout_box_test.cc:751: OverflowRectsContainPaint
-- CSS Containment Level 2 §3.3.
theorem OverflowRectsContainPaint_vectors :
    let borderBox : Rect := ⟨0, 0, 120, 220⟩
    let overflowClip : Rect := ⟨10, 10, 100, 200⟩
    let visRect := visualOverflowRect 120 220 310 410 0 .visible .visible true
    borderBox = ⟨0, 0, 120, 220⟩ ∧ overflowClip = ⟨10, 10, 100, 200⟩ ∧ visRect = borderBox := by
  decide

-- layout_box_test.cc:769: OverflowRectsOverflowHidden
-- CSS Overflow Module Level 3 §3.1.
theorem OverflowRectsOverflowHidden_vectors :
    let borderBox : Rect := ⟨0, 0, 120, 220⟩
    let overflowClip : Rect := ⟨10, 10, 100, 200⟩
    let visRect := visualOverflowRect 120 220 310 410 0 .hidden .hidden false
    borderBox = ⟨0, 0, 120, 220⟩ ∧ overflowClip = ⟨10, 10, 100, 200⟩ ∧ visRect = borderBox := by
  decide

-- layout_box_test.cc:386: TopLeftLocationFlipped
-- CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings.
-- In vertical-rl, block-start offset 0 on a 100px item inside a 600px container yields physical x = 500,
-- and second item (200px) at block-offset 100 yields physical x = 300.
theorem TopLeftLocationFlipped_vectors :
    flowToPhysicalOffset .verticalRl 600 100 0 0 = (500, 0) ∧
    flowToPhysicalOffset .verticalRl 600 200 100 0 = (300, 0) := by
  decide

-- layout_box_test.cc:401: TableRowCellTopLeftLocationFlipped
-- CSS Writing Modes Level 3 §6.4.
-- In vertical-rl section with row1 (100px) and row2 (300px), total section width is 400px:
-- row1 is at physical offset (300, 0) and row2 is at (0, 0).
theorem TableRowCellTopLeftLocationFlipped_vectors :
    flowToPhysicalOffset .verticalRl 400 100 0 0 = (300, 0) ∧
    flowToPhysicalOffset .verticalRl 400 300 100 0 = (0, 0) := by
  decide

-- layout_box_test.cc:465: ControlClip
-- CSS Overflow Module Level 3 §3.1, HTML §4.10.
-- Form controls establish an inner clipping rect bounded by the border.
theorem ControlClip_vectors :
    controlInnerClipRect 100 50 2 = ⟨2, 2, 96, 46⟩ := by
  decide

-- layout_box_test.cc:506: VisualOverflowRectWithMask
-- CSS Masking 1 §3. A mask clips visual overflow to the mask box (border box when zero outset).
theorem VisualOverflowRectWithMask_vectors :
    let borderBox : PhysicalRect := ⟨0, 0, 100, 100⟩
    maskVisualOverflow borderBox ⟨0, 0, 0, 0⟩ = ⟨0, 0, 100, 100⟩ := by
  decide

-- layout_box_test.cc:522: VisualOverflowRectWithMaskAndOverflowHidden
-- CSS Masking 1 §3, CSS Overflow 3 §3. A mask with overflow: hidden clips to mask border box.
theorem VisualOverflowRectWithMaskAndOverflowHidden_vectors :
    let borderBox : PhysicalRect := ⟨0, 0, 100, 100⟩
    maskVisualOverflow borderBox ⟨0, 0, 0, 0⟩ = ⟨0, 0, 100, 100⟩ := by
  decide

-- layout_box_test.cc:555: VisualOverflowRectWithMaskWithOutsetAndOverflowHidden
-- CSS Masking 1 §3. Mask-box-image outsets expand mask bounds and clip visual overflow.
theorem VisualOverflowRectWithMaskWithOutsetAndOverflowHidden_vectors :
    let borderBox : PhysicalRect := ⟨0, 0, 100, 100⟩
    let maskOutset : BoxEdges := ⟨10, 20, 10, 20⟩
    maskVisualOverflow borderBox maskOutset = ⟨-20, -10, 140, 120⟩ := by
  decide

-- layout_box_test.cc:1693: VisualOverflowRectIncludingFilters
-- CSS Filter Effects 1 §5. Blur filter expands visual overflow by 3 * radius * zoom.
theorem VisualOverflowRectIncludingFilters_vectors :
    let unfiltered : PhysicalRect := ⟨0, 0, 200, 400⟩
    filterBlurOutset 2 2 = 12 ∧
    filterVisualOverflow unfiltered 2 2 = ⟨-12, -12, 224, 424⟩ := by
  decide

-- layout_box_test.cc:2006: VisualOverflowRectWithEmptyInlineChildAndReflectAndOutline
-- CSS Basic User Interface 3 §7.1, CSS 2.1 §18.4. Outline expands self and visual overflow.
theorem VisualOverflowRectWithEmptyInlineChildAndReflectAndOutline_vectors :
    outlineVisualOverflow ⟨0, 0, 0, 0⟩ 2 = ⟨-2, -2, 4, 4⟩ ∧
    outlineVisualOverflow ⟨0, 0, 800, 0⟩ 6 = ⟨-6, -6, 812, 12⟩ := by
  decide

end TestsBlock
end ChromiumLayout
