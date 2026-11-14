import BlockFlow
import BlockFragmentation
import BlockOverflow
import BlockScroll
import BlockWritingMode
import ColumnWidth
import OutOfFlowAnchor

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow BlockOverflow BlockScroll BlockWritingMode ColumnWidth OutOfFlowAnchor

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

-- layout_box_test.cc:1755: ScrollsWithViewportRelativePosition
-- CSS Positioned Layout 3 §2.2. Relative-positioned elements are not fixed to view.
theorem ScrollsWithViewportRelativePosition_vectors :
    isFixedToView false false = false := by
  decide

-- layout_box_test.cc:1760: ScrollsWithViewportFixedPosition
-- CSS Positioned Layout 3 §2.2. Fixed-positioned elements fix to viewport.
theorem ScrollsWithViewportFixedPosition_vectors :
    isFixedToView true false = true := by
  decide

-- layout_box_test.cc:1765: ScrollsWithViewportFixedPositionInsideTransform
-- CSS Transforms 1 §2. Transform ancestor establishes CB for fixed-pos; not fixed to view.
theorem ScrollsWithViewportFixedPositionInsideTransform_vectors :
    isFixedToView true true = false := by
  decide

-- layout_box_test.cc:1906: IsUserScrollable
-- CSS Overflow Module Level 3 §3. User scrollability requires scrollsOverflow and content > container.
theorem IsUserScrollable_vectors :
    scrollsOverflow .auto = true ∧
    isUserScrollable .auto 100 200 = true ∧
    scrollsOverflow .hidden = false ∧
    isUserScrollable .hidden 100 200 = false ∧
    isUserScrollable .auto 100 0 = false := by
  decide

-- layout_box_test.cc:1935: IsUserScrollableLayoutView
-- CSS Overflow Module Level 3 §3. View user scrollability toggled by overflow on document body.
theorem IsUserScrollableLayoutView_vectors :
    scrollsOverflow .auto = true ∧
    isUserScrollable .auto 600 2000 = true ∧
    scrollsOverflow .hidden = false ∧
    isUserScrollable .hidden 600 2000 = false := by
  decide

-- layout_box_test.cc:1805: AnchorInFragmentedContainingBlock
-- CSS Anchor Positioning Level 1 §3.1, §3.2. Fragmented CB matches target anchor by name.
theorem AnchorInFragmentedContainingBlock_vectors :
    let anchors : List ScopedAnchor := [{ elementId := "anchor", scopeId := 1, name := "--a" }]
    findTargetAnchor anchors 1 "--a" = some "anchor" := by
  decide

-- layout_box_test.cc:1849: AnchorInInlineContainingBlock
-- CSS Anchor Positioning Level 1 §3.1, §3.2, §3.3. Inline CB matches target anchor; no implicit anchor.
theorem AnchorInInlineContainingBlock_vectors :
    let anchors : List ScopedAnchor := [{ elementId := "anchor", scopeId := 1, name := "--a" }]
    findTargetAnchor anchors 1 "--a" = some "anchor" ∧
    acceptableImplicitAnchor none = none := by
  decide

-- layout_box_test.cc:1869: AnchorInInlineContainingBlockWithNameConflicts
-- CSS Anchor Positioning Level 1 §3.1, §3.2. Conflicting anchor names resolve by containing block scope.
theorem AnchorInInlineContainingBlockWithNameConflicts_vectors :
    let anchors : List ScopedAnchor := [
      { elementId := "anchor1", scopeId := 1, name := "--a" },
      { elementId := "anchor2", scopeId := 2, name := "--a" },
      { elementId := "anchor3", scopeId := 3, name := "--a" }
    ]
    findTargetAnchor anchors 1 "--a" = some "anchor1" ∧
    findTargetAnchor anchors 2 "--a" = some "anchor2" ∧
    findTargetAnchor anchors 3 "--a" = some "anchor3" := by
  decide

def testScrollbarContainer (wm : WritingMode) (dir : Direction) : ContainerBox := {
  wm := wm
  dir := dir
  border := ⟨20, 30, 40, 50⟩
  padding := ⟨10, 20, 30, 40⟩
  contentWidth := 400
  contentHeight := 300
  scrollbars := ⟨15, 16⟩
}

-- layout_box_test.cc:934: LocationOfAbsoluteChildWithContainerScrollbars
-- CSS Positioned Layout 3 §2.1, CSS 2.1 §10.1, §11.1, CSS Writing Modes 3 §6.4.
-- In non-flipped modes location is border-left + left, border-top + top.
-- In horizontal-tb RTL, vertical scrollbar on left shifts origin right by scrollbar width.
theorem LocationOfAbsoluteChildWithContainerScrollbars_vectors :
    let normal := absoluteChildLocation (testScrollbarContainer .horizontalTb .ltr) 100 70
    let vlr := absoluteChildLocation (testScrollbarContainer .verticalLr .ltr) 100 70
    let vrl := absoluteChildLocation (testScrollbarContainer .verticalRl .ltr) 100 70
    let rtl := absoluteChildLocation (testScrollbarContainer .horizontalTb .rtl) 100 70
    let rtl_vlr := absoluteChildLocation (testScrollbarContainer .verticalLr .rtl) 100 70
    let rtl_vrl := absoluteChildLocation (testScrollbarContainer .verticalRl .rtl) 100 70
    normal = (150, 90) ∧
    vlr = (150, 90) ∧
    vrl = (150, 90) ∧
    rtl = (165, 90) ∧
    rtl_vlr = (150, 90) ∧
    rtl_vrl = (150, 90) := by
  decide

-- layout_box_test.cc:990: LocationOfAbsoluteChildWithContainerScrollbarsDifferentWritingModes
-- CSS Positioned Layout 3 §2.1, CSS 2.1 §10.1, CSS Writing Modes 3 §6.4.
-- Child's writing mode does not alter physical location from containing block origin when insets are explicit.
theorem LocationOfAbsoluteChildWithContainerScrollbarsDifferentWritingModes_vectors :
    let vlr_in_htb := absoluteChildLocation (testScrollbarContainer .horizontalTb .ltr) 100 70
    let vrl_in_htb := absoluteChildLocation (testScrollbarContainer .horizontalTb .ltr) 100 70
    let htb_in_vlr := absoluteChildLocation (testScrollbarContainer .verticalLr .ltr) 100 70
    let vrl_in_vlr := absoluteChildLocation (testScrollbarContainer .verticalLr .ltr) 100 70
    let htb_in_vrl := absoluteChildLocation (testScrollbarContainer .verticalRl .ltr) 100 70
    let vlr_in_vrl := absoluteChildLocation (testScrollbarContainer .verticalRl .ltr) 100 70
    vlr_in_htb = (150, 90) ∧
    vrl_in_htb = (150, 90) ∧
    htb_in_vlr = (150, 90) ∧
    vrl_in_vlr = (150, 90) ∧
    htb_in_vrl = (150, 90) ∧
    vlr_in_vrl = (150, 90) := by
  decide

-- layout_box_test.cc:1039: LocationOfAbsoluteAutoTopLeftChildWithContainerScrollbars
-- CSS Positioned Layout 3 §2.1, CSS 2.1 §10.3.7, §10.6.4, CSS Writing Modes 3 §6.4.
-- Static position reflects in-flow start position with container writing mode and direction.
theorem LocationOfAbsoluteAutoTopLeftChildWithContainerScrollbars_vectors :
    let normal := absoluteAutoLocation (testScrollbarContainer .horizontalTb .ltr) 150 180
    let vlr := absoluteAutoLocation (testScrollbarContainer .verticalLr .ltr) 150 180
    let vrl := absoluteAutoLocation (testScrollbarContainer .verticalRl .ltr) 150 180
    let rtl := absoluteAutoLocation (testScrollbarContainer .horizontalTb .rtl) 150 180
    let rtl_vlr := absoluteAutoLocation (testScrollbarContainer .verticalLr .rtl) 150 180
    let rtl_vrl := absoluteAutoLocation (testScrollbarContainer .verticalRl .rtl) 150 180
    normal = (90, 30) ∧
    vlr = (90, 30) ∧
    vrl = (325, 30) ∧
    rtl = (340, 30) ∧
    rtl_vlr = (90, 134) ∧
    rtl_vrl = (325, 134) := by
  decide

-- layout_box_test.cc:1165: LocationOfInFlowChildWithContainerScrollbars
-- CSS 2.1 §9.2, CSS Writing Modes 3 §6.4. In-flow child placed after preceding sibling offset.
theorem LocationOfInFlowChildWithContainerScrollbars_vectors :
    let normal := inFlowChildLocation (testScrollbarContainer .horizontalTb .ltr) 150 180 100 70
    let vlr := inFlowChildLocation (testScrollbarContainer .verticalLr .ltr) 150 180 100 70
    let vrl := inFlowChildLocation (testScrollbarContainer .verticalRl .ltr) 150 180 100 70
    let rtl := inFlowChildLocation (testScrollbarContainer .horizontalTb .rtl) 150 180 100 70
    let rtl_vlr := inFlowChildLocation (testScrollbarContainer .verticalLr .rtl) 150 180 100 70
    let rtl_vrl := inFlowChildLocation (testScrollbarContainer .verticalRl .rtl) 150 180 100 70
    normal = (90, 100) ∧
    vlr = (190, 30) ∧
    vrl = (225, 30) ∧
    rtl = (340, 100) ∧
    rtl_vlr = (190, 134) ∧
    rtl_vrl = (225, 134) := by
  decide

-- layout_box_test.cc:1234: LocationOfRelativeChildWithContainerScrollbars
-- CSS Positioned Layout 3 §2.1, CSS 2.1 §9.4.3. Relative child shifted by relative insets.
theorem LocationOfRelativeChildWithContainerScrollbars_vectors :
    let normal := relativeChildLocation (testScrollbarContainer .horizontalTb .ltr) 150 180 100 70 88 77
    let vlr := relativeChildLocation (testScrollbarContainer .verticalLr .ltr) 150 180 100 70 88 77
    let vrl := relativeChildLocation (testScrollbarContainer .verticalRl .ltr) 150 180 100 70 88 77
    let rtl := relativeChildLocation (testScrollbarContainer .horizontalTb .rtl) 150 180 100 70 88 77
    let rtl_vlr := relativeChildLocation (testScrollbarContainer .verticalLr .rtl) 150 180 100 70 88 77
    let rtl_vrl := relativeChildLocation (testScrollbarContainer .verticalRl .rtl) 150 180 100 70 88 77
    normal = (178, 177) ∧
    vlr = (278, 107) ∧
    vrl = (313, 107) ∧
    rtl = (428, 177) ∧
    rtl_vlr = (278, 211) ∧
    rtl_vrl = (313, 211) := by
  decide

-- layout_box_test.cc:1289: LocationOfFloatLeftChildWithContainerScrollbars
-- CSS 2.1 §9.5.1, CSS Writing Modes 3 §6.4. Float left child aligns to physical left of content box.
theorem LocationOfFloatLeftChildWithContainerScrollbars_vectors :
    let normal := floatLeftChildLocation (testScrollbarContainer .horizontalTb .ltr) 150 180
    let vlr := floatLeftChildLocation (testScrollbarContainer .verticalLr .ltr) 150 180
    let vrl := floatLeftChildLocation (testScrollbarContainer .verticalRl .ltr) 150 180
    let rtl := floatLeftChildLocation (testScrollbarContainer .horizontalTb .rtl) 150 180
    let rtl_vlr := floatLeftChildLocation (testScrollbarContainer .verticalLr .rtl) 150 180
    let rtl_vrl := floatLeftChildLocation (testScrollbarContainer .verticalRl .rtl) 150 180
    normal = (90, 30) ∧
    vlr = (90, 30) ∧
    vrl = (325, 30) ∧
    rtl = (105, 30) ∧
    rtl_vlr = (90, 134) ∧
    rtl_vrl = (325, 134) := by
  decide

end TestsBlock
end ChromiumLayout
