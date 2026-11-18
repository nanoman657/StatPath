/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineLineBox
import InlineGeometry

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-!
# Tests for LayoutInline

Corresponds to `core/layout/layout_inline_test.cc`.
-/

/-! ### Test 1: PhysicalLinesBoundingBox (`layout_inline_test.cc:38`) -/
theorem layoutInline_physicalLinesBoundingBox :
    physicalLinesBoundingBox 300 100 .horizontalTb .ltr [{ width := 30, height := 10 }, { width := 30, height := 10 }] =
      { x := 0, y := 0, width := 30, height := 20 } ∧
    physicalLinesBoundingBox 300 100 .horizontalTb .ltr [{ width := 110, height := 10 }] =
      { x := 0, y := 0, width := 110, height := 10 } ∧
    physicalLinesBoundingBox 300 100 .horizontalTb .rtl [{ width := 30, height := 10 }, { width := 30, height := 10 }] =
      { x := 270, y := 0, width := 30, height := 20 } ∧
    physicalLinesBoundingBox 300 100 .horizontalTb .rtl [{ width := 110, height := 10 }] =
      { x := 190, y := 0, width := 110, height := 10 } ∧
    physicalLinesBoundingBox 300 100 .verticalRl .ltr [{ width := 10, height := 30 }, { width := 10, height := 30 }] =
      { x := 280, y := 0, width := 20, height := 30 } := by
  decide

/-! ### Test 2: AbsoluteBoundingBoxRectHandlingEmptyInline (`layout_inline_test.cc:483`) -/
/-- Test `LayoutInlineTest, AbsoluteBoundingBoxRectHandlingEmptyInline` (`layout_inline_test.cc:483`).
    CSS 2.1 §9.4.2 & §10.8:
    Empty inlines on consecutive lines have 0x0 size at line coordinates,
    and continuation block has container width 400 with height 168. -/
theorem layoutInline_absoluteBoundingBoxRectHandlingEmptyInline :
    let t1 := emptyInlineAbsoluteBoundingBox 50 30 20 2
    let t2 := emptyInlineAbsoluteBoundingBox 50 30 20 3
    let t3 := emptyInlineAbsoluteBoundingBox 50 30 20 4
    let t4 := emptyInlineAbsoluteBoundingBox 50 30 20 5
    let t5 := emptyInlineAbsoluteBoundingBox 50 30 20 6
    let containerWidth := 400
    let fontDescent := 4
    let imgHeight := 30
    let divHeight := 100
    let continuationHeight := (imgHeight + fontDescent) * 2 + divHeight
    let continuationY := 30 + 7 * 20
    let t6 : PhysicalRect := { x := 50, y := continuationY, width := containerWidth, height := continuationHeight }
    (t1 = { x := 50, y := 70, width := 0, height := 0 }) ∧
    (t2 = { x := 50, y := 90, width := 0, height := 0 }) ∧
    (t3 = { x := 50, y := 110, width := 0, height := 0 }) ∧
    (t4 = { x := 50, y := 130, width := 0, height := 0 }) ∧
    (t5 = { x := 50, y := 150, width := 0, height := 0 }) ∧
    (t6 = { x := 50, y := 170, width := 400, height := 168 }) := by
  decide

/-! ### Test 3: RegionHitTest (`layout_inline_test.cc:139`) -/
/-- Test `LayoutInlineTest, RegionHitTest` (`layout_inline_test.cc:139`).
    CSS 2.1 §9.4.2: List-based hit testing rect intersects line box fragment. -/
theorem layoutInline_regionHitTest :
    let lineBox : LayoutUnitRect := { x := 0, y := 0, width := 150, height := 18 }
    let hitRect : LayoutUnitRect := { x := 1, y := 3, width := 2, height := 4 }
    hitTestCulledInlineIntersects lineBox hitRect = true := by
  decide

/-! ### Test 4: RelativePositionedHitTest (`layout_inline_test.cc:194`) -/
/-- Test `LayoutInlineTest, RelativePositionedHitTest` (`layout_inline_test.cc:194`).
    CSS 2.1 §9.3.1: Relative positioned inline in separate paint layer is ignored during normal-flow hit testing. -/
theorem layoutInline_relativePositionedHitTest :
    let items :=
      [ { nodeId := 2, bounds := { x := 0, y := 0, width := 30, height := 10 }, isPositioned := true }
      , { nodeId := 1, bounds := { x := 0, y := 0, width := 300, height := 50 }, isPositioned := false } ]
    (hitTestInlineItems 8 8 items true 18 15 = some 1) ∧
    (hitTestInlineItems 8 8 items false 18 15 = some 2) := by
  decide

/-! ### Test 5: MultilineRelativePositionedHitTest (`layout_inline_test.cc:241`) -/
/-- Test `LayoutInlineTest, MultilineRelativePositionedHitTest` (`layout_inline_test.cc:241`).
    CSS 2.1 §9.3.1 & §9.4.2: Hit testing multiline positioned inline selects item on corresponding line. -/
theorem layoutInline_multilineRelativePositionedHitTest :
    let items :=
      [ { nodeId := 1, bounds := { x := 0, y := 0, width := 30, height := 10 }, isPositioned := false }
      , { nodeId := 2, bounds := { x := 0, y := 10, width := 30, height := 10 }, isPositioned := false }
      , { nodeId := 3, bounds := { x := 0, y := 20, width := 10, height := 10 }, isPositioned := false } ]
    (hitTestInlineItems 8 8 items false 13 13 = some 1) ∧
    (hitTestInlineItems 8 8 items false 13 23 = some 2) ∧
    (hitTestInlineItems 8 8 items false 13 33 = some 3) := by
  decide

/-! ### Test 6: HitTestCulledInlinePreWrap (`layout_inline_test.cc:319`) -/
/-- Test `LayoutInlineTest, HitTestCulledInlinePreWrap` (`layout_inline_test.cc:319`).
    CSS Text 3 §5.1: Hit test on pre-wrap inline targets inner text node. -/
theorem layoutInline_hitTestCulledInlinePreWrap :
    let spanText := { nodeId := 1, bounds := { x := 0, y := 0, width := 250, height := 30 }, isPositioned := false }
    hitTestInlineItems 0 0 [spanText] false 100 15 = some 1 := by
  decide

/-! ### Test 7: AddDraggableRegions (`layout_inline_test.cc:575`) -/
/-- Test `LayoutInlineTest, AddDraggableRegions` (`layout_inline_test.cc:575`).
    CSS 2.1 §9.4.2: Multiline inline draggable region bounds united across lines. -/
theorem layoutInline_addDraggableRegions :
    let r1 := computeDraggableRegions .drag [{ x := 20, y := 10, width := 30, height := 10 }, { x := 0, y := 20, width := 30, height := 10 }]
    let r2 := computeDraggableRegions .noDrag [{ x := 40, y := 20, width := 30, height := 10 }, { x := 0, y := 30, width := 30, height := 10 }]
    let r3 := computeDraggableRegions .none [{ x := 40, y := 20, width := 30, height := 10 }]
    (r1 = [{ bounds := { x := 0, y := 10, width := 50, height := 20 }, draggable := true }]) ∧
    (r2 = [{ bounds := { x := 0, y := 20, width := 70, height := 20 }, draggable := false }]) ∧
    (r3 = []) := by
  decide

/-! ### Test 8: AddDraggableRegionsVerticalRL (`layout_inline_test.cc:609`) -/
/-- Test `LayoutInlineTest, AddDraggableRegionsVerticalRL` (`layout_inline_test.cc:609`).
    CSS Writing Modes 3 §3.1: Draggable region bounds under vertical-rl multiline layout. -/
theorem layoutInline_addDraggableRegionsVerticalRL :
    let r1 := computeDraggableRegions .drag [{ x := 580, y := 20, width := 10, height := 30 }, { x := 570, y := 0, width := 10, height := 30 }]
    let r2 := computeDraggableRegions .noDrag [{ x := 570, y := 40, width := 10, height := 30 }, { x := 560, y := 0, width := 10, height := 30 }]
    let r3 := computeDraggableRegions .none [{ x := 570, y := 40, width := 10, height := 30 }]
    (r1 = [{ bounds := { x := 570, y := 0, width := 20, height := 50 }, draggable := true }]) ∧
    (r2 = [{ bounds := { x := 560, y := 0, width := 20, height := 70 }, draggable := false }]) ∧
    (r3 = []) := by
  decide

/-! ### Test 9: SimpleContinuation (`layout_inline_test.cc:69`) -/
/-- Test `LayoutInlineTest, SimpleContinuation` (`layout_inline_test.cc:69`).
    CSS 2.1 §9.2.1.1: Inline element with block child splits into continuations:
    first child is inline `before`, followed by anonymous block-in-inline wrapper around `blockChild`,
    followed by inline `after`. -/
theorem layoutInline_simpleContinuation :
    let children := [(false, "before"), (true, "blockChild"), (false, "after")]
    wrapBlockInInlineChildren children =
      [.inline "before", .blockInInline "anon_blockChild" "blockChild", .inline "after"] := by
  rfl

/-! ### Test 10: BlockInInlineRemove (`layout_inline_test.cc:93`) -/
/-- Test `LayoutInlineTest, BlockInInlineRemove` (`layout_inline_test.cc:93`).
    CSS 2.1 §9.2.1.1: Removing block child leaves all remaining children as inlines,
    so no anonymous block-in-inline wrappers remain. -/
theorem layoutInline_blockInInlineRemove :
    let original := [(false, "before"), (true, "block"), (false, "after")]
    let remaining := removeInlineChild "block" original
    remaining = [(false, "before"), (false, "after")] ∧
    wrapBlockInInlineChildren remaining = [.inline "before", .inline "after"] := by
  decide

/-! ### Test 11: VisualOverflowRecalcLegacyLayout (`layout_inline_test.cc:643`) -/
/-- Test `LayoutInlineTest, VisualOverflowRecalcLegacyLayout` (`layout_inline_test.cc:643`).
    CSS 2.1 §18.4 & CSS UI 3 §3.1: Inline box visual overflow with and without 50px outline. -/
theorem layoutInline_visualOverflowRecalcLegacyLayout :
    let spanBox : SignedPhysicalRect := { x := 0, y := 0, width := 100, height := 20 }
    (inlineOutlineVisualOverflow spanBox 50 = { x := -50, y := -50, width := 200, height := 120 }) ∧
    (inlineOutlineVisualOverflow spanBox 0 = { x := 0, y := 0, width := 100, height := 20 }) := by
  decide

/-! ### Test 12: VisualOverflowRecalcLayoutNG (`layout_inline_test.cc:689`) -/
/-- Test `LayoutInlineTest, VisualOverflowRecalcLayoutNG` (`layout_inline_test.cc:689`).
    CSS 2.1 §18.4 & CSS UI 3 §3.1: LayoutNG inline box visual overflow with and without 50px outline. -/
theorem layoutInline_visualOverflowRecalcLayoutNG :
    let spanBox : SignedPhysicalRect := { x := 0, y := 0, width := 100, height := 20 }
    (inlineOutlineVisualOverflow spanBox 50 = { x := -50, y := -50, width := 200, height := 120 }) ∧
    (inlineOutlineVisualOverflow spanBox 0 = { x := 0, y := 0, width := 100, height := 20 }) := by
  decide

/-! ### Test 13: VisualOverflowRecalcLegacyLayoutPositionRelative (`layout_inline_test.cc:733`) -/
/-- Test `LayoutInlineTest, VisualOverflowRecalcLegacyLayoutPositionRelative` (`layout_inline_test.cc:733`).
    CSS 2.1 §18.4 & CSS UI 3 §3.1: Relative-positioned inline box visual overflow with 50px outline. -/
theorem layoutInline_visualOverflowRecalcLegacyLayoutPositionRelative :
    let spanBox : SignedPhysicalRect := { x := 0, y := 0, width := 80, height := 20 }
    inlineOutlineVisualOverflow spanBox 50 = { x := -50, y := -50, width := 180, height := 120 } := by
  decide

end ChromiumLayout.TestsInline
