/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineLineBox

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
    let t6 : PhysicalRect := { x := 50, y := 170, width := 400, height := 168 }
    (t1 = { x := 50, y := 70, width := 0, height := 0 }) ∧
    (t2 = { x := 50, y := 90, width := 0, height := 0 }) ∧
    (t3 = { x := 50, y := 110, width := 0, height := 0 }) ∧
    (t4 = { x := 50, y := 130, width := 0, height := 0 }) ∧
    (t5 = { x := 50, y := 150, width := 0, height := 0 }) ∧
    (t6 = { x := 50, y := 170, width := 400, height := 168 }) := by
  decide

end ChromiumLayout.TestsInline
