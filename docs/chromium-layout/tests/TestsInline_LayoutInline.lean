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

end ChromiumLayout.TestsInline
