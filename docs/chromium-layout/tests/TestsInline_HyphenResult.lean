/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineHyphen

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-!
# Tests for HyphenResult Font Shaping and Glyph Orientation

Transcribed from `inline/hyphen_result_test.cc`.
-/

/-! ### Test 1: Horizontal (`inline/hyphen_result_test.cc:37`) -/
theorem hyphenResult_horizontal :
    (shapeHyphenResult "+=" .horizontalTb .mixed false).rotations = [.regular, .regular] ∧
    (shapeHyphenResult "+=" .horizontalTb .mixed true).rotations = [.regular, .regular] := by
  decide

/-! ### Test 2: VerticalUpright (`inline/hyphen_result_test.cc:53`) -/
theorem hyphenResult_verticalUpright :
    (shapeHyphenResult "+=" .verticalRl .upright false).rotations = [.rotateCanvasUpright, .rotateCanvasUpright] ∧
    (shapeHyphenResult "+=" .verticalRl .upright true).rotations = [.rotateCanvasUpright, .rotateCanvasUpright] := by
  decide

/-! ### Test 3: VerticalMixed (`inline/hyphen_result_test.cc:70`) -/
theorem hyphenResult_verticalMixed :
    (shapeHyphenResult "+=" .verticalRl .mixed false).rotations = [.rotateCanvasUpright, .rotateCanvasUpright] ∧
    (shapeHyphenResult "+=" .verticalRl .mixed true).rotations = [.regular, .regular] := by
  decide

end ChromiumLayout.TestsInline
