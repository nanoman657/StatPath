/-
  docs/chromium-layout/tests/TestsInline_TextAutoSpace.lean

  Formalized layout tests for TextAutoSpace
  (`third_party/blink/renderer/core/layout/inline/text_auto_space_test.cc`).

  Covers:
  - MayApply (`inline/text_auto_space_test.cc:85`)
  - InsertSpacing (`inline/text_auto_space_test.cc:95`)
  - Apply (`inline/text_auto_space_test.cc:173`)
-/
import LayoutTypes
import InlineAutoSpace

namespace ChromiumLayout

/-! ## 1. MayApply (`inline/text_auto_space_test.cc:85`) -/

/-- Test `MayApplyTest, MayApply` (`inline/text_auto_space_test.cc:85`).
    Verifies early rejection optimization: only text containing East Asian ideographs may apply auto-spacing. -/
theorem textAutoSpace_mayApply :
    (mayApplyTextAutoSpace "English".toList = false) ∧
    (mayApplyTextAutoSpace "Café".toList = false) ∧
    (mayApplyTextAutoSpace ['\u200B', '\uFFFC'] = false) ∧
    (mayApplyTextAutoSpace ['\u2018', '\u2019', '\u201C', '\u201D'] = false) ∧
    (mayApplyTextAutoSpace "水".toList = true) := by
  decide

/-! ## 2. InsertSpacing (`inline/text_auto_space_test.cc:95`) -/

/-- Test `TextAutoSpaceTest, InsertSpacing` (`inline/text_auto_space_test.cc:95`).
    10px Ahem font with 1/8 em (1.25px = 10 eighths) inter-script spacing at boundaries 3 and 6
    produces cumulative start positions [0, 10, 20, 31.25, 41.25, 51.25, 62.5] (in 1/8 pixel units: [0, 80, 160, 250, 330, 410, 500]). -/
theorem textAutoSpace_insertSpacing :
    computeCharacterPositionsEighths "AAAあああa".toList 80 10 =
      [0, 80, 160, 250, 330, 410, 500] := by
  decide

/-! ## 3. HtmlTest.Apply (`inline/text_auto_space_test.cc:173`) -/

/-- Test `HtmlTest, Apply` (`inline/text_auto_space_test.cc:173`).
    Verifies auto-space boundary offset detection across inter-script text patterns. -/
theorem textAutoSpace_apply :
    (computeAutoSpaceOffsets "ああああ".toList = []) ∧
    (computeAutoSpaceOffsets "English only".toList = []) ∧
    (computeAutoSpaceOffsets "Abcあああ".toList = [3]) ∧
    (computeAutoSpaceOffsets "123あああ".toList = [3]) ∧
    (computeAutoSpaceOffsets "あああAbc".toList = [3]) ∧
    (computeAutoSpaceOffsets "あああ123".toList = [3]) ∧
    (computeAutoSpaceOffsets "ああAああ".toList = [2, 3]) ∧
    (computeAutoSpaceOffsets "ああ1ああ".toList = [2, 3]) ∧
    (computeAutoSpaceOffsets "ああAbcああ".toList = [2, 5]) ∧
    (computeAutoSpaceOffsets "ああ 12 ああ".toList = []) := by
  decide

end ChromiumLayout
