/-
  docs/chromium-layout/tests/TestsInline_InlineCursor.lean

  Test vectors and theorems transcribed from:
  - `inline/inline_cursor_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineGeometry
import InlineBidi

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test: BidiLevelInlineBoxLTR (inline_cursor_test.cc:125)
    In an LTR root, plain text and LTR inline boxes have bidi level 0,
    while an RTL <bdo> override assigns level 3. -/
theorem inlineCursor_bidiLevelInlineBoxLTR :
    let items := [
      BidiItem.text "abc",
      BidiItem.inlineBox "def",
      BidiItem.openBdo .rtl,
      BidiItem.inlineBox "ghi",
      BidiItem.closeBdo,
      BidiItem.text "jkl"
    ]
    bidiLevels .ltr items [] = [("abc", 0), ("def", 0), ("ghi", 3), ("jkl", 0)] := by
  decide

/-- Test: BidiLevelInlineBoxRTL (inline_cursor_test.cc:135)
    In an RTL root, Latin text and inline boxes resolve to level 2,
    while an RTL <bdo> override resolves to level 3. -/
theorem inlineCursor_bidiLevelInlineBoxRTL :
    let items := [
      BidiItem.text "abc",
      BidiItem.inlineBox "def",
      BidiItem.openBdo .rtl,
      BidiItem.inlineBox "ghi",
      BidiItem.closeBdo,
      BidiItem.text "jkl"
    ]
    bidiLevels .rtl items [] = [("abc", 2), ("def", 2), ("ghi", 3), ("jkl", 2)] := by
  decide

/-- Test: BidiLevelSimpleLTR (inline_cursor_test.cc:145)
    Nested RTL and LTR overrides produce bidi levels 3 and 6 respectively. -/
theorem inlineCursor_bidiLevelSimpleLTR :
    let items := [
      BidiItem.openBdo .rtl,
      BidiItem.text "GHI",
      BidiItem.openBdo .ltr,
      BidiItem.text "abc",
      BidiItem.closeBdo,
      BidiItem.text "DEF",
      BidiItem.closeBdo,
      BidiItem.br,
      BidiItem.text "123, jkl ",
      BidiItem.openBdo .rtl,
      BidiItem.text "MNO",
      BidiItem.closeBdo
    ]
    bidiLevels .ltr items [] = [
      ("GHI", 3), ("abc", 6), ("DEF", 3), ("<br>", 0),
      ("123, jkl ", 0), ("MNO", 3)
    ] := by
  decide

/-- Test: BidiLevelFirstLineTextTransform (inline_cursor_test.cc:166)
    First line text-transform uppercases German eszett ('ß' -> "SS") at level 0. -/
theorem inlineCursor_bidiLevelFirstLineTextTransform :
    let raw := "ß\t"
    let transformed := String.ofList (applyTextTransform true raw.toList)
    (transformed = "SS\t") ∧
    (bidiLevels .ltr [BidiItem.text "SS", BidiItem.text "\t"] [] = [("SS", 0), ("\t", 0)]) := by
  decide

/-- Test: BidiLevelFirstLineTextTransformBR (inline_cursor_test.cc:175)
    First line text-transform with line break `<br>`. -/
theorem inlineCursor_bidiLevelFirstLineTextTransformBR :
    let raw := "ß"
    let transformed := String.ofList (applyTextTransform true raw.toList)
    (transformed = "SS") ∧
    (bidiLevels .ltr [BidiItem.text "SS", BidiItem.br] [] = [("SS", 0), ("<br>", 0)]) := by
  decide

end ChromiumLayout.TestsInline
