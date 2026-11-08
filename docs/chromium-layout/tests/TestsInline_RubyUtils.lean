/-
  docs/chromium-layout/tests/TestsInline_RubyUtils.lean

  Formalized layout tests for RubyBlockPositionCalculator
  (`third_party/blink/renderer/core/layout/inline/ruby_utils_test.cc`).

  Covers:
  - GroupLinesEmpty (`inline/ruby_utils_test.cc:25`)
  - GroupLinesOneAnnotationLevel (`inline/ruby_utils_test.cc:32`)
  - GroupLinesNested (`inline/ruby_utils_test.cc:49`)
  - GroupLinesBothSides (`inline/ruby_utils_test.cc:67`)
  - GroupLinesAnnotationForAnnotation (`inline/ruby_utils_test.cc:106`)
-/
import LayoutTypes
import LayoutInline
import InlineRuby

namespace ChromiumLayout

/-! ## 1. GroupLinesEmpty (`inline/ruby_utils_test.cc:25`) -/

/-- Test `RubyBlockPositionCalculatorTest, GroupLinesEmpty` (`inline/ruby_utils_test.cc:25`).
    Empty ruby column list produces exactly one base-level ruby line. -/
theorem rubyBlockPositionCalculator_groupLinesEmpty :
    let lines := groupLines []
    (lines.length = 1) ∧
    (lines[0]!.isBaseLevel = true) := by
  decide

/-! ## 2. GroupLinesOneAnnotationLevel (`inline/ruby_utils_test.cc:32`) -/

/-- Test `RubyBlockPositionCalculatorTest, GroupLinesOneAnnotationLevel` (`inline/ruby_utils_test.cc:32`).
    Non-overlapping columns form a single annotation level [1] on the base. -/
theorem rubyBlockPositionCalculator_groupLinesOneAnnotationLevel :
    let col1 : LogicalRubyColumn := { startIndex := 1, size := 1 }
    let col2 : LogicalRubyColumn := { startIndex := 10, size := 3 }
    let lines := groupLines [col1, col2]
    (lines.length = 2) ∧
    (lines[0]!.isBaseLevel = true) ∧
    (lines[1]!.level = [1]) := by
  decide

/-! ## 3. GroupLinesNested (`inline/ruby_utils_test.cc:49`) -/

/-- Test `RubyBlockPositionCalculatorTest, GroupLinesNested` (`inline/ruby_utils_test.cc:49`).
    Nested ruby columns form tiered annotation levels [1] and [2]. -/
theorem rubyBlockPositionCalculator_groupLinesNested :
    let col1 : LogicalRubyColumn := { startIndex := 1, size := 10 }
    let col2 : LogicalRubyColumn := { startIndex := 3, size := 4 }
    let lines := groupLines [col1, col2]
    (lines.length = 3) ∧
    (lines[0]!.isBaseLevel = true) ∧
    (lines[1]!.level = [1]) ∧
    (lines[2]!.level = [2]) := by
  decide

/-! ## 4. GroupLinesBothSides (`inline/ruby_utils_test.cc:67`) -/

/-- Test `RubyBlockPositionCalculatorTest, GroupLinesBothSides` (`inline/ruby_utils_test.cc:67`).
    Over and under annotations group into separate lines with negative and positive depths. -/
theorem rubyBlockPositionCalculator_groupLinesBothSides :
    let col1 : LogicalRubyColumn := { startIndex := 1, size := 10, rubyPosition := .over }
    let col2 : LogicalRubyColumn := { startIndex := 2, size := 3, rubyPosition := .under }
    let col3 : LogicalRubyColumn := { startIndex := 20, size := 10, rubyPosition := .over }
    let col4 : LogicalRubyColumn := { startIndex := 22, size := 3, rubyPosition := .under }
    let lines := groupLines [col1, col2, col3, col4]
    (lines.length = 3) ∧
    (lines[0]!.isBaseLevel = true) ∧
    (lines[1]!.level = [-1]) ∧
    (lines[1]!.columns.length = 2) ∧
    (lines[2]!.level = [1]) ∧
    (lines[2]!.columns.length = 2) := by
  decide

/-! ## 5. GroupLinesAnnotationForAnnotation (`inline/ruby_utils_test.cc:106`) -/

/-- Test `RubyBlockPositionCalculatorTest, GroupLinesAnnotationForAnnotation` (`inline/ruby_utils_test.cc:106`).
    Sub-columns of an annotation column form sub-levels such as [1, -1]. -/
theorem rubyBlockPositionCalculator_groupLinesAnnotationForAnnotation :
    let colSub : LogicalRubyColumn := { startIndex := 2, size := 3, rubyPosition := .under }
    let col1 : LogicalRubyColumn := { startIndex := 1, size := 10, rubyPosition := .over, subColumns := [colSub] }
    let lines := groupLines [col1]
    (lines.length = 3) ∧
    (lines[0]!.isBaseLevel = true) ∧
    (lines[1]!.level = [1]) ∧
    (lines[2]!.level = [1, -1]) := by
  decide

end ChromiumLayout
