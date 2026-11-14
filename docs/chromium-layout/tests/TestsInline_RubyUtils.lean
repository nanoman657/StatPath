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

/-! ## 6. PlaceLinesNestedRubyWithTextEmphasis (`inline/ruby_utils_test.cc:146`) -/

/-- Test `RubyBlockPositionCalculatorTest, PlaceLinesNestedRubyWithTextEmphasis` (`inline/ruby_utils_test.cc:146`).
    CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Nested ruby annotations with text emphasis:
    - Non-ruby items (item_before) have zero annotation ascent.
    - Base item accumulates all nested annotations and emphasis marks:
      90 = 20 (first anno) + 10 (nested anno emphasis) + 20 (nested anno) + 10 (first anno emphasis)
         + 10 (second anno emphasis) + 20 (second anno).
    - First annotation inner base (first2) has ascent 30 = 10 (nested emphasis) + 20 (nested anno).
    - First annotation leaf (first1) has zero ascent. -/
theorem rubyBlockPositionCalculator_placeLinesNestedRubyWithTextEmphasis :
    let anno1 : NestedRubyAnnotation := { textHeight := 20, emphasisHeight := 10 }
    let annoNested : NestedRubyAnnotation := { textHeight := 20, emphasisHeight := 10 }
    let anno2 : NestedRubyAnnotation := { textHeight := 20, emphasisHeight := 10 }
    let baseAscent := computeNestedRubyAscent [anno1, annoNested, anno2]
    let first2Ascent := computeNestedRubyAscent [annoNested]
    let first1Ascent := computeNestedRubyAscent []
    let beforeMetrics := computeAnnotationMetrics { hasRuby := false }
    (beforeMetrics.ascent = 0) ∧
    (baseAscent = 90) ∧
    (first1Ascent = 0) ∧
    (first2Ascent = 30) := by
  decide

end ChromiumLayout
