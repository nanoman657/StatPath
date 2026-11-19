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
import InlineTextCombine

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
    let fontSize := 20
    let emphasisHeight := computeTextEmphasisHeight fontSize
    let anno1 : NestedRubyAnnotation := { textHeight := fontSize, emphasisHeight := emphasisHeight }
    let annoNested : NestedRubyAnnotation := { textHeight := fontSize, emphasisHeight := emphasisHeight }
    let anno2 : NestedRubyAnnotation := { textHeight := fontSize, emphasisHeight := emphasisHeight }
    let baseAscent := computeNestedRubyAscent [anno1, annoNested, anno2]
    let first2Ascent := computeNestedRubyAscent [annoNested]
    let first1Ascent := computeNestedRubyAscent []
    let beforeMetrics := computeAnnotationMetrics { hasRuby := false }
    (beforeMetrics.ascent = 0) ∧
    (baseAscent = 90) ∧
    (first1Ascent = 0) ∧
    (first2Ascent = 30) := by
  decide

/-! ## 7. Ruby Base and Ruby Block Layout Tests
    (`layout_ruby_base_test.cc` and `layout_ruby_as_block_test.cc`) -/

/-- Test `LayoutRubyBaseTest, AddChildNoBlockChildren` (`layout_ruby_base_test.cc:16`).
    CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1:
    Adding a table-cell child inside a ruby base inlinifies the table cell to inline-table
    and never moves prior text to an anonymous block. -/
theorem layoutRubyBase_addChildNoBlockChildren :
    movesPriorTextToAnonymousBlock .tableCell = false ∧
    inlinifyRubyChildDisplay .tableCell = .inlineTable ∧
    isRubyChildInline .tableCell = true := by
  decide

/-- Test `LayoutRubyBaseTest, AddImageNoBlockChildren` (`layout_ruby_base_test.cc:30`).
    CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1:
    Adding an image with display:table-caption inside a ruby base does not move prior text
    to an anonymous block, and the caption child is inline-level. -/
theorem layoutRubyBase_addImageNoBlockChildren :
    movesPriorTextToAnonymousBlock .tableCaption = false ∧
    inlinifyRubyChildDisplay .tableCaption = .tableCaption ∧
    isRubyChildInline .tableCaption = true := by
  decide

/-- Test `LayoutRubyBaseTest, AddSpecialWithTableInternalDisplayNoBlockChildren` (`layout_ruby_base_test.cc:52`).
    CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1:
    Adding an element with display:table-column inside a ruby base does not move prior text
    to an anonymous block, and the table column child is inline-level without inline-table wrapper. -/
theorem layoutRubyBase_addSpecialWithTableInternalDisplayNoBlockChildren :
    movesPriorTextToAnonymousBlock .tableColumn = false ∧
    inlinifyRubyChildDisplay .tableColumn = .tableColumn ∧
    isRubyChildInline .tableColumn = true := by
  decide

/-- Test `LayoutRubyBaseTest, ChangeToRubyNoBlockChildren` (`layout_ruby_base_test.cc:73`).
    CSS Ruby 1 §2.1:
    Changing container display to ruby inlinifies block-level children (such as <p>) into inline boxes. -/
theorem layoutRubyBase_changeToRubyNoBlockChildren :
    isRubyChildInline .block = true ∧
    inlinifyRubyChildDisplay .block = .inline := by
  decide

/-- Test `LayoutRubyAsBlockTest, TextCombineCrash` (`layout_ruby_as_block_test.cc:14`).
    CSS Writing Modes 3 §5.1 & CSS Ruby 1 §2.1:
    In vertical-rl writing mode with text-combine-upright:all, text in ruby block
    is combined into LayoutTextCombine without crash. -/
theorem layoutRubyAsBlock_textCombineCrash :
    isTextCombineActive .verticalRl .all = true ∧
    buildInlineDisplay true [.text "a"] = [.combined { children := [.text "a"] }] := by
  decide

/-! ## 8. Ruby Sizing and Justification Tests
    (`inline/line_breaker_test.cc`, `inline/inline_node_test.cc`, `inline/justification_utils_test.cc`) -/

/-- Test `LineBreakerTest, WideContentInRuby` (`inline/line_breaker_test.cc:1117`).
    CSS Ruby 1 §4:
    Ruby base containing wide atomic inline elements accommodates their total width,
    preventing overflow during column sizing. -/
theorem lineBreaker_wideContentInRuby :
    let div1Width := 109162843
    let div2Width := 10
    let totalBase := div1Width + div2Width
    let col : RubyColumnSizes := { baseMin := totalBase, baseMax := totalBase, annotationMins := [10], annotationMaxs := [10] }
    computeRubyColumnMinSize col = totalBase ∧
    computeRubyColumnMaxSize col = totalBase := by
  decide

/-- Test `LineBreakerTest, OverflowingContinuationRuby` (`inline/line_breaker_test.cc:1193`).
    CSS Ruby 1 §4:
    Overflowing ruby continuation annotations expand column min-content size to fit the annotation. -/
theorem lineBreaker_overflowingContinuationRuby :
    let baseWidth := 20
    let annoWidth := 100
    let col : RubyColumnSizes := { baseMin := baseWidth, baseMax := baseWidth, annotationMins := [annoWidth], annotationMaxs := [annoWidth] }
    computeRubyColumnMinSize col = annoWidth := by
  decide

/-- Test `LineBreakerTest, OverflowingContinuationRuby2` (`inline/line_breaker_test.cc:1208`).
    CSS Ruby 1 §4:
    Vertical ruby column with SVG atomic inline base and wide annotation establishes column size. -/
theorem lineBreaker_overflowingContinuationRuby2 :
    let baseWidth := 30
    let annoWidth := 80
    let col : RubyColumnSizes := { baseMin := baseWidth, baseMax := baseWidth, annotationMins := [annoWidth], annotationMaxs := [annoWidth] }
    computeRubyColumnMinSize col = annoWidth := by
  decide

/-- Test `LineBreakerTest, MinMaxWithAtomicInlineInRuby` (`inline/line_breaker_test.cc:1220`).
    CSS Ruby 1 §4:
    Ruby column with atomic inline in ruby base and empty annotation has column min size bounded by base. -/
theorem lineBreaker_minMaxWithAtomicInlineInRuby :
    let col : RubyColumnSizes := { baseMin := 50, baseMax := 50, annotationMins := [0], annotationMaxs := [0] }
    computeRubyColumnMinSize col = 50 := by
  decide

/-- Test `LineBreakerTest, MinMaxWithEmptyRubyBase` (`inline/line_breaker_test.cc:1241`).
    CSS Ruby 1 §4:
    Empty ruby base (size 0) takes column min size directly from the annotation. -/
theorem lineBreaker_minMaxWithEmptyRubyBase :
    let col : RubyColumnSizes := { baseMin := 0, baseMax := 0, annotationMins := [42], annotationMaxs := [42] }
    computeRubyColumnMinSize col = 42 := by
  decide

/-- Test `InlineNodeTest, NestedRubyMinMaxCrash` (`inline/inline_node_test.cc:1786`).
    CSS Ruby 1 §4:
    Nested ruby column intrinsic sizing: inner ruby column size feeds into the outer ruby base size. -/
theorem inlineNode_nestedRubyMinMaxCrash :
    let innerCol : RubyColumnSizes := { baseMin := 20, baseMax := 20, annotationMins := [15], annotationMaxs := [15] }
    let innerMin := computeRubyColumnMinSize innerCol
    let outerCol : RubyColumnSizes := { baseMin := innerMin, baseMax := innerMin, annotationMins := [25], annotationMaxs := [25] }
    computeRubyColumnMinSize outerCol = 25 := by
  decide

/-- Test `JustificationUtilsTest, SetupItemJustificationOpportunityCrash` (`inline/justification_utils_test.cc:14`).
    CSS Text 3 §7.3 & CSS Ruby 1 §3:
    In ruby containers with text-align: justify, ruby annotations and atomic inlines
    do not receive justification expansion opportunities. -/
theorem justificationUtils_setupItemJustificationOpportunityCrash :
    hasRubyJustificationOpportunity true true = false ∧
    hasRubyJustificationOpportunity false false = false := by
  decide

end ChromiumLayout
