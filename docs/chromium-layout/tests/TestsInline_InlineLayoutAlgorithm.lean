/-
  docs/chromium-layout/tests/TestsInline_InlineLayoutAlgorithm.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/inline_layout_algorithm_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineLayoutAlgorithm
import InlineRuby

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Test 4: BreakToken (inline_layout_algorithm_test.cc:192) -/
theorem test_BreakToken_chain :
    let t1 := advanceBreakToken 3 none 1
    let t2 := advanceBreakToken 3 t1 1
    let t3 := advanceBreakToken 3 t2 1
    t1 = some { itemIndex := 1, textOffset := 4 } ∧
    t2 = some { itemIndex := 2, textOffset := 8 } ∧
    t3 = none := by
  decide

/-! ### Test 7: InlineBoxBorderPadding (inline_layout_algorithm_test.cc:333) -/
theorem test_InlineBoxBorderPadding_partition :
    let borders : PhysicalBoxStrut := { left := 1, top := 2, right := 3, bottom := 4 }
    let padding : PhysicalBoxStrut := { left := 5, top := 6, right := 7, bottom := 8 }
    let b1 := partitionInlineStrut borders true false
    let p1 := partitionInlineStrut padding true false
    let b2 := partitionInlineStrut borders false true
    let p2 := partitionInlineStrut padding false true
    b1 = { left := 1, top := 2, right := 0, bottom := 4 } ∧
    p1 = { left := 5, top := 6, right := 0, bottom := 8 } ∧
    strutContentOffset b1 p1 = (6, 8) ∧
    b2 = { left := 0, top := 2, right := 3, bottom := 4 } ∧
    p2 = { left := 0, top := 6, right := 7, bottom := 8 } ∧
    strutContentOffset b2 p2 = (0, 8) := by
  decide

/-! ### Test 10: TextFloatsAroundFloatsBefore (inline_layout_algorithm_test.cc:454) -/
theorem test_TextFloatsAroundFloatsBefore :
    let fLeft1 : FloatExclusion := { isLeft := true, width := 30, height := 30 }
    let fLeft2 : FloatExclusion := { isLeft := true, width := 10, height := 10 }
    let offsetLine0 := lineLeftOffset [fLeft1, fLeft2] 0
    let offsetLine1 := lineLeftOffset [fLeft1] 0
    let offsetLine2 := lineLeftOffset [] 0
    offsetLine0 = 40 ∧ offsetLine1 = 30 ∧ offsetLine2 = 0 := by
  decide

/-! ### Test 15: PositionFloatsWithMargins (inline_layout_algorithm_test.cc:670) -/
theorem test_PositionFloatsWithMargins :
    let floatLeft : FloatExclusion := { isLeft := true, width := 5, height := 30, marginInlineStart := 20, marginInlineEnd := 20 }
    let bodyMargin := 8
    let spanOffsetLeft := bodyMargin + floatLeft.totalWidth
    floatLeft.totalWidth = 45 ∧ spanOffsetLeft = 53 := by
  decide

/-! ### Test 16: InkOverflow (inline_layout_algorithm_test.cc:694) -/
theorem test_InkOverflow :
    inkOverflowVertical 10 20 = (-5, 20) := by
  rfl

/-! ### Test 21: LineBoxWithHangingWidthRTLRightAligned (inline_layout_algorithm_test.cc:806) -/
theorem test_LineBoxWithHangingWidthRTLRightAligned :
    let a := computeHangingLineRect 100 30 20 10 .conditional .right
    let b := computeHangingLineRect 100 30 20 10 .unconditional .right
    let c := computeHangingLineRect 100 30 80 10 .conditional .right
    let d := computeHangingLineRect 100 30 80 10 .unconditional .right
    a = { x := 50, y := 0, width := 50, height := 10 } ∧
    b = { x := 70, y := 0, width := 30, height := 10 } ∧
    c = { x := 0, y := 0, width := 100, height := 10 } ∧
    d = { x := 70, y := 0, width := 30, height := 10 } := by
  decide

/-! ### Test 22: LineBoxWithHangingWidthRTLCenterAligned (inline_layout_algorithm_test.cc:839) -/
theorem test_LineBoxWithHangingWidthRTLCenterAligned :
    let a := computeHangingLineRect 100 30 20 10 .conditional .center
    let b := computeHangingLineRect 100 30 20 10 .unconditional .center
    let c := computeHangingLineRect 100 30 60 10 .conditional .center
    let d := computeHangingLineRect 100 30 60 10 .unconditional .center
    let e := computeHangingLineRect 100 30 80 10 .conditional .center
    let f := computeHangingLineRect 100 30 80 10 .unconditional .center
    a = { x := 25, y := 0, width := 50, height := 10 } ∧
    b = { x := 35, y := 0, width := 30, height := 10 } ∧
    c = { x := 5, y := 0, width := 90, height := 10 } ∧
    d = { x := 35, y := 0, width := 30, height := 10 } ∧
    e = { x := 0, y := 0, width := 100, height := 10 } ∧
    f = { x := 35, y := 0, width := 30, height := 10 } := by
  decide

/-! ### Test 23: TextBoxTrimConstraintSpace (inline_layout_algorithm_test.cc:888) -/
theorem test_TextBoxTrimConstraintSpace :
    let children : List TrimChild := [
      { id := "abs1", isInFlow := false },
      { id := "float1", isInFlow := false },
      { id := "empty_before", isInFlow := true },
      { id := "nested_empty_before", isInFlow := true },
      { id := "middle", isInFlow := true },
      { id := "nested_empty_after", isInFlow := true },
      { id := "empty_after", isInFlow := true },
      { id := "abs2", isInFlow := false },
      { id := "float2", isInFlow := false }
    ]
    let res := computeTextBoxTrim children true
    res.lookup "empty_before" = some { shouldTrimStart := true, shouldTrimEnd := false } ∧
    res.lookup "empty_after" = some { shouldTrimStart := false, shouldTrimEnd := true } ∧
    res.lookup "abs1" = some { shouldTrimStart := false, shouldTrimEnd := false } ∧
    res.lookup "float1" = some { shouldTrimStart := false, shouldTrimEnd := false } ∧
    res.lookup "middle" = some { shouldTrimStart := false, shouldTrimEnd := false } := by
  decide

/-! ### Test 24: TextBoxTrimConstraintSpaceSingle (inline_layout_algorithm_test.cc:944) -/
theorem test_TextBoxTrimConstraintSpaceSingle :
    let children : List TrimChild := [
      { id := "single", isInFlow := true },
      { id := "empty_after", isInFlow := true }
    ]
    let res := computeTextBoxTrim children true
    res.lookup "single" = some { shouldTrimStart := true, shouldTrimEnd := false } ∧
    res.lookup "empty_after" = some { shouldTrimStart := false, shouldTrimEnd := true } := by
  decide

/-! ### Test 25: TextBoxTrimConstraintSpaceEmptyOnly (inline_layout_algorithm_test.cc:967) -/
theorem test_TextBoxTrimConstraintSpaceEmptyOnly :
    let children : List TrimChild := [
      { id := "empty", isInFlow := true }
    ]
    let res := computeTextBoxTrim children true
    res.lookup "empty" = some { shouldTrimStart := true, shouldTrimEnd := true } := by
  decide

/-! ### Test 26: TextBoxTrimConstraintSpaceNone (inline_layout_algorithm_test.cc:984) -/
theorem test_TextBoxTrimConstraintSpaceNone :
    computeTextBoxTrim [] true = [] := by
  rfl

/-! ### Test 31: EllipsisFallbackToDots (inline_layout_algorithm_test.cc:1086) -/
theorem test_EllipsisFallbackToDots :
    selectEllipsisString false = "..." := by
  rfl

/-- Test `InlineLayoutAlgorithmTest.TypesForBlockInInline` (`inline/inline_layout_algorithm_test.cc:137`).
    CSS 2.1 §9.2.1.1: Anonymous block-in-inline line box fragment classification across
    regular, self-collapsing, and fixed-height blocks. -/
theorem inlineLayoutAlgorithm_typesForBlockInInline :
    let normal := classifyBlockInInline false false
    let empty := classifyBlockInInline true false
    let height := classifyBlockInInline true true
    -- Normal block
    (normal[0]!.isEmptyLineBox = true ∧ normal[0]!.isBlockInInline = false) ∧
    (normal[1]!.isEmptyLineBox = false ∧ normal[1]!.isBlockInInline = true ∧ normal[1]!.blockCount = 1) ∧
    (normal[2]!.isEmptyLineBox = true ∧ normal[2]!.isBlockInInline = false) ∧
    -- Self-collapsing block
    (empty[1]!.isEmptyLineBox = true ∧ empty[1]!.isBlockInInline = true) ∧
    -- Non-self-collapsing block with height
    (height[1]!.isEmptyLineBox = false ∧ height[1]!.isBlockInInline = true) := by
  decide

/-- Test `InlineLayoutAlgorithmTest.RubyTextEmphasisAnnotationMetricsVerticalLr` (`inline/inline_layout_algorithm_test.cc:1272`).
    CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Annotation metrics in vertical-lr writing mode for ruby with text emphasis. -/
theorem inlineLayoutAlgorithm_rubyTextEmphasisAnnotationMetricsVerticalLr :
    let test1 := computeAnnotationMetrics { hasRuby := true, rubyPosition := .under, hasEmphasis := true, emphasisPosition := .under, fontSize := 20 }
    let test2 := computeAnnotationMetrics { hasRuby := true, rubyPosition := .over, hasEmphasis := true, emphasisPosition := .over, fontSize := 20 }
    let test3 := computeAnnotationMetrics { hasRuby := false, fontSize := 20 }
    (test1.ascent = 0 ∧ test1.descent = 10) ∧
    (test2.ascent = 10 ∧ test2.descent = 0) ∧
    (test3.ascent = 0 ∧ test3.descent = 0) := by
  decide

/-- Test `InlineLayoutAlgorithmTest.RubyTextEmphasisAnnotationMetricsVerticalRl` (`inline/inline_layout_algorithm_test.cc:1276`).
    CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Annotation metrics in vertical-rl writing mode for ruby with text emphasis. -/
theorem inlineLayoutAlgorithm_rubyTextEmphasisAnnotationMetricsVerticalRl :
    let test1 := computeAnnotationMetrics { hasRuby := true, rubyPosition := .under, hasEmphasis := true, emphasisPosition := .under, fontSize := 20 }
    let test2 := computeAnnotationMetrics { hasRuby := true, rubyPosition := .over, hasEmphasis := true, emphasisPosition := .over, fontSize := 20 }
    let test3 := computeAnnotationMetrics { hasRuby := false, fontSize := 20 }
    (test1.ascent = 0 ∧ test1.descent = 10) ∧
    (test2.ascent = 10 ∧ test2.descent = 0) ∧
    (test3.ascent = 0 ∧ test3.descent = 0) := by
  decide

/-- Test `InlineLayoutAlgorithmTest.RubyTextEmphasisAnnotationMetricsHorizontal` (`inline/inline_layout_algorithm_test.cc:1280`).
    CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Annotation metrics in horizontal writing mode:
    1. Ruby and Emphasis both Under: ascent = 0, descent = 10; non-ruby text after: 0, 0.
    2. Ruby and Emphasis both Over: ascent = 10, descent = 0.
    3. Base only with Emphasis Under: 0, 0.
    4. Multiple columns on same line: column A ascent 20, column B aligned ascent 12. -/
theorem inlineLayoutAlgorithm_rubyTextEmphasisAnnotationMetricsHorizontal :
    let test1A := computeAnnotationMetrics { hasRuby := true, rubyPosition := .under, hasEmphasis := true, emphasisPosition := .under, fontSize := 20 }
    let test1After := computeAnnotationMetrics { hasRuby := false, fontSize := 20 }
    let test2B := computeAnnotationMetrics { hasRuby := true, rubyPosition := .over, hasEmphasis := true, emphasisPosition := .over, fontSize := 20 }
    let test3C := computeAnnotationMetrics { hasRuby := false, fontSize := 20 }
    let test4A := computeAnnotationMetrics { hasRuby := true, rubyPosition := .over, rubyAnnoHeight := 20, fontSize := 20 }
    let test4B := computeAnnotationMetrics { hasRuby := true, rubyPosition := .over, rubyAnnoHeight := 12, fontSize := 20 }
    (test1A.ascent = 0 ∧ test1A.descent = 10) ∧
    (test1After.ascent = 0 ∧ test1After.descent = 0) ∧
    (test2B.ascent = 10 ∧ test2B.descent = 0) ∧
    (test3C.ascent = 0 ∧ test3C.descent = 0) ∧
    (test4A.ascent = 20 ∧ test4A.descent = 0) ∧
    (test4B.ascent = 12 ∧ test4B.descent = 0) := by
  decide

/-- Test `InlineLayoutAlgorithmTest.RubyTextEmphasisHeight` (`inline/inline_layout_algorithm_test.cc:1373`).
    CSS 2.1 §10.8, CSS Ruby 1 §3.2, CSS Text Decoration 3 §3.5:
    Line box height for text with emphasis only, both ruby & emphasis, and ruby only are all equal. -/
theorem inlineLayoutAlgorithm_rubyTextEmphasisHeight :
    let p1Height := computeAnnotatedLineHeight 80 0 40 0 0 + 2
    let p2Height := computeAnnotatedLineHeight 80 40 40 0 0 + 2
    let p3Height := computeAnnotatedLineHeight 80 40 0 0 0 + 2
    (p1Height = 122) ∧
    (p1Height = p2Height) ∧
    (p1Height = p3Height) := by
  decide

end ChromiumLayout.TestsInline
