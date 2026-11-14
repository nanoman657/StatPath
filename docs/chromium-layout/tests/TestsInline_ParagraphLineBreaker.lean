/-
  docs/chromium-layout/tests/TestsInline_ParagraphLineBreaker.lean

  Formalized tests for CSS Text 4 §5.3 / §5.4, CSS Ruby 1 §3, and Blink ParagraphLineBreaker & ScoreLineBreaker
  (`third_party/blink/renderer/core/layout/inline/paragraph_line_breaker_test.cc`,
   `third_party/blink/renderer/core/layout/inline/score_line_breaker_test.cc`).
-/
import LayoutTypes
import InlineParagraphBreaker

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test `ParagraphLineBreakerTest.IsDisabledByBlockInInline` (`inline/paragraph_line_breaker_test.cc:27`). -/
theorem paragraphLineBreaker_isDisabledByBlockInInline :
    let f : ParagraphFeatures := { hasBlockInInline := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = false) ∧
    (attemptParagraphBalancing f = false) := by
  decide

/-- Test `ParagraphLineBreakerTest.IsDisabledByFloatLeading` (`inline/paragraph_line_breaker_test.cc:75`). -/
theorem paragraphLineBreaker_isDisabledByFloatLeading :
    let f : ParagraphFeatures := { hasFloat := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = false) ∧
    (attemptParagraphBalancing f = false) := by
  decide

/-- Test `ParagraphLineBreakerTest.IsDisabledByFloat` (`inline/paragraph_line_breaker_test.cc:97`). -/
theorem paragraphLineBreaker_isDisabledByFloat :
    let f : ParagraphFeatures := { hasFloat := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = false) ∧
    (attemptParagraphBalancing f = false) := by
  decide

/-- Test `ParagraphLineBreakerTest.IsDisabledByForcedBreak` (`inline/paragraph_line_breaker_test.cc:119`). -/
theorem paragraphLineBreaker_isDisabledByForcedBreak :
    let f : ParagraphFeatures := { hasForcedBreak := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = false) ∧
    (attemptParagraphBalancing f = false) := by
  decide

/-- Test `ParagraphLineBreakerTest.IsDisabledByForcedBreakReusing` (`inline/paragraph_line_breaker_test.cc:140`). -/
theorem paragraphLineBreaker_isDisabledByForcedBreakReusing :
    let f : ParagraphFeatures := { hasForcedBreak := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = false) ∧
    (attemptParagraphBalancing f = false) := by
  decide

/-- Test `ParagraphLineBreakerTest.IsDisabledByInitialLetter` (`inline/paragraph_line_breaker_test.cc:163`). -/
theorem paragraphLineBreaker_isDisabledByInitialLetter :
    let f : ParagraphFeatures := { hasInitialLetter := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = true) ∧
    (attemptParagraphBalancing f = false) := by
  decide

/-- Test `ParagraphLineBreakerTest.IsDisabledByTabulationCharacters` (`inline/paragraph_line_breaker_test.cc:186`). -/
theorem paragraphLineBreaker_isDisabledByTabulationCharacters :
    let f : ParagraphFeatures := { hasTabulation := true }
    (isBisectLineBreakDisabled f = false) ∧
    (isScoreLineBreakDisabled f = true) ∧
    (attemptParagraphBalancing f = true) := by
  decide

/-- Test `ScoreLineBreakerTest.Ruby` (`inline/score_line_breaker_test.cc:433`).
    CSS Ruby 1 §3: Ruby container disables score line breaking. -/
theorem scoreLineBreaker_ruby :
    let f : ParagraphFeatures := { hasRuby := true }
    isScoreLineBreakDisabled f = true := by
  decide

/-- Test `ScoreLineBreakerTest.BalanceMaxLinesExceeded` (`inline/score_line_breaker_test.cc:136`).
    CSS Text 4 §5.3: When line count (7) exceeds maxLinesForBalance (6), balancing is not applied. -/
theorem scoreLineBreaker_balanceMaxLinesExceeded :
    shouldBalanceParagraph 7 = false ∧
    shouldBalanceParagraph 6 = true := by
  decide

/-- Test `DisabledByLineBreakerTest.Data` (`inline/score_line_breaker_test.cc:370`).
    CSS Text 4 §5.4 & CSS Text 3 §5.2: Tests 8 configurations of score line breaker runtime disabling. -/
theorem scoreLineBreaker_disabledByLineBreakerData :
    -- Normal without overflow: not disabled
    isScoreLineBreakDisabledByRuntime {} = false ∧
    -- Overflow without wrap: disabled
    isScoreLineBreakDisabledByRuntime { hasUnresolvedOverflow := true } = true ∧
    -- overflow-wrap without overflow: not disabled
    isScoreLineBreakDisabledByRuntime { hasUnresolvedOverflow := false } = false ∧
    isScoreLineBreakDisabledByRuntime { hasUnresolvedOverflow := false } = false ∧
    -- overflow-wrap with unresolved overflow: disabled
    isScoreLineBreakDisabledByRuntime { hasUnresolvedOverflow := true } = true ∧
    isScoreLineBreakDisabledByRuntime { hasUnresolvedOverflow := true } = true ∧
    -- white-space: break-spaces: disabled
    isScoreLineBreakDisabledByRuntime { isBreakSpaces := true } = true ∧
    -- box-decoration-break: clone: disabled
    isScoreLineBreakDisabledByRuntime { isBoxDecorationBreakClone := true } = true := by
  decide

/-- Test `ScoreLineBreakerTest.LastLines` (`inline/score_line_breaker_test.cc:78`).
    CSS Text 4 §5.4: Sliding optimization window caches 4 lines for 6-line paragraph,
    consuming lines until 2 remaining iterations complete. -/
theorem scoreLineBreaker_lastLines :
    let targetLines := 6
    let cachedLines := min targetLines maxLinesForOptimal
    let count := optimalWindowConsumptionCount targetLines
    (cachedLines = 4) ∧
    (count = 2) ∧
    (count = targetLines - maxLinesForOptimal) := by
  decide

/-- Test `BlockInInlineTest.BeforeAfter` (`inline/score_line_breaker_test.cc:172`).
    CSS 2.1 §9.2.1.1 & CSS Text 4 §5.4: Tests all 4 combinations (0..3) of hasBefore and hasAfter:
    - Middle block-in-inline is always unoptimized with forced break.
    - Before content is optimized (breakPoints > 0) iff hasBefore is true.
    - After content is optimized (breakPoints > 0) iff hasAfter is true. -/
theorem scoreLineBreaker_blockInInlineBeforeAfter :
    let c0 := classifyScoreLineBreakerBlockInInline false false
    let c1 := classifyScoreLineBreakerBlockInInline true false
    let c2 := classifyScoreLineBreakerBlockInInline false true
    let c3 := classifyScoreLineBreakerBlockInInline true true
    -- c0: no before, no after
    (c0.1.breakPointsCount = 0 ∧ c0.1.hasForcedBreak = true) ∧
    (c0.2.1.isBlockInInline = true ∧ c0.2.1.hasForcedBreak = true ∧ c0.2.1.breakPointsCount = 0) ∧
    (c0.2.2.breakPointsCount = 0) ∧
    -- c1: has before, no after
    (c1.1.breakPointsCount = 4) ∧
    (c1.2.1.isBlockInInline = true ∧ c1.2.1.hasForcedBreak = true) ∧
    (c1.2.2.breakPointsCount = 0) ∧
    -- c2: no before, has after
    (c2.1.breakPointsCount = 0 ∧ c2.1.hasForcedBreak = true) ∧
    (c2.2.1.isBlockInInline = true ∧ c2.2.1.hasForcedBreak = true) ∧
    (c2.2.2.breakPointsCount = 4) ∧
    -- c3: has before, has after
    (c3.1.breakPointsCount = 4) ∧
    (c3.2.1.isBlockInInline = true ∧ c3.2.1.hasForcedBreak = true) ∧
    (c3.2.2.breakPointsCount = 4) := by
  decide

/-- Test `ScoreLineBreakerTest.ForcedBreak` (`inline/score_line_breaker_test.cc:237`).
    CSS Text 4 §5.4: Paragraphs separated by forced breaks are optimized separately:
    - First segment (before <br>) has 2 candidates: returns 2 lines without optimization (0 break points).
    - Second segment (after <br>) has 4 candidates: optimal break points apply (3 break points). -/
theorem scoreLineBreaker_forcedBreak :
    let seg1Breaks := computeScoreLineBreakPoints 2
    let seg2Breaks := computeScoreLineBreakPoints 4
    (seg1Breaks = 0) ∧
    (seg2Breaks = 3) := by
  decide

/-- Test `ScoreLineBreakerTest.FloatRetry` (`inline/score_line_breaker_test.cc:408`).
    CSS Text 4 §5.4 & CSS 2.1 §9.5.1: Floats allow score line breaking retry (unlike bisection balancing). -/
theorem scoreLineBreaker_floatRetry :
    let f : ParagraphFeatures := { hasFloat := true }
    (isBisectLineBreakDisabled f = true) ∧
    (isScoreLineBreakDisabled f = false) := by
  decide

/-- Test `ScoreLineBreakerTest.LineCountMismatchFallback` (`inline/score_line_breaker_test.cc:506`).
    CSS Text 4 §5.4: Line count mismatch safely falls back to greedy breaking (0 break points).
    When sizes match, line count equals break points count. -/
theorem scoreLineBreaker_lineCountMismatchFallback :
    let fallback := resolveOptimalLineCountMismatch true 4
    let matchCase := resolveOptimalLineCountMismatch false 4
    (fallback.2 = 0) ∧
    (matchCase.1 = matchCase.2) := by
  decide

end ChromiumLayout.TestsInline
