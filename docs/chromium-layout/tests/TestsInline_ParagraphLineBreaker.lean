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

end ChromiumLayout.TestsInline
