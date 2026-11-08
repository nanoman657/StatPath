/-
  docs/chromium-layout/tests/TestsInline_ParagraphLineBreaker.lean

  Formalized tests for CSS Text 4 §5.3 / §5.4 and Blink ParagraphLineBreaker
  (`third_party/blink/renderer/core/layout/inline/paragraph_line_breaker_test.cc`).
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

end ChromiumLayout.TestsInline
