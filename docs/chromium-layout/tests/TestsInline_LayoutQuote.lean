/-
  docs/chromium-layout/tests/TestsInline_LayoutQuote.lean

  Formalized layout tests for LayoutQuote
  (`third_party/blink/renderer/core/layout/layout_quote_test.cc`).

  Covers:
  - Locale (`layout_quote_test.cc:40`)
-/
import LayoutTypes
import InlineQuote

namespace ChromiumLayout

/-! ## 1. Locale (`layout_quote_test.cc:40`) -/

/-- Test `LayoutQuoteTest, Locale` (`layout_quote_test.cc:40`).
    `<q>` element delimiters use language from parent, while quote text uses element language. -/
theorem layoutQuote_locale :
    let q_ja : QuoteNode := { id := "ja", lang := some "ja", parentLang := "en" }
    let q_fr : QuoteNode := { id := "fr", lang := some "fr", parentLang := "ja" }
    let q_nan : QuoteNode := { id := "nan", lang := none, parentLang := "ja" }
    (quoteElementLocale q_ja = "ja") ∧
    (quoteBeforeLocale q_ja = "en") ∧
    (quoteAfterLocale q_ja = "en") ∧
    (quoteTextLocale q_ja = "ja") ∧
    (quoteElementLocale q_fr = "fr") ∧
    (quoteBeforeLocale q_fr = "ja") ∧
    (quoteAfterLocale q_fr = "ja") ∧
    (quoteTextLocale q_fr = "fr") ∧
    (quoteElementLocale q_nan = "ja") ∧
    (quoteBeforeLocale q_nan = "ja") ∧
    (quoteAfterLocale q_nan = "ja") ∧
    (quoteTextLocale q_nan = "ja") := by
  decide

end ChromiumLayout
