/-
  docs/chromium-layout/InlineQuote.lean

  Formal model for CSS 2.1 §12.3 quotes and HTML 5 §4.5.8 <q> language inheritance
  (`third_party/blink/renderer/core/layout/layout_quote.h`).
-/
import LayoutTypes

namespace ChromiumLayout

/-! ## 1. Quote Delimiter Locale Resolution -/

/-- HTML 5 §4.5.8: Quote element node specifying optional language and parent context language. -/
structure QuoteNode where
  id : String
  lang : Option String := none
  parentLang : String
  deriving DecidableEq, Repr, Inhabited

/-- CSS 2.1 §12.3 & HTML 5 §4.5.8: Quotation punctuation delimiters (::before and ::after)
    inherit the language of the surrounding parent container, not the quote itself. -/
def quoteDelimiterLocale (parentLang : String) : String :=
  parentLang

/-- HTML 5 §4.5.8: The effective content language of the quote element. -/
def quoteContentLocale (q : QuoteNode) : String :=
  match q.lang with
  | some l => l
  | none => q.parentLang

/-- Language of the ::before quote delimiter pseudo-element. -/
def quoteBeforeLocale (q : QuoteNode) : String :=
  quoteDelimiterLocale q.parentLang

/-- Language of the ::after quote delimiter pseudo-element. -/
def quoteAfterLocale (q : QuoteNode) : String :=
  quoteDelimiterLocale q.parentLang

/-! ## 2. General Laws -/

/-- General Law: Quote delimiter language is always the surrounding parent language for any input. -/
theorem quote_delimiter_lang (p : String) :
    quoteDelimiterLocale p = p := by
  rfl

/-- General Law: Content language with no explicit language is the parent language for any inputs. -/
theorem quote_content_lang_none (p id : String) :
    quoteContentLocale { id := id, lang := none, parentLang := p } = p := by
  rfl

/-- General Law: Content language with explicit language l is l for any inputs. -/
theorem quote_content_lang_some (p id l : String) :
    quoteContentLocale { id := id, lang := some l, parentLang := p } = l := by
  rfl

end ChromiumLayout
