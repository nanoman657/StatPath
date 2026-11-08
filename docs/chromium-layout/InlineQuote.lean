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

/-- HTML 5 §4.5.8: The effective language of the quote element itself. -/
def quoteElementLocale (q : QuoteNode) : String :=
  match q.lang with
  | some l => l
  | none => q.parentLang

/-- CSS 2.1 §12.3 & HTML 5 §4.5.8: Quotation punctuation delimiters (::before and ::after)
    inherit the language of the surrounding parent container, not the quote itself. -/
def quoteDelimiterLocale (parentLang : String) (_optLang : Option String) : String :=
  parentLang

/-- HTML 5 §4.5.8: The content text of the quote uses the quote's effective language. -/
def quoteContentLocale (parentLang : String) (optLang : Option String) : String :=
  match optLang with
  | some l => l
  | none => parentLang

/-- Language of the ::before quote delimiter pseudo-element. -/
def quoteBeforeLocale (q : QuoteNode) : String :=
  quoteDelimiterLocale q.parentLang q.lang

/-- Language of the ::after quote delimiter pseudo-element. -/
def quoteAfterLocale (q : QuoteNode) : String :=
  quoteDelimiterLocale q.parentLang q.lang

/-- Language of the text content inside the quote. -/
def quoteTextLocale (q : QuoteNode) : String :=
  quoteContentLocale q.parentLang q.lang

/-! ## 2. General Laws -/

/-- General Law: Quote delimiter language is always the surrounding parent language for any inputs. -/
theorem quote_delimiter_lang (p : String) (optL : Option String) :
    quoteDelimiterLocale p optL = p := by
  rfl

/-- General Law: Content language with no explicit language is the parent language for any inputs. -/
theorem quote_content_lang_none (p : String) :
    quoteContentLocale p none = p := by
  rfl

/-- General Law: Content language with explicit language l is l for any inputs. -/
theorem quote_content_lang_some (p l : String) :
    quoteContentLocale p (some l) = l := by
  rfl

end ChromiumLayout
