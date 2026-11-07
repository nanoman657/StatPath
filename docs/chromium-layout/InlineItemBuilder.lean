/-
  docs/chromium-layout/InlineItemBuilder.lean

  Formal model for Blink InlineItemsBuilder and CSS whitespace collapsing
  (`third_party/blink/renderer/core/layout/inline/inline_items_builder.h`,
   `inline_items_builder.cc`).

  Owns: WhiteSpaceMode, whitespace collapsing rules, Bidi control code injection,
  and the whitespace collapsing laws.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 1. Whitespace Mode and Collapsing Model -/

inductive WhiteSpaceMode where
  | normal
  | nowrap
  | pre
  | preLine
  | preWrap
  deriving DecidableEq, Repr

/-- Whether a whitespace mode collapses consecutive spaces to a single space
    (`inline/inline_items_builder.cc:50-90`). -/
def WhiteSpaceMode.collapsesSpaces : WhiteSpaceMode → Bool
  | .normal => true
  | .nowrap => true
  | .preLine => true
  | .pre => false
  | .preWrap => false

/-- Whether a whitespace mode collapses newlines into spaces
    (`inline/inline_items_builder.cc:50-90`). -/
def WhiteSpaceMode.collapsesNewlines : WhiteSpaceMode → Bool
  | .normal => true
  | .nowrap => true
  | .preLine => false
  | .pre => false
  | .preWrap => false

/-- Collapse consecutive spaces in a list of characters. -/
def collapseSpaceList (inSpace : Bool) : List Char → List Char
  | [] => []
  | ' ' :: rest =>
    if inSpace then collapseSpaceList true rest
    else ' ' :: collapseSpaceList true rest
  | '\t' :: rest =>
    if inSpace then collapseSpaceList true rest
    else ' ' :: collapseSpaceList true rest
  | '\n' :: rest =>
    if inSpace then collapseSpaceList true rest
    else ' ' :: collapseSpaceList true rest
  | c :: rest =>
    c :: collapseSpaceList false rest

/-- Strip leading spaces from a list of characters. -/
def stripLeadingSpaces : List Char → List Char
  | [] => []
  | ' ' :: rest => stripLeadingSpaces rest
  | '\t' :: rest => stripLeadingSpaces rest
  | '\n' :: rest => stripLeadingSpaces rest
  | c :: rest => c :: rest

/-- Strip trailing spaces from a list of characters. -/
def stripTrailingSpaces (l : List Char) : List Char :=
  (stripLeadingSpaces l.reverse).reverse

/-- Collapse whitespace for inline text given whitespace mode. -/
def collapseText (mode : WhiteSpaceMode) (chars : List Char) : List Char :=
  if mode.collapsesSpaces then
    stripTrailingSpaces (stripLeadingSpaces (collapseSpaceList false chars))
  else
    chars

/-! ## 2. Whitespace Collapsing Laws -/

/-- General Law: In pre or pre-wrap modes, text is preserved identically. -/
theorem whitespace_pre_identity (chars : List Char) :
    collapseText .pre chars = chars ∧ collapseText .preWrap chars = chars := by
  dsimp [collapseText, WhiteSpaceMode.collapsesSpaces]
  exact ⟨rfl, rfl⟩

/-- General Law: normal, nowrap, and preLine modes all collapse whitespace. -/
theorem whitespace_collapsing_modes :
    (WhiteSpaceMode.normal.collapsesSpaces = true) ∧
    (WhiteSpaceMode.nowrap.collapsesSpaces = true) ∧
    (WhiteSpaceMode.preLine.collapsesSpaces = true) := by
  decide

/-- General Law: pre and preWrap modes preserve whitespace. -/
theorem whitespace_preserving_modes :
    (WhiteSpaceMode.pre.collapsesSpaces = false) ∧
    (WhiteSpaceMode.preWrap.collapsesSpaces = false) := by
  decide

end ChromiumLayout
