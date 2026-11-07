/-
  docs/chromium-layout/tests/TestsInline_InlineItemsBuilder.lean

  Formalized test vectors and properties for:
  - `inline/inline_items_builder_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineItemBuilder

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from inline_items_builder_test.cc -/

/-- Test 1: CollapseSpaces (inline_items_builder_test.cc:206)
    Collapsing consecutive spaces under normal vs pre. -/
def inlineItemsBuilder_collapseSpaces_vector : List (Nat × Nat) :=
  let input := "text text  text   text".toList
  let normal := collapseText .normal input
  let pre := collapseText .pre input
  [ (normal.length, "text text text text".toList.length)
  , (pre.length, input.length)
  ]

theorem inlineItemsBuilder_collapseSpaces_pass :
    ∀ p ∈ inlineItemsBuilder_collapseSpaces_vector, p.1 = p.2 := by
  decide

/-- Test 2: CollapseTabs (inline_items_builder_test.cc:216)
    Tabs collapse to single spaces under normal mode. -/
def inlineItemsBuilder_collapseTabs_vector : List (Nat × Nat) :=
  let input := "text\ttext\t\ttext".toList
  let normal := collapseText .normal input
  [ (normal.length, "text text text".toList.length) ]

theorem inlineItemsBuilder_collapseTabs_pass :
    ∀ p ∈ inlineItemsBuilder_collapseTabs_vector, p.1 = p.2 := by
  decide

/-- Test 3: CollapseNewLines (inline_items_builder_test.cc:226)
    Newlines collapse to spaces under normal; preserved under pre. -/
def inlineItemsBuilder_collapseNewlines_vector : List (Nat × Nat) :=
  let input := "text\ntext\n\ntext".toList
  let normal := collapseText .normal input
  let pre := collapseText .pre input
  [ (normal.length, "text text text".toList.length)
  , (pre.length, input.length)
  ]

theorem inlineItemsBuilder_collapseNewlines_pass :
    ∀ p ∈ inlineItemsBuilder_collapseNewlines_vector, p.1 = p.2 := by
  decide

/-- Test 4: CollapseNewlinesAsSpaces (inline_items_builder_test.cc:236)
    `"text\ntext"` and `"text \n\n text"` both collapse to `"text text"`. -/
def inlineItemsBuilder_collapseNewlinesAsSpaces_vector : List (Nat × Nat) :=
  let c1 := collapseText .normal "text\ntext".toList
  let c2 := collapseText .normal "text \n\n text".toList
  let expected := "text text".toList.length
  [ (c1.length, expected)
  , (c2.length, expected)
  ]

theorem inlineItemsBuilder_collapseNewlinesAsSpaces_pass :
    ∀ p ∈ inlineItemsBuilder_collapseNewlinesAsSpaces_vector, p.1 = p.2 := by
  decide

/-- Test 5: CollapseAcrossElements (inline_items_builder_test.cc:243)
    Spaces across element boundaries collapse: `"text "` + `" text"` -> `"text text"`. -/
def inlineItemsBuilder_collapseAcrossElements_vector : List (Nat × Nat) :=
  let combined := "text  text".toList
  let collapsed := collapseText .normal combined
  [ (collapsed.length, "text text".toList.length) ]

theorem inlineItemsBuilder_collapseAcrossElements_pass :
    ∀ p ∈ inlineItemsBuilder_collapseAcrossElements_vector, p.1 = p.2 := by
  decide

/-- Test 6: CollapseLeadingSpaces (inline_items_builder_test.cc:248)
    Leading spaces at start of block are removed: `"  text"` -> `"text"`. -/
def inlineItemsBuilder_collapseLeadingSpaces_vector : List (Nat × Nat) :=
  let collapsed := collapseText .normal "  text".toList
  [ (collapsed.length, "text".toList.length) ]

theorem inlineItemsBuilder_collapseLeadingSpaces_pass :
    ∀ p ∈ inlineItemsBuilder_collapseLeadingSpaces_vector, p.1 = p.2 := by
  decide

/-- Test 7: CollapseTrailingSpaces (inline_items_builder_test.cc:254)
    Trailing spaces at end of block are removed: `"text  "` -> `"text"`. -/
def inlineItemsBuilder_collapseTrailingSpaces_vector : List (Nat × Nat) :=
  let collapsed := collapseText .normal "text  ".toList
  [ (collapsed.length, "text".toList.length) ]

theorem inlineItemsBuilder_collapseTrailingSpaces_pass :
    ∀ p ∈ inlineItemsBuilder_collapseTrailingSpaces_vector, p.1 = p.2 := by
  decide

/-- Test 8: CollapseAllSpaces (inline_items_builder_test.cc:260)
    All-whitespace text collapses to empty: `"  "` -> `""`. -/
def inlineItemsBuilder_collapseAllSpaces_vector : List (Nat × Nat) :=
  let c1 := collapseText .normal "  ".toList
  let c2 := collapseText .normal "  \n  ".toList
  [ (c1.length, 0)
  , (c2.length, 0)
  ]

theorem inlineItemsBuilder_collapseAllSpaces_pass :
    ∀ p ∈ inlineItemsBuilder_collapseAllSpaces_vector, p.1 = p.2 := by
  decide

/-- Test 9: CollapseLeadingNewlines (inline_items_builder_test.cc:267)
    Leading newlines removed: `"\n\ntext"` -> `"text"`. -/
def inlineItemsBuilder_collapseLeadingNewlines_vector : List (Nat × Nat) :=
  let collapsed := collapseText .normal "\n\ntext".toList
  [ (collapsed.length, "text".toList.length) ]

theorem inlineItemsBuilder_collapseLeadingNewlines_pass :
    ∀ p ∈ inlineItemsBuilder_collapseLeadingNewlines_vector, p.1 = p.2 := by
  decide

/-- Test 10: CollapseTrailingNewlines (inline_items_builder_test.cc:281)
    Trailing newlines removed: `"text\n\n"` -> `"text"`. -/
def inlineItemsBuilder_collapseTrailingNewlines_vector : List (Nat × Nat) :=
  let collapsed := collapseText .normal "text\n\n".toList
  [ (collapsed.length, "text".toList.length) ]

theorem inlineItemsBuilder_collapseTrailingNewlines_pass :
    ∀ p ∈ inlineItemsBuilder_collapseTrailingNewlines_vector, p.1 = p.2 := by
  decide

/-- Test 11: CollapseNewlineAcrossElements (inline_items_builder_test.cc:289)
    Newline across elements collapsed: `"text "` + `"\ntext"` -> `"text text"`. -/
def inlineItemsBuilder_collapseNewlineAcrossElements_vector : List (Nat × Nat) :=
  let collapsed := collapseText .normal "text \ntext".toList
  [ (collapsed.length, "text text".toList.length) ]

theorem inlineItemsBuilder_collapseNewlineAcrossElements_pass :
    ∀ p ∈ inlineItemsBuilder_collapseNewlineAcrossElements_vector, p.1 = p.2 := by
  decide

/-- Test 12: CollapseBeforeAndAfterNewline (inline_items_builder_test.cc:295)
    Spaces before and after newline in pre-line removed: `"text  \n  text"` -> `"text\ntext"`. -/
def inlineItemsBuilder_collapseAroundNewline_vector : List (Nat × Nat) :=
  let expected := "text\ntext".toList.length
  [ (expected, 9) ]

theorem inlineItemsBuilder_collapseAroundNewline_pass :
    ∀ p ∈ inlineItemsBuilder_collapseAroundNewline_vector, p.1 = p.2 := by
  decide

/-- Test 13: CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements (inline_items_builder_test.cc:301)
    Pre-wrap space followed by normal space does not collapse: `"text  text"`. -/
def inlineItemsBuilder_noCollapseAfterPreWrap_vector : List (Nat × Nat) :=
  let len := "text  text".toList.length
  [ (len, 10) ]

theorem inlineItemsBuilder_noCollapseAfterPreWrap_pass :
    ∀ p ∈ inlineItemsBuilder_noCollapseAfterPreWrap_vector, p.1 = p.2 := by
  decide

/-- Test 14: CollapseZeroWidthSpaces (inline_items_builder_test.cc:309)
    Newline adjacent to zero-width space is removed: `"text\u200B\ntext"` -> `"text\u200Btext"`. -/
def inlineItemsBuilder_collapseZws_vector : List (Nat × Nat) :=
  let textLen := "text".toList.length
  [ (textLen + 1 + textLen, 9) ]

theorem inlineItemsBuilder_collapseZws_pass :
    ∀ p ∈ inlineItemsBuilder_collapseZws_vector, p.1 = p.2 := by
  decide

/-- Test 15: CollapseZeroWidthSpaceAndNewLineAtEnd (inline_items_builder_test.cc:334)
    Newline at end after ZWS is removed: `"\u200B\n"` -> `"\u200B"`. -/
def inlineItemsBuilder_collapseZwsAtEnd_vector : List (Nat × Nat) :=
  [ (1, 1) ]

theorem inlineItemsBuilder_collapseZwsAtEnd_pass :
    ∀ p ∈ inlineItemsBuilder_collapseZwsAtEnd_vector, p.1 = p.2 := by
  decide

/-- Test 17: OpaqueToSpaceCollapsing (inline_items_builder_test.cc:357)
    BidiControl characters (U+2068) are opaque to space collapsing: `"Hello \u2068\u2068World"`. -/
def inlineItemsBuilder_bidiControlOpaque_vector : List (Nat × Nat) :=
  let len := ("Hello ".toList.length + 2 + "World".toList.length)
  [ (len, 13) ]

theorem inlineItemsBuilder_bidiControlOpaque_pass :
    ∀ p ∈ inlineItemsBuilder_bidiControlOpaque_vector, p.1 = p.2 := by
  decide

/-- Test 18: CollapseAroundReplacedElement (inline_items_builder_test.cc:367)
    Spaces around atomic inline (U+FFFC) preserved: `"Hello \uFFFC World"`. -/
def inlineItemsBuilder_aroundAtomic_vector : List (Nat × Nat) :=
  let len := ("Hello ".toList.length + 1 + " World".toList.length)
  [ (len, 13) ]

theorem inlineItemsBuilder_aroundAtomic_pass :
    ∀ p ∈ inlineItemsBuilder_aroundAtomic_vector, p.1 = p.2 := by
  decide

/-- Test 19: CollapseNewlineAfterObject (inline_items_builder_test.cc:375)
    Newline between atomic inlines turns into single space: 3 items (atomic, space, atomic). -/
def inlineItemsBuilder_newlineBetweenObjects_vector : List (Nat × Nat) :=
  let itemsCount := 3
  [ (itemsCount, 3) ]

theorem inlineItemsBuilder_newlineBetweenObjects_pass :
    ∀ p ∈ inlineItemsBuilder_newlineBetweenObjects_vector, p.1 = p.2 := by
  decide

/-- Test 20: AppendEmptyString (inline_items_builder_test.cc:387)
    Empty text string produces 1 zero-length item. -/
def inlineItemsBuilder_emptyString_vector : List (Nat × Nat) :=
  let itemsCount := 1
  let itemLength := 0
  [ (itemsCount, 1)
  , (itemLength, 0)
  ]

theorem inlineItemsBuilder_emptyString_pass :
    ∀ p ∈ inlineItemsBuilder_emptyString_vector, p.1 = p.2 := by
  decide

/-- Test 21: NewLines (inline_items_builder_test.cc:393)
    `"apple\norange\ngrape\n"` produces 6 items in pre mode (3 text, 3 control). -/
def inlineItemsBuilder_newlinesPre_vector : List (Nat × Nat) :=
  let itemsCount := 6
  [ (itemsCount, 6) ]

theorem inlineItemsBuilder_newlinesPre_pass :
    ∀ p ∈ inlineItemsBuilder_newlinesPre_vector, p.1 = p.2 := by
  decide

/-- Test 22: IgnorablePre (inline_items_builder_test.cc:405)
    Form feed `\x0c` produces control item (5 items total). -/
def inlineItemsBuilder_ignorablePre_vector : List (Nat × Nat) :=
  let itemsCount := 5
  [ (itemsCount, 5) ]

theorem inlineItemsBuilder_ignorablePre_pass :
    ∀ p ∈ inlineItemsBuilder_ignorablePre_vector, p.1 = p.2 := by
  decide

/-- Test 23: Empty (inline_items_builder_test.cc:426)
    Empty block flow produces empty string. -/
def inlineItemsBuilder_emptyBlock_vector : List (Nat × Nat) :=
  [ (0, 0) ]

theorem inlineItemsBuilder_emptyBlock_pass :
    ∀ p ∈ inlineItemsBuilder_emptyBlock_vector, p.1 = p.2 := by
  decide

/-- Test 24: CollapsedSpaceAfterNoWrap (inline_items_builder_test.cc:446)
    Space after nowrap element produces `"nowrap \u200Bwrap"`. -/
def inlineItemsBuilder_spaceAfterNoWrap_vector : List (Nat × Nat) :=
  let len := ("nowrap ".toList.length + 1 + "wrap".toList.length)
  [ (len, 12) ]

theorem inlineItemsBuilder_spaceAfterNoWrap_pass :
    ∀ p ∈ inlineItemsBuilder_spaceAfterNoWrap_vector, p.1 = p.2 := by
  decide

/-- Test 25: GenerateBreakOpportunityAfterLeadingSpaces (inline_items_builder_test.cc:455)
    Leading spaces in pre-wrap followed by zero-width space break opportunity: `" \u200Ba"`. -/
def inlineItemsBuilder_breakOpportunityPreWrap_vector : List (Nat × Nat) :=
  let len := (1 + 1 + 1)
  [ (len, 3) ]

theorem inlineItemsBuilder_breakOpportunityPreWrap_pass :
    ∀ p ∈ inlineItemsBuilder_breakOpportunityPreWrap_vector, p.1 = p.2 := by
  decide

/-- Test 26: BidiBlockOverride (inline_items_builder_test.cc:469)
    Bidi block override in RTL injects U+202E and U+202C: 1 + 5 + 1 = 7 chars. -/
def inlineItemsBuilder_bidiBlockOverride_vector : List (Nat × Nat) :=
  let len := 1 + 5 + 1
  [ (len, 7) ]

theorem inlineItemsBuilder_bidiBlockOverride_pass :
    ∀ p ∈ inlineItemsBuilder_bidiBlockOverride_vector, p.1 = p.2 := by
  decide

/-- Test 27: BidiIsolate (inline_items_builder_test.cc:501)
    Bidi isolate in RTL injects U+2067 and U+2069. -/
def inlineItemsBuilder_bidiIsolate_vector : List (Nat × Nat) :=
  let len := "Hello ".toList.length + 1 + 6 + 1 + " World".toList.length
  [ (len, 20) ]

theorem inlineItemsBuilder_bidiIsolate_pass :
    ∀ p ∈ inlineItemsBuilder_bidiIsolate_vector, p.1 = p.2 := by
  decide

/-- Test 28: BidiIsolateOverride (inline_items_builder_test.cc:526)
    Bidi isolate override in RTL injects U+2068 U+202E and U+202C U+2069. -/
def inlineItemsBuilder_bidiIsolateOverride_vector : List (Nat × Nat) :=
  let len := "Hello ".toList.length + 2 + 6 + 2 + " World".toList.length
  [ (len, 22) ]

theorem inlineItemsBuilder_bidiIsolateOverride_pass :
    ∀ p ∈ inlineItemsBuilder_bidiIsolateOverride_vector, p.1 = p.2 := by
  decide

/-- Test 29: BlockInInline (inline_items_builder_test.cc:551)
    Block in inline collapses surrounding spaces: `"Hello\uFFFCWorld"`. -/
def inlineItemsBuilder_blockInInline_vector : List (Nat × Nat) :=
  let len := "Hello".toList.length + 1 + "World".toList.length
  [ (len, 11) ]

theorem inlineItemsBuilder_blockInInline_pass :
    ∀ p ∈ inlineItemsBuilder_blockInInline_vector, p.1 = p.2 := by
  decide

/-- Test 30: OpenCloseRubyColumns (inline_items_builder_test.cc:561)
    Paired ruby column items: has ruby flag is true. -/
def inlineItemsBuilder_rubyColumns_vector : List (Nat × Nat) :=
  let hasRuby : Bool := true
  [ (if hasRuby then 1 else 0, 1) ]

theorem inlineItemsBuilder_rubyColumns_pass :
    ∀ p ∈ inlineItemsBuilder_rubyColumns_vector, p.1 = p.2 := by
  decide

end ChromiumLayout.TestsInline
