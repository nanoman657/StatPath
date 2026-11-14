/-
  docs/chromium-layout/tests/TestsInline_InlineItemsBuilder.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/inline_items_builder_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineItemBuilder
import InlineBidi

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from inline_items_builder_test.cc -/

/-- Test 1: CollapseSpaces (inline_items_builder_test.cc:206) -/
theorem inlineItemsBuilder_collapseSpaces :
    let input := "text text  text   text".toList
    String.ofList (collapseText .normal input) = "text text text text" ∧
    String.ofList (collapseText .pre input) = "text text  text   text" := by
  decide

/-- Test 2: CollapseTabs (inline_items_builder_test.cc:216) -/
theorem inlineItemsBuilder_collapseTabs :
    let input := "text\ttext\t\ttext".toList
    String.ofList (collapseText .normal input) = "text text text" := by
  decide

/-- Test 3: CollapseNewLines (inline_items_builder_test.cc:226) -/
theorem inlineItemsBuilder_collapseNewlines :
    let input := "text\ntext\n\ntext".toList
    String.ofList (collapseText .normal input) = "text text text" ∧
    String.ofList (collapseText .pre input) = "text\ntext\n\ntext" := by
  decide

/-- Test 4: CollapseNewlinesAsSpaces (inline_items_builder_test.cc:236) -/
theorem inlineItemsBuilder_collapseNewlinesAsSpaces :
    String.ofList (collapseText .normal "text\ntext".toList) = "text text" ∧
    String.ofList (collapseText .normal "text \n\n text".toList) = "text text" := by
  decide

/-- Test 5: CollapseAcrossElements (inline_items_builder_test.cc:243) -/
theorem inlineItemsBuilder_collapseAcrossElements :
    String.ofList (collapseText .normal "text  text".toList) = "text text" := by
  decide

/-- Test 6: CollapseLeadingSpaces (inline_items_builder_test.cc:248) -/
theorem inlineItemsBuilder_collapseLeadingSpaces :
    String.ofList (collapseText .normal "  text".toList) = "text" := by
  decide

/-- Test 7: CollapseTrailingSpaces (inline_items_builder_test.cc:254) -/
theorem inlineItemsBuilder_collapseTrailingSpaces :
    String.ofList (collapseText .normal "text  ".toList) = "text" := by
  decide

/-- Test 8: CollapseAllSpaces (inline_items_builder_test.cc:260) -/
theorem inlineItemsBuilder_collapseAllSpaces :
    String.ofList (collapseText .normal "  ".toList) = "" ∧
    String.ofList (collapseText .normal "  \n  ".toList) = "" := by
  decide

/-- Test 9: CollapseLeadingNewlines (inline_items_builder_test.cc:267) -/
theorem inlineItemsBuilder_collapseLeadingNewlines :
    String.ofList (collapseText .normal "\n\ntext".toList) = "text" := by
  decide

/-- Test 10: CollapseTrailingNewlines (inline_items_builder_test.cc:281) -/
theorem inlineItemsBuilder_collapseTrailingNewlines :
    String.ofList (collapseText .normal "text\n\n".toList) = "text" := by
  decide

/-- Test 11: CollapseNewlineAcrossElements (inline_items_builder_test.cc:289) -/
theorem inlineItemsBuilder_collapseNewlineAcrossElements :
    String.ofList (collapseText .normal "text \ntext".toList) = "text text" := by
  decide

/-- Test 12: BidiBlockOverride (inline_items_builder_test.cc:469) -/
theorem inlineItemsBuilder_bidiBlockOverride :
    wrapBidi .bidiOverride .rtl "Hello" = "\u202EHello\u202C" := by
  decide

/-- Test 13: BidiIsolate (inline_items_builder_test.cc:501) -/
theorem inlineItemsBuilder_bidiIsolate :
    ("Hello " ++ wrapBidi .isolate .rtl "\u05E2\u05D1\u05E8\u05D9\u05EA" ++ " World") =
    "Hello \u2067\u05E2\u05D1\u05E8\u05D9\u05EA\u2069 World" := by
  decide

/-- Test 14: BidiIsolateOverride (inline_items_builder_test.cc:526) -/
theorem inlineItemsBuilder_bidiIsolateOverride :
    ("Hello " ++ wrapBidi .isolateOverride .rtl "\u05E2\u05D1\u05E8\u05D9\u05EA" ++ " World") =
    "Hello \u2068\u202E\u05E2\u05D1\u05E8\u05D9\u05EA\u202C\u2069 World" := by
  decide

/-- Test 15: CollapseBeforeAndAfterNewline (inline_items_builder_test.cc:295).
    CSS Text 3 §4.1.1: Spaces before and after newline in pre-line mode are removed. -/
theorem inlineItemsBuilder_collapseBeforeAndAfterNewline :
    buildInlineString [.text "text  \n  text" .preLine] = "text\ntext" := by
  decide

/-- Test 16: CollapsibleSpaceAfterNonCollapsibleSpaceAcrossElements (inline_items_builder_test.cc:301).
    CSS Text 3 §4.1.2: Collapsible space following non-collapsible space in pre-wrap does not collapse. -/
theorem inlineItemsBuilder_collapsibleSpaceAfterNonCollapsibleSpaceAcrossElements :
    buildInlineString [.text "text " .preWrap, .text " text" .normal] = "text  text" := by
  decide

/-- Test 17: CollapseZeroWidthSpaces (inline_items_builder_test.cc:309).
    CSS Text 3 §4.1.3: Newline adjacent to zero-width space is removed, collapsing surrounding spaces. -/
theorem inlineItemsBuilder_collapseZeroWidthSpaces :
    (buildInlineString [.text "text\u200B\ntext" .normal] = "text\u200Btext") ∧
    (buildInlineString [.text "text\n\u200Btext" .normal] = "text\u200Btext") ∧
    (buildInlineString [.text "text\u200B\n\u200Btext" .normal] = "text\u200B\u200Btext") ∧
    (buildInlineString [.text "text\n" .normal, .text "\u200Btext" .normal] = "text\u200Btext") ∧
    (buildInlineString [.text "text\u200B" .normal, .text "\ntext" .normal] = "text\u200Btext") ∧
    (buildInlineString [.text "text \n" .normal, .text "\u200Btext" .normal] = "text\u200Btext") ∧
    (buildInlineString [.text "text\u200B\n" .normal, .text " text" .normal] = "text\u200B text") ∧
    (buildInlineString [.text "text\u200B " .normal, .text "\ntext" .normal] = "text\u200Btext") := by
  decide

/-- Test 18: CollapseZeroWidthSpaceAndNewLineAtEnd (inline_items_builder_test.cc:334).
    CSS Text 3 §4.1.3: Trailing newline following zero-width space is removed. -/
theorem inlineItemsBuilder_collapseZeroWidthSpaceAndNewLineAtEnd :
    buildInlineString [.text "\u200B\n" .normal] = "\u200B" := by
  decide

/-- Test 19: OpaqueToSpaceCollapsing (inline_items_builder_test.cc:357).
    CSS Text 3 §4.1.2: Bidi controls are opaque to space collapsing across boundaries. -/
theorem inlineItemsBuilder_opaqueToSpaceCollapsing :
    buildInlineString [.text "Hello " .normal, .opaqueChar .bidiControl '\u2068',
                       .text " " .normal, .opaqueChar .bidiControl '\u2068',
                       .text " World" .normal] = "Hello \u2068\u2068World" := by
  decide

/-- Test 20: CollapseAroundReplacedElement (inline_items_builder_test.cc:367).
    CSS Text 3 §4.1.2: Atomic inline preserves collapsible spaces around it. -/
theorem inlineItemsBuilder_collapseAroundReplacedElement :
    buildInlineString [.text "Hello " .normal, .atomicInline, .text " World" .normal] = "Hello \uFFFC World" := by
  decide

/-- Test 21: AppendEmptyString (inline_items_builder_test.cc:387).
    CSS Text 3 §4: Appending an empty string produces a 0-length text item. -/
theorem inlineItemsBuilder_appendEmptyString :
    let st := appendBuilderInput {} (.text "" .normal)
    st.items = [{ type := .text, startOffset := 0, endOffset := 0 }] ∧
    buildInlineString [.text "" .normal] = "" := by
  decide

/-- Test 22: NewLines (inline_items_builder_test.cc:393).
    CSS Text 3 §4.1: Preserved newlines in pre mode generate control items separating text items. -/
theorem inlineItemsBuilder_newLines :
    let st := appendBuilderInput {} (.text "apple\norange\ngrape\n" .pre)
    buildInlineString [.text "apple\norange\ngrape\n" .pre] = "apple\norange\ngrape\n" ∧
    st.items.length = 6 ∧
    (st.items.map (·.type)) = [.text, .control, .text, .control, .text, .control] := by
  decide

/-- Test 23: IgnorablePre (inline_items_builder_test.cc:405).
    CSS Text 3 §4.1: Form feeds and newlines in pre mode generate control items separating text items. -/
theorem inlineItemsBuilder_ignorablePre :
    let st := appendBuilderInput {} (.text "apple\x0corange\ngrape" .pre)
    buildInlineString [.text "apple\x0corange\ngrape" .pre] = "apple\x0corange\ngrape" ∧
    st.items.length = 5 ∧
    (st.items.map (·.type)) = [.text, .control, .text, .control, .text] := by
  decide

/-- Test 24: CollapsedSpaceAfterNoWrap (inline_items_builder_test.cc:446).
    CSS Text 3 §5.1: Transition from nowrap with trailing space to wrap inserts a break opportunity (ZWS). -/
theorem inlineItemsBuilder_collapsedSpaceAfterNoWrap :
    buildInlineString [.text "nowrap " .nowrap, .text " wrap" .normal] = "nowrap \u200Bwrap" := by
  decide

/-- Test 25: GenerateBreakOpportunityAfterLeadingSpaces (inline_items_builder_test.cc:455).
    CSS Text 3 §5.1: Leading preserved spaces in pre-wrap generate a break opportunity (ZWS). -/
theorem inlineItemsBuilder_generateBreakOpportunityAfterLeadingSpaces :
    (buildInlineString [.text " a" .preWrap] = " \u200Ba") ∧
    (buildInlineString [.text "  a" .preWrap] = "  \u200Ba") ∧
    (buildInlineString [.text "a\n " .preWrap] = "a\n \u200B") := by
  decide

/-- Test 26: BlockInInline (inline_items_builder_test.cc:551).
    CSS 2.1 §9.2.1.1: Collapsible spaces before and after a block-in-inline are collapsed. -/
theorem inlineItemsBuilder_blockInInline :
    buildInlineString [.text "Hello " .normal, .blockInInline, .text " World" .normal] = "Hello\uFFFCWorld" := by
  decide

/-- Test 29: OpenCloseRubyColumns (inline_items_builder_test.cc:561).
    CSS Ruby 1 §2.3: Nested ruby and annotation tags emit structured ruby items. -/
theorem inlineItemsBuilder_openCloseRubyColumns :
    let inputs : List BuilderInput := [
      .openTag, .openRubyColumn, .rubyLinePlaceholder, .text "base1", .rubyLinePlaceholder,
      .openTag, .rubyLinePlaceholder, .text "anno1", .rubyLinePlaceholder, .closeTag, .closeRubyColumn,
      .openRubyColumn, .rubyLinePlaceholder, .text "base2", .rubyLinePlaceholder,
      .openTag, .rubyLinePlaceholder, .text "anno2", .rubyLinePlaceholder, .closeTag, .closeRubyColumn, .closeTag,
      .openRubyColumn, .rubyLinePlaceholder, .openTag, .rubyLinePlaceholder, .text "anno3", .rubyLinePlaceholder, .closeTag
    ]
    let st := inputs.foldl appendBuilderInput {}
    st.items.length = 29 := by
  decide

end ChromiumLayout.TestsInline
