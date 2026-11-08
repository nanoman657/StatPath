/-
  docs/chromium-layout/tests/TestsInline_LayoutText.lean

  Formalized layout tests for LayoutText
  (`third_party/blink/renderer/core/layout/layout_text_test.cc`).

  Covers:
  - CaretMinMaxOffset (`layout_text_test.cc:326`)
  - ResolvedTextLength (`layout_text_test.cc:344`)
  - ContainsCaretOffset (`layout_text_test.cc:358`)
  - ContainsCaretOffsetInPre (`layout_text_test.cc:383`)
  - IsBeforeAfterNonCollapsedCharacterBR (`layout_text_test.cc:972`)
  - WordBreakElement (`layout_text_test.cc:1134`)
  - IsBeforeAfterNonCollapsedCharacterNoLineWrap (`layout_text_test.cc:826`)
-/
import LayoutTypes
import LayoutInline
import InlineItemBuilder
import InlineOffsetMapping

namespace ChromiumLayout

/-! ## 1. CaretMinMaxOffset (`layout_text_test.cc:326`) -/

/-- Test `LayoutTextTest, CaretMinMaxOffset` (`layout_text_test.cc:326`).
    Checks DOM caret minimum and maximum offsets under CSS whitespace collapsing. -/
theorem layoutText_caretMinMaxOffset :
    (caretMinOffset .normal "foo" = 0) ∧
    (caretMaxOffset .normal "foo" = 3) ∧
    (caretMinOffset .normal "  foo" = 2) ∧
    (caretMaxOffset .normal "  foo" = 5) ∧
    (caretMinOffset .normal "foo  " = 0) ∧
    (caretMaxOffset .normal "foo  " = 3) ∧
    (caretMinOffset .normal " foo  " = 1) ∧
    (caretMaxOffset .normal " foo  " = 4) := by
  decide

/-! ## 2. ResolvedTextLength (`layout_text_test.cc:344`) -/

/-- Test `LayoutTextTest, ResolvedTextLength` (`layout_text_test.cc:344`).
    Checks resolved non-collapsed text length for normal whitespace. -/
theorem layoutText_resolvedTextLength :
    (resolvedTextLength .normal "foo" = 3) ∧
    (resolvedTextLength .normal "  foo" = 3) ∧
    (resolvedTextLength .normal "foo  " = 3) ∧
    (resolvedTextLength .normal " foo  " = 3) := by
  decide

/-! ## 3. ContainsCaretOffset (`layout_text_test.cc:358`) -/

/-- Test `LayoutTextTest, ContainsCaretOffset` (`layout_text_test.cc:358`).
    Verifies caret snap codes for " foo   bar " at all character offsets. -/
theorem layoutText_containsCaretOffset :
    let s := " foo   bar "
    (getSnapCode .normal s 0 = "---") ∧
    (getSnapCode .normal s 1 = "BC-") ∧
    (getSnapCode .normal s 2 = "BCA") ∧
    (getSnapCode .normal s 3 = "BCA") ∧
    (getSnapCode .normal s 4 = "BCA") ∧
    (getSnapCode .normal s 5 = "-CA") ∧
    (getSnapCode .normal s 6 = "---") ∧
    (getSnapCode .normal s 7 = "BC-") ∧
    (getSnapCode .normal s 8 = "BCA") ∧
    (getSnapCode .normal s 9 = "BCA") ∧
    (getSnapCode .normal s 10 = "-CA") ∧
    (getSnapCode .normal s 11 = "---") ∧
    (getSnapCode .normal s 12 = "--_") := by
  decide

/-! ## 4. ContainsCaretOffsetInPre (`layout_text_test.cc:383`) -/

/-- Test `LayoutTextTest, ContainsCaretOffsetInPre` (`layout_text_test.cc:383`).
    In pre mode, non-collapsed spaces and newlines are preserved, and caret cannot
    reside immediately after a newline. -/
theorem layoutText_containsCaretOffsetInPre :
    let s1 := "foo   bar"
    let s2 := "abc\n"
    (getSnapCode .pre s1 0 = "BC-") ∧
    (getSnapCode .pre s1 1 = "BCA") ∧
    (getSnapCode .pre s1 4 = "BCA") ∧
    (getSnapCode .pre s1 9 = "-CA") ∧
    (getSnapCode .pre s2 0 = "BC-") ∧
    (getSnapCode .pre s2 3 = "BCA") ∧
    (getSnapCode .pre s2 4 = "--A") := by
  decide

/-! ## 5. IsBeforeAfterNonCollapsedCharacterBR (`layout_text_test.cc:972`) -/

/-- Test `LayoutTextTest, IsBeforeAfterNonCollapsedCharacterBR` (`layout_text_test.cc:972`).
    Line break character `<br>` emits newline: offset 0 is before, offset 1 is after. -/
theorem layoutText_isBeforeAfterNonCollapsedCharacterBR :
    let nodes := [DomNode.br 0]
    let units := buildDomOffsetMapping nodes
    (domNodeSnapCode units nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 1 = "--A") := by
  decide

/-! ## 6. WordBreakElement (`layout_text_test.cc:1134`) -/

/-- Test `LayoutTextTest, WordBreakElement` (`layout_text_test.cc:1134`).
    `<wbr>` element has 0 resolved text length and 0 min/max caret offsets. -/
theorem layoutText_wordBreakElement :
    (resolvedTextLength .normal "" = 0) ∧
    (caretMinOffset .normal "" = 0) ∧
    (caretMaxOffset .normal "" = 0) := by
  decide

/-! ## 7. IsBeforeAfterNonCollapsedCharacterNoLineWrap (`layout_text_test.cc:826`) -/

/-- Test `LayoutTextTest, IsBeforeAfterNonCollapsedCharacterNoLineWrap` (`layout_text_test.cc:826`).
    Checks non-collapsed snap codes on plain strings, inner runs, and leading spaces. -/
theorem layoutText_isBeforeAfterNonCollapsedCharacterNoLineWrap :
    (getSnapCode .normal "foo" 0 = "BC-") ∧
    (getSnapCode .normal "foo" 1 = "BCA") ∧
    (getSnapCode .normal "foo" 3 = "-CA") ∧
    (getSnapCode .normal "f   bar" 0 = "BC-") ∧
    (getSnapCode .normal "f   bar" 1 = "BCA") ∧
    (getSnapCode .normal "f   bar" 2 = "-CA") ∧
    (getSnapCode .normal "f   bar" 3 = "---") ∧
    (getSnapCode .normal "f   bar" 4 = "BC-") ∧
    (getSnapCode .normal "  foo" 0 = "---") ∧
    (getSnapCode .normal "  foo" 1 = "---") ∧
    (getSnapCode .normal "  foo" 2 = "BC-") ∧
    (getSnapCode .normal "  foo" 3 = "BCA") := by
  decide

/-! ## 8. ContainsCaretOffsetInPreLine (`layout_text_test.cc:420`) -/

/-- Test `LayoutTextTest, ContainsCaretOffsetInPreLine` (`layout_text_test.cc:420`).
    In pre-line mode, spaces collapse around newlines, but the newline character is preserved
    as an identity unit and serves as a caret positioning target. -/
theorem layoutText_containsCaretOffsetInPreLine :
    let nodes := [DomNode.text 0 "ab \n cd" .preLine]
    let units := buildDomOffsetMapping nodes
    (domNodeSnapCode units nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 1 = "BCA") ∧
    (domNodeSnapCode units nodes[0]! 2 = "-CA") ∧
    (domNodeSnapCode units nodes[0]! 3 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 4 = "--A") ∧
    (domNodeSnapCode units nodes[0]! 5 = "BC-") := by
  decide

/-! ## 9. ContainsCaretOffsetWithTrailingSpace (`layout_text_test.cc:525`) -/

/-- Test `LayoutTextTest, ContainsCaretOffsetWithTrailingSpace` (`layout_text_test.cc:525`).
    `<div id=target>ab<br>cd</div>` caret snap codes across text and `<br>`. -/
theorem layoutText_containsCaretOffsetWithTrailingSpace :
    let nodes := [DomNode.text 0 "ab", DomNode.br 1, DomNode.text 2 "cd"]
    let units := buildDomOffsetMapping nodes
    (domNodeSnapCode units nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 1 = "BCA") ∧
    (domNodeSnapCode units nodes[0]! 2 = "-CA") ∧
    (domNodeSnapCode units nodes[1]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[1]! 1 = "--A") ∧
    (domNodeSnapCode units nodes[2]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[2]! 1 = "BCA") ∧
    (domNodeSnapCode units nodes[2]! 2 = "-CA") := by
  decide

/-! ## 10. ContainsCaretOffsetWithTrailingSpace1 (`layout_text_test.cc:541`) -/

/-- Test `LayoutTextTest, ContainsCaretOffsetWithTrailingSpace1` (`layout_text_test.cc:541`).
    `<div id=target>ab <br> cd</div>` trailing space before `<br>` and leading space after `<br>` collapse. -/
theorem layoutText_containsCaretOffsetWithTrailingSpace1 :
    let nodes := [DomNode.text 0 "ab ", DomNode.br 1, DomNode.text 2 " cd"]
    let units := buildDomOffsetMapping nodes
    (domNodeSnapCode units nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 1 = "BCA") ∧
    (domNodeSnapCode units nodes[0]! 2 = "-CA") ∧
    (domNodeSnapCode units nodes[0]! 3 = "---") ∧
    (domNodeSnapCode units nodes[1]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[1]! 1 = "--A") ∧
    (domNodeSnapCode units nodes[2]! 0 = "---") ∧
    (domNodeSnapCode units nodes[2]! 1 = "BC-") ∧
    (domNodeSnapCode units nodes[2]! 2 = "BCA") ∧
    (domNodeSnapCode units nodes[2]! 3 = "-CA") := by
  decide

/-! ## 11. ContainsCaretOffsetWithTrailingSpace2 (`layout_text_test.cc:568`) -/

/-- Test `LayoutTextTest, ContainsCaretOffsetWithTrailingSpace2` (`layout_text_test.cc:568`).
    `<div id=target>ab  <br>  cd</div>` multiple spaces collapse before and after `<br>`. -/
theorem layoutText_containsCaretOffsetWithTrailingSpace2 :
    let nodes := [DomNode.text 0 "ab  ", DomNode.br 1, DomNode.text 2 "  cd"]
    let units := buildDomOffsetMapping nodes
    (domNodeSnapCode units nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 1 = "BCA") ∧
    (domNodeSnapCode units nodes[0]! 2 = "-CA") ∧
    (domNodeSnapCode units nodes[0]! 3 = "---") ∧
    (domNodeSnapCode units nodes[0]! 4 = "---") ∧
    (domNodeSnapCode units nodes[1]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[1]! 1 = "--A") ∧
    (domNodeSnapCode units nodes[2]! 0 = "---") ∧
    (domNodeSnapCode units nodes[2]! 1 = "---") ∧
    (domNodeSnapCode units nodes[2]! 2 = "BC-") ∧
    (domNodeSnapCode units nodes[2]! 3 = "BCA") ∧
    (domNodeSnapCode units nodes[2]! 4 = "-CA") := by
  decide

end ChromiumLayout
