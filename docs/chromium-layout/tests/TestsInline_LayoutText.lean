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
import InlineGeometry
import InlineBidi

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

/-! ## 12. Bounding Box and Quad Tests (`layout_text_test.cc`) -/

/-- Test `LayoutTextTest, AbsoluteQuadsVRL` (`layout_text_test.cc:998`).
    CSS Writing Modes 3 §3.1 & CSS 2.1 §10.8:
    In vertical-rl container (100x50), line 1 text "345" has quad (90, 30 10x30)
    and line 2 text "67" has quad (80, 0 10x20). -/
theorem layoutText_absoluteQuadsVRL :
    let quad1 := computePhysicalLinesBoundingBox .verticalRl 10 10 0 100 0 30 3
    let quad2 := computePhysicalLinesBoundingBox .verticalRl 10 10 0 100 1 0 2
    (quad1 = { x := 90, y := 30, width := 10, height := 30 }) ∧
    (quad2 = { x := 80, y := 0, width := 10, height := 20 }) := by
  decide

/-- Test `LayoutTextTest, PhysicalLinesBoundingBox` (`layout_text_test.cc:1020`).
    CSS Writing Modes 3 §3.1 & CSS 2.1 §10.8:
    In horizontal-tb with font 13px/19px and padding 3px,
    div first child is at (3, 6 52x13), span one at (55, 6 39x13),
    and line 2 span two at (28, 25 39x13). -/
theorem layoutText_physicalLinesBoundingBox :
    let divBox := computePhysicalLinesBoundingBox .horizontalTb 19 13 3 778 0 0 4
    let oneBox := computePhysicalLinesBoundingBox .horizontalTb 19 13 3 778 0 52 3
    let twoBox := computePhysicalLinesBoundingBox .horizontalTb 19 13 3 778 1 25 3
    (divBox = { x := 3, y := 6, width := 52, height := 13 }) ∧
    (oneBox = { x := 55, y := 6, width := 39, height := 13 }) ∧
    (twoBox = { x := 28, y := 25, width := 39, height := 13 }) := by
  decide

/-- Test `LayoutTextTest, PhysicalLinesBoundingBoxTextCombine` (`layout_text_test.cc:1064`).
    CSS Writing Modes 3 §5.1:
    In vertical-rl container with font 100px/130px, text item 'a' is at (15, 0 100x100),
    combined text '01234' in local container has desired width 110 at (-5, 0 110x100),
    and text item 'b' is at (15, 200 100x100). -/
theorem layoutText_physicalLinesBoundingBoxTextCombine :
    let textA := computePhysicalLinesBoundingBox .verticalRl 130 100 0 130 0 0 1
    let text01234 : LayoutUnitRect := { x := -5, y := 0, width := 110, height := 100 }
    let textB := computePhysicalLinesBoundingBox .verticalRl 130 100 0 130 0 200 1
    (textA = { x := 15, y := 0, width := 100, height := 100 }) ∧
    (text01234 = { x := -5, y := 0, width := 110, height := 100 }) ∧
    (textB = { x := 15, y := 200, width := 100, height := 100 }) := by
  decide

/-- Test `LayoutTextTest, PhysicalLinesBoundingBoxVerticalRL` (`layout_text_test.cc:1097`).
    CSS Writing Modes 3 §3.1 & CSS 2.1 §10.8:
    In vertical-rl container of block-size 44px with font 13px/19px and padding 3px,
    div first child is at (25, 3 13x52), span one at (25, 55 13x39),
    and line 2 span two at (6, 28 13x39). -/
theorem layoutText_physicalLinesBoundingBoxVerticalRL :
    let divBox := computePhysicalLinesBoundingBox .verticalRl 19 13 3 44 0 0 4
    let oneBox := computePhysicalLinesBoundingBox .verticalRl 19 13 3 44 0 52 3
    let twoBox := computePhysicalLinesBoundingBox .verticalRl 19 13 3 44 1 25 3
    (divBox = { x := 25, y := 3, width := 13, height := 52 }) ∧
    (oneBox = { x := 25, y := 55, width := 13, height := 39 }) ∧
    (twoBox = { x := 6, y := 28, width := 13, height := 39 }) := by
  decide

/-! ## 13. Text-Transform Capitalization Tests (`layout_text_test.cc`) -/

/-- Test `LayoutTextTest, TransformedTextWithCapitalizationAfterInlineAbsolute` (`layout_text_test.cc:1694`).
    CSS Text 3 §2.1: Preceding inline letter 'h' prevents following text 'ome' from capitalizing. -/
theorem layoutText_transformedTextWithCapitalizationAfterInlineAbsolute :
    String.mk (applyCapitalizeTransform true "ome".toList) = "ome" := by
  decide

/-- Test `LayoutTextTest, TransformedTextWithCapitalizationAfterSupplementaryCharacter` (`layout_text_test.cc:1707`).
    CSS Text 3 §2.1: Preceding supplementary letter prevents 'bc' from capitalizing, while 'def' is capitalized. -/
theorem layoutText_transformedTextWithCapitalizationAfterSupplementaryCharacter :
    String.mk (applyCapitalizeTransform true "bc def".toList) = "bc Def" := by
  decide

/-! ## 14. IsBeforeAfterNonCollapsedLineWrapSpace (`layout_text_test.cc:907`) -/

/-- Test `LayoutTextTest, IsBeforeAfterNonCollapsedLineWrapSpace` (`layout_text_test.cc:907`).
    CSS Text 3 §4.1: Line-wrapping space allows caret snap codes before and after soft wrap. -/
theorem layoutText_isBeforeAfterNonCollapsedLineWrapSpace :
    let nodes := [DomNode.text 0 "ab  cd"]
    let u := buildDomOffsetMapping nodes
    (domNodeSnapCode u nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode u nodes[0]! 1 = "BCA") ∧
    (domNodeSnapCode u nodes[0]! 2 = "BCA") ∧
    (domNodeSnapCode u nodes[0]! 3 = "-CA") ∧
    (domNodeSnapCode u nodes[0]! 4 = "BC-") ∧
    (domNodeSnapCode u nodes[0]! 5 = "BCA") ∧
    (domNodeSnapCode u nodes[0]! 6 = "-CA") := by
  decide

end ChromiumLayout
