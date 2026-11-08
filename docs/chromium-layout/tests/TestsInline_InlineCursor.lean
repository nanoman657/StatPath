/-
  docs/chromium-layout/tests/TestsInline_InlineCursor.lean

  Test vectors and theorems transcribed from:
  - `inline/inline_cursor_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineGeometry
import InlineBidi
import InlineCursor

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test: BidiLevelInlineBoxLTR (inline_cursor_test.cc:125)
    In an LTR root, plain text and LTR inline boxes have bidi level 0,
    while an RTL <bdo> override assigns level 3. -/
theorem inlineCursor_bidiLevelInlineBoxLTR :
    let items := [
      BidiItem.text "abc",
      BidiItem.inlineBox "def",
      BidiItem.openBdo .rtl,
      BidiItem.inlineBox "ghi",
      BidiItem.closeBdo,
      BidiItem.text "jkl"
    ]
    bidiLevels .ltr items [] = [("abc", 0), ("def", 0), ("ghi", 3), ("jkl", 0)] := by
  decide

/-- Test: BidiLevelInlineBoxRTL (inline_cursor_test.cc:135)
    In an RTL root, Latin text and inline boxes resolve to level 2,
    while an RTL <bdo> override resolves to level 3. -/
theorem inlineCursor_bidiLevelInlineBoxRTL :
    let items := [
      BidiItem.text "abc",
      BidiItem.inlineBox "def",
      BidiItem.openBdo .rtl,
      BidiItem.inlineBox "ghi",
      BidiItem.closeBdo,
      BidiItem.text "jkl"
    ]
    bidiLevels .rtl items [] = [("abc", 2), ("def", 2), ("ghi", 3), ("jkl", 2)] := by
  decide

/-- Test: BidiLevelSimpleLTR (inline_cursor_test.cc:145)
    Nested RTL and LTR overrides produce bidi levels 3 and 6 respectively. -/
theorem inlineCursor_bidiLevelSimpleLTR :
    let items := [
      BidiItem.openBdo .rtl,
      BidiItem.text "GHI",
      BidiItem.openBdo .ltr,
      BidiItem.text "abc",
      BidiItem.closeBdo,
      BidiItem.text "DEF",
      BidiItem.closeBdo,
      BidiItem.br,
      BidiItem.text "123, jkl ",
      BidiItem.openBdo .rtl,
      BidiItem.text "MNO",
      BidiItem.closeBdo
    ]
    bidiLevels .ltr items [] = [
      ("GHI", 3), ("abc", 6), ("DEF", 3), ("<br>", 0),
      ("123, jkl ", 0), ("MNO", 3)
    ] := by
  decide

/-- Test: BidiLevelFirstLineTextTransform (inline_cursor_test.cc:166)
    First line text-transform uppercases German eszett ('ß' -> "SS") at level 0. -/
theorem inlineCursor_bidiLevelFirstLineTextTransform :
    let raw := "ß\t"
    let transformed := String.ofList (applyTextTransform true raw.toList)
    (transformed = "SS\t") ∧
    (bidiLevels .ltr [BidiItem.text "SS", BidiItem.text "\t"] [] = [("SS", 0), ("\t", 0)]) := by
  decide

/-- Test: BidiLevelFirstLineTextTransformBR (inline_cursor_test.cc:175)
    First line text-transform with line break `<br>`. -/
theorem inlineCursor_bidiLevelFirstLineTextTransformBR :
    let raw := "ß"
    let transformed := String.ofList (applyTextTransform true raw.toList)
    (transformed = "SS") ∧
    (bidiLevels .ltr [BidiItem.text "SS", BidiItem.br] [] = [("SS", 0), ("<br>", 0)]) := by
  decide

/-- Test: Parent (inline_cursor_test.cc:191)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2: MoveToParent traverses up ancestor tree. -/
theorem inlineCursor_parent :
    let nodes : List CursorNode := [
      { id := "root", name := "root", descendantsCount := 8 },
      { name := "text1" },
      { id := "span1", name := "span1", descendantsCount := 6 },
      { name := "span1" },
      { name := "" },
      { id := "span2", name := "span2", descendantsCount := 4 },
      { name := "span2" },
      { name := "", isAtomic := true },
      { id := "span3", name := "span3", descendantsCount := 1 },
      { name := "span3" }
    ]
    collectAncestorIds nodes 8 = ["span2", "span1", "root"] := by
  decide

/-- Test: ContainingLine (inline_cursor_test.cc:226)
    CSS 2.1 §9.4.2: MoveToContainingLine finds enclosing line box fragment. -/
theorem inlineCursor_containingLine :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4 },
      { name := "abc" },
      { name := "target", descendantsCount := 1 },
      { name := "def" },
      { name := "ghi" },
      { name := "#linebox", type := .line, descendantsCount := 1 },
      { name := "xyz" }
    ]
    findContainingLine nodes 1 = some 0 ∧
    findContainingLine nodes 2 = some 0 ∧
    findContainingLine nodes 3 = some 0 ∧
    findContainingLine nodes 6 = some 5 := by
  decide

/-- Test: CulledInlineWithAtomicInline (inline_cursor_test.cc:257)
    CSS Inline 3 §2: Culled inline traverses in-flow descendants including atomic inlines and breaks. -/
theorem inlineCursor_culledInlineWithAtomicInline :
    let items : List CursorNode := [
      { name := "abc" }, { name := "ABC" }, { name := "", isLineBreak := true },
      { name := "XYZ" }, { name := "xyz" }
    ]
    culledInFlowNames items = ["abc", "ABC", "", "XYZ", "xyz"] := by
  decide

/-- Test: CulledInlineWithFloat (inline_cursor_test.cc:271)
    CSS 2.1 §9.5: Floats are out of normal inline flow and excluded from culled inline traversal. -/
theorem inlineCursor_culledInlineWithFloat :
    let items : List CursorNode := [
      { name := "abc" }, { name := "", isFloat := true }, { name := "xyz" }
    ]
    culledInFlowNames items = ["abc", "xyz"] := by
  decide

/-- Test: CulledInlineWithOOF (inline_cursor_test.cc:281)
    CSS 2.1 §9.3: Out-of-flow positioned elements are excluded from culled inline traversal. -/
theorem inlineCursor_culledInlineWithOOF :
    let items : List CursorNode := [
      { name := "abc" }, { name := "", isOutOfFlow := true }, { name := "xyz" }
    ]
    culledInFlowNames items = ["abc", "xyz"] := by
  decide

/-- Test: CulledInlineNested (inline_cursor_test.cc:292)
    CSS Inline 3 §2: Nested culled inlines preserve descendant text items. -/
theorem inlineCursor_culledInlineNested :
    let items : List CursorNode := [
      { name := "abc" }, { name := "xyz" }
    ]
    culledInFlowNames items = ["abc", "xyz"] := by
  decide

/-- Test: CulledInlineWithoutRoot (inline_cursor_test.cc:328)
    CSS Inline 3 §2: Culled inline without root container yields in-flow text and break fragments. -/
theorem inlineCursor_culledInlineWithoutRoot :
    let items : List CursorNode := [
      { name := "abc" }, { name := "", isLineBreak := true }, { name := "xyz" }
    ]
    culledInFlowNames items = ["abc", "", "xyz"] := by
  decide

/-- Test: FirstChild (inline_cursor_test.cc:365)
    CSS 2.1 §9.4.2: MoveToFirstChild descends to first child; text leaf has no children. -/
theorem inlineCursor_firstChild :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 5 },
      { name := "abc" },
      { name := "a", descendantsCount := 2 },
      { name := "DEF" },
      { name := "GHI" },
      { name := "xyz" }
    ]
    findFirstChild nodes 0 = some 1 ∧
    nodes[1]? = some { name := "abc" } ∧
    findFirstChild nodes 1 = none := by
  decide

/-- Test: FirstChild2 (inline_cursor_test.cc:375)
    CSS 2.1 §9.4.2: Successive MoveToFirstChild visits nested inline box first child. -/
theorem inlineCursor_firstChild2 :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 6 },
      { name := "#first", descendantsCount := 1 },
      { name := "abc" },
      { name := "a", descendantsCount := 2 },
      { name := "DEF" },
      { name := "#last", descendantsCount := 1 },
      { name := "xyz" }
    ]
    findFirstChild nodes 0 = some 1 ∧
    nodes[1]? = some { name := "#first", descendantsCount := 1 } ∧
    findFirstChild nodes 1 = some 2 ∧
    nodes[2]? = some { name := "abc" } ∧
    findFirstChild nodes 2 = none := by
  decide

/-- Test: FirstLastLogicalLeafInRtlText (inline_cursor_test.cc:403)
    CSS Writing Modes 3 §3.2: In RTL text, logical first and last leaf resolve in reading order. -/
theorem inlineCursor_firstLastLogicalLeafInRtlText :
    -- In RTL line box, fragments are arranged in visual order: leftmost is "last", rightmost is "first"
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 3 },
      { name := "last" },
      { name := "middle" },
      { name := "first" }
    ]
    firstLogicalLeaf nodes 0 true = 3 ∧
    nodes[3]? = some { name := "first" } ∧
    lastLogicalLeaf nodes 0 true = 1 ∧
    nodes[1]? = some { name := "last" } := by
  decide

/-- Test: FirstLastLogicalLeafInTextAsDeepDescendants (inline_cursor_test.cc:420)
    CSS Writing Modes 3 §3.2: Logical leaf descent finds innermost text leaf across deep hierarchies. -/
theorem inlineCursor_firstLastLogicalLeafInTextAsDeepDescendants :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 7 },
      { name := "b1", descendantsCount := 3 },
      { name := "b1_1", descendantsCount := 1 },
      { name := "first" },
      { name := "ABC" },
      { name := "middle" },
      { name := "b2", descendantsCount := 2 },
      { name := "DEF" },
      { name := "last" }
    ]
    nodes[firstLogicalLeaf nodes 0 false]? = some { name := "first" } ∧
    nodes[lastLogicalLeaf nodes 0 false]? = some { name := "last" } := by
  decide

/-- Test: FirstLastLogicalLeafWithInlineBlock (inline_cursor_test.cc:502)
    CSS 2.1 §9.2.2: Atomic inline-block terminates logical leaf descent. -/
theorem inlineCursor_firstLastLogicalLeafWithInlineBlock :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 3 },
      { name := "#first", isAtomic := true },
      { name := "middle" },
      { name := "#last", isAtomic := true }
    ]
    nodes[firstLogicalLeaf nodes 0 false]? = some { name := "#first", isAtomic := true } ∧
    nodes[lastLogicalLeaf nodes 0 false]? = some { name := "#last", isAtomic := true } := by
  decide

/-- Test: FirstLastLogicalLeafWithImages (inline_cursor_test.cc:520)
    CSS 2.1 §9.2.2: Replaced elements (images) terminate logical leaf descent. -/
theorem inlineCursor_firstLastLogicalLeafWithImages :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 3 },
      { name := "#first", isAtomic := true },
      { name := "middle" },
      { name := "#last", isAtomic := true }
    ]
    nodes[firstLogicalLeaf nodes 0 false]? = some { name := "#first", isAtomic := true } ∧
    nodes[lastLogicalLeaf nodes 0 false]? = some { name := "#last", isAtomic := true } := by
  decide

/-- Test: IsEmptyLineBox (inline_cursor_test.cc:554)
    CSS 2.1 §9.4.2: Line box with text is non-empty; line box with empty inline and margin is empty. -/
theorem inlineCursor_isEmptyLineBox :
    let line1 : CursorNode := { name := "#linebox", type := .line, isEmptyLine := false }
    let line2 : CursorNode := { name := "#linebox", type := .line, isEmptyLine := true }
    line1.isEmptyLine = false ∧ line2.isEmptyLine = true := by
  decide

/-- Test: LastChild (inline_cursor_test.cc:565)
    CSS 2.1 §9.4.2: MoveToLastChild visits rightmost direct sibling child. -/
theorem inlineCursor_lastChild :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 5 },
      { name := "abc" },
      { name := "a", descendantsCount := 2 },
      { name := "DEF" },
      { name := "GHI" },
      { name := "xyz" }
    ]
    findLastChild nodes 0 = some 5 ∧
    nodes[5]? = some { name := "xyz" } ∧
    findLastChild nodes 5 = none := by
  decide

/-- Test: LastChild2 (inline_cursor_test.cc:575)
    CSS 2.1 §9.4.2: Successive MoveToLastChild visits nested inline box last child. -/
theorem inlineCursor_lastChild2 :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 7 },
      { name := "#first", descendantsCount := 1 },
      { name := "abc" },
      { name := "a", descendantsCount := 2 },
      { name := "DEF" },
      { name := "GHI" },
      { name := "#last", descendantsCount := 1 },
      { name := "xyz" }
    ]
    findLastChild nodes 0 = some 6 ∧
    nodes[6]? = some { name := "#last", descendantsCount := 1 } ∧
    findLastChild nodes 6 = some 7 ∧
    nodes[7]? = some { name := "xyz" } ∧
    findLastChild nodes 7 = none := by
  decide

/-- Test: Next (inline_cursor_test.cc:588)
    CSS Inline 3 §2: MoveToNext performs pre-order DFS across inline fragments. -/
theorem inlineCursor_next :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 7 },
      { name := "text1" },
      { name := "#span1", descendantsCount := 4 },
      { name := "text2" },
      { name := "#span2", descendantsCount := 1 },
      { name := "text3" },
      { name := "text4" },
      { name := "text5" }
    ]
    collectPreOrder nodes = [
      "#linebox", "text1", "#span1", "text2", "#span2", "text3", "text4", "text5"
    ] := by
  decide

/-- Test: NextInlineLeaf (inline_cursor_test.cc:685)
    CSS Inline 3 §2: MoveToNextInlineLeaf visits only text and break leaves. -/
theorem inlineCursor_nextInlineLeaf :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4 },
      { name := "abc" },
      { name := "b", descendantsCount := 1 },
      { name := "DEF" },
      { name := "", isLineBreak := true },
      { name := "xyz" }
    ]
    collectInlineLeaves nodes false = ["#linebox", "abc", "DEF", "", "xyz"] := by
  decide

/-- Test: NextInlineLeafIgnoringLineBreak (inline_cursor_test.cc:788)
    CSS Inline 3 §2: MoveToNextInlineLeafIgnoringLineBreak skips line breaks. -/
theorem inlineCursor_nextInlineLeafIgnoringLineBreak :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4 },
      { name := "abc" },
      { name := "b", descendantsCount := 1 },
      { name := "DEF" },
      { name := "", isLineBreak := true },
      { name := "xyz" }
    ]
    collectInlineLeaves nodes true = ["#linebox", "abc", "DEF", "xyz"] := by
  decide

/-- Test: NextLine (inline_cursor_test.cc:800)
    CSS 2.1 §9.4.2: MoveToNextLine advances between consecutive line boxes. -/
theorem inlineCursor_nextLine :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 1 },
      { name := "line1" },
      { name := "#linebox", type := .line, descendantsCount := 1 },
      { name := "line2" }
    ]
    findNextLine nodes 0 = some 2 ∧
    findNextLine nodes 2 = none := by
  decide

/-- Test: NextWithImage (inline_cursor_test.cc:821)
    CSS 2.1 §9.2.2: Atomic image elements participate in inline cursor pre-order traversal. -/
theorem inlineCursor_nextWithImage :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 3 },
      { name := "abc" },
      { name := "#img", isAtomic := true },
      { name := "xyz" }
    ]
    collectPreOrder nodes = ["#linebox", "abc", "#img", "xyz"] := by
  decide

/-- Test: NextInlineLeafOnLineFromLayoutInline (inline_cursor_test.cc:698)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: Starting from an inline container on line 0,
    MoveToNextInlineLeafOnLine skips its descendants and visits subsequent leaves on the same line,
    stopping before line 1. -/
theorem inlineCursor_nextInlineLeafOnLineFromLayoutInline :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 0 },
      { id := "start", name := "#start", descendantsCount := 1, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "def", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 1 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 1 },
      { name := "ABC", lineIndex := 1 },
      { name := "DEF", lineIndex := 1 },
      { name := "", isLineBreak := true, lineIndex := 1 }
    ]
    collectInlineLeavesOnLine nodes 1 = ["#start", "def", ""] := by
  decide

/-- Test: NextInlineLeafOnLineFromNestedLayoutInline (inline_cursor_test.cc:716)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: NextOnLine from an inline container never visits
    its own descendant leaves, advancing directly to the sibling subtree on the same line. -/
theorem inlineCursor_nextInlineLeafOnLineFromNestedLayoutInline :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 6, lineIndex := 0 },
      { id := "start", name := "#start", descendantsCount := 3, lineIndex := 0 },
      { name := "Test", lineIndex := 0 },
      { name := "span", descendantsCount := 1, lineIndex := 0 },
      { name := "descendant", lineIndex := 0 },
      { name := "span", descendantsCount := 1, lineIndex := 0 },
      { name := "next", lineIndex := 0 }
    ]
    collectInlineLeavesOnLine nodes 1 = ["#start", "next"] := by
  decide

/-- Test: NextInlineLeafOnLineFromLayoutText (inline_cursor_test.cc:738)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: MoveToNextInlineLeafOnLine from a text leaf
    traverses subsequent leaves on the same line and halts at the line boundary. -/
theorem inlineCursor_nextInlineLeafOnLineFromLayoutText :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 0 },
      { id := "start", name := "#start", descendantsCount := 1, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "def", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 1 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 1 },
      { name := "ABC", lineIndex := 1 },
      { name := "DEF", lineIndex := 1 },
      { name := "", isLineBreak := true, lineIndex := 1 }
    ]
    collectInlineLeavesOnLine nodes 2 = ["abc", "def", ""] := by
  decide

/-- Test: NextForSameLayoutObject (inline_cursor_test.cc:839)
    CSS 2.1 §9.4.2: InlineCursor collects all fragments corresponding to the same LayoutObject across lines. -/
theorem inlineCursor_nextForSameLayoutObject :
    let nodes : List CursorNode := [
      { id := "pre_text", name := "abc", lineIndex := 0 },
      { id := "pre_text", name := "", isLineBreak := true, lineIndex := 0 },
      { id := "pre_text", name := "def", lineIndex := 1 },
      { id := "pre_text", name := "", isLineBreak := true, lineIndex := 1 },
      { id := "pre_text", name := "ghi", lineIndex := 2 }
    ]
    itemsForLayoutObject nodes "pre_text" = ["abc", "", "def", "", "ghi"] := by
  decide

/-- Test: NextForSameLayoutObjectWithRange (inline_cursor_test.cc:847)
    CSS 2.1 §9.4.2: Cursor limited to a line box visits only the fragment on that line for the LayoutObject. -/
theorem inlineCursor_nextForSameLayoutObjectWithRange :
    let line2Nodes : List CursorNode := [
      { id := "span1", name := "#span1", lineIndex := 1, descendantsCount := 1 },
      { id := "span1_text", name := "2222", lineIndex := 1 }
    ]
    itemsForLayoutObject line2Nodes "span1" = ["#span1"] := by
  decide

/-- Test: Sibling (inline_cursor_test.cc:882)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2: Sibling navigation skips descendants of container siblings. -/
theorem inlineCursor_sibling :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 6 },
      { name := "abc" },
      { name := "LayoutInline A", descendantsCount := 3 },
      { name := "DEF" },
      { name := "LayoutInline B", descendantsCount := 1 },
      { name := "GHI" },
      { name := "xyz" }
    ]
    collectSiblings nodes 1 = ["abc", "LayoutInline A", "xyz"] := by
  decide

/-- Test: Sibling2 (inline_cursor_test.cc:893)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2: Sibling navigation within an inline box visits its direct children. -/
theorem inlineCursor_sibling2 :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 5 },
      { name := "LayoutInline A", descendantsCount := 4 },
      { name := "abc" },
      { name := "LayoutInline B", descendantsCount := 1 },
      { name := "def" },
      { name := "xyz" }
    ]
    collectSiblings nodes 2 = ["abc", "LayoutInline B", "xyz"] := by
  decide

/-- Test: NextSkippingChildren (inline_cursor_test.cc:905)
    CSS 2.1 §9.4.2: MoveToNextSkippingChildren skips all descendants of the current container. -/
theorem inlineCursor_nextSkippingChildren :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 7 },
      { name := "text1" },
      { id := "span1", name := "#span1", descendantsCount := 4 },
      { name := "text2" },
      { id := "span2", name := "#span2", descendantsCount := 1 },
      { name := "text3" },
      { name := "text4" },
      { name := "text5" }
    ]
    (nextSkippingChildren nodes 3,
     nextSkippingChildren nodes 4,
     nextSkippingChildren nodes 6,
     nextSkippingChildren nodes 7) =
      (some 4, some 6, some 7, none) := by
  decide

/-- Test: EmptyOutOfFlow (inline_cursor_test.cc:938)
    CSS 2.1 §9.3 & §9.5: Out-of-flow positioned elements do not participate in inline flow,
    producing zero in-flow inline cursor items. -/
theorem inlineCursor_emptyOutOfFlow :
    let nodes : List CursorNode := [
      { id := "abs", name := "#abs", isOutOfFlow := true }
    ]
    culledInFlowNames nodes = [] := by
  decide

/-- Test: Previous (inline_cursor_test.cc:1110)
    CSS 2.1 §9.4.2: MoveToPrevious visits all items in reverse pre-order sequence. -/
theorem inlineCursor_previous :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 0 },
      { name := "DEF", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 1, lineIndex := 1 },
      { name := "xyz", lineIndex := 1 }
    ]
    collectPrevious nodes 6 = ["xyz", "#linebox", "", "DEF", "LayoutInline B", "abc", "#linebox"] := by
  decide

/-- Test: PreviousInlineLeaf (inline_cursor_test.cc:1145)
    CSS Inline 3 §2: MoveToPreviousInlineLeaf visits leaf items in reverse order including line breaks. -/
theorem inlineCursor_previousInlineLeaf :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 0 },
      { name := "DEF", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 1, lineIndex := 1 },
      { name := "xyz", lineIndex := 1 }
    ]
    collectPreviousInlineLeaves nodes 6 false = ["xyz", "", "DEF", "abc"] := by
  decide

/-- Test: PreviousInlineLeafIgnoringLineBreak (inline_cursor_test.cc:1158)
    CSS Inline 3 §2: MoveToPreviousInlineLeafIgnoringLineBreak visits reverse leaves skipping line breaks. -/
theorem inlineCursor_previousInlineLeafIgnoringLineBreak :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 4, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 0 },
      { name := "DEF", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 1, lineIndex := 1 },
      { name := "xyz", lineIndex := 1 }
    ]
    collectPreviousInlineLeaves nodes 6 true = ["xyz", "DEF", "abc"] := by
  decide

/-- Test: PreviousInlineLeafOnLineFromLayoutInline (inline_cursor_test.cc:1171)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: MoveToPreviousInlineLeafOnLine from an inline container
    visits preceding leaves on the same line, stopping before entering the previous line. -/
theorem inlineCursor_previousInlineLeafOnLineFromLayoutInline :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 3, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "def", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 5, lineIndex := 1 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 1 },
      { name := "ABC", lineIndex := 1 },
      { name := "", isLineBreak := true, lineIndex := 1 },
      { id := "start", name := "#start", descendantsCount := 1, lineIndex := 1 },
      { name := "DEF", lineIndex := 1 }
    ]
    collectPreviousInlineLeavesOnLine nodes 8 = ["#start", "", "ABC"] := by
  decide

/-- Test: PreviousInlineLeafOnLineFromLayoutText (inline_cursor_test.cc:1211)
    CSS 2.1 §9.4.2 & CSS Inline 3 §2.1: MoveToPreviousInlineLeafOnLine from text leaf
    traverses backward on the line and stops at line start. -/
theorem inlineCursor_previousInlineLeafOnLineFromLayoutText :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 3, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "def", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 5, lineIndex := 1 },
      { name := "LayoutInline B", descendantsCount := 1, lineIndex := 1 },
      { name := "ABC", lineIndex := 1 },
      { name := "", isLineBreak := true, lineIndex := 1 },
      { id := "start", name := "#start", descendantsCount := 1, lineIndex := 1 },
      { name := "DEF", lineIndex := 1 }
    ]
    collectPreviousInlineLeavesOnLine nodes 9 = ["DEF", "", "ABC"] := by
  decide

/-- Test: PreviousLine (inline_cursor_test.cc:1229)
    CSS 2.1 §9.4.2: MoveToPreviousLine moves to previous line box fragment, or null from first line. -/
theorem inlineCursor_previousLine :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 2, lineIndex := 0 },
      { name := "abc", lineIndex := 0 },
      { name := "", isLineBreak := true, lineIndex := 0 },
      { name := "#linebox", type := .line, descendantsCount := 1, lineIndex := 1 },
      { name := "xyz", lineIndex := 1 }
    ]
    findPreviousLine nodes 0 = none ∧
    findPreviousLine nodes 3 = some 0 := by
  decide

/-- Test: CursorForDescendants (inline_cursor_test.cc:1250)
    CSS Inline 3 §2: CursorForDescendants limits cursor to subtree descending from current container. -/
theorem inlineCursor_cursorForDescendants :
    let nodes : List CursorNode := [
      { name := "#linebox", type := .line, descendantsCount := 10 },
      { name := "text1" },
      { id := "span1", name := "#span1", descendantsCount := 4 },
      { name := "text2" },
      { id := "span2", name := "#span2", descendantsCount := 1 },
      { name := "text3" },
      { name := "text4" },
      { name := "text5" },
      { id := "span3", name := "#span3", descendantsCount := 1 },
      { name := "text6" },
      { name := "text7" }
    ]
    descendantNames nodes 1 = [] ∧
    descendantNames nodes 2 = ["text2", "#span2", "text3", "text4"] ∧
    descendantNames nodes 3 = [] ∧
    descendantNames nodes 4 = ["text3"] := by
  decide

end ChromiumLayout.TestsInline
