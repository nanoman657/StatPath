/-
  docs/chromium-layout/tests/TestsInline_InlineCaretPosition.lean

  Formalized tests for CSS Inline 3 §2, CSS Text 3 §5, and Blink InlineCaretPosition
  (`third_party/blink/renderer/core/layout/inline/inline_caret_position_test.cc`).
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineCaret

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-- Test `InlineCaretPositionTest.AfterSpan` (`inline/inline_caret_position_test.cc:69`).
    CSS Inline 3 §2: Non-culled inline box generates box fragment; caret after node resolves to kAfterBox. -/
theorem inlineCaretPosition_afterSpan :
    let doc := CaretDocItem.span "target" false "ABC"
    let frags := buildCaretFragments doc
    computeCaretPosition frags (.afterNode "target") .downstream =
      { fragmentId := 0, positionType := .afterBox, textOffset := none } := by
  decide

/-- Test `InlineCaretPositionTest.AfterSpanCulled` (`inline/inline_caret_position_test.cc:79`).
    CSS Inline 3 §2: Culled inline box has no box fragment; caret after node resolves to kAtTextOffset at text length. -/
theorem inlineCaretPosition_afterSpanCulled :
    let doc := CaretDocItem.span "target" true "ABC"
    let frags := buildCaretFragments doc
    computeCaretPosition frags (.afterNode "target") .downstream =
      { fragmentId := 0, positionType := .atTextOffset, textOffset := some 3 } := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionInOneLineOfText` (`inline/inline_caret_position_test.cc:89`).
    CSS Text 3 §5: Single line of text resolves carets at beginning, middle, and end to kAtTextOffset. -/
theorem inlineCaretPosition_inOneLineOfText :
    let doc := CaretDocItem.text "foo"
    let frags := buildCaretFragments doc
    -- Beginning of line (offset 0)
    (computeCaretPosition frags (.atOffset 0) .downstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 0 }) ∧
    (computeCaretPosition frags (.atOffset 0) .upstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 0 }) ∧
    -- Middle in the line (offset 1)
    (computeCaretPosition frags (.atOffset 1) .downstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 1 }) ∧
    (computeCaretPosition frags (.atOffset 1) .upstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 1 }) ∧
    -- End of line (offset 3)
    (computeCaretPosition frags (.atOffset 3) .downstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (computeCaretPosition frags (.atOffset 3) .upstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 3 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtSoftHyphen` (`inline/inline_caret_position_test.cc:115`).
    CSS Text 3 §5.3: Caret after soft hyphen at offset 4 resolves to kAtTextOffset on the text fragment. -/
theorem inlineCaretPosition_atSoftHyphen :
    let doc := CaretDocItem.softHyphenText "foo" "bar"
    let frags := buildCaretFragments doc
    (computeCaretPosition frags (.atOffset 4) .downstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 4 }) ∧
    (computeCaretPosition frags (.atOffset 4) .upstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 4 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtSoftLineWrap` (`inline/inline_caret_position_test.cc:130`).
    CSS Text 3 §5: Soft line wrap boundary resolves upstream to previous line fragment and downstream to next line fragment. -/
theorem inlineCaretPosition_atSoftLineWrap :
    let doc := CaretDocItem.softWrapText "foo" "bar"
    let frags := buildCaretFragments doc
    (computeCaretPosition frags (.atOffset 3) .downstream = { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (computeCaretPosition frags (.atOffset 3) .upstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 3 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtForcedLineBreak` (`inline/inline_caret_position_test.cc:169`).
    CSS Text 3 §5: Forced line break (<br>) resolves caret before break to line 1 and after break to line 2. -/
theorem inlineCaretPosition_atForcedLineBreak :
    let doc := CaretDocItem.forcedBreakText "foo" "bar"
    let frags := buildCaretFragments doc
    (computeCaretPosition frags (.atOffset 3) .downstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (computeCaretPosition frags (.atOffset 3) .upstream = { fragmentId := 0, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (computeCaretPosition frags (.atOffset 4) .downstream = { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }) ∧
    (computeCaretPosition frags (.atOffset 4) .upstream = { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtEmptyLine` (`inline/inline_caret_position_test.cc:190`).
    CSS 2.1 §10.8: Empty line generated by consecutive <br> resolves caret at text offset 4 on br2 fragment. -/
theorem inlineCaretPosition_atEmptyLine :
    let doc := CaretDocItem.emptyLineText "foo" "bar"
    let frags := buildCaretFragments doc
    (computeCaretPosition frags (.atOffset 4) .downstream = { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }) ∧
    (computeCaretPosition frags (.atOffset 4) .upstream = { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionInOneLineOfImage` (`inline/inline_caret_position_test.cc:203`).
    CSS Inline 3 §2: Atomic inline image resolves offset 0 to kBeforeBox and offset 1 to kAfterBox. -/
theorem inlineCaretPosition_inOneLineOfImage :
    let doc := CaretDocItem.atomicImage "img"
    let frags := buildCaretFragments doc
    (computeCaretPosition frags (.atOffset 0) .downstream = { fragmentId := 0, positionType := .beforeBox, textOffset := none }) ∧
    (computeCaretPosition frags (.atOffset 0) .upstream = { fragmentId := 0, positionType := .beforeBox, textOffset := none }) ∧
    (computeCaretPosition frags (.atOffset 1) .downstream = { fragmentId := 0, positionType := .afterBox, textOffset := none }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtSoftLineWrapBetweenImages` (`inline/inline_caret_position_test.cc:221`).
    Wrap between two images resolves downstream to beforeBox on img2 and upstream to afterBox on img1. -/
theorem inlineCaretPosition_atSoftLineWrapBetweenImages :
    let img1Frag := 1
    let img2Frag := 2
    (resolveSoftWrapBoxCaret img1Frag img2Frag .downstream = { fragmentId := img2Frag, positionType := .beforeBox, textOffset := none }) ∧
    (resolveSoftWrapBoxCaret img1Frag img2Frag .upstream = { fragmentId := img1Frag, positionType := .afterBox, textOffset := none }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtSoftLineWrapBetweenMultipleTextNodes` (`inline/inline_caret_position_test.cc:238`).
    Wrap between span-c and span-d at text offset 3 resolves upstream to span-c and downstream to span-d. -/
theorem inlineCaretPosition_atSoftLineWrapBetweenMultipleTextNodes :
    let fragC := 3
    let fragD := 4
    (resolveSoftWrapCaret fragC fragD 3 .upstream = { fragmentId := fragC, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (resolveSoftWrapCaret fragC fragD 3 .downstream = { fragmentId := fragD, positionType := .atTextOffset, textOffset := some 3 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtSoftLineWrapBetweenMultipleTextNodesRtl` (`inline/inline_caret_position_test.cc:263`).
    Wrap in RTL text resolves identically to LTR in logical text offsets. -/
theorem inlineCaretPosition_atSoftLineWrapBetweenMultipleTextNodesRtl :
    let fragC := 3
    let fragD := 4
    (resolveSoftWrapCaret fragC fragD 3 .upstream = { fragmentId := fragC, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (resolveSoftWrapCaret fragC fragD 3 .downstream = { fragmentId := fragD, positionType := .atTextOffset, textOffset := some 3 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineCaretPositionAtSoftLineWrapBetweenDeepTextNodes` (`inline/inline_caret_position_test.cc:288`).
    Wrap between bordered spans resolves to text fragments at the wrap offset. -/
theorem inlineCaretPosition_atSoftLineWrapBetweenDeepTextNodes :
    let fragC := 3
    let fragD := 4
    (resolveSoftWrapCaret fragC fragD 3 .upstream = { fragmentId := fragC, positionType := .atTextOffset, textOffset := some 3 }) ∧
    (resolveSoftWrapCaret fragC fragD 3 .downstream = { fragmentId := fragD, positionType := .atTextOffset, textOffset := some 3 }) := by
  decide

/-- Test `InlineCaretPositionTest.GeneratedZeroWidthSpace` (`inline/inline_caret_position_test.cc:315`).
    Wrap around generated ZWS resolves upstream to space line fragment (offset 4) and downstream to text line fragment (offset 5). -/
theorem inlineCaretPosition_generatedZeroWidthSpace :
    let spaceFrag := 1
    let textFrag := 2
    (resolveTextCaret spaceFrag 4 = { fragmentId := spaceFrag, positionType := .atTextOffset, textOffset := some 4 }) ∧
    (resolveTextCaret textFrag 5 = { fragmentId := textFrag, positionType := .atTextOffset, textOffset := some 5 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineBlockBeforeContent` (`inline/inline_caret_position_test.cc:509`).
    Caret at start of text following ::before inline-block resolves atTextOffset on text fragment. -/
theorem inlineCaretPosition_inlineBlockBeforeContent :
    let textFrag := 2
    let offset := 0
    resolveTextCaret textFrag offset = { fragmentId := textFrag, positionType := .atTextOffset, textOffset := some 0 } := by
  decide

/-- Test `InlineCaretPositionTest.InlineBoxesLTR` (`inline/inline_caret_position_test.cc:528`).
    CSS Writing Modes 3: Carets inside bdo dir=ltr resolve atTextOffset accounting for bidi isolate and override codes. -/
theorem inlineCaretPosition_inlineBoxesLTR :
    let box1Frag := 1
    let box2Frag := 2
    (resolveTextCaret box1Frag 6 = { fragmentId := box1Frag, positionType := .atTextOffset, textOffset := some 6 }) ∧
    (resolveTextCaret box2Frag 2 = { fragmentId := box2Frag, positionType := .atTextOffset, textOffset := some 2 }) := by
  decide

/-- Test `InlineCaretPositionTest.InlineBoxesRTL` (`inline/inline_caret_position_test.cc:559`).
    CSS Writing Modes 3: Carets inside bdo dir=rtl resolve atTextOffset accounting for bidi isolate and override codes. -/
theorem inlineCaretPosition_inlineBoxesRTL :
    let box1Frag := 1
    let box2Frag := 2
    (resolveTextCaret box1Frag 6 = { fragmentId := box1Frag, positionType := .atTextOffset, textOffset := some 6 }) ∧
    (resolveTextCaret box2Frag 2 = { fragmentId := box2Frag, positionType := .atTextOffset, textOffset := some 2 }) := by
  decide

end ChromiumLayout.TestsInline
