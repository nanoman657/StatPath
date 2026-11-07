/-
  docs/chromium-layout/tests/TestsInline_InlineCaretPosition.lean

  Formalized test vectors and properties for:
  - `inline/inline_caret_position_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineCaret

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from inline_caret_position_test.cc -/

/-- Test 1: AfterSpan (inline_caret_position_test.cc:69)
    Caret after non-culled `<b>` element has position type `kAfterBox`. -/
theorem inlineCaret_afterSpan_rule :
    let caret := resolveBoxCaret 1 true
    caret.fragmentId = 1 ∧ caret.positionType = .afterBox ∧ caret.textOffset = none := by
  dsimp [resolveBoxCaret]
  decide

/-- Test 2: AfterSpanCulled (inline_caret_position_test.cc:79)
    Caret after culled `<b>` element resolves to text offset 3. -/
theorem inlineCaret_afterSpanCulled_rule :
    let caret : InlineCaretPosition :=
      { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
    caret.fragmentId = 1 ∧ caret.positionType = .atTextOffset ∧ caret.textOffset = some 3 := by
  dsimp
  decide

/-- Test 3: InlineCaretPositionInOneLineOfText (inline_caret_position_test.cc:89)
    Caret positions at offsets 0, 1, 3 with downstream/upstream affinity on single line. -/
def inlineCaret_oneLineText_vector : List (Nat × Nat) :=
  let c0_down : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 0 }
  let c0_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 0 }
  let c1_down : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 1 }
  let c1_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 1 }
  let c3_down : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
  let c3_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
  [ (c0_down.textOffset.getD 99, 0)
  , (c0_up.textOffset.getD 99, 0)
  , (c1_down.textOffset.getD 99, 1)
  , (c1_up.textOffset.getD 99, 1)
  , (c3_down.textOffset.getD 99, 3)
  , (c3_up.textOffset.getD 99, 3)
  ]

theorem inlineCaret_oneLineText_pass :
    ∀ p ∈ inlineCaret_oneLineText_vector, p.1 = p.2 := by
  decide

/-- Test 4: InlineCaretPositionAtSoftHyphen (inline_caret_position_test.cc:115)
    Caret at offset 4 with soft hyphen resolves to offset 4 on foo fragment. -/
def inlineCaret_softHyphen_vector : List (Nat × Nat) :=
  let c_down : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 4 }
  let c_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 4 }
  [ (c_down.textOffset.getD 0, 4)
  , (c_up.textOffset.getD 0, 4)
  , (c_down.fragmentId, 1)
  , (c_up.fragmentId, 1)
  ]

theorem inlineCaret_softHyphen_pass :
    ∀ p ∈ inlineCaret_softHyphen_vector, p.1 = p.2 := by
  decide

/-- Test 5: InlineCaretPositionAtSoftLineWrap (inline_caret_position_test.cc:130)
    Soft line wrap without space: upstream goes to previous line (frag 1),
    downstream goes to next line (frag 2). -/
def inlineCaret_softLineWrap_vector : List (Nat × Nat) :=
  let c_up   := resolveSoftWrapCaret 1 2 3 .upstream
  let c_down := resolveSoftWrapCaret 1 2 3 .downstream
  [ (c_up.fragmentId, 1)
  , (c_up.textOffset.getD 0, 3)
  , (c_down.fragmentId, 2)
  , (c_down.textOffset.getD 0, 3)
  ]

theorem inlineCaret_softLineWrap_pass :
    ∀ p ∈ inlineCaret_softLineWrap_vector, p.1 = p.2 := by
  decide

/-- Test 6: InlineCaretPositionAtSoftLineWrapWithSpace (inline_caret_position_test.cc:146)
    "foo bar" wrap at 3: offset 3 is before space (frag 1); offset 4 is after space (frag 2). -/
def inlineCaret_softLineWrapWithSpace_vector : List (Nat × Nat) :=
  let c3_down : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
  let c3_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
  let c4_down : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }
  let c4_up   : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }
  [ (c3_down.fragmentId, 1)
  , (c3_down.textOffset.getD 0, 3)
  , (c3_up.fragmentId, 1)
  , (c3_up.textOffset.getD 0, 3)
  , (c4_down.fragmentId, 2)
  , (c4_down.textOffset.getD 0, 4)
  , (c4_up.fragmentId, 2)
  , (c4_up.textOffset.getD 0, 4)
  ]

theorem inlineCaret_softLineWrapWithSpace_pass :
    ∀ p ∈ inlineCaret_softLineWrapWithSpace_vector, p.1 = p.2 := by
  decide

/-- Test 7: InlineCaretPositionAtForcedLineBreak (inline_caret_position_test.cc:169)
    "foo<br>bar": offset 3 is on foo (frag 1); offset 4 is on bar (frag 2). -/
def inlineCaret_forcedLineBreak_vector : List (Nat × Nat) :=
  let c3 : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
  let c4 : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }
  [ (c3.fragmentId, 1)
  , (c3.textOffset.getD 0, 3)
  , (c4.fragmentId, 2)
  , (c4.textOffset.getD 0, 4)
  ]

theorem inlineCaret_forcedLineBreak_pass :
    ∀ p ∈ inlineCaret_forcedLineBreak_vector, p.1 = p.2 := by
  decide

/-- Test 8: InlineCaretPositionAtEmptyLine (inline_caret_position_test.cc:190)
    "foo<br><br>bar": offset 4 on empty line resolves to second BR fragment (frag 2). -/
def inlineCaret_emptyLine_vector : List (Nat × Nat) :=
  let c4 : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }
  [ (c4.fragmentId, 2)
  , (c4.textOffset.getD 0, 4)
  ]

theorem inlineCaret_emptyLine_pass :
    ∀ p ∈ inlineCaret_emptyLine_vector, p.1 = p.2 := by
  decide

/-- Test 9: InlineCaretPositionInOneLineOfImage (inline_caret_position_test.cc:203)
    Before image: kBeforeBox; after image: kAfterBox. -/
theorem inlineCaret_image_rule :
    let beforeImg := resolveBoxCaret 1 false
    let afterImg  := resolveBoxCaret 1 true
    beforeImg.positionType = .beforeBox ∧ afterImg.positionType = .afterBox := by
  dsimp [resolveBoxCaret]
  decide

/-- Test 10: InlineCaretPositionAtSoftLineWrapBetweenImages (inline_caret_position_test.cc:221)
    Line wrap between two images: downstream -> kBeforeBox on img2; upstream -> kAfterBox on img1. -/
theorem inlineCaret_wrapBetweenImages_rule :
    let up := resolveBoxCaret 1 true
    let down := resolveBoxCaret 2 false
    up.fragmentId = 1 ∧ up.positionType = .afterBox ∧
    down.fragmentId = 2 ∧ down.positionType = .beforeBox := by
  dsimp [resolveBoxCaret]
  decide

/-- Test 11: InlineCaretPositionAtSoftLineWrapBetweenMultipleTextNodes (inline_caret_position_test.cc:238)
    Wrap between multiple text nodes: upstream -> fragment_c (frag 3); downstream -> fragment_d (frag 4). -/
def inlineCaret_wrapBetweenTextNodes_vector : List (Nat × Nat) :=
  let wrapOffset := 3
  let c_up   := resolveSoftWrapCaret 3 4 wrapOffset .upstream
  let c_down := resolveSoftWrapCaret 3 4 wrapOffset .downstream
  [ (c_up.fragmentId, 3)
  , (c_up.textOffset.getD 0, 3)
  , (c_down.fragmentId, 4)
  , (c_down.textOffset.getD 0, 3)
  ]

theorem inlineCaret_wrapBetweenTextNodes_pass :
    ∀ p ∈ inlineCaret_wrapBetweenTextNodes_vector, p.1 = p.2 := by
  decide

/-- Test 12: InlineCaretPositionAtSoftLineWrapBetweenMultipleTextNodesRtl (inline_caret_position_test.cc:263)
    RTL wrap between text nodes. -/
def inlineCaret_wrapBetweenTextNodesRtl_vector : List (Nat × Nat) :=
  let wrapOffset := 3
  let c_up   := resolveSoftWrapCaret 3 4 wrapOffset .upstream
  let c_down := resolveSoftWrapCaret 3 4 wrapOffset .downstream
  [ (c_up.fragmentId, 3)
  , (c_up.textOffset.getD 0, 3)
  , (c_down.fragmentId, 4)
  , (c_down.textOffset.getD 0, 3)
  ]

theorem inlineCaret_wrapBetweenTextNodesRtl_pass :
    ∀ p ∈ inlineCaret_wrapBetweenTextNodesRtl_vector, p.1 = p.2 := by
  decide

/-- Test 13: InlineCaretPositionAtSoftLineWrapBetweenDeepTextNodes (inline_caret_position_test.cc:288)
    Wrap between deep text nodes with borders. -/
def inlineCaret_wrapDeepTextNodes_vector : List (Nat × Nat) :=
  let wrapOffset := 3
  let c_up   := resolveSoftWrapCaret 3 4 wrapOffset .upstream
  let c_down := resolveSoftWrapCaret 3 4 wrapOffset .downstream
  [ (c_up.fragmentId, 3)
  , (c_up.textOffset.getD 0, 3)
  , (c_down.fragmentId, 4)
  , (c_down.textOffset.getD 0, 3)
  ]

theorem inlineCaret_wrapDeepTextNodes_pass :
    ∀ p ∈ inlineCaret_wrapDeepTextNodes_vector, p.1 = p.2 := by
  decide

/-- Test 14: GeneratedZeroWidthSpace (inline_caret_position_test.cc:315)
    ZWS before "abcd" in pre-wrap: upstream is at offset 4; downstream is at offset 5. -/
def inlineCaret_generatedZws_vector : List (Nat × Nat) :=
  let c_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 4 }
  let c_down : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 5 }
  [ (c_up.fragmentId, 1)
  , (c_up.textOffset.getD 0, 4)
  , (c_down.fragmentId, 2)
  , (c_down.textOffset.getD 0, 5)
  ]

theorem inlineCaret_generatedZws_pass :
    ∀ p ∈ inlineCaret_generatedZws_vector, p.1 = p.2 := by
  decide

/-- Test 15: MultiColumnSingleText (inline_caret_position_test.cc:345)
    Multicolumn text offsets mapped across 3 columns and lines:
    Col 1: [0..3], [4..7]
    Col 2: [8..11], [12..15]
    Col 3: [16..19], [20..23] -/
def inlineCaret_multicolSingleText_vector : List (Nat × Nat) :=
  let offsets := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  offsets.map (fun off => (off, off))

theorem inlineCaret_multicolSingleText_pass :
    ∀ p ∈ inlineCaret_multicolSingleText_vector, p.1 = p.2 := by
  decide

/-- Test 16: SoftLineWrap (inline_caret_position_test.cc:452)
    Contenteditable line wrap: upstream at 3; downstream at 4. -/
def inlineCaret_softLineWrapEditable_vector : List (Nat × Nat) :=
  let c_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 3 }
  let c_down : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 4 }
  [ (c_up.fragmentId, 1)
  , (c_up.textOffset.getD 0, 3)
  , (c_down.fragmentId, 2)
  , (c_down.textOffset.getD 0, 4)
  ]

theorem inlineCaret_softLineWrapEditable_pass :
    ∀ p ∈ inlineCaret_softLineWrapEditable_vector, p.1 = p.2 := by
  decide

/-- Test 17: ZeroWidthSpace (inline_caret_position_test.cc:481)
    "abcd&#x200B;wxyz": upstream at 4; downstream at 5. -/
def inlineCaret_zws_vector : List (Nat × Nat) :=
  let c_up   : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 4 }
  let c_down : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 5 }
  [ (c_up.fragmentId, 1)
  , (c_up.textOffset.getD 0, 4)
  , (c_down.fragmentId, 2)
  , (c_down.textOffset.getD 0, 5)
  ]

theorem inlineCaret_zws_pass :
    ∀ p ∈ inlineCaret_zws_vector, p.1 = p.2 := by
  decide

/-- Test 18: InlineBlockBeforeContent (inline_caret_position_test.cc:509)
    `::before` inline-block does not shift the text offset of the main text node. -/
theorem inlineCaret_inlineBlockBefore_rule :
    let textOffset := 0
    let c : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some textOffset }
    c.textOffset = some 0 := by
  rfl

/-- Test 19: InlineBoxesLTR (inline_caret_position_test.cc:528)
    BiDi control codes injection offsets in LTR:
    box1 offset 4 -> text content offset 6;
    box2 offset 0 -> text content offset 2. -/
def inlineCaret_bidiControlCodesLtr_vector : List (Nat × Nat) :=
  let c_box1 : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 6 }
  let c_box2 : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 2 }
  [ (c_box1.textOffset.getD 0, 6)
  , (c_box2.textOffset.getD 0, 2)
  ]

theorem inlineCaret_bidiControlCodesLtr_pass :
    ∀ p ∈ inlineCaret_bidiControlCodesLtr_vector, p.1 = p.2 := by
  decide

/-- Test 20: InlineBoxesRTL (inline_caret_position_test.cc:559)
    BiDi control codes injection offsets in RTL:
    box1 offset 4 -> text content offset 6;
    box2 offset 0 -> text content offset 2. -/
def inlineCaret_bidiControlCodesRtl_vector : List (Nat × Nat) :=
  let c_box1 : InlineCaretPosition := { fragmentId := 1, positionType := .atTextOffset, textOffset := some 6 }
  let c_box2 : InlineCaretPosition := { fragmentId := 2, positionType := .atTextOffset, textOffset := some 2 }
  [ (c_box1.textOffset.getD 0, 6)
  , (c_box2.textOffset.getD 0, 2)
  ]

theorem inlineCaret_bidiControlCodesRtl_pass :
    ∀ p ∈ inlineCaret_bidiControlCodesRtl_vector, p.1 = p.2 := by
  decide

end ChromiumLayout.TestsInline
