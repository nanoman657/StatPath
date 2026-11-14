import InlineGeometry
import InlineTextControl

namespace ChromiumLayout

/-! ## Form Text Control Layout Tests
    Specifications:
    - HTML 5.2 §4.10.5 The input element
    - HTML 5.2 §4.10.11 The textarea element
    - CSS 2.1 §9.2.1.1 Anonymous block boxes
    - CSS Pseudo 4 §4.1 Highlighting pseudos: the ::selection pseudo-element
    - CSS Backgrounds and Borders 3 §7.1 Box-shadow visual overflow
-/

/-- Test `LayoutTextControlInnerEditorTest, AddChildWithoutTrailingLf` (`forms/layout_text_control_inner_editor_test.cc:12`). -/
theorem layoutTextControl_addChildWithoutTrailingLf :
    let blocks := buildTextareaAnonymousBlocks "foo\nbar"
    blocks = [
      { children := [InnerEditorNode.text "foo", InnerEditorNode.br] },
      { children := [InnerEditorNode.text "bar"] }
    ] :=
  rfl

/-- Test `LayoutTextControlInnerEditorTest, AddChildWithTrailingLf` (`forms/layout_text_control_inner_editor_test.cc:43`). -/
theorem layoutTextControl_addChildWithTrailingLf :
    let blocks := buildTextareaAnonymousBlocks "foo\nbar\n"
    blocks = [
      { children := [InnerEditorNode.text "foo", InnerEditorNode.br] },
      { children := [InnerEditorNode.text "bar", InnerEditorNode.br] },
      { children := [InnerEditorNode.placeholderBr] }
    ] :=
  rfl

/-- Test `LayoutTextControlInnerEditorTest, RemoveChildWithoutTrailingLf` (`forms/layout_text_control_inner_editor_test.cc:85`). -/
theorem layoutTextControl_removeChildWithoutTrailingLf :
    let before := buildTextareaAnonymousBlocks "foo\nbar"
    let afterRemove := buildTextareaAnonymousBlocks "foo"
    before.length = 2 ∧
    afterRemove = [{ children := [InnerEditorNode.text "foo"] }] :=
  ⟨rfl, rfl⟩

/-- Test `LayoutTextControlInnerEditorTest, AddChildBeforeTestRenderingHolder` (`forms/layout_text_control_inner_editor_test.cc:114`). -/
theorem layoutTextControl_addChildBeforeTestRenderingHolder :
    let blocks := buildTextareaAnonymousBlocks "A\n"
    blocks = [
      { children := [InnerEditorNode.text "A", InnerEditorNode.br] },
      { children := [InnerEditorNode.placeholderBr] }
    ] :=
  rfl

/-- Test `LayoutTextControlInnerEditorTest, EnableDynamic` (`forms/layout_text_control_inner_editor_test.cc:126`). -/
theorem layoutTextControl_enableDynamic :
    let blocks := buildTextareaAnonymousBlocks ""
    blocks = [] :=
  rfl

/-- Test `LayoutTextControlTest, ChangingPseudoSelectionStyleShouldInvalidateSelectionSingle` (`forms/layout_text_control_test.cc:56`). -/
theorem layoutTextControl_changingPseudoSelectionStyleSingle :
    let st0 : TextControlSelectionState := { hasSelection := true, currentPseudoStyle := some { backgroundColor := some "blue" } }
    let st1 := updateSelectionPseudoStyle st0 (some { backgroundColor := some "green" })
    st1.shouldInvalidate = true ∧ st1.currentPseudoStyle = some { backgroundColor := some "green" } :=
  ⟨rfl, rfl⟩

/-- Test `LayoutTextControlTest, ChangingPseudoSelectionStyleShouldInvalidateSelectionMulti` (`forms/layout_text_control_test.cc:74`). -/
theorem layoutTextControl_changingPseudoSelectionStyleMulti :
    let st0 : TextControlSelectionState := { hasSelection := true, currentPseudoStyle := some { backgroundColor := some "blue" } }
    let st1 := updateSelectionPseudoStyle st0 (some { backgroundColor := some "green" })
    st1.shouldInvalidate = true ∧ st1.currentPseudoStyle = some { backgroundColor := some "green" } :=
  ⟨rfl, rfl⟩

/-- Test `LayoutTextControlTest, AddingPseudoSelectionStyleShouldInvalidateSelectionSingle` (`forms/layout_text_control_test.cc:92`). -/
theorem layoutTextControl_addingPseudoSelectionStyleSingle :
    let st0 : TextControlSelectionState := { hasSelection := true, currentPseudoStyle := none }
    let st1 := updateSelectionPseudoStyle st0 (some { backgroundColor := some "green" })
    st1.shouldInvalidate = true ∧ st1.currentPseudoStyle = some { backgroundColor := some "green" } :=
  ⟨rfl, rfl⟩

/-- Test `LayoutTextControlTest, RemovingPseudoSelectionStyleShouldInvalidateSelectionSingle` (`forms/layout_text_control_test.cc:126`). -/
theorem layoutTextControl_removingPseudoSelectionStyleSingle :
    let st0 : TextControlSelectionState := { hasSelection := true, currentPseudoStyle := some { backgroundColor := some "green" } }
    let st1 := updateSelectionPseudoStyle st0 none
    st1.shouldInvalidate = true ∧ st1.currentPseudoStyle = none :=
  ⟨rfl, rfl⟩

/-- Test `LayoutTextControlTest, RemovingPseudoSelectionStyleShouldInvalidateSelectionMulti` (`forms/layout_text_control_test.cc:142`). -/
theorem layoutTextControl_removingPseudoSelectionStyleMulti :
    let st0 : TextControlSelectionState := { hasSelection := true, currentPseudoStyle := some { backgroundColor := some "green" } }
    let st1 := updateSelectionPseudoStyle st0 none
    st1.shouldInvalidate = true ∧ st1.currentPseudoStyle = none :=
  ⟨rfl, rfl⟩

/-- Test `LayoutTextControlTest, HitTestSearchInput` (`forms/layout_text_control_test.cc:158`). -/
theorem layoutTextControl_hitTestSearchInput :
    let ctrl : TextControlLayout := {
      border := { top := 20, right := 20, bottom := 20, left := 20 }
    }
    let pt : PhysicalOffset := { left := 40, top := 30 }
    mapPointToInnerEditor ctrl pt = { left := 20, top := 10 } :=
  rfl

/-- Test `LayoutTextControlSingleLineTest, VisualOverflowCleared` (`forms/layout_text_control_single_line_test.cc:13`). -/
theorem layoutTextControl_visualOverflowCleared :
    let borderBox : LayoutUnitRect := { x := 0, y := 0, width := 58, height := 56 }
    let shadow : BoxShadow := { offsetX := 5, offsetY := 5, blurRadius := 5 }
    let withShadow := computeSelfVisualOverflow borderBox (some shadow)
    let cleared := computeSelfVisualOverflow borderBox none
    withShadow = { x := -3, y := -3, width := 74, height := 72 } ∧
    cleared = { x := 0, y := 0, width := 58, height := 56 } :=
  ⟨rfl, rfl⟩

end ChromiumLayout
