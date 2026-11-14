import InlineGeometry

namespace ChromiumLayout

/-! ## HTML Form Text Control Layout Model
    Specifications:
    - HTML 5.2 §4.10.5 The input element
    - HTML 5.2 §4.10.11 The textarea element
    - CSS 2.1 §9.2.1.1 Anonymous block boxes
    - CSS Pseudo 4 §4.1 Highlighting pseudos: the ::selection pseudo-element
    - CSS Backgrounds and Borders 3 §7.1 Box-shadow visual overflow
    Blink reference:
    - `third_party/blink/renderer/core/layout/forms/layout_text_control.cc`
    - `third_party/blink/renderer/core/layout/forms/layout_text_control_single_line.cc`
    - `third_party/blink/renderer/core/layout/forms/layout_text_control_inner_editor.cc`
-/

/-- Child node inside an inner editor anonymous block flow (HTML 5.2 §4.10.11). -/
inductive InnerEditorNode where
  | text (content : String)
  | br
  | placeholderBr
  deriving DecidableEq, Repr, Inhabited

/-- Anonymous block box containing line contents of a textarea (CSS 2.1 §9.2.1.1). -/
structure AnonymousBlockFlow where
  children : List InnerEditorNode
  deriving DecidableEq, Repr, Inhabited

/-- Helper to split a plain text string into lines for textarea layout (HTML 5.2 §4.10.11). -/
def splitTextareaLines (content : String) : List (String × Bool) :=
  let chars := content.toList
  let rec loop (cur : List Char) (cs : List Char) (acc : List (String × Bool)) : List (String × Bool) :=
    match cs with
    | [] =>
      if cur.isEmpty then acc.reverse
      else (String.ofList cur.reverse, false) :: acc |>.reverse
    | '\n' :: rest =>
      loop [] rest ((String.ofList cur.reverse, true) :: acc)
    | c :: rest =>
      loop (c :: cur) rest acc
  loop [] chars []

/-- Build anonymous block flows for a textarea's inner editor (HTML 5.2 §4.10.11, CSS 2.1 §9.2.1.1).
    Each line becomes an anonymous block flow.
    A line terminated by newline has a `br` node following its text.
    If content has a trailing newline, a trailing block with `placeholderBr` is added. -/
def buildTextareaAnonymousBlocks (content : String) : List AnonymousBlockFlow :=
  let lines := splitTextareaLines content
  let hasTrailingLf := !content.isEmpty && content.toList.reverse.head? == some '\n'
  let lineBlocks := lines.map (fun (lineText, hasLf) =>
    let kids : List InnerEditorNode :=
      if lineText.isEmpty then
        if hasLf then [InnerEditorNode.br] else []
      else
        if hasLf then [InnerEditorNode.text lineText, InnerEditorNode.br]
        else [InnerEditorNode.text lineText]
    { children := kids })
  if hasTrailingLf then
    lineBlocks ++ [{ children := [InnerEditorNode.placeholderBr] }]
  else
    lineBlocks

/-- Pseudo selection style specification (CSS Pseudo 4 §4.1). -/
structure SelectionPseudoStyle where
  backgroundColor : Option String := none
  color : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- Selection state of a text control element (CSS Pseudo 4 §4.1). -/
structure TextControlSelectionState where
  hasSelection : Bool := true
  currentPseudoStyle : Option SelectionPseudoStyle := none
  shouldInvalidate : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Update pseudo selection style on a text control (CSS Pseudo 4 §4.1).
    When the computed style of ::selection changes (added, modified, or removed),
    the selection display must be invalidated. -/
def updateSelectionPseudoStyle (st : TextControlSelectionState) (newStyle : Option SelectionPseudoStyle) : TextControlSelectionState :=
  let styleChanged := st.currentPseudoStyle != newStyle
  { st with currentPseudoStyle := newStyle, shouldInvalidate := st.hasSelection && styleChanged }

/-- Layout geometry for a text control (HTML 5.2 §4.10.5, CSS 2.1 §10). -/
structure TextControlLayout where
  border : PhysicalBoxStrut := {}
  padding : PhysicalBoxStrut := {}
  contentSize : PhysicalSize := {}
  deriving DecidableEq, Repr, Inhabited

/-- Map a hit-test point in the text control coordinate space to the inner editor coordinate space. -/
def mapPointToInnerEditor (ctrl : TextControlLayout) (point : PhysicalOffset) : PhysicalOffset :=
  { left := point.left - ctrl.border.left, top := point.top - ctrl.border.top }

/-- Box shadow definition for visual overflow computation (CSS Backgrounds and Borders 3 §7.1). -/
structure BoxShadow where
  offsetX : Int
  offsetY : Int
  blurRadius : Nat
  spreadRadius : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Compute self visual overflow rect for a box with optional box shadow (CSS Backgrounds and Borders 3 §7.1).
    Blink blurs expand shadow bounds by ceil(3 * blur / 2). -/
def computeSelfVisualOverflow (borderBox : LayoutUnitRect) (shadow : Option BoxShadow) : LayoutUnitRect :=
  match shadow with
  | none => borderBox
  | some s =>
    let blurExt : Int := (3 * (s.blurRadius : Int) + 1) / 2
    let xMin : Int := s.offsetX - blurExt
    let yMin : Int := s.offsetY - blurExt
    let xMax : Int := borderBox.width + s.offsetX + blurExt
    let yMax : Int := borderBox.height + s.offsetY + blurExt
    let outX : Int := min 0 xMin
    let outY : Int := min 0 yMin
    let outW : Int := max borderBox.width xMax - outX
    let outH : Int := max borderBox.height yMax - outY
    { x := outX, y := outY, width := outW, height := outH }

/-- General Law: Updating selection pseudo style to a different style always marks selection for invalidation when selection exists (CSS Pseudo 4 §4.1). -/
theorem selection_pseudo_style_invalidation (st : TextControlSelectionState) (newStyle : Option SelectionPseudoStyle)
    (h_sel : st.hasSelection = true) (h_diff : st.currentPseudoStyle ≠ newStyle) :
    (updateSelectionPseudoStyle st newStyle).shouldInvalidate = true := by
  dsimp [updateSelectionPseudoStyle]
  have h_bne : (st.currentPseudoStyle != newStyle) = true := by
    rw [bne_iff_ne]
    exact h_diff
  simp [h_bne, h_sel]

/-- General Law: Self visual overflow with no shadow is the identity on the border box (CSS Backgrounds and Borders 3 §7.1). -/
theorem visual_overflow_none_identity (bb : LayoutUnitRect) :
    computeSelfVisualOverflow bb none = bb := by
  rfl

/-- General Law: Mapping a point to inner editor coordinates preserves relative distance from the border (CSS 2.1 §10). -/
theorem map_point_inner_editor_shift (ctrl : TextControlLayout) (point : PhysicalOffset)
    (h_l : point.left ≥ ctrl.border.left) (h_t : point.top ≥ ctrl.border.top) :
    (mapPointToInnerEditor ctrl point).left + ctrl.border.left = point.left ∧
    (mapPointToInnerEditor ctrl point).top + ctrl.border.top = point.top := by
  dsimp [mapPointToInnerEditor]
  omega

end ChromiumLayout
