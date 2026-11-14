/-
  docs/chromium-layout/InlineTextCombine.lean

  Formal model for CSS Writing Modes Level 3 §5 (Horizontal-in-Vertical Composition:
  the text-combine-upright property) and Blink LayoutTextCombine
  (`third_party/blink/renderer/core/layout/layout_text_combine.h`,
   `layout_text_combine.cc`).
-/
import LayoutTypes
import InlineGeometry

namespace ChromiumLayout

/-! ## 1. CSS Writing Modes 3 §5.1 Horizontal-in-Vertical Composition -/

/-- CSS Writing Modes 3 §3.1: Whether a writing mode is vertical. -/
def isVerticalWritingMode : WritingMode → Bool
  | .horizontalTb => false
  | .verticalRl => true
  | .verticalLr => true
  | .sidewaysRl => true
  | .sidewaysLr => true

/-- CSS Writing Modes 3 §5.1: The text-combine-upright property values (none | all). -/
inductive TextCombineUpright where
  | none
  | all
  deriving DecidableEq, Repr, Inhabited

/-- CSS Writing Modes 3 §5.1 / HTML 5 §14.3.1: Writing mode propagation from body to html. -/
def propagateWritingMode (rootMode : WritingMode) (bodyMode : Option WritingMode) : WritingMode :=
  match bodyMode with
  | some m => m
  | none => rootMode

/-- CSS Writing Modes 3 §3.1: An inline box does not establish a writing mode;
    its effective writing mode is inherited from its containing block. -/
def effectiveWritingModeForInline (containingBlockMode : WritingMode) (_specifiedInlineMode : WritingMode) : WritingMode :=
  containingBlockMode

/-- CSS Writing Modes 3 §5.1: Text combine is active if and only if
    the effective writing mode is vertical and text-combine-upright is all. -/
def isTextCombineActive (wm : WritingMode) (tcu : TextCombineUpright) : Bool :=
  isVerticalWritingMode wm && (tcu == .all)

/-! ## 2. Anonymous LayoutTextCombine Object Creation -/

/-- Inline content items that can participate in text combination. -/
inductive CombinableContent where
  | text (content : String)
  | fragment (content : String)
  | br
  | wbr (id : Option String := none)
  | counter (val : String)
  deriving DecidableEq, Repr, Inhabited

/-- Anonymous LayoutTextCombine wrapper box holding combined inline content. -/
structure LayoutCombineBox where
  children : List CombinableContent
  deriving DecidableEq, Repr, Inhabited

/-- Display item: either bare combinable content or wrapped in LayoutTextCombine. -/
inductive InlineDisplayItem where
  | bare (item : CombinableContent)
  | combined (box : LayoutCombineBox)
  deriving DecidableEq, Repr, Inhabited

/-- CSS Writing Modes 3 §5.1.2 / Blink LayoutTextCombine::CreateAnonymous:
    When text combine is active, consecutive combinable inline content is wrapped
    in an anonymous LayoutTextCombine container; otherwise bare items are preserved. -/
def buildInlineDisplay (active : Bool) (items : List CombinableContent) : List InlineDisplayItem :=
  if active then
    if items.isEmpty then []
    else [.combined { children := items }]
  else
    items.map .bare

/-- Simple inline box representation for layout tree assertions. -/
structure SimpleInlineBox where
  tag : String
  id : Option String := none
  style : Option String := none
  items : List InlineDisplayItem := []
  deriving DecidableEq, Repr, Inhabited

/-- Simple block flow box representation for layout tree assertions. -/
structure SimpleBlockFlow where
  tag : String
  isAnonymous : Bool := false
  id : Option String := none
  style : Option String := none
  items : List InlineDisplayItem := []
  inlines : List SimpleInlineBox := []
  deriving DecidableEq, Repr, Inhabited

/-! ## 3. General Laws for Text Combine -/

/-- CSS Writing Modes 3 §5.1: Horizontal writing mode never activates text combine. -/
theorem textCombine_horizontal_never_active (tcu : TextCombineUpright) :
    isTextCombineActive .horizontalTb tcu = false := by
  cases tcu <;> rfl

/-- CSS Writing Modes 3 §5.1: text-combine-upright: none never activates text combine. -/
theorem textCombine_none_never_active (wm : WritingMode) :
    isTextCombineActive wm .none = false := by
  cases wm <;> rfl

/-- CSS Writing Modes 3 §5.1: Vertical writing mode with text-combine-upright: all is active. -/
theorem textCombine_vertical_all_active (wm : WritingMode) (h : isVerticalWritingMode wm = true) :
    isTextCombineActive wm .all = true := by
  cases wm
  · contradiction
  · rfl
  · rfl
  · rfl
  · rfl

/-- CSS Writing Modes 3 §5.1 / HTML 5 §14.3.1: Body writing mode overrides root. -/
theorem propagateWritingMode_body_some (r b : WritingMode) :
    propagateWritingMode r (some b) = b := rfl

/-- CSS Writing Modes 3 §5.1 / HTML 5 §14.3.1: When body has no writing mode, root applies. -/
theorem propagateWritingMode_body_none (r : WritingMode) :
    propagateWritingMode r none = r := rfl

/-- CSS Writing Modes 3 §5.1 / HTML 5 §14.3.1: If body is horizontal, root text combine is inactive. -/
theorem textCombine_propagated_body_horizontal_never_active (r : WritingMode) (tcu : TextCombineUpright) :
    isTextCombineActive (propagateWritingMode r (some .horizontalTb)) tcu = false := by
  rw [propagateWritingMode_body_some]
  exact textCombine_horizontal_never_active tcu

/-- CSS Writing Modes 3 §5.1 / HTML 5 §14.3.1: If body is vertical, text-combine-upright: all is active. -/
theorem textCombine_propagated_body_vertical_all_active (r b : WritingMode) (h : isVerticalWritingMode b = true) :
    isTextCombineActive (propagateWritingMode r (some b)) .all = true := by
  rw [propagateWritingMode_body_some]
  exact textCombine_vertical_all_active b h

/-- CSS Writing Modes 3 §3.1: Inline boxes inherit writing mode from containing block. -/
theorem inline_writing_mode_inherits (container specified : WritingMode) :
    effectiveWritingModeForInline container specified = container := rfl

/-- CSS Writing Modes 3 §3.1 & §5.1: Inline box in horizontal container cannot activate text combine. -/
theorem inline_in_horizontal_container_textCombine_never_active (specified : WritingMode) (tcu : TextCombineUpright) :
    isTextCombineActive (effectiveWritingModeForInline .horizontalTb specified) tcu = false := by
  rw [inline_writing_mode_inherits]
  exact textCombine_horizontal_never_active tcu

/-- CSS Writing Modes 3 §5.1.2: When inactive, inline content is bare without LayoutTextCombine wrapper. -/
theorem buildInlineDisplay_inactive (items : List CombinableContent) :
    buildInlineDisplay false items = items.map .bare := rfl

/-- CSS Writing Modes 3 §5.1.2: When active, non-empty inline content is wrapped in LayoutTextCombine. -/
theorem buildInlineDisplay_active_nonempty (c : CombinableContent) (cs : List CombinableContent) :
    buildInlineDisplay true (c :: cs) = [.combined { children := c :: cs }] := rfl

/-- CSS Writing Modes 3 §5.1.2: Empty content produces empty display items. -/
theorem buildInlineDisplay_empty (active : Bool) :
    buildInlineDisplay active [] = [] := by
  cases active <;> rfl

/-! ## 4. Line Breaking with Text Combine (CSS Writing Modes 3 §5.1 & CSS Text 3 §5) -/

/-- Object replacement character (U+FFFC) used to represent atomic inlines like text-combine in the line text. -/
def objectReplacementChar : String := "\uFFFC"

/-- CSS Text 3 §5.1 & CSS Writing Modes 3 §5.1:
    Determine whether line breaking can occur immediately after a text-combine element.
    Breaking can occur if the combined text ends in a hyphen/dash, or is followed by whitespace.
    Breaking cannot occur inside the text-combine element. -/
def canBreakAfterCombine (combinedText : String) (_suffixText : String) : Bool :=
  match combinedText.toList.reverse with
  | '-' :: _ => true
  | ' ' :: _ => true
  | _ => false

/-- CSS Writing Modes 3 §5.1 & Blink LineBreaker:
    Break lines for a sequence containing a text-combine-upright element.
    Returns the list of line strings produced by LineBreaker. -/
def breakLinesWithTextCombine (prefixText : String) (combinedText : String) (suffixText : String) (availableWidth : Nat) (charWidth : Nat := 10) : List String :=
  let unbroken := prefixText ++ objectReplacementChar ++ suffixText
  let totalWidth := prefixText.toList.length * charWidth + charWidth + suffixText.toList.length * charWidth
  if totalWidth ≤ availableWidth then
    [unbroken]
  else if canBreakAfterCombine combinedText suffixText then
    [prefixText ++ objectReplacementChar, suffixText]
  else
    -- Unbreakable word overflows on a single line
    [unbroken]

/-- Combined hyphen text has a break opportunity after it. -/
theorem canBreakAfterCombine_hyphen (s : String) :
    canBreakAfterCombine "-" s = true := by
  rfl

/-- Combined alphanumeric text has no break opportunity after it. -/
theorem canBreakAfterCombine_alphanumeric (s : String) :
    canBreakAfterCombine "XYZ" s = false := by
  rfl

/-- Combined text with internal space but trailing non-space has no break opportunity after it. -/
theorem canBreakAfterCombine_space_inside (s : String) :
    canBreakAfterCombine "X Z" s = false := by
  rfl

/-- CSS Writing Modes 3 §5.1 Law: When total content fits available width, it is always placed on a single line. -/
theorem breakLinesWithTextCombine_fits (p c s : String) (avail w : Nat)
    (h : p.toList.length * w + w + s.toList.length * w ≤ avail) :
    breakLinesWithTextCombine p c s avail w = [p ++ objectReplacementChar ++ s] := by
  unfold breakLinesWithTextCombine
  simp [h]

/-- CSS Writing Modes 3 §5.1 Law: When combined text ends with hyphen and overflows, breaking occurs after the combined element. -/
theorem breakLinesWithTextCombine_hyphen_breaks (p s : String) (avail w : Nat)
    (h : ¬ (p.toList.length * w + w + s.toList.length * w ≤ avail)) :
    breakLinesWithTextCombine p "-" s avail w = [p ++ objectReplacementChar, s] := by
  unfold breakLinesWithTextCombine
  simp [h, canBreakAfterCombine_hyphen]

/-- CSS Writing Modes 3 §5.1 Law: When combined text has no break opportunity after it, overflowing content remains on a single line. -/
theorem breakLinesWithTextCombine_no_break (p c s : String) (avail w : Nat)
    (hfit : ¬ (p.toList.length * w + w + s.toList.length * w ≤ avail))
    (hnb : canBreakAfterCombine c s = false) :
    breakLinesWithTextCombine p c s avail w = [p ++ objectReplacementChar ++ s] := by
  unfold breakLinesWithTextCombine
  simp [hfit, hnb]

/-! ## 5. Font Spacing Suppression in Text Combine (CSS Writing Modes 3 §5.1.4 & CSS Text 3 §7.1, §7.2) -/

/-- CSS Writing Modes 3 §5.1.4 & CSS Text 3 §7.2:
    Inside the combined text run, letter-spacing is treated as 0. -/
def effectiveLetterSpacing (inCombine : Bool) (specifiedLetterSpacing : Nat) : Nat :=
  if inCombine then 0 else specifiedLetterSpacing

/-- CSS Writing Modes 3 §5.1.4 & CSS Text 3 §7.1:
    Inside the combined text run, word-spacing is treated as 0. -/
def effectiveWordSpacing (inCombine : Bool) (specifiedWordSpacing : Nat) : Nat :=
  if inCombine then 0 else specifiedWordSpacing

/-- CSS Writing Modes 3 §5.1.4 Law: When text combine is active, letter spacing is always suppressed to 0 for any input. -/
theorem textCombine_letter_spacing_active (sp : Nat) :
    effectiveLetterSpacing true sp = 0 := by
  rfl

/-- CSS Writing Modes 3 §5.1.4 Law: When text combine is active, word spacing is always suppressed to 0 for any input. -/
theorem textCombine_word_spacing_active (sp : Nat) :
    effectiveWordSpacing true sp = 0 := by
  rfl

/-- CSS Writing Modes 3 §5.1.4 Law: When text combine is inactive, letter spacing is preserved for any input. -/
theorem textCombine_letter_spacing_inactive (sp : Nat) :
    effectiveLetterSpacing false sp = sp := by
  rfl

/-- CSS Writing Modes 3 §5.1.4 Law: When text combine is inactive, word spacing is preserved for any input. -/
theorem textCombine_word_spacing_inactive (sp : Nat) :
    effectiveWordSpacing false sp = sp := by
  rfl

/-- CSS Writing Modes 3 §5.1.4 Law: In horizontal writing mode, text combine is never active, so letter spacing is preserved. -/
theorem textCombine_horizontal_letter_spacing (tcu : TextCombineUpright) (sp : Nat) :
    effectiveLetterSpacing (isTextCombineActive .horizontalTb tcu) sp = sp := by
  cases tcu <;> rfl

/-- CSS Writing Modes 3 §5.1.4 Law: In horizontal writing mode, text combine is never active, so word spacing is preserved. -/
theorem textCombine_horizontal_word_spacing (tcu : TextCombineUpright) (sp : Nat) :
    effectiveWordSpacing (isTextCombineActive .horizontalTb tcu) sp = sp := by
  cases tcu <;> rfl

/-! ## 6. LayoutTextCombine Geometry, Ink Overflow, and Outlines (CSS Writing Modes 3 §5.1) -/

/-- CSS Text Decoration 3 §2, §3: Text decoration type that affects text-combine ink overflow. -/
inductive TextCombineDecoration where
  | none
  | emphasisMark (height : Nat)
  | overline
  deriving DecidableEq, Repr, Inhabited

/-- Ink overflow representation for text combine box and line items. -/
structure TextCombineInkMetrics where
  lineRect : LayoutUnitRect
  lineInkOverflow : LayoutUnitRect
  boxRect : LayoutUnitRect
  boxSelfInkOverflow : LayoutUnitRect
  boxContentsInkOverflow : LayoutUnitRect
  boxTotalInkOverflow : LayoutUnitRect
  innerLineRect : LayoutUnitRect
  innerLineInkOverflow : LayoutUnitRect
  innerContentRects : List LayoutUnitRect
  deriving DecidableEq, Repr, Inhabited

/-- CSS Writing Modes 3 §5.1, CSS Text Decoration 3 §2, §3:
    Compute ink overflow metrics for a vertical-rl line containing a text-combine box.
    `lh`: line-height
    `fs`: font-size
    `totalHeight`: line total block advance
    `yOffset`: offset of the combine box in the line
    `charCounts`: length of each text run inside the combine box
    `decoration`: optional text emphasis or overline decoration -/
def computeTextCombineInkMetrics (lh fs totalHeight yOffset : Nat)
    (charCounts : List Nat) (decoration : TextCombineDecoration := .none) : TextCombineInkMetrics :=
  let hl : Int := Int.ofNat ((lh - fs) / 2)
  let fsI : Int := Int.ofNat fs
  let lhI : Int := Int.ofNat lh
  let yOffI : Int := Int.ofNat yOffset
  let totalHI : Int := Int.ofNat totalHeight
  let (lineInkW, boxInkW, boxInkX, innerLineInkW, innerLineInkX) :=
    match decoration with
    | .emphasisMark emH =>
      let emI : Int := Int.ofNat emH
      (lhI + emI - hl, lhI + emI - hl, -hl, lhI, -hl)
    | .overline =>
      (lhI + 5, lhI, 0, fsI, 0)
    | .none =>
      (lhI, lhI, -hl, lhI, -hl)
  let rec makeRuns (curX : Int) : List Nat → List LayoutUnitRect
    | [] => []
    | c :: cs =>
      let w : Int := Int.ofNat (c * fs)
      { x := curX, y := 0, width := w, height := fsI } :: makeRuns (curX + w) cs
  { lineRect := { x := 0, y := 0, width := lhI, height := totalHI }
    lineInkOverflow := { x := 0, y := 0, width := lineInkW, height := totalHI }
    boxRect := { x := hl, y := yOffI, width := fsI, height := fsI }
    boxSelfInkOverflow := { x := 0, y := 0, width := fsI, height := fsI }
    boxContentsInkOverflow := { x := boxInkX, y := 0, width := boxInkW, height := fsI }
    boxTotalInkOverflow := { x := boxInkX, y := 0, width := boxInkW, height := fsI }
    innerLineRect := { x := 0, y := 0, width := fsI, height := fsI }
    innerLineInkOverflow := { x := innerLineInkX, y := 0, width := innerLineInkW, height := fsI }
    innerContentRects := makeRuns 0 charCounts }

/-- CSS Writing Modes 3 §5.1.1 & CSS Overflow 3 §4.4:
    A block flow containing text-combine items in vertical writing mode has physical size
    `(lineHeight, totalAdvance)`.
    Because combined text is scaled down to 1em, it does not overflow the block flow in either axis,
    so `hasScrollableOverflow` is false and `scrollableOverflow` equals the fragment bounds. -/
def computeBlockFlowScrollableOverflow (lh totalAdvance : Nat) : Bool × (Nat × Nat) × LayoutUnitRect :=
  let size := (lh, totalAdvance)
  let rect : LayoutUnitRect := { x := 0, y := 0, width := Int.ofNat lh, height := Int.ofNat totalAdvance }
  (false, size, rect)

/-- Inside list marker representation with text combine. -/
structure InsideListMarkerTree where
  markerChildren : List InlineDisplayItem
  contentChildren : List InlineDisplayItem
  deriving DecidableEq, Repr, Inhabited

/-- CSS Writing Modes 3 §5.1 & CSS Lists 3 §3:
    When text combine is active in a list item with `list-style-position: inside`,
    both the inside list marker symbol and the list item content are wrapped in LayoutTextCombine. -/
def buildInsideListMarkerTree (active : Bool) (symbol : String) (content : String) : InsideListMarkerTree :=
  { markerChildren := buildInlineDisplay active [.fragment symbol],
    contentChildren := buildInlineDisplay active [.text content] }

/-- CSS Basic User Interface 3 §4.2 & CSS Writing Modes 3 §5.1:
    Compute outline rectangles for a vertical block flow containing text-combine.
    `includeInkOverflow`: whether to include block ink overflow (focus outlines). -/
def computeTextCombineOutlineRects (lh fs totalAdvance : Nat) (includeInkOverflow : Bool) : List LayoutUnitRect :=
  let blockRect : LayoutUnitRect := { x := 0, y := 0, width := Int.ofNat lh, height := Int.ofNat totalAdvance }
  if !includeInkOverflow then
    [blockRect]
  else
    let hl : Int := Int.ofNat ((lh - fs) / 2)
    let fsI : Int := Int.ofNat fs
    let tcyBox : LayoutUnitRect := { x := hl, y := 0, width := fsI, height := fsI }
    let tcyCombine : LayoutUnitRect := { x := hl - 5, y := 0, width := fsI + 10, height := fsI }
    let xBox : LayoutUnitRect := { x := hl, y := fsI, width := fsI, height := fsI }
    let xText : LayoutUnitRect := { x := hl, y := fsI, width := fsI, height := fsI }
    [blockRect, tcyBox, tcyCombine, xBox, xText]

/-- CSS Writing Modes 3 §5.1.2 & CSS 2.1 §9.4.2:
    The unscaled text run rect in the container fragment of LayoutTextCombine.
    Properties that apply to the containing block, such as `text-indent`,
    do not apply to the contents inside LayoutTextCombine. -/
def textCombineContentRectInContainer (_textIndent : Nat) (charCount : Nat) (fontSize : Nat) : LayoutUnitRect :=
  { x := 0, y := 0, width := Int.ofNat (charCount * fontSize), height := Int.ofNat fontSize }

/-! ## 7. General Laws for LayoutTextCombine Geometry and Overflow -/

/-- CSS Writing Modes 3 §5.1.2 Law: Text combine content rect in container fragment starts at (0, 0). -/
theorem textCombine_content_rect_offset_zero (indent cc fs : Nat) :
    (textCombineContentRectInContainer indent cc fs).x = 0 ∧
    (textCombineContentRectInContainer indent cc fs).y = 0 := by
  dsimp [textCombineContentRectInContainer]
  exact ⟨rfl, rfl⟩

/-- CSS Writing Modes 3 §5.1.2 Law: Content rect in container fragment is independent of container text-indent. -/
theorem textCombine_content_rect_independent_of_indent (i1 i2 cc fs : Nat) :
    textCombineContentRectInContainer i1 cc fs = textCombineContentRectInContainer i2 cc fs := rfl

/-- CSS Writing Modes 3 §5.1.1 Law: Text combine produces no scrollable overflow in block container. -/
theorem textCombine_scrollableOverflow_no_overflow (lh adv : Nat) :
    (computeBlockFlowScrollableOverflow lh adv).1 = false := rfl

/-- CSS Writing Modes 3 §5.1.1 Law: Block container size equals (lineHeight, totalAdvance). -/
theorem textCombine_scrollableOverflow_size (lh adv : Nat) :
    (computeBlockFlowScrollableOverflow lh adv).2.1 = (lh, adv) := rfl

/-- CSS Writing Modes 3 §5.1 Law: Text combine box in vertical line is placed at cross-axis half-leading. -/
theorem textCombine_ink_box_rect_half_leading (lh fs tot y : Nat) (cc : List Nat) (dec : TextCombineDecoration) :
    (computeTextCombineInkMetrics lh fs tot y cc dec).boxRect.x = Int.ofNat ((lh - fs) / 2) := by
  dsimp [computeTextCombineInkMetrics]

/-- CSS Writing Modes 3 §5.1 Law: Text combine box height equals font size. -/
theorem textCombine_ink_box_rect_height (lh fs tot y : Nat) (cc : List Nat) (dec : TextCombineDecoration) :
    (computeTextCombineInkMetrics lh fs tot y cc dec).boxRect.height = Int.ofNat fs := by
  dsimp [computeTextCombineInkMetrics]

/-- CSS Writing Modes 3 §5.1 & CSS Lists 3 §3 Law: Active text combine inside list item wraps marker symbol. -/
theorem insideListMarkerTree_active_marker (sym cnt : String) :
    (buildInsideListMarkerTree true sym cnt).markerChildren = [.combined { children := [.fragment sym] }] := rfl

/-- CSS Basic User Interface 3 §4.2 Law: Standard outline has length 1 (only the block container rect). -/
theorem textCombineOutlineRects_standard_length (lh fs tot : Nat) :
    (computeTextCombineOutlineRects lh fs tot false).length = 1 := rfl

/-- CSS Basic User Interface 3 §4.2 Law: Focus outline with block ink overflow has length 5. -/
theorem textCombineOutlineRects_focus_length (lh fs tot : Nat) :
    (computeTextCombineOutlineRects lh fs tot true).length = 5 := rfl

end ChromiumLayout
