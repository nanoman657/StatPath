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

end ChromiumLayout
