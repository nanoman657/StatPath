/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineGeometry

/-!
# CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1: Hyphenation and Text Orientation

Formalizes:
- CSS Text 3 §5.3: Hyphenation: The 'hyphenate-character' Property
- CSS Writing Modes 3 §5.1: Orienting Text: The 'text-orientation' Property
- CSS Writing Modes 3 §3.1: Block Flow Direction: The 'writing-mode' Property
- `third_party/blink/renderer/core/layout/inline/hyphen_result.h`
- `third_party/blink/renderer/core/layout/inline/hyphen_result.cc`

Owns:
- `CanvasRotationInVertical`
- `TextOrientation`
- `WritingMode.isVertical`
- `computeHyphenCharRotation`
- `HyphenResult`
- `shapeHyphenResult`
-/

namespace ChromiumLayout

/-! ## 1. Core Model Definitions -/

/-- CSS Writing Modes 3 §3.1: Whether a writing mode is vertical. -/
def WritingMode.isVertical : WritingMode → Bool
  | .horizontalTb => false
  | .verticalRl | .verticalLr | .sidewaysRl | .sidewaysLr => true

/-- CSS Writing Modes 3 §5.1: The 'text-orientation' property. -/
inductive TextOrientation where
  | mixed
  | upright
  | sideways
  deriving DecidableEq, Repr, Inhabited

/-- Blink `CanvasRotationInVertical`: rotation applied to canvas when drawing glyphs in vertical text. -/
inductive CanvasRotationInVertical where
  | regular
  | rotateCanvasUpright
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1: Compute canvas glyph rotation for a hyphen character.
    In horizontal writing modes, glyphs are never rotated (`regular`).
    In vertical writing modes:
    - with `text-orientation: upright`, glyphs are drawn standing upright (`rotateCanvasUpright`);
    - with `text-orientation: sideways`, glyphs are drawn sideways (`regular`);
    - with `text-orientation: mixed`, punctuation and symbols like `+`, `=`, `-` are typeset sideways (`regular`)
      when the vertical orientation fix feature is enabled, or upright (`rotateCanvasUpright`) under legacy Blink behavior. -/
def computeHyphenCharRotation (wm : WritingMode) (orientation : TextOrientation) (fixEnabled : Bool) : CanvasRotationInVertical :=
  if ¬ wm.isVertical then
    .regular
  else
    match orientation with
    | .upright => .rotateCanvasUpright
    | .sideways => .regular
    | .mixed =>
      if fixEnabled then .regular else .rotateCanvasUpright

/-- CSS Text 3 §5.3: Hyphenation result containing shaped hyphen text and glyph orientation. -/
structure HyphenResult where
  text : String
  writingMode : WritingMode := .horizontalTb
  orientation : TextOrientation := .mixed
  rotations : List CanvasRotationInVertical := []
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1: Shape hyphen text for a given style context.
    Computes per-glyph canvas rotation according to writing mode, text orientation,
    and the hyphen vertical orientation feature fix. -/
def shapeHyphenResult (hyphenText : String) (wm : WritingMode) (orientation : TextOrientation) (fixEnabled : Bool) : HyphenResult :=
  let rot := computeHyphenCharRotation wm orientation fixEnabled
  { text := hyphenText
  , writingMode := wm
  , orientation := orientation
  , rotations := hyphenText.toList.map (fun _ => rot) }

/-! ## 2. General Laws (CSS Text 3 §5.3 & CSS Writing Modes 3 §5.1) -/

/-- CSS Writing Modes 3 §5.1 Law: In horizontal writing mode, hyphen glyphs are always rendered without canvas rotation (regular). -/
theorem hyphen_horizontal_always_regular (text : String) (orientation : TextOrientation) (fixEnabled : Bool) :
    ∀ r ∈ (shapeHyphenResult text .horizontalTb orientation fixEnabled).rotations, r = .regular := by
  intro r hr
  unfold shapeHyphenResult at hr
  simp [computeHyphenCharRotation, WritingMode.isVertical] at hr
  rcases hr with ⟨c, _, rfl⟩
  rfl

/-- CSS Writing Modes 3 §5.1 Law: In any vertical writing mode with text-orientation upright,
    hyphen glyphs are always rotated upright. -/
theorem hyphen_vertical_upright_always_upright (text : String) (wm : WritingMode) (hwm : wm.isVertical = true) (fixEnabled : Bool) :
    ∀ r ∈ (shapeHyphenResult text wm .upright fixEnabled).rotations, r = .rotateCanvasUpright := by
  intro r hr
  unfold shapeHyphenResult at hr
  have hrot : computeHyphenCharRotation wm .upright fixEnabled = .rotateCanvasUpright := by
    unfold computeHyphenCharRotation
    simp [hwm]
  simp [hrot] at hr
  rcases hr with ⟨c, _, rfl⟩
  rfl

/-- CSS Writing Modes 3 §5.1 Law: In any vertical writing mode with text-orientation mixed and the orientation fix enabled,
    hyphen glyphs are typeset sideways (regular canvas orientation). -/
theorem hyphen_vertical_mixed_with_fix_is_regular (text : String) (wm : WritingMode) (hwm : wm.isVertical = true) :
    ∀ r ∈ (shapeHyphenResult text wm .mixed true).rotations, r = .regular := by
  intro r hr
  unfold shapeHyphenResult at hr
  have hrot : computeHyphenCharRotation wm .mixed true = .regular := by
    unfold computeHyphenCharRotation
    simp [hwm]
  simp [hrot] at hr
  rcases hr with ⟨c, _, rfl⟩
  rfl

/-- CSS Text 3 §5.3 Law: The number of glyph rotations is always equal to the character count of the hyphen string. -/
theorem hyphen_rotations_length_eq_text_length (text : String) (wm : WritingMode) (orientation : TextOrientation) (fixEnabled : Bool) :
    (shapeHyphenResult text wm orientation fixEnabled).rotations.length = text.toList.length := by
  unfold shapeHyphenResult
  simp

/-- CSS Text 3 §5.3 Law: An empty hyphen string produces empty glyph rotations. -/
theorem hyphen_empty_text_rotations_empty (wm : WritingMode) (orientation : TextOrientation) (fixEnabled : Bool) :
    (shapeHyphenResult "" wm orientation fixEnabled).rotations = [] := by
  rfl

end ChromiumLayout
