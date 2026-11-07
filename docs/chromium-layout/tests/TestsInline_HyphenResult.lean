/-
  docs/chromium-layout/tests/TestsInline_HyphenResult.lean

  Formalized test vectors and properties for:
  - `inline/hyphen_result_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineCaret

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from hyphen_result_test.cc -/

/-- Test 1: Horizontal (hyphen_result_test.cc:37)
    `writing-mode: horizontal-tb; hyphenate-character: '+='`
    Expect regular rotation. -/
def hyphenResult_horizontal_vector : List (Nat × Nat) :=
  let rot := hyphenGlyphRotation false false
  let val := match rot with | .regular => 0 | .rotateCanvasUpright => 1
  [ (val, 0) ]

theorem hyphenResult_horizontal_pass :
    ∀ p ∈ hyphenResult_horizontal_vector, p.1 = p.2 := by
  decide

/-- Test 2: VerticalUpright (hyphen_result_test.cc:53)
    `writing-mode: vertical-rl; text-orientation: upright; hyphenate-character: '+='`
    Expect rotate canvas upright. -/
def hyphenResult_verticalUpright_vector : List (Nat × Nat) :=
  let rot := hyphenGlyphRotation true true
  let val := match rot with | .regular => 0 | .rotateCanvasUpright => 1
  [ (val, 1) ]

theorem hyphenResult_verticalUpright_pass :
    ∀ p ∈ hyphenResult_verticalUpright_vector, p.1 = p.2 := by
  decide

/-- Test 3: VerticalMixed (hyphen_result_test.cc:70)
    `writing-mode: vertical-rl; text-orientation: mixed; hyphenate-character: '+='`
    With fix enabled, regular rotation. -/
def hyphenResult_verticalMixed_vector : List (Nat × Nat) :=
  let rot := hyphenGlyphRotation true false
  let val := match rot with | .regular => 0 | .rotateCanvasUpright => 1
  [ (val, 0) ]

theorem hyphenResult_verticalMixed_pass :
    ∀ p ∈ hyphenResult_verticalMixed_vector, p.1 = p.2 := by
  decide

end ChromiumLayout.TestsInline
