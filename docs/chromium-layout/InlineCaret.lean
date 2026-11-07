/-
  docs/chromium-layout/InlineCaret.lean

  Formal model for Blink InlineCaretPosition and caret resolution
  (`third_party/blink/renderer/core/layout/inline/inline_caret_position.h`,
   `hyphen_result.h`).

  Owns: TextAffinity, InlineCaretPositionType, InlineCaretPosition,
  caret resolution rules, and HyphenResult glyph rotation.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 1. Hyphen Glyph Orientation -/

inductive GlyphRotation where
  | regular
  | rotateCanvasUpright
  deriving DecidableEq, Repr

/-- Hyphen glyph rotation for horizontal vs vertical writing modes
    (`inline/hyphen_result.cc:25-60`). -/
def hyphenGlyphRotation (isVertical : Bool) (isUpright : Bool) : GlyphRotation :=
  if !isVertical then .regular
  else if isUpright then .rotateCanvasUpright
  else .regular

/-! ## 2. Inline Caret Position -/

inductive TextAffinity where
  | upstream
  | downstream
  deriving DecidableEq, Repr

inductive InlineCaretPositionType where
  | beforeBox
  | afterBox
  | atTextOffset
  deriving DecidableEq, Repr

/-- `InlineCaretPosition` (`inline/inline_caret_position.h:35-120`). -/
structure InlineCaretPosition where
  fragmentId : Nat := 0
  positionType : InlineCaretPositionType := .atTextOffset
  textOffset : Option Nat := none
  deriving DecidableEq, Repr

/-- Caret resolution at soft wrap boundary between two consecutive fragments
    (`inline/inline_caret_position.cc:350-420`).
    `upstream` affinity binds to the end of `frag1`;
    `downstream` affinity binds to the start of `frag2`. -/
def resolveSoftWrapCaret (frag1 frag2 : Nat) (wrapOffset : Nat) (affinity : TextAffinity) :
    InlineCaretPosition :=
  match affinity with
  | .upstream => { fragmentId := frag1, positionType := .atTextOffset, textOffset := some wrapOffset }
  | .downstream => { fragmentId := frag2, positionType := .atTextOffset, textOffset := some wrapOffset }

/-- Caret resolution at atomic box boundary (e.g. image)
    (`inline/inline_caret_position.cc:200-240`). -/
def resolveBoxCaret (fragId : Nat) (isAfter : Bool) : InlineCaretPosition :=
  if isAfter then
    { fragmentId := fragId, positionType := .afterBox, textOffset := none }
  else
    { fragmentId := fragId, positionType := .beforeBox, textOffset := none }

/-! ## 3. General Laws for Inline Caret Position -/

/-- Theorem: Upstream and downstream caret positions at a wrap boundary between distinct
    fragments always target distinct fragments. -/
theorem caret_wrap_affinity_targets_distinct (frag1 frag2 : Nat) (offset : Nat)
    (hDistinct : frag1 ≠ frag2) :
    (resolveSoftWrapCaret frag1 frag2 offset .upstream).fragmentId ≠
    (resolveSoftWrapCaret frag1 frag2 offset .downstream).fragmentId := by
  dsimp [resolveSoftWrapCaret]
  exact hDistinct

/-- Theorem: Hyphen glyph rotation is always regular in horizontal mode regardless of upright flag. -/
theorem hyphen_horizontal_always_regular (isUpright : Bool) :
    hyphenGlyphRotation false isUpright = .regular := by
  dsimp [hyphenGlyphRotation]

end ChromiumLayout
