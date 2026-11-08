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

/-- CSS Inline 3 §2 & Blink ComputeInlineCaretPosition:
    Caret resolution at soft wrap boundary between two consecutive atomic inline boxes (e.g. images).
    - Upstream affinity binds to the end of the first box (afterBox).
    - Downstream affinity binds to the start of the second box (beforeBox). -/
def resolveSoftWrapBoxCaret (box1 box2 : Nat) (affinity : TextAffinity) : InlineCaretPosition :=
  match affinity with
  | .upstream => { fragmentId := box1, positionType := .afterBox, textOffset := none }
  | .downstream => { fragmentId := box2, positionType := .beforeBox, textOffset := none }

/-- Caret resolution at atomic box boundary (e.g. image)
    (`inline/inline_caret_position.cc:200-240`). -/
def resolveBoxCaret (fragId : Nat) (isAfter : Bool) : InlineCaretPosition :=
  if isAfter then
    { fragmentId := fragId, positionType := .afterBox, textOffset := none }
  else
    { fragmentId := fragId, positionType := .beforeBox, textOffset := none }

/-- Caret resolution at text offset within a single fragment
    (`inline/inline_caret_position.cc:280-340`). -/
def resolveTextCaret (fragId : Nat) (offset : Nat) : InlineCaretPosition :=
  { fragmentId := fragId, positionType := .atTextOffset, textOffset := some offset }

/-- Caret resolution after an element node:
    - If box is non-culled (generates box fragment), returns afterBox on that box fragment.
    - If box is culled, returns atTextOffset at the text node length. -/
def resolveAfterNodeCaret (isCulled : Bool) (boxFragId textFragId : Nat) (textLen : Nat) : InlineCaretPosition :=
  if isCulled then
    { fragmentId := textFragId, positionType := .atTextOffset, textOffset := some textLen }
  else
    { fragmentId := boxFragId, positionType := .afterBox, textOffset := none }

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

/-- General Law: Text caret position type is always atTextOffset for all fragment IDs and offsets. -/
theorem resolveTextCaret_type (fragId offset : Nat) :
    (resolveTextCaret fragId offset).positionType = .atTextOffset := by
  rfl

/-- General Law: Text caret offset is always the specified offset for all inputs. -/
theorem resolveTextCaret_offset (fragId offset : Nat) :
    (resolveTextCaret fragId offset).textOffset = some offset := by
  rfl

/-- General Law: Text caret fragment ID is always the specified fragment ID for all inputs. -/
theorem resolveTextCaret_frag (fragId offset : Nat) :
    (resolveTextCaret fragId offset).fragmentId = fragId := by
  rfl

/-- General Law: Culled span after-node caret resolves to atTextOffset on text fragment. -/
theorem resolveAfterNodeCaret_culled (bf tf len : Nat) :
    resolveAfterNodeCaret true bf tf len = { fragmentId := tf, positionType := .atTextOffset, textOffset := some len } := by
  rfl

/-- General Law: Non-culled span after-node caret resolves to afterBox on box fragment. -/
theorem resolveAfterNodeCaret_non_culled (bf tf len : Nat) :
    resolveAfterNodeCaret false bf tf len = { fragmentId := bf, positionType := .afterBox, textOffset := none } := by
  rfl

/-- General Law: Box caret before resolves to beforeBox for all fragment IDs. -/
theorem resolveBoxCaret_before (fragId : Nat) :
    resolveBoxCaret fragId false = { fragmentId := fragId, positionType := .beforeBox, textOffset := none } := by
  rfl

/-- General Law: Box caret after resolves to afterBox for all fragment IDs. -/
theorem resolveBoxCaret_after (fragId : Nat) :
    resolveBoxCaret fragId true = { fragmentId := fragId, positionType := .afterBox, textOffset := none } := by
  rfl

/-- CSS Inline 3 §2 Law: Upstream caret at box wrap boundary targets the first box with afterBox. -/
theorem soft_wrap_box_upstream (b1 b2 : Nat) :
    resolveSoftWrapBoxCaret b1 b2 .upstream = { fragmentId := b1, positionType := .afterBox, textOffset := none } := by
  rfl

/-- CSS Inline 3 §2 Law: Downstream caret at box wrap boundary targets the second box with beforeBox. -/
theorem soft_wrap_box_downstream (b1 b2 : Nat) :
    resolveSoftWrapBoxCaret b1 b2 .downstream = { fragmentId := b2, positionType := .beforeBox, textOffset := none } := by
  rfl

/-- CSS Inline 3 §2 Law: Upstream and downstream box carets at distinct boxes target distinct fragments. -/
theorem soft_wrap_box_distinct (b1 b2 : Nat) (h : b1 ≠ b2) :
    (resolveSoftWrapBoxCaret b1 b2 .upstream).fragmentId ≠
    (resolveSoftWrapBoxCaret b1 b2 .downstream).fragmentId := by
  dsimp [resolveSoftWrapBoxCaret]
  exact h

end ChromiumLayout
