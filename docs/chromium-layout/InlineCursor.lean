/-
  docs/chromium-layout/InlineCursor.lean

  Formal model for Blink InlineCursor
  (`third_party/blink/renderer/core/layout/inline/inline_cursor.h`,
   `inline_cursor.cc`).

  Owns: CursorItem, cursor tree navigation (parent, child, line, leaf),
  and hit-testing monotonicity laws for LTR and RTL.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 1. Cursor Item Model -/

/-- An item visited by `InlineCursor` (`inline/inline_cursor.h:85-230`). -/
structure CursorItem where
  id : Nat := 0
  type : FragmentItemType := .text
  parentId : Option Nat := none
  lineIndex : Nat := 0
  bidiLevel : Nat := 0
  textOffset : Nat := 0
  textLength : Nat := 0
  isLeaf : Bool := true
  isLineBox : Bool := false
  deriving DecidableEq, Repr

/-- Clamped character count for hit testing. -/
def clampedHitCount (rel : Nat) (charWidth : Nat) (textLength : Nat) : Nat :=
  if charWidth == 0 then 0
  else Nat.min textLength (rel / charWidth)

theorem clampedHitCount_le_textLength (rel : Nat) (charWidth : Nat) (textLength : Nat) :
    clampedHitCount rel charWidth textLength ≤ textLength := by
  dsimp [clampedHitCount]
  split
  · omega
  · exact Nat.min_le_left _ _

theorem clampedHitCount_mono (charWidth : Nat) (textLength : Nat)
    (rel1 rel2 : Nat) (hLe : rel1 ≤ rel2) :
    clampedHitCount rel1 charWidth textLength ≤ clampedHitCount rel2 charWidth textLength := by
  dsimp [clampedHitCount]
  split
  · omega
  · have hDiv : rel1 / charWidth ≤ rel2 / charWidth := Nat.div_le_div_right hLe
    exact Nat.le_min.mpr ⟨Nat.min_le_left _ _, Nat.le_trans (Nat.min_le_right _ _) hDiv⟩

/-- Hit testing: map local coordinate to character offset within text run
    (`inline/inline_cursor.cc:1420-1550`, `PositionForPointInChild`).
    In LTR: charOffset = clampedHitCount(relX, charWidth, textLength).
    In RTL: charOffset = textLength - clampedHitCount(relX, charWidth, textLength). -/
def hitTestTextOffset (isRtl : Bool) (x : Int) (left : Int) (charWidth : Nat) (textLength : Nat) : Nat :=
  let relX := x - left
  if relX ≤ 0 then
    if isRtl then textLength else 0
  else
    let c := clampedHitCount relX.toNat charWidth textLength
    if isRtl then textLength - c else c

/-! ## 2. Hit Testing Monotonicity Laws -/

/-- In LTR mode, hit-testing character offset is monotonically non-decreasing with coordinate `x`. -/
theorem hitTest_ltr_monotonic (left : Int) (charWidth : Nat) (textLength : Nat) :
    ∀ (x1 x2 : Int), x1 ≤ x2 →
      hitTestTextOffset false x1 left charWidth textLength ≤
      hitTestTextOffset false x2 left charWidth textLength := by
  intro x1 x2 hLe
  dsimp [hitTestTextOffset]
  split
  · -- x1 - left <= 0
    split
    · omega
    · omega
  · -- x1 - left > 0
    split
    · -- x2 - left <= 0, impossible since x1 <= x2
      omega
    · -- x2 - left > 0
      have hRelLe : (x1 - left).toNat ≤ (x2 - left).toNat :=
        Int.toNat_le_toNat (by omega)
      exact clampedHitCount_mono charWidth textLength (x1 - left).toNat (x2 - left).toNat hRelLe

/-- In RTL mode, hit-testing character offset is monotonically non-increasing with coordinate `x`. -/
theorem hitTest_rtl_monotonic (left : Int) (charWidth : Nat) (textLength : Nat) :
    ∀ (x1 x2 : Int), x1 ≤ x2 →
      hitTestTextOffset true x2 left charWidth textLength ≤
      hitTestTextOffset true x1 left charWidth textLength := by
  intro x1 x2 hLe
  dsimp [hitTestTextOffset]
  split
  · -- x2 - left <= 0
    split
    · omega
    · omega
  · -- x2 - left > 0
    split
    · -- x1 - left <= 0
      have hBound := clampedHitCount_le_textLength (x2 - left).toNat charWidth textLength
      omega
    · -- x1 - left > 0
      have hRelLe : (x1 - left).toNat ≤ (x2 - left).toNat :=
        Int.toNat_le_toNat (by omega)
      have hCLe := clampedHitCount_mono charWidth textLength (x1 - left).toNat (x2 - left).toNat hRelLe
      omega

end ChromiumLayout
