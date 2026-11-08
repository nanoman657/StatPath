/-
  docs/chromium-layout/InlineAutoSpace.lean

  Formal model for CSS Text Module Level 4 §8.2 (Spacing Between Ideographs and Non-Ideographs:
  the text-autospace property), Unicode Technical Report #59 (East Asian Spacing),
  and Blink TextAutoSpace (`third_party/blink/renderer/core/layout/inline/text_auto_space.h`,
  `text_auto_space.cc`).
-/
import LayoutTypes
import InlineGeometry

namespace ChromiumLayout

/-! ## 1. Character Classification (CSS Text 4 §8.2, UTR#59) -/

/-- CSS Text 4 §8.2: Check whether a character is an East Asian ideograph (Han, Hiragana, Katakana). -/
def isEastAsianIdeograph (c : Char) : Bool :=
  let n := c.toNat
  (n ≥ 0x3040 && n ≤ 0x309F) || -- Hiragana
  (n ≥ 0x30A0 && n ≤ 0x30FF) || -- Katakana
  (n ≥ 0x4E00 && n ≤ 0x9FFF) || -- CJK Unified Ideographs
  (n ≥ 0x3400 && n ≤ 0x4DBF) || -- CJK Extension A
  (n ≥ 0x20000 && n ≤ 0x2A6DF) || -- CJK Extension B
  (n ≥ 0x739A0 && n ≤ 0x739AF) || -- CJK Extension
  (n ≥ 0xF900 && n ≤ 0xFAFF)    -- CJK Compatibility

/-- CSS Text 4 §8.2: Check whether a character is a non-ideographic text unit (Latin, digits, Hebrew). -/
def isNonIdeographText (c : Char) : Bool :=
  let n := c.toNat
  (n ≥ 0x0041 && n ≤ 0x005A) || -- Latin A-Z
  (n ≥ 0x0061 && n ≤ 0x007A) || -- Latin a-z
  (n ≥ 0x0030 && n ≤ 0x0039) || -- ASCII digits 0-9
  (n ≥ 0x0590 && n ≤ 0x05FF)    -- Hebrew

/-- Check whether a character is whitespace or punctuation boundary. -/
def isSpaceOrBoundary (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n'

/-- Character class for auto-spacing decisions. -/
inductive AutoSpaceCharClass where
  | ideograph
  | nonIdeograph
  | space
  | other
  deriving DecidableEq, Repr, Inhabited

/-- Classify a character for text-autospace boundary resolution. -/
def classifyAutoSpaceChar (c : Char) : AutoSpaceCharClass :=
  if isSpaceOrBoundary c then .space
  else if isEastAsianIdeograph c then .ideograph
  else if isNonIdeographText c then .nonIdeograph
  else .other

/-! ## 2. TextAutoSpace Optimization and Boundary Computation -/

/-- CSS Text 4 §8.2 / Blink TextAutoSpace::MayApply:
    Early rejection check: auto-spacing may only apply if text contains ideographs. -/
def mayApplyTextAutoSpace (chars : List Char) : Bool :=
  chars.any isEastAsianIdeograph

/-- Helper to zip a list with consecutive 0-based indices. -/
def zipWithIndex (l : List α) : List (Nat × α) :=
  let rec loop (idx : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (idx, x) :: loop (idx + 1) xs
  loop 0 l

/-- Find auto-space boundaries between adjacent ideograph and non-ideograph characters. -/
def findAutoSpaceBoundaries : List (Nat × Char) → List Nat
  | [] | [_] => []
  | (_, c1) :: (idx2, c2) :: rest =>
    let cls1 := classifyAutoSpaceChar c1
    let cls2 := classifyAutoSpaceChar c2
    let hasBoundary :=
      (cls1 == .ideograph && cls2 == .nonIdeograph) ||
      (cls1 == .nonIdeograph && cls2 == .ideograph)
    let tail := findAutoSpaceBoundaries ((idx2, c2) :: rest)
    if hasBoundary then idx2 :: tail else tail

/-- CSS Text 4 §8.2 / Blink TextAutoSpace::Apply:
    Compute character offsets where 1/8 em inter-script spacing must be inserted. -/
def computeAutoSpaceOffsets (chars : List Char) : List Nat :=
  findAutoSpaceBoundaries (zipWithIndex chars)

/-- Compute cumulative character start positions in 1/8 pixel quanta.
    Nominal glyph advance defaults to 80 (10px) and auto-space width to 10 (1.25px). -/
def computeCharacterPositionsEighths (chars : List Char) (nominalAdvance : Nat := 80) (autoSpaceWidth : Nat := 10) : List Nat :=
  let boundaries := computeAutoSpaceOffsets chars
  let rec walk (idx : Nat) (curPos : Nat) : List Char → List Nat
    | [] => []
    | _ :: rest =>
      let nextPos :=
        if boundaries.contains (idx + 1) then curPos + nominalAdvance + autoSpaceWidth
        else curPos + nominalAdvance
      curPos :: walk (idx + 1) nextPos rest
  walk 0 0 chars

/-! ## 3. General Laws -/

/-- CSS Text 4 §8.2: Empty text stream never applies auto-spacing. -/
theorem mayApply_empty :
    mayApplyTextAutoSpace [] = false := rfl

/-- CSS Text 4 §8.2: A single ideograph character always enables mayApply. -/
theorem mayApply_single_ideograph (c : Char) (h : isEastAsianIdeograph c = true) :
    mayApplyTextAutoSpace [c] = true := by
  dsimp [mayApplyTextAutoSpace]
  rw [h]
  rfl

/-- CSS Text 4 §8.2: Empty text stream produces zero boundary offsets. -/
theorem autoSpaceOffsets_empty :
    computeAutoSpaceOffsets [] = [] := rfl

/-- CSS Text 4 §8.2: Single character has no boundaries. -/
theorem autoSpaceOffsets_single (c : Char) :
    computeAutoSpaceOffsets [c] = [] := rfl

/-- CSS Text 4 §8.2: Boundary between ideograph and non-ideograph occurs at index 1. -/
theorem autoSpaceOffsets_boundary_ideograph_latin (c1 c2 : Char)
    (h1 : classifyAutoSpaceChar c1 = .ideograph) (h2 : classifyAutoSpaceChar c2 = .nonIdeograph) :
    computeAutoSpaceOffsets [c1, c2] = [1] := by
  dsimp [computeAutoSpaceOffsets, zipWithIndex, zipWithIndex.loop, findAutoSpaceBoundaries]
  rw [h1, h2]
  rfl

/-- CSS Text 4 §8.2: Boundary between non-ideograph and ideograph occurs at index 1. -/
theorem autoSpaceOffsets_boundary_latin_ideograph (c1 c2 : Char)
    (h1 : classifyAutoSpaceChar c1 = .nonIdeograph) (h2 : classifyAutoSpaceChar c2 = .ideograph) :
    computeAutoSpaceOffsets [c1, c2] = [1] := by
  dsimp [computeAutoSpaceOffsets, zipWithIndex, zipWithIndex.loop, findAutoSpaceBoundaries]
  rw [h1, h2]
  rfl

/-- CSS Text 4 §8.2: Characters separated by whitespace never trigger auto-spacing. -/
theorem autoSpaceOffsets_space_separated_never_autospaces (c1 c2 : Char) :
    computeAutoSpaceOffsets [c1, ' ', c2] = [] := by
  dsimp [computeAutoSpaceOffsets, zipWithIndex, zipWithIndex.loop, findAutoSpaceBoundaries]
  have hSpace : classifyAutoSpaceChar ' ' = .space := rfl
  rw [hSpace]
  cases (classifyAutoSpaceChar c1) <;> cases (classifyAutoSpaceChar c2) <;> rfl

/-- Character positions for empty input are empty. -/
theorem character_positions_empty (nom sp : Nat) :
    computeCharacterPositionsEighths [] nom sp = [] := rfl

/-- Character positions for single input always start at 0. -/
theorem character_positions_single (c : Char) (nom sp : Nat) :
    computeCharacterPositionsEighths [c] nom sp = [0] := rfl

end ChromiumLayout
