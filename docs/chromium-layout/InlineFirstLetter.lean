/-
  docs/chromium-layout/InlineFirstLetter.lean

  Formal model for CSS Pseudo-Elements Level 4 §2.2 (::first-letter)
  and Blink LayoutTextFragment (`third_party/blink/renderer/core/layout/layout_text_fragment.h`).
-/
import LayoutTypes
import LayoutInline
import InlineItemBuilder
import InlineOffsetMapping

namespace ChromiumLayout

/-! ## 1. CSS Pseudo-Elements 4 §2.2 First-Letter Text Identification -/

/-- CSS Pseudo-Elements 4 §2.2.1: Associated punctuation for first-letter (Unicode category P*). -/
def isFirstLetterPunctuation (c : Char) : Bool :=
  c == '(' || c == ')' || c == '[' || c == ']' || c == '{' || c == '}' ||
  c == '"' || c == '\'' || c == '!' || c == '?' || c == '.' || c == ',' || c == ':' || c == ';'

/-- CSS Pseudo-Elements 4 §2.2: The first letter target is a letter or digit (Unicode L*, N*). -/
def isFirstLetterTarget (c : Char) : Bool :=
  c.isAlpha || c.isDigit

/-- CSS Pseudo-Elements 4 §2.2.1: Find the DOM character length of the first-letter fragment.
    Includes leading whitespace, preceding punctuation, the base letter/digit, and following punctuation. -/
def firstLetterLength (chars : List Char) : Nat :=
  let leadingWs := (chars.takeWhile (fun c => c == ' ' || c == '\t' || c == '\n')).length
  let afterWs := chars.drop leadingWs
  let prePunct := (afterWs.takeWhile isFirstLetterPunctuation).length
  let afterPre := afterWs.drop prePunct
  match afterPre with
  | [] => 0
  | c :: rest =>
    if isFirstLetterTarget c then
      let postPunct := (rest.takeWhile isFirstLetterPunctuation).length
      leadingWs + prePunct + 1 + postPunct
    else 0

/-! ## 2. Blink LayoutTextFragment Structure -/

/-- CSS Pseudo-Elements 4 §2.2: LayoutTextFragment representing either the ::first-letter
    pseudo-element or the remaining text of a split DOM text node. -/
structure LayoutTextFragment where
  start : Nat := 0
  fragmentLength : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- CSS Pseudo-Elements 4 §2.2: Split a DOM text node into first-letter and remaining-text fragments. -/
def splitFirstLetter (s : String) : LayoutTextFragment × LayoutTextFragment :=
  let len := firstLetterLength s.toList
  ({ start := 0, fragmentLength := len }, { start := len, fragmentLength := s.length - len })

/-! ## 3. Caret & Offset Query Operations on LayoutTextFragment -/

/-- CSS Text 3 §4.1: Check whether a fragment offset precedes a non-collapsed DOM character. -/
def fragmentIsBeforeNonCollapsed (units : List OffsetMappingUnit) (frag : LayoutTextFragment) (offset : Nat) : Bool :=
  if offset ≥ frag.fragmentLength then false
  else
    let absPos := frag.start + offset
    units.any (fun u => u.unitType == .identity && absPos ≥ u.domStart && absPos < u.domEnd)

/-- CSS Text 3 §4.1: Check whether a fragment offset succeeds a non-collapsed DOM character. -/
def fragmentIsAfterNonCollapsed (units : List OffsetMappingUnit) (frag : LayoutTextFragment) (offset : Nat) : Bool :=
  if offset == 0 || offset > frag.fragmentLength then false
  else
    let absPos := frag.start + offset - 1
    units.any (fun u => u.unitType == .identity && absPos ≥ u.domStart && absPos < u.domEnd)

/-- CSS Text 3 §4.1: Check whether a fragment offset contains a valid caret position. -/
def fragmentContainsCaretOffset (units : List OffsetMappingUnit) (domChars : List Char)
    (frag : LayoutTextFragment) (offset : Nat) : Bool :=
  if offset > frag.fragmentLength then false
  else if offset < frag.fragmentLength && fragmentIsBeforeNonCollapsed units frag offset then true
  else if offset == 0 || !fragmentIsAfterNonCollapsed units frag offset then false
  else
    let prevAbs := frag.start + offset - 1
    if h : prevAbs < domChars.length then
      domChars[prevAbs] != '\n'
    else false

/-- CSS Text 3 §4.1: Minimum non-collapsed DOM caret offset relative to fragment start. -/
def fragmentCaretMinOffset (units : List OffsetMappingUnit) (frag : LayoutTextFragment) : Nat :=
  let nonCollapsed := (List.range frag.fragmentLength).filter (fun k => fragmentIsBeforeNonCollapsed units frag k)
  match nonCollapsed with
  | [] => 0
  | k :: _ => k

/-- CSS Text 3 §4.1: Maximum non-collapsed DOM caret offset relative to fragment start. -/
def fragmentCaretMaxOffset (units : List OffsetMappingUnit) (frag : LayoutTextFragment) : Nat :=
  let nonCollapsed := (List.range frag.fragmentLength).filter (fun k => fragmentIsBeforeNonCollapsed units frag k)
  match nonCollapsed.reverse with
  | [] => frag.fragmentLength
  | last :: _ => last + 1

/-- CSS Text 3 §4.1: Count of resolved (non-collapsed) characters belonging to the fragment. -/
def fragmentResolvedTextLength (units : List OffsetMappingUnit) (frag : LayoutTextFragment) : Nat :=
  ((List.range frag.fragmentLength).filter (fun k => fragmentIsBeforeNonCollapsed units frag k)).length

/-! ## 4. General Laws -/

/-- General Law: When offset exceeds fragment length, ContainsCaretOffset is false for all inputs. -/
theorem fragmentContainsCaretOffset_out_of_bounds (units : List OffsetMappingUnit) (domChars : List Char)
    (frag : LayoutTextFragment) (offset : Nat) (h : offset > frag.fragmentLength) :
    fragmentContainsCaretOffset units domChars frag offset = false := by
  dsimp [fragmentContainsCaretOffset]
  split
  · rfl
  · rename_i h_not
    exfalso
    exact h_not h

/-- General Law: When offset is greater than or equal to fragment length, IsBeforeNonCollapsed is false for all inputs. -/
theorem fragmentIsBeforeNonCollapsed_out_of_bounds (units : List OffsetMappingUnit)
    (frag : LayoutTextFragment) (offset : Nat) (h : offset ≥ frag.fragmentLength) :
    fragmentIsBeforeNonCollapsed units frag offset = false := by
  dsimp [fragmentIsBeforeNonCollapsed]
  split
  · rfl
  · rename_i h_not
    exfalso
    exact h_not h

/-- General Law: IsAfterNonCollapsed is always false at offset 0 for all inputs. -/
theorem fragmentIsAfterNonCollapsed_zero (units : List OffsetMappingUnit)
    (frag : LayoutTextFragment) :
    fragmentIsAfterNonCollapsed units frag 0 = false := by
  rfl

/-- General Law: First-letter length of an empty character sequence is zero. -/
theorem firstLetterLength_empty :
    firstLetterLength [] = 0 := by
  rfl

/-- General Law: Splitting an empty string yields two empty fragments. -/
theorem splitFirstLetter_empty :
    splitFirstLetter "" = ({ start := 0, fragmentLength := 0 }, { start := 0, fragmentLength := 0 }) := by
  rfl

end ChromiumLayout
