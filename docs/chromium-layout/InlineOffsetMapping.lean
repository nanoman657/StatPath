/-
  docs/chromium-layout/InlineOffsetMapping.lean

  Formal model for Blink OffsetMapping
  (`third_party/blink/renderer/core/layout/inline/offset_mapping.h`,
   `offset_mapping_builder.h`).

  Formalizes the mapping between DOM character offsets and rendered
  text content offsets under CSS whitespace collapsing.
-/
import LayoutTypes
import LayoutInline
import InlineItemBuilder

namespace ChromiumLayout

/-! ## 1. Offset Mapping Unit Types -/

inductive OffsetMappingUnitType where
  | identity
  | collapsed
  | expanded
  deriving DecidableEq, Repr, Inhabited

structure OffsetMappingUnit where
  unitType : OffsetMappingUnitType := .identity
  domStart : Nat := 0
  domEnd : Nat := 0
  textStart : Nat := 0
  textEnd : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Collapsed Character Index Computation -/

/-- Determine whether a character is CSS whitespace (space, tab, or newline). -/
def isCssWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n'

/-- Compute collapsed character indices for a list of characters with tracking. -/
def computeCollapsedAux (mode : WhiteSpaceMode) (inSpace : Bool) (idx : Nat) :
    List Char → List Nat
  | [] => []
  | c :: rest =>
    if isCssWhitespace c then
      if inSpace then
        idx :: computeCollapsedAux mode true (idx + 1) rest
      else
        computeCollapsedAux mode true (idx + 1) rest
    else
      computeCollapsedAux mode false (idx + 1) rest

/-- Find all leading whitespace indices up to the first non-whitespace character. -/
def leadingWhitespaceIndices (idx : Nat) : List Char → List Nat
  | [] => []
  | c :: rest =>
    if isCssWhitespace c then idx :: leadingWhitespaceIndices (idx + 1) rest
    else []

/-- Find trailing whitespace indices from the end of the character list. -/
def trailingWhitespaceIndices (chars : List Char) : List Nat :=
  let indexed := (List.range chars.length).zip chars
  let nonWs := indexed.filter (fun (_, c) => !isCssWhitespace c)
  match nonWs.reverse with
  | [] => indexed.map Prod.fst
  | (lastNonWsIdx, _) :: _ =>
    (indexed.filter (fun (i, c) => i > lastNonWsIdx && isCssWhitespace c)).map Prod.fst

/-- Compute all collapsed DOM character indices under the given whitespace mode. -/
def collapsedIndices (mode : WhiteSpaceMode) (s : String) : List Nat :=
  if !mode.collapsesSpaces then []
  else
    let chars := s.toList
    let leading := leadingWhitespaceIndices 0 chars
    let inner := computeCollapsedAux mode false 0 chars
    let trailing := trailingWhitespaceIndices chars
    (leading ++ inner ++ trailing).eraseDups.filter (fun i => i < chars.length)

/-- General Law: In pre and pre-wrap modes, no characters are collapsed. -/
theorem offsetMapping_pre_no_collapsed (s : String) :
    collapsedIndices .pre s = [] ∧ collapsedIndices .preWrap s = [] := by
  dsimp [collapsedIndices, WhiteSpaceMode.collapsesSpaces]
  exact ⟨rfl, rfl⟩

/-! ## 3. Offset Mapping Units Construction -/

/-- Structurally recursive helper over characters to segment DOM text into mapping units. -/
def buildUnitsAux (collapsed : List Nat) (domIdx textIdx : Nat) (units : List OffsetMappingUnit) :
    List Char → List OffsetMappingUnit
  | [] => units.reverse
  | _ :: rest =>
    let isCol := collapsed.contains domIdx
    if isCol then
      let colEnd := domIdx + 1
      match units with
      | u :: us =>
        if u.unitType == .collapsed then
          buildUnitsAux collapsed (domIdx + 1) textIdx ({ u with domEnd := colEnd } :: us) rest
        else
          buildUnitsAux collapsed (domIdx + 1) textIdx ({ unitType := .collapsed, domStart := domIdx, domEnd := colEnd, textStart := textIdx, textEnd := textIdx } :: units) rest
      | [] =>
        buildUnitsAux collapsed (domIdx + 1) textIdx [{ unitType := .collapsed, domStart := domIdx, domEnd := colEnd, textStart := textIdx, textEnd := textIdx }] rest
    else
      let idEnd := domIdx + 1
      let nextText := textIdx + 1
      match units with
      | u :: us =>
        if u.unitType == .identity then
          buildUnitsAux collapsed (domIdx + 1) nextText ({ u with domEnd := idEnd, textEnd := nextText } :: us) rest
        else
          buildUnitsAux collapsed (domIdx + 1) nextText ({ unitType := .identity, domStart := domIdx, domEnd := idEnd, textStart := textIdx, textEnd := nextText } :: units) rest
      | [] =>
        buildUnitsAux collapsed (domIdx + 1) nextText [{ unitType := .identity, domStart := domIdx, domEnd := idEnd, textStart := textIdx, textEnd := nextText }] rest

/-- Build OffsetMappingUnits for a single text string under whitespace mode. -/
def computeOffsetMappingUnits (mode : WhiteSpaceMode) (s : String) : List OffsetMappingUnit :=
  let collapsed := collapsedIndices mode s
  let chars := s.toList
  if collapsed.isEmpty then
    if chars.isEmpty then []
    else [{ unitType := .identity, domStart := 0, domEnd := chars.length, textStart := 0, textEnd := chars.length }]
  else
    buildUnitsAux collapsed 0 0 [] chars

/-! ## 4. LayoutText Caret & Offset Query Operations -/

/-- Find the minimum non-collapsed DOM caret offset (`LayoutText::CaretMinOffset`). -/
def caretMinOffset (mode : WhiteSpaceMode) (s : String) : Nat :=
  let units := computeOffsetMappingUnits mode s
  match units.find? (fun u => u.unitType == .identity) with
  | some u => u.domStart
  | none => 0

/-- Find the maximum non-collapsed DOM caret offset (`LayoutText::CaretMaxOffset`). -/
def caretMaxOffset (mode : WhiteSpaceMode) (s : String) : Nat :=
  let units := computeOffsetMappingUnits mode s
  match (units.filter (fun u => u.unitType == .identity)).reverse with
  | [] => 0
  | last :: _ => last.domEnd

/-- Calculate the resolved (non-collapsed) text length (`LayoutText::ResolvedTextLength`). -/
def resolvedTextLength (mode : WhiteSpaceMode) (s : String) : Nat :=
  let units := computeOffsetMappingUnits mode s
  (units.filter (fun u => u.unitType == .identity)).foldl (fun acc u => acc + (u.textEnd - u.textStart)) 0

/-- Check if a DOM offset precedes a non-collapsed character (`LayoutText::IsBeforeNonCollapsedCharacter`). -/
def isBeforeNonCollapsed (units : List OffsetMappingUnit) (offset : Nat) : Bool :=
  units.any (fun u => u.unitType == .identity && offset ≥ u.domStart && offset < u.domEnd)

/-- Check if a DOM offset succeeds a non-collapsed character (`LayoutText::IsAfterNonCollapsedCharacter`). -/
def isAfterNonCollapsed (units : List OffsetMappingUnit) (offset : Nat) : Bool :=
  if offset == 0 then false
  else units.any (fun u => u.unitType == .identity && (offset - 1) ≥ u.domStart && (offset - 1) < u.domEnd)

/-- Mapping units generated for a `<br>` break element (`LayoutBR::UpdateOffsetMapping`). -/
def layoutBRUnits : List OffsetMappingUnit :=
  [{ unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }]

/-- Check if an offset contains a caret position for given units and characters (`LayoutText::ContainsCaretOffset`). -/
def containsCaretOffsetWithUnits (units : List OffsetMappingUnit) (chars : List Char) (offset : Nat) : Bool :=
  let maxOff := match (units.filter (fun u => u.unitType == .identity)).reverse with
    | [] => 0
    | last :: _ => last.domEnd
  if offset > maxOff then false
  else if offset < maxOff && isBeforeNonCollapsed units offset then true
  else if offset == 0 || !isAfterNonCollapsed units offset then false
  else
    if h : offset - 1 < chars.length then
      chars[offset - 1] != '\n'
    else false

/-- Compute the 3-character caret snap code: `Before`, `Contains`, `After` for given units and characters (`GetSnapCode`). -/
def getSnapCodeWithUnits (units : List OffsetMappingUnit) (chars : List Char) (offset : Nat) : String :=
  let b := if isBeforeNonCollapsed units offset then 'B' else '-'
  let c := if containsCaretOffsetWithUnits units chars offset then 'C' else '-'
  let a := if offset ≤ chars.length then (if isAfterNonCollapsed units offset then 'A' else '-') else '_'
  String.ofList [b, c, a]

/-- Check if a DOM offset contains a caret position under whitespace mode (`LayoutText::ContainsCaretOffset`). -/
def containsCaretOffset (mode : WhiteSpaceMode) (s : String) (offset : Nat) : Bool :=
  containsCaretOffsetWithUnits (computeOffsetMappingUnits mode s) s.toList offset

/-- Compute the 3-character caret snap code under whitespace mode (`GetSnapCode`). -/
def getSnapCode (mode : WhiteSpaceMode) (s : String) (offset : Nat) : String :=
  getSnapCodeWithUnits (computeOffsetMappingUnits mode s) s.toList offset

end ChromiumLayout
