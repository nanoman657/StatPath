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
  deriving DecidableEq, Repr

structure OffsetMappingUnit where
  unitType : OffsetMappingUnitType
  domStart : Nat
  domEnd : Nat
  textStart : Nat
  textEnd : Nat
  deriving DecidableEq, Repr

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

/-- Compute all collapsed DOM character indices under the given whitespace mode. -/
def collapsedIndices (mode : WhiteSpaceMode) (s : String) : List Nat :=
  if !mode.collapsesSpaces then []
  else
    let chars := s.toList
    let leading := leadingWhitespaceIndices 0 chars
    let inner := computeCollapsedAux mode false 0 chars
    (leading ++ inner).eraseDups.filter (fun i => i < chars.length)

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

end ChromiumLayout
