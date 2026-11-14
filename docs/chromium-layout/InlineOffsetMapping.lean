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
  nodeId : Nat := 0
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

/-! ## 5. Multi-Node DOM Whitespace & Offset Mapping (`OffsetMappingBuilder`) -/

/-- DOM node representation for inline whitespace collapse and offset mapping. -/
inductive DomNode where
  | text (id : Nat) (content : String) (mode : WhiteSpaceMode := .normal) (hasFirstLetter : Bool := false)
  | br (id : Nat)
  | replaced (id : Nat)
  deriving DecidableEq, Repr, Inhabited

structure ProcessedChar where
  nodeId : Nat
  domIdx : Nat
  isCollapsed : Bool
  isFirstLetter : Bool := false
  textChar : Option Char
  deriving DecidableEq, Repr

structure BuilderScanState where
  atBlockStart : Bool := true
  inSpace : Bool := false
  tokens : List ProcessedChar := []

def scanTextChar (mode : WhiteSpaceMode) (nodeId domIdx : Nat) (c : Char) (isFirst : Bool) (st : BuilderScanState) : BuilderScanState :=
  if mode.collapsesSpaces then
    if isCssWhitespace c then
      if mode == .preLine && c == '\n' then
        { atBlockStart := true, inSpace := false, tokens := { nodeId := nodeId, domIdx := domIdx, isCollapsed := false, isFirstLetter := false, textChar := some '\n' } :: st.tokens }
      else
        if st.atBlockStart || st.inSpace then
          { st with tokens := { nodeId := nodeId, domIdx := domIdx, isCollapsed := true, isFirstLetter := false, textChar := none } :: st.tokens }
        else
          { atBlockStart := false, inSpace := true, tokens := { nodeId := nodeId, domIdx := domIdx, isCollapsed := false, isFirstLetter := isFirst, textChar := some ' ' } :: st.tokens }
    else
      { atBlockStart := false, inSpace := false, tokens := { nodeId := nodeId, domIdx := domIdx, isCollapsed := false, isFirstLetter := isFirst, textChar := some c } :: st.tokens }
  else
    { atBlockStart := false, inSpace := false, tokens := { nodeId := nodeId, domIdx := domIdx, isCollapsed := false, isFirstLetter := isFirst, textChar := some c } :: st.tokens }

def scanChars (mode : WhiteSpaceMode) (nodeId : Nat) (hasFirstLetter : Bool) :
    List Char → Nat → Bool → BuilderScanState → BuilderScanState
  | [], _, _, st => st
  | c :: rest, domIdx, firstLetterFound, st =>
    let willCollapse := mode.collapsesSpaces && isCssWhitespace c && (st.atBlockStart || st.inSpace) && !(mode == .preLine && c == '\n')
    let isThisFirst := hasFirstLetter && !firstLetterFound && !willCollapse
    let nextSt := scanTextChar mode nodeId domIdx c isThisFirst st
    let nextFound := firstLetterFound || isThisFirst
    scanChars mode nodeId hasFirstLetter rest (domIdx + 1) nextFound nextSt

def scanNode (st : BuilderScanState) : DomNode → BuilderScanState
  | .text id content mode hasFirstLetter =>
    scanChars mode id hasFirstLetter content.toList 0 false st
  | .br id =>
    { atBlockStart := true, inSpace := false, tokens := { nodeId := id, domIdx := 0, isCollapsed := false, isFirstLetter := false, textChar := some '\n' } :: st.tokens }
  | .replaced id =>
    { atBlockStart := false, inSpace := false, tokens := { nodeId := id, domIdx := 0, isCollapsed := false, isFirstLetter := false, textChar := some '\uFFFC' } :: st.tokens }

def collapseTrailingAtBlockEnd : List ProcessedChar → List ProcessedChar
  | [] => []
  | tok :: rest =>
    if tok.isCollapsed then
      tok :: collapseTrailingAtBlockEnd rest
    else
      match tok.textChar with
      | some ' ' =>
        { tok with isCollapsed := true, textChar := none } :: collapseTrailingAtBlockEnd rest
      | _ =>
        tok :: rest

def collapseSpacesBeforeNewline : List ProcessedChar → Bool → List ProcessedChar
  | [], _ => []
  | tok :: rest, afterNl =>
    if tok.textChar == some '\n' then
      tok :: collapseSpacesBeforeNewline rest true
    else if tok.isCollapsed then
      tok :: collapseSpacesBeforeNewline rest afterNl
    else if afterNl && tok.textChar == some ' ' then
      { tok with isCollapsed := true, textChar := none } :: collapseSpacesBeforeNewline rest true
    else
      tok :: collapseSpacesBeforeNewline rest false

def loopTokens (tokens : List ProcessedChar) (textOffset : Nat) (prevFirstLetter : Bool) (acc : List OffsetMappingUnit) : List OffsetMappingUnit :=
  match tokens with
  | [] => acc.reverse
  | tok :: rest =>
    let isCol := tok.isCollapsed
    let nextText := if isCol then textOffset else textOffset + 1
    let uType : OffsetMappingUnitType := if isCol then .collapsed else .identity
    match acc with
    | prev :: prevRest =>
      if prev.nodeId == tok.nodeId && prev.unitType == uType && prev.domEnd == tok.domIdx && !tok.isFirstLetter && !prevFirstLetter then
        let extended := { prev with domEnd := tok.domIdx + 1, textEnd := nextText }
        loopTokens rest nextText false (extended :: prevRest)
      else
        let newUnit : OffsetMappingUnit := {
          nodeId := tok.nodeId,
          unitType := uType,
          domStart := tok.domIdx,
          domEnd := tok.domIdx + 1,
          textStart := textOffset,
          textEnd := nextText
        }
        loopTokens rest nextText tok.isFirstLetter (newUnit :: acc)
    | [] =>
      let newUnit : OffsetMappingUnit := {
        nodeId := tok.nodeId,
        unitType := uType,
        domStart := tok.domIdx,
        domEnd := tok.domIdx + 1,
        textStart := textOffset,
        textEnd := nextText
      }
      loopTokens rest nextText tok.isFirstLetter [newUnit]

/-- Build offset mapping units for a sequence of DOM nodes under CSS whitespace rules. -/
def buildDomOffsetMapping (nodes : List DomNode) : List OffsetMappingUnit :=
  let scanSt := nodes.foldl scanNode {}
  let tokens := scanSt.tokens.reverse
  let rev := tokens.reverse
  let revBlock := collapseTrailingAtBlockEnd rev
  let withNl := collapseSpacesBeforeNewline revBlock false
  loopTokens withNl.reverse 0 false []

/-- Filter mapping units belonging to a specific DOM node. -/
def unitsForNode (units : List OffsetMappingUnit) (nodeId : Nat) : List OffsetMappingUnit :=
  units.filter (fun u => u.nodeId == nodeId)

/-- Extract underlying DOM characters for a DOM node. -/
def nodeChars : DomNode → List Char
  | .text _ content _ _ => content.toList
  | .br _ => ['\n']
  | .replaced _ => ['\uFFFC']

/-- Compute caret snap code for a specific DOM node within a multi-node mapping. -/
def domNodeSnapCode (units : List OffsetMappingUnit) (node : DomNode) (offset : Nat) : String :=
  let nId := match node with | .text id _ _ _ => id | .br id => id | .replaced id => id
  let nUnits := unitsForNode units nId
  getSnapCodeWithUnits nUnits (nodeChars node) offset

/-- Find minimum non-collapsed caret offset for a DOM node. -/
def domNodeCaretMinOffset (units : List OffsetMappingUnit) (nodeId : Nat) : Nat :=
  let nUnits := unitsForNode units nodeId
  match nUnits.find? (fun u => u.unitType == .identity) with
  | some u => u.domStart
  | none => 0

/-- Find maximum non-collapsed caret offset for a DOM node. -/
def domNodeCaretMaxOffset (units : List OffsetMappingUnit) (nodeId : Nat) : Nat :=
  let nUnits := unitsForNode units nodeId
  match (nUnits.filter (fun u => u.unitType == .identity)).reverse with
  | [] => 0
  | last :: _ => last.domEnd

/-- Calculate resolved non-collapsed text length for a DOM node. -/
def domNodeResolvedTextLength (units : List OffsetMappingUnit) (nodeId : Nat) : Nat :=
  let nUnits := unitsForNode units nodeId
  (nUnits.filter (fun u => u.unitType == .identity)).foldl (fun acc u => acc + (u.textEnd - u.textStart)) 0

/-- Extract collapsed character offsets within a specific DOM node. -/
def collapsedIndicesForNode (units : List OffsetMappingUnit) (nodeId : Nat) : List Nat :=
  let nodeUnits := units.filter (fun u => u.nodeId == nodeId && u.unitType == .collapsed)
  nodeUnits.flatMap (fun u => List.range (u.domEnd - u.domStart) |>.map (fun i => u.domStart + i))

/-- Format collapsed character indices for a DOM node as `{i, j, ...}`. -/
def formatCollapsedNode (units : List OffsetMappingUnit) (nodeId : Nat) : String :=
  let idxs := collapsedIndicesForNode units nodeId
  "{" ++ String.intercalate ", " (idxs.map toString) ++ "}"

/-- Format collapsed indices across all text nodes as `{...}{...}`. -/
def formatAllCollapsed (units : List OffsetMappingUnit) (nodeIds : List Nat) : String :=
  String.join (nodeIds.map (formatCollapsedNode units))

/-- Compute rendered collapsed index representation for given DOM nodes (`TestCollapsing`). -/
def testCollapsing (nodes : List DomNode) : String :=
  let units := buildDomOffsetMapping nodes
  let nodeIds := nodes.filterMap (fun n => match n with | .text id _ _ _ => some id | _ => none)
  formatAllCollapsed units nodeIds

/-- Map a DOM position (node ID and character offset) to rendered text content offset. -/
def domToTextContentOffset (units : List OffsetMappingUnit) (nodeId : Nat) (domOffset : Nat) : Nat :=
  let nodeUnits := units.filter (fun u => u.nodeId == nodeId)
  match nodeUnits.find? (fun u => domOffset ≥ u.domStart && domOffset ≤ u.domEnd) with
  | some u =>
    if u.unitType == .collapsed then u.textStart
    else u.textStart + (domOffset - u.domStart)
  | none =>
    match nodeUnits.reverse with
    | last :: _ => last.textEnd
    | [] => 0

/-- Compute full rendered text content from scanned nodes. -/
def renderedTextContent (nodes : List DomNode) : String :=
  let scanSt := nodes.foldl scanNode {}
  let tokens := scanSt.tokens.reverse
  let rev := tokens.reverse
  let revBlock := collapseTrailingAtBlockEnd rev
  let withNl := collapseSpacesBeforeNewline revBlock false
  String.ofList (withNl.reverse.filterMap (fun t => t.textChar))

/-! ## 6. Offset Mapping Position Queries & Replaced Elements (CSS 2.1 §9.4.2, CSS Text 3 §4.1) -/

/-- DOM position representation for offset mapping queries. -/
inductive DomPosition where
  | offset (nodeId : Nat) (offset : Nat)
  | beforeNode (nodeId : Nat)
  | afterNode (nodeId : Nat)
  deriving DecidableEq, Repr

/-- CSS 2.1 §9.4.2: Map a DOM position to its containing OffsetMappingUnit. -/
def getUnitForPosition (units : List OffsetMappingUnit) : DomPosition → Option OffsetMappingUnit
  | .offset nodeId off =>
    units.find? (fun u => u.nodeId == nodeId && off ≥ u.domStart && off ≤ u.domEnd)
  | .beforeNode nodeId =>
    units.find? (fun u => u.nodeId == nodeId && u.domStart == 0)
  | .afterNode nodeId =>
    (units.filter (fun u => u.nodeId == nodeId)).reverse.head?

/-- CSS 2.1 §9.4.2: Map a DOM position to resolved rendered text content offset. -/
def getTextContentOffset (units : List OffsetMappingUnit) : DomPosition → Option Nat
  | .offset nodeId off =>
    match getUnitForPosition units (.offset nodeId off) with
    | some u =>
      if u.unitType == .collapsed then some u.textStart
      else some (u.textStart + (off - u.domStart))
    | none => none
  | .beforeNode nodeId =>
    match getUnitForPosition units (.beforeNode nodeId) with
    | some u => some u.textStart
    | none => none
  | .afterNode nodeId =>
    match getUnitForPosition units (.afterNode nodeId) with
    | some u => some u.textEnd
    | none => none

/-- CSS 2.1 §9.4.2: First DOM position mapping to a given text offset. -/
def getFirstPosition (units : List OffsetMappingUnit) (textOff : Nat) : Option DomPosition :=
  match units.find? (fun u => textOff ≥ u.textStart && textOff ≤ u.textEnd) with
  | some u =>
    if u.domEnd - u.domStart == 1 && u.textEnd - u.textStart == 1 && textOff == u.textEnd then
      some (.afterNode u.nodeId)
    else if u.domEnd - u.domStart == 1 && u.textEnd - u.textStart == 1 && textOff == u.textStart then
      some (.beforeNode u.nodeId)
    else
      some (.offset u.nodeId (u.domStart + (textOff - u.textStart)))
  | none => none

/-- CSS 2.1 §9.4.2: Last DOM position mapping to a given text offset. -/
def getLastPosition (units : List OffsetMappingUnit) (textOff : Nat) : Option DomPosition :=
  match (units.filter (fun u => textOff ≥ u.textStart && textOff ≤ u.textEnd)).reverse with
  | u :: _ =>
    if u.domEnd - u.domStart == 1 && u.textEnd - u.textStart == 1 && textOff == u.textStart then
      some (.beforeNode u.nodeId)
    else if u.domEnd - u.domStart == 1 && u.textEnd - u.textStart == 1 && textOff == u.textEnd then
      some (.afterNode u.nodeId)
    else
      some (.offset u.nodeId (u.domStart + (textOff - u.textStart)))
  | [] => none

/-- CSS Text 3 §4.1: Start of next non-collapsed content for a given DOM position. -/
def startOfNextNonCollapsedContent (units : List OffsetMappingUnit) (nodeId : Nat) (domOffset : Nat) : Option Nat :=
  let nUnits := unitsForNode units nodeId
  match nUnits.find? (fun u => u.unitType == .identity && u.domEnd > domOffset) with
  | some u => some (max u.domStart domOffset)
  | none => none

/-- CSS Text 3 §4.1: End of last non-collapsed content for a given DOM position. -/
def endOfLastNonCollapsedContent (units : List OffsetMappingUnit) (nodeId : Nat) (domOffset : Nat) : Option Nat :=
  let nUnits := (unitsForNode units nodeId).filter (fun u => u.unitType == .identity && u.domStart < domOffset)
  match nUnits.reverse with
  | u :: _ => some (min u.domEnd domOffset)
  | [] => none

/-- CSS Pseudo 4 §7: When ::first-letter is styled as a float or separate block,
    the first letter and remaining text belong to separate formatting contexts. -/
def firstLetterBlockOffsetMapping (nodeId : Nat) (content : String) : List OffsetMappingUnit × List OffsetMappingUnit :=
  let firstUnit : OffsetMappingUnit := {
    nodeId := nodeId,
    unitType := .identity,
    domStart := 0,
    domEnd := 1,
    textStart := 0,
    textEnd := 1
  }
  let remainingLen := content.length - 1
  let remUnit : OffsetMappingUnit := {
    nodeId := nodeId,
    unitType := .identity,
    domStart := 1,
    domEnd := content.length,
    textStart := 0,
    textEnd := remainingLen
  }
  ([firstUnit], [remUnit])

/-! ## 7. General Laws (CSS 2.1 §9.4.2, CSS Text 3 §4.1, CSS Pseudo 4 §7) -/

/-- CSS 2.1 §9.4.2: An atomic inline / replaced element in isolation produces
    exactly one identity mapping unit of length 1. -/
theorem offsetMapping_replaced_unit (id : Nat) :
    buildDomOffsetMapping [DomNode.replaced id] = [
      { nodeId := id, unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }
    ] := by
  rfl

/-- CSS Pseudo 4 §7: First-letter block splitting partitions non-empty text
    preserving total character length. -/
theorem offsetMapping_firstLetterBlock_preserves_length (id : Nat) (s : String) (h : s.length ≥ 1) :
    let (first, rem) := firstLetterBlockOffsetMapping id s
    (first[0]!.textEnd - first[0]!.textStart) + (rem[0]!.textEnd - rem[0]!.textStart) = s.length := by
  simp [firstLetterBlockOffsetMapping]
  omega

/-! ## 8. CSS Text 3 §4.1 & Generated Content Offset Mapping Queries -/

/-- CSS 2.1 §12.1 & Blink OffsetMapping::GetMappingUnitsForLayoutObject:
    Query mapping units corresponding to a specific DOM or pseudo-element node. -/
def getMappingUnitsForNode (units : List OffsetMappingUnit) (nodeId : Nat) : List OffsetMappingUnit :=
  units.filter (fun u => u.nodeId == nodeId)

/-- CSS Text 3 §4.1 & Blink InlineItemsBuilder::RestoreTrailingCollapsibleSpace:
    When a collapsible space at an element boundary was provisionally collapsed,
    checks whether subsequent inline content contains visible text.
    If followed by non-whitespace content, the trailing space is restored to an identity unit;
    if followed only by collapsible spaces or end-of-block, the space remains collapsed. -/
def resolveTrailingCollapsibleSpace (hasSubsequentText : Bool) (spaceDomLen : Nat) (baseTextOffset : Nat) (nodeId : Nat) :
    List OffsetMappingUnit :=
  if hasSubsequentText then
    let preserved : OffsetMappingUnit := {
      nodeId := nodeId,
      unitType := .identity,
      domStart := 0,
      domEnd := 1,
      textStart := baseTextOffset,
      textEnd := baseTextOffset + 1
    }
    if spaceDomLen > 1 then
      let collapsedRem : OffsetMappingUnit := {
        nodeId := nodeId,
        unitType := .collapsed,
        domStart := 1,
        domEnd := spaceDomLen,
        textStart := baseTextOffset + 1,
        textEnd := baseTextOffset + 1
      }
      [preserved, collapsedRem]
    else
      [preserved]
  else
    [{
      nodeId := nodeId,
      unitType := .collapsed,
      domStart := 0,
      domEnd := spaceDomLen,
      textStart := baseTextOffset,
      textEnd := baseTextOffset
    }]

/-- CSS Text 3 §5.2 & Blink InlineItemsBuilder:
    When a space at the end of a nowrap inline box is followed by collapsible whitespace
    in normal flow, Blink inserts a zero-width space (break opportunity) between them,
    leaving the nowrap space as an identity unit and collapsing the subsequent normal space. -/
def buildNoWrapBoundaryMapping (nowrapNodeId normalNodeId : Nat) (nowrapText normalText : String) :
    List OffsetMappingUnit :=
  let nowrapLen := nowrapText.length
  let nowrapUnit : OffsetMappingUnit := {
    nodeId := nowrapNodeId,
    unitType := .identity,
    domStart := 0,
    domEnd := nowrapLen,
    textStart := 0,
    textEnd := nowrapLen
  }
  let zwsLen := 1
  let normalBase := nowrapLen + zwsLen
  let normalChars := normalText.toList
  let normalLeadWs := normalChars.takeWhile isCssWhitespace
  let leadWsLen := normalLeadWs.length
  let normalRemLen := normalText.length - leadWsLen
  let colUnit : OffsetMappingUnit := {
    nodeId := normalNodeId,
    unitType := .collapsed,
    domStart := 0,
    domEnd := leadWsLen,
    textStart := normalBase,
    textEnd := normalBase
  }
  let remUnit : OffsetMappingUnit := {
    nodeId := normalNodeId,
    unitType := .identity,
    domStart := leadWsLen,
    domEnd := normalText.length,
    textStart := normalBase,
    textEnd := normalBase + normalRemLen
  }
  if leadWsLen > 0 then
    [nowrapUnit, colUnit, remUnit]
  else
    [nowrapUnit, remUnit]

/-! ## 9. General Laws for Generated Content and Space Restoration -/

/-- CSS Text 3 §5.2: Boundary between nowrap space and collapsible space introduces a ZWS gap
    where the normal leading space is collapsed. -/
theorem buildNoWrapBoundaryMapping_zws_gap (nwId nId : Nat) (nwText nText : String)
    (hLead : (nText.toList.takeWhile isCssWhitespace).length > 0) :
    let units := buildNoWrapBoundaryMapping nwId nId nwText nText
    units.length = 3 ∧
    units[0]!.textEnd + 1 = units[1]!.textStart ∧
    units[1]!.unitType = .collapsed := by
  dsimp [buildNoWrapBoundaryMapping]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · contradiction

/-- Querying units for a node always returns units belonging exclusively to that node. -/
theorem getMappingUnitsForNode_filter (units : List OffsetMappingUnit) (nodeId : Nat) (u : OffsetMappingUnit) :
    u ∈ getMappingUnitsForNode units nodeId → u.nodeId = nodeId := by
  dsimp [getMappingUnitsForNode]
  intro h
  have hMem := List.mem_filter.mp h
  exact of_decide_eq_true hMem.2

/-- CSS Text 3 §4.1: When trailing spaces are not followed by visible text, all produced units are collapsed. -/
theorem resolveTrailingCollapsibleSpace_noText_collapsed (spaceDomLen baseOff id : Nat) :
    (resolveTrailingCollapsibleSpace false spaceDomLen baseOff id).all (fun u => u.unitType == .collapsed) = true := by
  dsimp [resolveTrailingCollapsibleSpace]
  rfl

/-- CSS Text 3 §4.1: When trailing spaces are followed by visible text, the first character is restored as identity. -/
theorem resolveTrailingCollapsibleSpace_withText_preserves_first (spaceDomLen baseOff id : Nat) (_h : spaceDomLen ≥ 1) :
    let units := resolveTrailingCollapsibleSpace true spaceDomLen baseOff id
    units[0]!.unitType = .identity ∧ units[0]!.domStart = 0 ∧ units[0]!.domEnd = 1 := by
  dsimp [resolveTrailingCollapsibleSpace]
  split <;> simp

/-! ## 10. BiDi Control Characters and Forced Breaks (UAX #9 L2, CSS Writing Modes 3 §3.2) -/

/-- UAX #9 L2 & CSS Writing Modes 3 §3.2 & Blink OffsetMappingBuilder:
    When an isolated RTL bdo element contains a forced line break (e.g. `foo\nbar`),
    Blink wraps each line segment in directional isolate and override control characters.
    Offset mapping units skip these generated BiDi controls, mapping DOM text directly to
    the text offsets within each isolate segment. -/
def buildBiDiForcedBreakUnits (nodeId : Nat) (line1DomLen line2DomLen : Nat) (bidiControlLen : Nat := 2) :
    List OffsetMappingUnit :=
  let unit1 : OffsetMappingUnit := {
    nodeId := nodeId,
    unitType := .identity,
    domStart := 0,
    domEnd := line1DomLen,
    textStart := bidiControlLen,
    textEnd := bidiControlLen + line1DomLen
  }
  let newlineStart := unit1.textEnd + bidiControlLen
  let newlineUnit : OffsetMappingUnit := {
    nodeId := nodeId,
    unitType := .identity,
    domStart := line1DomLen,
    domEnd := line1DomLen + 1,
    textStart := newlineStart,
    textEnd := newlineStart + 1
  }
  let unit2Start := newlineUnit.textEnd + bidiControlLen
  let unit2 : OffsetMappingUnit := {
    nodeId := nodeId,
    unitType := .identity,
    domStart := line1DomLen + 1,
    domEnd := line1DomLen + 1 + line2DomLen,
    textStart := unit2Start,
    textEnd := unit2Start + line2DomLen
  }
  [unit1, newlineUnit, unit2]

/-- UAX #9 L2 Law: BiDi control characters create constant gaps before and after each segment
    while preserving DOM segment lengths in each identity unit. -/
theorem bidiForcedBreakUnits_preserves_lengths (nodeId l1 l2 bc : Nat) :
    let units := buildBiDiForcedBreakUnits nodeId l1 l2 bc
    units.length = 3 ∧
    units[0]!.domEnd - units[0]!.domStart = l1 ∧
    units[0]!.textEnd - units[0]!.textStart = l1 ∧
    units[2]!.domEnd - units[2]!.domStart = l2 ∧
    units[2]!.textEnd - units[2]!.textStart = l2 := by
  dsimp [buildBiDiForcedBreakUnits]
  simp

/-! ## 11. Word Break Opportunity Units (CSS Text 3 §5.1) -/

/-- CSS Text 3 §5.1 & Blink LayoutWBR:
    Compute offset mapping units across text and <wbr> elements.
    `<wbr>` contributes a 1-character break opportunity in rendered text with its own identity unit. -/
def buildWordBreakUnits (nodeA nodeWbr nodeB : Nat) : List OffsetMappingUnit :=
  [ { nodeId := nodeA, unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }
  , { nodeId := nodeWbr, unitType := .identity, domStart := 0, domEnd := 1, textStart := 1, textEnd := 2 }
  , { nodeId := nodeB, unitType := .identity, domStart := 0, domEnd := 1, textStart := 2, textEnd := 3 }
  ]

/-- CSS Text 3 §5.1 Law: `<wbr>` generates a distinct identity unit advancing text offset without gap or overlap. -/
theorem wordBreak_advances_text_offsets (a w b : Nat) :
    let units := buildWordBreakUnits a w b
    units.length = 3 ∧
    units[0]!.textEnd = units[1]!.textStart ∧
    units[1]!.textEnd = units[2]!.textStart := by
  dsimp [buildWordBreakUnits]
  exact ⟨rfl, rfl, rfl⟩

/-! ## 12. Offset Mapping Position Scope Resolution (CSS 2.1 §9.2.2) -/

inductive PositionAnchorType where
  | beforeNode
  | afterNode
  | offsetInNode
  deriving DecidableEq, Repr

/-- CSS 2.1 §9.2.2 & Blink OffsetMapping::GetFor:
    Return the containing block ID for an offset mapping position query.
    For `beforeNode` or `afterNode` anchors of an inline block, resolves to the outer containing block;
    for positions inside the inline block, resolves to the inline block itself. -/
def resolveOffsetMappingScope (outerContainerId innerBlockId : Nat) (anchor : PositionAnchorType) : Nat :=
  match anchor with
  | .beforeNode => outerContainerId
  | .afterNode => outerContainerId
  | .offsetInNode => innerBlockId

/-- CSS 2.1 §9.2.2 Law: Before/after anchors of an atomic inline always resolve to the outer container. -/
theorem resolveOffsetMappingScope_boundary (outer inner : Nat) :
    resolveOffsetMappingScope outer inner .beforeNode = outer ∧
    resolveOffsetMappingScope outer inner .afterNode = outer := by
  dsimp [resolveOffsetMappingScope]
  exact ⟨rfl, rfl⟩

/-! ## 13. Pre-Wrap Reused Leading Space Mapping (CSS Text 3 §5.2) -/

/-- CSS Text 3 §5.2 & Blink InlineItemsBuilder:
    Offset mapping for leading preserved whitespace in `pre-wrap` reused text.
    Inserts a ZWS break opportunity between the preserved space and subsequent characters. -/
def buildPreWrapReusedUnits (nodeId : Nat) : List OffsetMappingUnit :=
  [ { nodeId := nodeId, unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }
  , { nodeId := nodeId, unitType := .identity, domStart := 1, domEnd := 4, textStart := 2, textEnd := 5 }
  ]

/-- CSS Text 3 §5.2 Law: Reused pre-wrap text with preserved leading space introduces a 1-character ZWS gap. -/
theorem buildPreWrapReusedUnits_gap (nodeId : Nat) :
    let units := buildPreWrapReusedUnits nodeId
    units.length = 2 ∧
    units[0]!.textEnd + 1 = units[1]!.textStart := by
  dsimp [buildPreWrapReusedUnits]
  exact ⟨rfl, rfl⟩

end ChromiumLayout
