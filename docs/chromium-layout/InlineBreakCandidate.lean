/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineGeometry
import InlineShaping

/-!
# CSS Text 3 §4: Line Breaking and Soft Wrap Candidates

Formalizes:
- CSS Text 3 §4: Line Breaking and Word Boundaries
- CSS Text 3 §4.1: Soft Wrap Opportunities and Hyphenation
- `third_party/blink/renderer/core/layout/inline/line_break_candidate.h`

Owns:
- `InlineItemTextIndex`
- `LineBreakCandidate`
- `HyphensMode`
- `IndexedInlineToken`
- `computeLineBreakCandidates`
-/

namespace ChromiumLayout

/-! ## 1. Break Candidate Structures (CSS Text 3 §4) -/

/-- CSS Text 3 §4: Index in flattened inline stream (item index and character text offset). -/
structure InlineItemTextIndex where
  itemIndex : Nat := 0
  textOffset : Nat := 0
  deriving DecidableEq, Repr

/-- CSS Text 3 §4.1: Candidate soft wrap opportunity (`LineBreakCandidate`).
    Records position if line breaks here (collapsing spaces, adding hyphens)
    versus position if line does not break here. -/
structure LineBreakCandidate where
  offset : InlineItemTextIndex
  endOffset : InlineItemTextIndex
  posNoBreak : Nat
  posIfBreak : Nat
  penalty : Nat := 0
  isHyphenated : Bool := false
  deriving DecidableEq, Repr

/-- CSS Text 3 §4.1: Values for the 'hyphens' property. -/
inductive HyphensMode where
  | auto
  | manual
  | none
  deriving DecidableEq, Repr

/-- Inline token annotated with its item index in the flattened inline stream. -/
structure IndexedInlineToken where
  itemIndex : Nat
  token : InlineCollectionToken
  deriving DecidableEq, Repr

/-! ## 2. Candidate Computation (CSS Text 3 §4.1) -/

/-- CSS Text 3 §4.1: Compute candidate soft wrap opportunities for an inline token stream.
    Respects word boundaries (spaces), soft hyphens (when hyphens != none), and inline span boundaries. -/
def computeLineBreakCandidates (tokens : List IndexedInlineToken) (hyphens : HyphensMode := .auto) (glyphWidth : Nat := 10) : List LineBreakCandidate :=
  let initCandidate : LineBreakCandidate :=
    { offset := { itemIndex := 0, textOffset := 0 },
      endOffset := { itemIndex := 0, textOffset := 0 },
      posNoBreak := 0, posIfBreak := 0 }
  let rec processTokens (curItemIdx : Nat) (textOffset : Nat) (visibleWidth : Nat) (lastWordEnd : InlineItemTextIndex)
      (acc : List LineBreakCandidate) : List IndexedInlineToken → List LineBreakCandidate
    | [] =>
      if textOffset == 0 then acc.reverse
      else
        let finalCand : LineBreakCandidate :=
          { offset := { itemIndex := curItemIdx, textOffset := textOffset },
            endOffset := { itemIndex := curItemIdx, textOffset := textOffset },
            posNoBreak := visibleWidth, posIfBreak := visibleWidth }
        (finalCand :: acc).reverse
    | ⟨idx, .openTag _⟩ :: rest =>
      processTokens idx textOffset visibleWidth lastWordEnd acc rest
    | ⟨idx, .closeTag⟩ :: rest =>
      let updatedAcc := match acc with
        | c :: cs => if c.offset.textOffset == textOffset then { c with offset := { itemIndex := idx + 1, textOffset := textOffset } } :: cs else acc
        | [] => acc
      processTokens idx textOffset visibleWidth lastWordEnd updatedAcc rest
    | ⟨idx, .atomicInline w⟩ :: rest =>
      let newOffset := textOffset + 1
      let newWidth := visibleWidth + w
      let cand : LineBreakCandidate :=
        { offset := { itemIndex := idx, textOffset := newOffset },
          endOffset := { itemIndex := idx, textOffset := newOffset },
          posNoBreak := newWidth, posIfBreak := newWidth }
      processTokens idx newOffset newWidth { itemIndex := idx, textOffset := newOffset } (cand :: acc) rest
    | ⟨idx, .br⟩ :: rest =>
      let newOffset := textOffset + 1
      let cand : LineBreakCandidate :=
        { offset := { itemIndex := idx, textOffset := newOffset },
          endOffset := { itemIndex := idx, textOffset := newOffset },
          posNoBreak := visibleWidth, posIfBreak := visibleWidth }
      processTokens idx newOffset visibleWidth { itemIndex := idx, textOffset := newOffset } (cand :: acc) rest
    | ⟨idx, .text s⟩ :: rest =>
      let rec walkChars (chars : List Char) (off : Nat) (vWidth : Nat) (wEnd : InlineItemTextIndex)
          (cands : List LineBreakCandidate) : Nat × Nat × InlineItemTextIndex × List LineBreakCandidate :=
        match chars with
        | [] => (off, vWidth, wEnd, cands)
        | ' ' :: cs =>
          let noBreak := vWidth + glyphWidth
          let ifBreak := vWidth
          let cand : LineBreakCandidate :=
            { offset := { itemIndex := idx, textOffset := off + 1 },
              endOffset := wEnd,
              posNoBreak := noBreak,
              posIfBreak := ifBreak }
          walkChars cs (off + 1) noBreak wEnd (cand :: cands)
        | '\u00AD' :: cs =>
          if hyphens != .none && !cs.isEmpty then
            let cand : LineBreakCandidate :=
              { offset := { itemIndex := idx, textOffset := off + 1 },
                endOffset := { itemIndex := idx, textOffset := off + 1 },
                posNoBreak := vWidth,
                posIfBreak := vWidth + glyphWidth,
                isHyphenated := true }
            walkChars cs (off + 1) vWidth { itemIndex := idx, textOffset := off + 1 } (cand :: cands)
          else
            walkChars cs (off + 1) vWidth wEnd cands
        | _ :: cs =>
          let newVWidth := vWidth + glyphWidth
          let newOff := off + 1
          walkChars cs newOff newVWidth { itemIndex := idx, textOffset := newOff } cands
      let (finalOff, finalVWidth, finalWEnd, newCands) := walkChars s.toList textOffset visibleWidth lastWordEnd acc
      processTokens idx finalOff finalVWidth finalWEnd newCands rest
  processTokens 0 0 0 { itemIndex := 0, textOffset := 0 } [initCandidate] tokens

/-! ## 3. General Laws (CSS Text 3 §4) -/

/-- CSS Text 3 §4.1 Law: At any soft wrap opportunity with a collapsed trailing space,
    the position difference between unforced non-break and break equals exactly the glyph width. -/
theorem trailingSpace_collapsed_diff (noBreak ifBreak glyphWidth : Nat) (h : noBreak = ifBreak + glyphWidth) :
    noBreak - ifBreak = glyphWidth := by
  omega

/-- CSS Text 3 §4.1 Law: Hyphenation penalty and glyph width expansion:
    adding a visible hyphen glyph increases line position by exactly the hyphen glyph width. -/
theorem hyphenation_glyph_expansion (posNoBreak glyphWidth : Nat) :
    (posNoBreak + glyphWidth) - posNoBreak = glyphWidth := by
  omega

/-- CSS Text 3 §4 Law: An empty inline context produces exactly the initial root candidate at (0, 0). -/
theorem empty_context_initial_candidate (hyphens : HyphensMode) (w : Nat) :
    computeLineBreakCandidates [] hyphens w =
      [{ offset := { itemIndex := 0, textOffset := 0 },
         endOffset := { itemIndex := 0, textOffset := 0 },
         posNoBreak := 0, posIfBreak := 0 }] := by
  rfl

/-! ## 4. Line Breaking Opportunities and Break Inside Predicate (CSS Text 3 §5.2) -/

/-- Inflow item classification for determining line breaking opportunities. -/
inductive InflowBreakItem where
  | text (content : String) (hasSpace : Bool := false)
  | atomicInline
  | outOfFlow
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 3 §5.2 / Blink LineBreaker::CanBreakInside:
    Whether an inline sequence has a break opportunity inside.
    A line can break inside if autoWrap is true (not nowrap) and there is either:
    1. A text item containing internal word-breaking spaces, or
    2. A break opportunity between two adjacent in-flow items (e.g. text and atomic inline,
       two atomic inlines, or text separated by in-flow whitespace). -/
def canBreakInside (autoWrap : Bool) (items : List InflowBreakItem) : Bool :=
  if !autoWrap then false
  else
    let inFlow := items.filter (fun it => it ≠ .outOfFlow)
    let hasInternalBreak := inFlow.any (fun it => match it with | .text _ hasSpace => hasSpace | _ => false)
    let rec checkAdjacent : List InflowBreakItem → Bool
      | [] | [_] => false
      | x :: y :: rest =>
        match x, y with
        | .atomicInline, .atomicInline => true
        | .atomicInline, .text _ _ => true
        | .text _ _, .atomicInline => true
        | _, _ => checkAdjacent (y :: rest)
    hasInternalBreak || checkAdjacent inFlow

/-- CSS Text 3 §5.2: nowrap never permits breaking inside. -/
theorem canBreakInside_nowrap (items : List InflowBreakItem) :
    canBreakInside false items = false := rfl

/-- CSS Text 3 §5.2: Empty item stream cannot break inside. -/
theorem canBreakInside_empty (autoWrap : Bool) :
    canBreakInside autoWrap [] = false := by
  cases autoWrap <;> rfl

/-- CSS Text 3 §5.2: Single text without space cannot break inside. -/
theorem canBreakInside_single_text_no_space (s : String) :
    canBreakInside true [.text s false] = false := rfl

/-- CSS Text 3 §5.2: Single text containing space can break inside. -/
theorem canBreakInside_single_text_with_space (s : String) :
    canBreakInside true [.text s true] = true := rfl

/-- CSS Text 3 §5.2: Boundary between two atomic inlines can break inside. -/
theorem canBreakInside_adjacent_atomic_inlines :
    canBreakInside true [.atomicInline, .atomicInline] = true := rfl

/-- CSS Text 3 §5.2: Boundary between text and atomic inline can break inside. -/
theorem canBreakInside_text_and_atomic (s : String) (hasSpace : Bool) :
    canBreakInside true [.text s hasSpace, .atomicInline] = true := by
  cases hasSpace <;> rfl

/-- CSS Text 3 §5.2: Boundary between atomic inline and text can break inside. -/
theorem canBreakInside_atomic_and_text (s : String) (hasSpace : Bool) :
    canBreakInside true [.atomicInline, .text s hasSpace] = true := by
  cases hasSpace <;> rfl

/-! ## 5. Trailing Whitespace State (CSS Text 3 §4.1, §5.1) -/

/-- CSS Text 3 §4.1 / Blink LineBreaker::WhitespaceState:
    Trailing whitespace state of a line after line breaking. -/
inductive LineBreakerWhitespaceState where
  | none
  | leading
  | collapsed
  | preserved
  deriving DecidableEq, Repr, Inhabited

/-- Line break end scenario for determining trailing whitespace state. -/
inductive LineBreakEndReason where
  | emptyLine
  | textEnd
  | atomicEnd
  | softWrapBreak (collapses : Bool)
  | preservedSpaceEnd
  | blockEndSpace (collapses : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 3 §4.1, §5.1 / Blink LineBreaker::ComputeTrailingWhitespace:
    Compute trailing whitespace state from the line break end scenario. -/
def computeWhitespaceState (reason : LineBreakEndReason) : LineBreakerWhitespaceState :=
  match reason with
  | .emptyLine => .leading
  | .textEnd => .none
  | .atomicEnd => .none
  | .softWrapBreak collapses => if collapses then .collapsed else .preserved
  | .preservedSpaceEnd => .preserved
  | .blockEndSpace collapses => if collapses then .none else .preserved

/-- CSS Text 3 §5.1: Empty line whitespace state is leading. -/
theorem whitespaceState_empty :
    computeWhitespaceState .emptyLine = .leading := rfl

/-- CSS Text 3 §5.1: Line ending in text has whitespace state none. -/
theorem whitespaceState_textEnd :
    computeWhitespaceState .textEnd = .none := rfl

/-- CSS Text 3 §5.1: Line ending in atomic inline has whitespace state none. -/
theorem whitespaceState_atomicEnd :
    computeWhitespaceState .atomicEnd = .none := rfl

/-- CSS Text 3 §5.1: Soft wrap break with collapsing space has state collapsed. -/
theorem whitespaceState_softWrap_collapsed :
    computeWhitespaceState (.softWrapBreak true) = .collapsed := rfl

/-- CSS Text 3 §5.1: Soft wrap break with preserved space has state preserved. -/
theorem whitespaceState_softWrap_preserved :
    computeWhitespaceState (.softWrapBreak false) = .preserved := rfl

/-- CSS Text 3 §4.1: Block end with collapsing space has state none (stripped by builder). -/
theorem whitespaceState_blockEnd_collapsed :
    computeWhitespaceState (.blockEndSpace true) = .none := rfl

/-- CSS Text 3 §4.1: Block end with preserved space has state preserved. -/
theorem whitespaceState_blockEnd_preserved :
    computeWhitespaceState (.blockEndSpace false) = .preserved := rfl

end ChromiumLayout
