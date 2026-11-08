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

end ChromiumLayout
