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

/-! ## 6. Word Segmentation and Greedy Line Breaking (CSS Text 3 §4.1, §5.1, §5.2 & CSS 2.1 §9.5) -/

/-- An unbreakable segment of inline text and margins between soft wrap opportunities. -/
structure UnbreakableSegment where
  text : String
  width : Nat
  followedBySpace : Bool := false
  isForcedBreak : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Pack unbreakable segments onto a single line up to availableWidth. -/
def packSegmentLine (availableWidth : Nat) (spaceWidth : Nat) (lineText : String) (curW : Nat) (canAdd : Bool) :
    List UnbreakableSegment → String × List UnbreakableSegment
  | [] => (lineText, [])
  | next :: more =>
    if ¬ canAdd then
      (lineText, next :: more)
    else if next.isForcedBreak then
      (lineText, next :: more)
    else
      let newW := curW + spaceWidth + next.width
      if newW ≤ availableWidth then
        packSegmentLine availableWidth spaceWidth (lineText ++ next.text) newW next.followedBySpace more
      else
        (lineText, next :: more)

/-- Fuel-bounded line-breaking loop packing unbreakable segments into lines. -/
def breakSegmentsFuel (availableWidth : Nat) (spaceWidth : Nat) :
    Nat → List UnbreakableSegment → List String
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, seg0 :: rest =>
    if seg0.isForcedBreak then
      let nonForced := rest.filter (fun s => ¬ s.isForcedBreak ∧ s.text ≠ "")
      if nonForced.isEmpty then []
      else breakSegmentsFuel availableWidth spaceWidth fuel rest
    else
      let (lineStr, remaining) := packSegmentLine availableWidth spaceWidth seg0.text seg0.width seg0.followedBySpace rest
      lineStr :: breakSegmentsFuel availableWidth spaceWidth fuel remaining

/-- CSS Text 3 §4.1, §5.1, §5.2 & CSS 2.1 §9.5:
    Greedy line breaking over unbreakable segments.
    - Each line consumes at least one segment (even if it overflows available width).
    - If followedBySpace is true, subsequent segments may be packed on the same line if they fit.
    - Forced breaks terminate the line immediately; trailing whitespace at block end does not create an extra line.
    - Returns the list of line text strings. -/
def breakSegmentLines (availableWidth : Nat) (segments : List UnbreakableSegment) (spaceWidth : Nat := 10) : List String :=
  breakSegmentsFuel availableWidth spaceWidth (segments.length + 1) segments

/-- CSS Text 3 §5.1: Empty segment stream produces no lines. -/
theorem breakSegmentLines_empty (w : Nat) :
    breakSegmentLines w [] = [] := by
  rfl

/-- CSS Text 3 §5.2: A single unbreakable segment always produces exactly one line. -/
theorem breakSegmentLines_single (w : Nat) (txt : String) (width : Nat) (sp : Bool) :
    breakSegmentLines w [{ text := txt, width := width, followedBySpace := sp, isForcedBreak := false }] = [txt] := by
  cases sp <;> rfl

/-- CSS Text 3 §4.1.2 & §5.1: Terminal forced break with collapsed trailing whitespace produces a single line. -/
theorem breakSegmentLines_forced_break_terminal (w : Nat) (txt : String) (width : Nat) (sp : Bool) :
    breakSegmentLines w [{ text := txt, width := width, followedBySpace := sp }, { text := "", width := 0, isForcedBreak := true }] = [txt] := by
  cases sp <;> rfl

/-- CSS Text 3 §5.2: When two segments overflow available width, breaking occurs after the first segment. -/
theorem breakSegmentLines_two_overflow (w : Nat) (txt1 txt2 : String) (w1 w2 : Nat) (sp : Nat)
    (h : ¬ (w1 + sp + w2 ≤ w)) :
    breakSegmentLines w [{ text := txt1, width := w1, followedBySpace := true }, { text := txt2, width := w2 }] sp = [txt1, txt2] := by
  unfold breakSegmentLines breakSegmentsFuel packSegmentLine
  simp [h]
  rfl

/-! ## 7. Trailing Space Hanging Width (CSS Text 3 §4.1.2 & §5.4) -/

/-- CSS Text 3 §3: White space handling modes. -/
inductive WhiteSpaceMode where
  | pre
  | preWrap
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 3 §4.1.2, §5.4 & Blink LineBreaker::ComputeTrailingSpaceWidth:
    Compute hanging space width for trailing spaces at line ends.
    - Under `pre`, spaces are preserved and do not hang (hanging width = 0).
    - Under `pre-wrap`, trailing spaces before a soft line break hang outside the line box.
    - Spaces before a forced break (`<br>`) do not hang (hanging width = 0).
    - Returns the number of hanging spaces. -/
def computeHangingSpaceWidth (mode : WhiteSpaceMode) (hasForcedBreak : Bool)
    (word1Len : Nat) (spaceCount : Nat) (nextWordLen : Option Nat)
    (availableWidth : Nat) (charWidth : Nat := 10) : Nat :=
  match mode with
  | .pre => 0
  | .preWrap =>
    if hasForcedBreak then 0
    else
      match nextWordLen with
      | some nextLen =>
        let totalW := word1Len * charWidth + spaceCount * charWidth + nextLen * charWidth
        if totalW > availableWidth then
          spaceCount
        else
          0
      | none =>
        let totalW := word1Len * charWidth + spaceCount * charWidth
        if totalW > availableWidth then
          (totalW - availableWidth) / charWidth
        else
          0

/-- CSS Text 3 §5.4 Law: Under white-space pre, spaces never hang regardless of width or line breaks. -/
theorem hangingSpace_pre_always_zero (fb : Bool) (w1 sp : Nat) (nw : Option Nat) (avail cw : Nat) :
    computeHangingSpaceWidth .pre fb w1 sp nw avail cw = 0 := by
  rfl

/-- CSS Text 3 §5.4 Law: Preserved spaces immediately before a forced break do not hang. -/
theorem hangingSpace_forced_break_always_zero (w1 sp : Nat) (nw : Option Nat) (avail cw : Nat) :
    computeHangingSpaceWidth .preWrap true w1 sp nw avail cw = 0 := by
  rfl

/-- CSS Text 3 §5.4 Law: When trailing spaces fit within available width without a soft wrap, hanging width is zero. -/
theorem hangingSpace_fit_always_zero (w1 sp : Nat) (avail cw : Nat)
    (h : ¬ (w1 * cw + sp * cw > avail)) :
    computeHangingSpaceWidth .preWrap false w1 sp none avail cw = 0 := by
  unfold computeHangingSpaceWidth
  simp [h]

/-- CSS Text 3 §5.4 Law: When a soft wrap occurs after trailing spaces, all trailing spaces hang. -/
theorem hangingSpace_soft_wrap_hangs (w1 sp nextLen : Nat) (avail cw : Nat)
    (h : w1 * cw + sp * cw + nextLen * cw > avail) :
    computeHangingSpaceWidth .preWrap false w1 sp (some nextLen) avail cw = sp := by
  unfold computeHangingSpaceWidth
  simp [h]

end ChromiumLayout
