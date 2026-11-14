/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineBreakCandidate

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-!
# Tests for Line Break Candidate Opportunities

Corresponds to `core/layout/inline/line_break_candidate_test.cc`.
-/

/-! ### Test 1: Text (`line_break_candidate_test.cc:50`) -/
def target_Text : List IndexedInlineToken :=
  [ ⟨0, .text "01 345"⟩ ]

theorem lineBreak_Text :
    computeLineBreakCandidates target_Text =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 3 }, endOffset := { itemIndex := 0, textOffset := 2 }, posNoBreak := 30, posIfBreak := 20 },
        { offset := { itemIndex := 0, textOffset := 6 }, endOffset := { itemIndex := 0, textOffset := 6 }, posNoBreak := 60, posIfBreak := 60 } ] := by
  decide

/-! ### Test 2: SoftHyphen (`line_break_candidate_test.cc:76`) -/
def target_SoftHyphen : List IndexedInlineToken :=
  [ ⟨0, .text "01\u00AD345\u00AD7890\u00AD"⟩ ]

theorem lineBreak_SoftHyphen :
    computeLineBreakCandidates target_SoftHyphen =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 3 }, endOffset := { itemIndex := 0, textOffset := 3 }, posNoBreak := 20, posIfBreak := 30, isHyphenated := true },
        { offset := { itemIndex := 0, textOffset := 7 }, endOffset := { itemIndex := 0, textOffset := 7 }, posNoBreak := 50, posIfBreak := 60, isHyphenated := true },
        { offset := { itemIndex := 0, textOffset := 12 }, endOffset := { itemIndex := 0, textOffset := 12 }, posNoBreak := 90, posIfBreak := 90 } ] := by
  decide

/-! ### Test 3: SoftHyphenDisabled (`line_break_candidate_test.cc:104`) -/
def target_SoftHyphenDisabled : List IndexedInlineToken :=
  [ ⟨0, .text "01\u00AD345\u00AD7890"⟩ ]

theorem lineBreak_SoftHyphenDisabled :
    computeLineBreakCandidates target_SoftHyphenDisabled .none =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 11 }, endOffset := { itemIndex := 0, textOffset := 11 }, posNoBreak := 90, posIfBreak := 90 } ] := by
  decide

/-! ### Test 4: Span (`line_break_candidate_test.cc:130`) -/
def target_Span : List IndexedInlineToken :=
  [ ⟨0, .text "01 "⟩,
    ⟨1, .openTag "span"⟩,
    ⟨2, .text "345"⟩,
    ⟨3, .closeTag⟩,
    ⟨4, .text " 7890"⟩ ]

theorem lineBreak_Span :
    computeLineBreakCandidates target_Span =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 3 }, endOffset := { itemIndex := 0, textOffset := 2 }, posNoBreak := 30, posIfBreak := 20 },
        { offset := { itemIndex := 4, textOffset := 7 }, endOffset := { itemIndex := 2, textOffset := 6 }, posNoBreak := 70, posIfBreak := 60 },
        { offset := { itemIndex := 4, textOffset := 11 }, endOffset := { itemIndex := 4, textOffset := 11 }, posNoBreak := 110, posIfBreak := 110 } ] := by
  decide

/-! ### Test 5: SpanMidWord (`line_break_candidate_test.cc:157`) -/
def target_SpanMidWord : List IndexedInlineToken :=
  [ ⟨0, .text "0"⟩,
    ⟨1, .openTag "span"⟩,
    ⟨2, .text "12"⟩,
    ⟨3, .closeTag⟩,
    ⟨4, .text "345 7890"⟩ ]

theorem lineBreak_SpanMidWord :
    computeLineBreakCandidates target_SpanMidWord =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 4, textOffset := 7 }, endOffset := { itemIndex := 4, textOffset := 6 }, posNoBreak := 70, posIfBreak := 60 },
        { offset := { itemIndex := 4, textOffset := 11 }, endOffset := { itemIndex := 4, textOffset := 11 }, posNoBreak := 110, posIfBreak := 110 } ] := by
  decide

/-! ### Test 6: SpanCloseAfterSpace (`line_break_candidate_test.cc:183`) -/
def target_SpanCloseAfterSpace : List IndexedInlineToken :=
  [ ⟨0, .text "01 "⟩,
    ⟨1, .openTag "span"⟩,
    ⟨2, .text "345 "⟩,
    ⟨3, .closeTag⟩,
    ⟨4, .text "7890"⟩ ]

theorem lineBreak_SpanCloseAfterSpace :
    computeLineBreakCandidates target_SpanCloseAfterSpace =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 3 }, endOffset := { itemIndex := 0, textOffset := 2 }, posNoBreak := 30, posIfBreak := 20 },
        { offset := { itemIndex := 4, textOffset := 7 }, endOffset := { itemIndex := 2, textOffset := 6 }, posNoBreak := 70, posIfBreak := 60 },
        { offset := { itemIndex := 4, textOffset := 11 }, endOffset := { itemIndex := 4, textOffset := 11 }, posNoBreak := 110, posIfBreak := 110 } ] := by
  decide

/-! ### Test 7: OutOfFlowPositioned (`line_break_candidate_test.cc:368`) -/
def target_OutOfFlowPositioned : List IndexedInlineToken :=
  [ ⟨0, .text "012 456 89 012 456 89 01"⟩,
    ⟨1, .openTag "span"⟩,
    ⟨2, .closeTag⟩ ]

theorem lineBreak_OutOfFlowPositioned :
    computeLineBreakCandidates target_OutOfFlowPositioned =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 4 }, endOffset := { itemIndex := 0, textOffset := 3 }, posNoBreak := 40, posIfBreak := 30 },
        { offset := { itemIndex := 0, textOffset := 8 }, endOffset := { itemIndex := 0, textOffset := 7 }, posNoBreak := 80, posIfBreak := 70 },
        { offset := { itemIndex := 0, textOffset := 11 }, endOffset := { itemIndex := 0, textOffset := 10 }, posNoBreak := 110, posIfBreak := 100 },
        { offset := { itemIndex := 0, textOffset := 15 }, endOffset := { itemIndex := 0, textOffset := 14 }, posNoBreak := 150, posIfBreak := 140 },
        { offset := { itemIndex := 0, textOffset := 19 }, endOffset := { itemIndex := 0, textOffset := 18 }, posNoBreak := 190, posIfBreak := 180 },
        { offset := { itemIndex := 0, textOffset := 22 }, endOffset := { itemIndex := 0, textOffset := 21 }, posNoBreak := 220, posIfBreak := 210 },
        { offset := { itemIndex := 2, textOffset := 24 }, endOffset := { itemIndex := 2, textOffset := 24 }, posNoBreak := 240, posIfBreak := 240 } ] := by
  decide

/-! ### Test 8: ForcedBreak (`line_break_candidate_test.cc:339`) -/
def target_ForcedBreak : List IndexedInlineToken :=
  [ ⟨0, .text "01 345"⟩,
    ⟨1, .br⟩,
    ⟨2, .text "01 3456"⟩,
    ⟨3, .br⟩ ]

/-- Test `LineBreakCandidateTest.ForcedBreak` (`inline/line_break_candidate_test.cc:339`).
    CSS Text 3 §4: Forced breaks (<br>) create unconditional candidates with posIfBreak = posNoBreak. -/
theorem lineBreak_ForcedBreak :
    computeLineBreakCandidates target_ForcedBreak =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 3 }, endOffset := { itemIndex := 0, textOffset := 2 }, posNoBreak := 30, posIfBreak := 20 },
        { offset := { itemIndex := 1, textOffset := 7 }, endOffset := { itemIndex := 0, textOffset := 6 }, posNoBreak := 60, posIfBreak := 60 },
        { offset := { itemIndex := 2, textOffset := 10 }, endOffset := { itemIndex := 2, textOffset := 9 }, posNoBreak := 90, posIfBreak := 80 },
        { offset := { itemIndex := 3, textOffset := 15 }, endOffset := { itemIndex := 2, textOffset := 14 }, posNoBreak := 130, posIfBreak := 130 } ] := by
  decide

/-! ### Test 9: AtomicInlineBr (`line_break_candidate_test.cc:276`) -/
def target_AtomicInlineBr : List IndexedInlineToken :=
  [ ⟨0, .atomicInline 10⟩,
    ⟨1, .closeTag⟩,
    ⟨2, .br⟩ ]

/-- Test `LineBreakCandidateTest.AtomicInlineBr` (`inline/line_break_candidate_test.cc:276`).
    CSS Text 3 §4 & CSS 2.1 §9.5.1: Atomic inline followed by <br> produces forced break candidate. -/
theorem lineBreak_AtomicInlineBr :
    computeLineBreakCandidates target_AtomicInlineBr =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 2, textOffset := 2 }, endOffset := { itemIndex := 1, textOffset := 1 }, posNoBreak := 10, posIfBreak := 10 } ] := by
  decide

/-! ### Test 10: AtomicInlineTrailingSpaces (`line_break_candidate_test.cc:307`) -/
def target_AtomicInlineTrailingSpaces : List IndexedInlineToken :=
  [ ⟨0, .openTag "span"⟩,
    ⟨1, .atomicInline 10⟩,
    ⟨2, .closeTag⟩,
    ⟨3, .text " "⟩,
    ⟨4, .openTag "span"⟩,
    ⟨5, .text "23"⟩,
    ⟨7, .closeTag⟩ ]

/-- Test `LineBreakCandidateTest.AtomicInlineTrailingSpaces` (`inline/line_break_candidate_test.cc:307`).
    CSS Text 3 §4.1: Whitespace between atomic inline and text produces soft wrap opportunity. -/
theorem lineBreak_AtomicInlineTrailingSpaces :
    computeLineBreakCandidates target_AtomicInlineTrailingSpaces =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 3, textOffset := 2 }, endOffset := { itemIndex := 2, textOffset := 1 }, posNoBreak := 20, posIfBreak := 10 },
        { offset := { itemIndex := 7, textOffset := 4 }, endOffset := { itemIndex := 7, textOffset := 4 }, posNoBreak := 40, posIfBreak := 40 } ] := by
  decide

/-! ### Test 11: TrailingSpacesCollapsed (`line_break_candidate_test.cc:210`) -/
def target_TrailingSpacesCollapsed : List IndexedInlineToken :=
  [ ⟨0, .text "012 "⟩,
    ⟨1, .openTag "span"⟩,
    ⟨3, .closeTag⟩,
    ⟨4, .text "456"⟩ ]

/-- Test `LineBreakCandidateTest.TrailingSpacesCollapsed` (`inline/line_break_candidate_test.cc:210`).
    CSS Text 3 §4.1 & §5.2: Boundary sentinels emitted under constrained available width. -/
theorem lineBreak_TrailingSpacesCollapsed :
    (computeLineBreakCandidates target_TrailingSpacesCollapsed =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 4 }, endOffset := { itemIndex := 0, textOffset := 3 }, posNoBreak := 40, posIfBreak := 30 },
        { offset := { itemIndex := 4, textOffset := 7 }, endOffset := { itemIndex := 4, textOffset := 7 }, posNoBreak := 70, posIfBreak := 70 } ]) ∧
    (computeLineBreakCandidates target_TrailingSpacesCollapsed .auto 10 (some 50) =
      [ { offset := { itemIndex := 0, textOffset := 0 }, endOffset := { itemIndex := 0, textOffset := 0 }, posNoBreak := 0, posIfBreak := 0 },
        { offset := { itemIndex := 0, textOffset := 4 }, endOffset := { itemIndex := 0, textOffset := 3 }, posNoBreak := 40, posIfBreak := 30 },
        { offset := { itemIndex := 4, textOffset := 4 }, endOffset := { itemIndex := 0, textOffset := 3 }, posNoBreak := 40, posIfBreak := 30 },
        { offset := { itemIndex := 4, textOffset := 7 }, endOffset := { itemIndex := 4, textOffset := 7 }, posNoBreak := 70, posIfBreak := 70 } ]) := by
  decide

end ChromiumLayout.TestsInline
