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

end ChromiumLayout.TestsInline
