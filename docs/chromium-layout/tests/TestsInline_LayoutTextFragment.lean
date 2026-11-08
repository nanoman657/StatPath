/-
  docs/chromium-layout/tests/TestsInline_LayoutTextFragment.lean

  Formalized layout tests for LayoutTextFragment
  (`third_party/blink/renderer/core/layout/layout_text_fragment_test.cc`).

  Covers:
  - Basics (`layout_text_fragment_test.cc:47`)
  - CaretMinMaxOffset (`layout_text_fragment_test.cc:81`)
  - CaretMinMaxOffsetCollapsedRemainingText (`layout_text_fragment_test.cc:133`)
  - ResolvedTextLength (`layout_text_fragment_test.cc:151`)
  - ResolvedTextLengthSpacesInBetween (`layout_text_fragment_test.cc:169`)
  - ResolvedTextLengthCollapsedRemainingText (`layout_text_fragment_test.cc:187`)
  - ContainsCaretOffset (`layout_text_fragment_test.cc:197`)
  - ContainsCaretOffsetSpacesInBetween (`layout_text_fragment_test.cc:244`)
  - ContainsCaretOffsetPre (`layout_text_fragment_test.cc:258`)
  - ContainsCaretOffsetPreLine (`layout_text_fragment_test.cc:273`)
  - IsBeforeAfterNonCollapsedCharacterNoLineWrap (`layout_text_fragment_test.cc:288`)
-/
import LayoutTypes
import LayoutInline
import InlineItemBuilder
import InlineOffsetMapping
import InlineFirstLetter

namespace ChromiumLayout

/-! ## 1. Basics (`layout_text_fragment_test.cc:47`) -/

/-- Test `LayoutTextFragmentTest, Basics` (`layout_text_fragment_test.cc:47`).
    Basic caret offset and resolved text length for first-letter and remaining text. -/
theorem layoutTextFragment_basics :
    let s := "foo"
    let u := buildDomOffsetMapping [DomNode.text 0 s .normal]
    let (firstLetter, remainingText) := splitFirstLetter s
    (fragmentCaretMinOffset u firstLetter = 0) ∧
    (fragmentCaretMaxOffset u firstLetter = 1) ∧
    (fragmentResolvedTextLength u firstLetter = 1) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 0 = true) ∧
    (fragmentCaretMinOffset u remainingText = 0) ∧
    (fragmentCaretMaxOffset u remainingText = 2) ∧
    (fragmentResolvedTextLength u remainingText = 2) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 0 = true) := by
  decide

/-! ## 2. CaretMinMaxOffset (`layout_text_fragment_test.cc:81`) -/

/-- Test `LayoutTextFragmentTest, CaretMinMaxOffset` (`layout_text_fragment_test.cc:81`).
    Caret min/max offset queries with punctuation and surrounding whitespace. -/
theorem layoutTextFragment_caretMinMaxOffset :
    let s1 := "(f)oo"
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "  (f)oo"
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (f2, r2) := splitFirstLetter s2
    let s3 := "(f)oo  "
    let u3 := buildDomOffsetMapping [DomNode.text 0 s3 .normal]
    let (f3, r3) := splitFirstLetter s3
    let s4 := " (f)oo  "
    let u4 := buildDomOffsetMapping [DomNode.text 0 s4 .normal]
    let (f4, r4) := splitFirstLetter s4
    (fragmentCaretMinOffset u1 f1 = 0) ∧
    (fragmentCaretMaxOffset u1 f1 = 3) ∧
    (fragmentCaretMinOffset u1 r1 = 0) ∧
    (fragmentCaretMaxOffset u1 r1 = 2) ∧
    (fragmentCaretMinOffset u2 f2 = 2) ∧
    (fragmentCaretMaxOffset u2 f2 = 5) ∧
    (fragmentCaretMinOffset u2 r2 = 0) ∧
    (fragmentCaretMaxOffset u2 r2 = 2) ∧
    (fragmentCaretMinOffset u3 f3 = 0) ∧
    (fragmentCaretMaxOffset u3 f3 = 3) ∧
    (fragmentCaretMinOffset u3 r3 = 0) ∧
    (fragmentCaretMaxOffset u3 r3 = 2) ∧
    (fragmentCaretMinOffset u4 f4 = 1) ∧
    (fragmentCaretMaxOffset u4 f4 = 4) ∧
    (fragmentCaretMinOffset u4 r4 = 0) ∧
    (fragmentCaretMaxOffset u4 r4 = 2) := by
  decide

/-! ## 3. CaretMinMaxOffsetCollapsedRemainingText (`layout_text_fragment_test.cc:133`) -/

/-- Test `LayoutTextFragmentTest, CaretMinMaxOffsetCollapsedRemainingText` (`layout_text_fragment_test.cc:133`).
    When remaining text is fully collapsed, CaretMin/MaxOffset return 0 and fragment length. -/
theorem layoutTextFragment_caretMinMaxOffsetCollapsedRemainingText :
    let s1 := "(f)  "
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "  (f)  "
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (f2, r2) := splitFirstLetter s2
    (fragmentCaretMinOffset u1 f1 = 0) ∧
    (fragmentCaretMaxOffset u1 f1 = 3) ∧
    (fragmentCaretMinOffset u1 r1 = 0) ∧
    (fragmentCaretMaxOffset u1 r1 = 2) ∧
    (fragmentCaretMinOffset u2 f2 = 2) ∧
    (fragmentCaretMaxOffset u2 f2 = 5) ∧
    (fragmentCaretMinOffset u2 r2 = 0) ∧
    (fragmentCaretMaxOffset u2 r2 = 2) := by
  decide

/-! ## 4. ResolvedTextLength (`layout_text_fragment_test.cc:151`) -/

/-- Test `LayoutTextFragmentTest, ResolvedTextLength` (`layout_text_fragment_test.cc:151`).
    Resolved text length for first-letter and remaining text with punctuation and whitespace. -/
theorem layoutTextFragment_resolvedTextLength :
    let s1 := "(f)oo"
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "  (f)oo"
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (f2, r2) := splitFirstLetter s2
    let s3 := "(f)oo  "
    let u3 := buildDomOffsetMapping [DomNode.text 0 s3 .normal]
    let (f3, r3) := splitFirstLetter s3
    let s4 := " (f)oo  "
    let u4 := buildDomOffsetMapping [DomNode.text 0 s4 .normal]
    let (f4, r4) := splitFirstLetter s4
    (fragmentResolvedTextLength u1 f1 = 3) ∧
    (fragmentResolvedTextLength u1 r1 = 2) ∧
    (fragmentResolvedTextLength u2 f2 = 3) ∧
    (fragmentResolvedTextLength u2 r2 = 2) ∧
    (fragmentResolvedTextLength u3 f3 = 3) ∧
    (fragmentResolvedTextLength u3 r3 = 2) ∧
    (fragmentResolvedTextLength u4 f4 = 3) ∧
    (fragmentResolvedTextLength u4 r4 = 2) := by
  decide

/-! ## 5. ResolvedTextLengthSpacesInBetween (`layout_text_fragment_test.cc:169`) -/

/-- Test `LayoutTextFragmentTest, ResolvedTextLengthSpacesInBetween` (`layout_text_fragment_test.cc:169`).
    Multiple spaces between first-letter and remaining text collapse to a single space. -/
theorem layoutTextFragment_resolvedTextLengthSpacesInBetween :
    let s1 := "(f)  oo"
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "  (f)  oo"
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (f2, r2) := splitFirstLetter s2
    let s3 := "(f)  oo  "
    let u3 := buildDomOffsetMapping [DomNode.text 0 s3 .normal]
    let (f3, r3) := splitFirstLetter s3
    let s4 := " (f)  oo  "
    let u4 := buildDomOffsetMapping [DomNode.text 0 s4 .normal]
    let (f4, r4) := splitFirstLetter s4
    (fragmentResolvedTextLength u1 f1 = 3) ∧
    (fragmentResolvedTextLength u1 r1 = 3) ∧
    (fragmentResolvedTextLength u2 f2 = 3) ∧
    (fragmentResolvedTextLength u2 r2 = 3) ∧
    (fragmentResolvedTextLength u3 f3 = 3) ∧
    (fragmentResolvedTextLength u3 r3 = 3) ∧
    (fragmentResolvedTextLength u4 f4 = 3) ∧
    (fragmentResolvedTextLength u4 r4 = 3) := by
  decide

/-! ## 6. ResolvedTextLengthCollapsedRemainingText (`layout_text_fragment_test.cc:187`) -/

/-- Test `LayoutTextFragmentTest, ResolvedTextLengthCollapsedRemainingText` (`layout_text_fragment_test.cc:187`).
    Fully collapsed remaining text has resolved text length 0. -/
theorem layoutTextFragment_resolvedTextLengthCollapsedRemainingText :
    let s1 := "(f)  "
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "  (f)  "
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (f2, r2) := splitFirstLetter s2
    (fragmentResolvedTextLength u1 f1 = 3) ∧
    (fragmentResolvedTextLength u1 r1 = 0) ∧
    (fragmentResolvedTextLength u2 f2 = 3) ∧
    (fragmentResolvedTextLength u2 r2 = 0) := by
  decide

/-! ## 7. ContainsCaretOffset (`layout_text_fragment_test.cc:197`) -/

/-- Test `LayoutTextFragmentTest, ContainsCaretOffset` (`layout_text_fragment_test.cc:197`).
    Caret offset membership across whitespace collapsed first-letter and remaining text. -/
theorem layoutTextFragment_containsCaretOffset :
    let s1 := "(f)oo"
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "  (f)oo"
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (f2, r2) := splitFirstLetter s2
    let s3 := "(f)oo  "
    let u3 := buildDomOffsetMapping [DomNode.text 0 s3 .normal]
    let (f3, r3) := splitFirstLetter s3
    let s4 := " (f)oo  "
    let u4 := buildDomOffsetMapping [DomNode.text 0 s4 .normal]
    let (f4, r4) := splitFirstLetter s4
    (fragmentContainsCaretOffset u1 s1.toList f1 0 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList f1 1 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList f1 2 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList f1 3 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList f1 4 = false) ∧
    (fragmentContainsCaretOffset u1 s1.toList r1 0 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList r1 1 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList r1 2 = true) ∧
    (fragmentContainsCaretOffset u1 s1.toList r1 3 = false) ∧
    (fragmentContainsCaretOffset u2 s2.toList f2 0 = false) ∧
    (fragmentContainsCaretOffset u2 s2.toList f2 1 = false) ∧
    (fragmentContainsCaretOffset u2 s2.toList f2 2 = true) ∧
    (fragmentContainsCaretOffset u2 s2.toList f2 3 = true) ∧
    (fragmentContainsCaretOffset u2 s2.toList f2 4 = true) ∧
    (fragmentContainsCaretOffset u2 s2.toList f2 5 = true) ∧
    (fragmentContainsCaretOffset u2 s2.toList r2 0 = true) ∧
    (fragmentContainsCaretOffset u2 s2.toList r2 1 = true) ∧
    (fragmentContainsCaretOffset u2 s2.toList r2 2 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList f3 0 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList f3 1 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList f3 2 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList f3 3 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList r3 0 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList r3 1 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList r3 2 = true) ∧
    (fragmentContainsCaretOffset u3 s3.toList r3 3 = false) ∧
    (fragmentContainsCaretOffset u3 s3.toList r3 4 = false) ∧
    (fragmentContainsCaretOffset u4 s4.toList f4 0 = false) ∧
    (fragmentContainsCaretOffset u4 s4.toList f4 1 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList f4 2 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList f4 3 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList f4 4 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList r4 0 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList r4 1 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList r4 2 = true) ∧
    (fragmentContainsCaretOffset u4 s4.toList r4 3 = false) ∧
    (fragmentContainsCaretOffset u4 s4.toList r4 4 = false) := by
  decide

/-! ## 8. ContainsCaretOffsetSpacesInBetween (`layout_text_fragment_test.cc:244`) -/

/-- Test `LayoutTextFragmentTest, ContainsCaretOffsetSpacesInBetween` (`layout_text_fragment_test.cc:244`).
    Caret offset membership across consecutive spaces between fragments. -/
theorem layoutTextFragment_containsCaretOffsetSpacesInBetween :
    let s := "(f)   oo"
    let u := buildDomOffsetMapping [DomNode.text 0 s .normal]
    let (firstLetter, remainingText) := splitFirstLetter s
    (fragmentContainsCaretOffset u s.toList firstLetter 0 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 1 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 2 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 3 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 0 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 1 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 2 = false) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 3 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 4 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 5 = true) := by
  decide

/-! ## 9. ContainsCaretOffsetPre (`layout_text_fragment_test.cc:258`) -/

/-- Test `LayoutTextFragmentTest, ContainsCaretOffsetPre` (`layout_text_fragment_test.cc:258`).
    Caret offset membership under white-space: pre preserving spaces and terminating at newline. -/
theorem layoutTextFragment_containsCaretOffsetPre :
    let s := "(f)   oo\n"
    let u := buildDomOffsetMapping [DomNode.text 0 s .pre]
    let (firstLetter, remainingText) := splitFirstLetter s
    (fragmentContainsCaretOffset u s.toList firstLetter 0 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 1 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 2 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 3 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 0 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 1 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 2 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 3 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 4 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 5 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 6 = false) := by
  decide

/-! ## 10. ContainsCaretOffsetPreLine (`layout_text_fragment_test.cc:273`) -/

/-- Test `LayoutTextFragmentTest, ContainsCaretOffsetPreLine` (`layout_text_fragment_test.cc:273`).
    Caret offset membership under white-space: pre-line collapsing spaces before newline. -/
theorem layoutTextFragment_containsCaretOffsetPreLine :
    let s := "F \n \noo"
    let u := buildDomOffsetMapping [DomNode.text 0 s .preLine]
    let (firstLetter, remainingText) := splitFirstLetter s
    (fragmentContainsCaretOffset u s.toList firstLetter 0 = true) ∧
    (fragmentContainsCaretOffset u s.toList firstLetter 1 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 0 = false) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 1 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 2 = false) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 3 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 4 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 5 = true) ∧
    (fragmentContainsCaretOffset u s.toList remainingText 6 = true) := by
  decide

/-! ## 11. IsBeforeAfterNonCollapsedCharacterNoLineWrap (`layout_text_fragment_test.cc:288`) -/

/-- Test `LayoutTextFragmentTest, IsBeforeAfterNonCollapsedCharacterNoLineWrap` (`layout_text_fragment_test.cc:288`).
    Before/after non-collapsed character queries across first-letter and remaining text fragments. -/
theorem layoutTextFragment_isBeforeAfterNonCollapsedCharacterNoLineWrap :
    let s1 := "foo"
    let u1 := buildDomOffsetMapping [DomNode.text 0 s1 .normal]
    let (f1, r1) := splitFirstLetter s1
    let s2 := "f   bar"
    let u2 := buildDomOffsetMapping [DomNode.text 0 s2 .normal]
    let (_, r2) := splitFirstLetter s2
    let s3 := "  foo"
    let u3 := buildDomOffsetMapping [DomNode.text 0 s3 .normal]
    let (f3, _) := splitFirstLetter s3
    let s4 := "foo  "
    let u4 := buildDomOffsetMapping [DomNode.text 0 s4 .normal]
    let (_, r4) := splitFirstLetter s4
    -- Basics
    (fragmentIsBeforeNonCollapsed u1 f1 0 = true) ∧
    (fragmentIsAfterNonCollapsed u1 f1 1 = true) ∧
    (fragmentIsBeforeNonCollapsed u1 r1 0 = true) ∧
    (fragmentIsAfterNonCollapsed u1 r1 2 = true) ∧
    (fragmentIsAfterNonCollapsed u1 f1 0 = false) ∧
    (fragmentIsBeforeNonCollapsed u1 f1 1 = false) ∧
    (fragmentIsAfterNonCollapsed u1 r1 0 = false) ∧
    (fragmentIsBeforeNonCollapsed u1 r1 2 = false) ∧
    -- Consecutive spaces between first letter and remaining text
    (fragmentIsBeforeNonCollapsed u2 r2 0 = true) ∧
    (fragmentIsBeforeNonCollapsed u2 r2 1 = false) ∧
    (fragmentIsBeforeNonCollapsed u2 r2 2 = false) ∧
    (fragmentIsAfterNonCollapsed u2 r2 1 = true) ∧
    (fragmentIsAfterNonCollapsed u2 r2 2 = false) ∧
    (fragmentIsAfterNonCollapsed u2 r2 3 = false) ∧
    -- Leading spaces in first letter are collapsed
    (fragmentIsBeforeNonCollapsed u3 f3 0 = false) ∧
    (fragmentIsBeforeNonCollapsed u3 f3 1 = false) ∧
    (fragmentIsAfterNonCollapsed u3 f3 1 = false) ∧
    (fragmentIsAfterNonCollapsed u3 f3 2 = false) ∧
    -- Trailing spaces in remaining text are collapsed
    (fragmentIsBeforeNonCollapsed u4 r4 2 = false) ∧
    (fragmentIsBeforeNonCollapsed u4 r4 3 = false) ∧
    (fragmentIsAfterNonCollapsed u4 r4 3 = false) ∧
    (fragmentIsAfterNonCollapsed u4 r4 4 = false) := by
  decide

end ChromiumLayout
