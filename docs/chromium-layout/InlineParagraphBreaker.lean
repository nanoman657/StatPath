/-
  docs/chromium-layout/InlineParagraphBreaker.lean

  Formal model for CSS Text 4 §5.3 / §5.4 paragraph line breaking
  (`text-wrap: balance` and `text-wrap: pretty`) and Blink ParagraphLineBreaker
  (`third_party/blink/renderer/core/layout/inline/paragraph_line_breaker.h`,
   `paragraph_line_breaker.cc`,
   `inline_node_data.h`,
   `inline_items_builder.cc`).
-/
import LayoutTypes

namespace ChromiumLayout

/-! ## 1. Paragraph Features and Advanced Line Breaking Suitability -/

/-- CSS Text 4 §5.3, §5.4 & Blink InlineNodeData:
    Features of an inline formatting context that determine suitability for
    bisection paragraph line balancing (`text-wrap: balance`) and
    optimal score line breaking (`text-wrap: pretty`). -/
structure ParagraphFeatures where
  hasBlockInInline : Bool := false
  hasFloat : Bool := false
  hasForcedBreak : Bool := false
  hasInitialLetter : Bool := false
  hasTabulation : Bool := false
  hasFirstLineStyle : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 4 §5.3 & Blink InlineNode::IsBisectLineBreakDisabled:
    Bisection line balancing (text-wrap: balance) requires a single contiguous logical paragraph
    with constant available width across lines. It is disabled by:
    - Block-in-inline (divides into separate blocks)
    - Floats (indents lines non-uniformly)
    - Forced line breaks (divides paragraph into multiple lines)
    - Initial letter boxes (intrudes across multiple lines). -/
def isBisectLineBreakDisabled (f : ParagraphFeatures) : Bool :=
  f.hasBlockInInline || f.hasFloat || f.hasForcedBreak || f.hasInitialLetter

/-- CSS Text 4 §5.4 & Blink InlineNode::IsScoreLineBreakDisabled:
    Knuth-Plass score line breaking (text-wrap: pretty) is disabled by:
    - Initial letter boxes (intrudes across multiple lines)
    - Tabulation characters (non-uniform tab stop widths)
    - First-line pseudo-element style changes. -/
def isScoreLineBreakDisabled (f : ParagraphFeatures) : Bool :=
  f.hasInitialLetter || f.hasTabulation || f.hasFirstLineStyle

/-- CSS Text 4 §5.3 & Blink ParagraphLineBreaker::AttemptParagraphBalancing:
    Attempts binary search balancing for text-wrap: balance.
    Fails (returns false) if bisection is disabled by paragraph features. -/
def attemptParagraphBalancing (f : ParagraphFeatures) : Bool :=
  !isBisectLineBreakDisabled f

/-! ## 2. General Laws for Paragraph Line Breaking Suitability -/

/-- CSS Text 4 §5.3 & §5.4 Law: Initial letter boxes disable both bisection balancing and score line breaking. -/
theorem initial_letter_disables_both (f : ParagraphFeatures) (h : f.hasInitialLetter = true) :
    isBisectLineBreakDisabled f = true ∧ isScoreLineBreakDisabled f = true := by
  constructor
  · unfold isBisectLineBreakDisabled
    simp [h]
  · unfold isScoreLineBreakDisabled
    simp [h]

/-- CSS Text 4 §5.3 Law: Paragraph balancing succeeds if and only if bisection line breaking is not disabled. -/
theorem balancing_iff_bisect_not_disabled (f : ParagraphFeatures) :
    attemptParagraphBalancing f = true ↔ isBisectLineBreakDisabled f = false := by
  unfold attemptParagraphBalancing
  simp

/-- CSS Text 4 §5.3 Law: Block-in-inline always disables paragraph balancing for all inputs. -/
theorem block_in_inline_disables_balancing (f : ParagraphFeatures) (h : f.hasBlockInInline = true) :
    attemptParagraphBalancing f = false := by
  unfold attemptParagraphBalancing isBisectLineBreakDisabled
  simp [h]

/-- CSS Text 4 §5.3 Law: Floats always disable paragraph balancing for all inputs. -/
theorem float_disables_balancing (f : ParagraphFeatures) (h : f.hasFloat = true) :
    attemptParagraphBalancing f = false := by
  unfold attemptParagraphBalancing isBisectLineBreakDisabled
  simp [h]

/-- CSS Text 4 §5.3 Law: Forced breaks always disable paragraph balancing for all inputs. -/
theorem forced_break_disables_balancing (f : ParagraphFeatures) (h : f.hasForcedBreak = true) :
    attemptParagraphBalancing f = false := by
  unfold attemptParagraphBalancing isBisectLineBreakDisabled
  simp [h]

/-- CSS Text 4 §5.3 Law: Clean paragraphs without block-in-inline, floats, forced breaks, or initial letters allow bisection balancing even with tabs. -/
theorem tabulation_preserves_bisect (f : ParagraphFeatures)
    (hb : f.hasBlockInInline = false) (hfl : f.hasFloat = false)
    (hfb : f.hasForcedBreak = false) (hi : f.hasInitialLetter = false) :
    isBisectLineBreakDisabled f = false := by
  unfold isBisectLineBreakDisabled
  simp [hb, hfl, hfb, hi]

/-- CSS Text 4 §5.4 Law: Tabulation characters always disable score line breaking for all inputs. -/
theorem tabulation_disables_score_breaking (f : ParagraphFeatures) (h : f.hasTabulation = true) :
    isScoreLineBreakDisabled f = true := by
  unfold isScoreLineBreakDisabled
  simp [h]

end ChromiumLayout
