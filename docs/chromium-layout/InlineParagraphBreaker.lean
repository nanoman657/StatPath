/-
  docs/chromium-layout/InlineParagraphBreaker.lean

  Formal model for CSS Text 4 §5.3 / §5.4 paragraph line breaking
  (`text-wrap: balance` and `text-wrap: pretty`), CSS Ruby 1 §3 interaction,
  and Blink ParagraphLineBreaker & ScoreLineBreaker
  (`third_party/blink/renderer/core/layout/inline/paragraph_line_breaker.h`,
   `paragraph_line_breaker.cc`,
   `score_line_breaker.h`,
   `score_line_breaker.cc`,
   `inline_node_data.h`,
   `inline_items_builder.cc`).
-/
import LayoutTypes

namespace ChromiumLayout

/-! ## 1. Paragraph Features and Advanced Line Breaking Suitability -/

/-- CSS Text 4 §5.3, §5.4, CSS Ruby 1 §3 & Blink InlineNodeData:
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
  hasRuby : Bool := false
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

/-- CSS Text 4 §5.4, CSS Ruby 1 §3 & Blink InlineNode::IsScoreLineBreakDisabled:
    Knuth-Plass score line breaking (text-wrap: pretty) is disabled by:
    - Initial letter boxes (intrudes across multiple lines)
    - Tabulation characters (non-uniform tab stop widths)
    - First-line pseudo-element style changes
    - Ruby containers (paired base/annotation formatting). -/
def isScoreLineBreakDisabled (f : ParagraphFeatures) : Bool :=
  f.hasInitialLetter || f.hasTabulation || f.hasFirstLineStyle || f.hasRuby

/-- CSS Text 4 §5.3 & Blink ParagraphLineBreaker::AttemptParagraphBalancing:
    Attempts binary search balancing for text-wrap: balance.
    Fails (returns false) if bisection is disabled by paragraph features. -/
def attemptParagraphBalancing (f : ParagraphFeatures) : Bool :=
  !isBisectLineBreakDisabled f

/-! ## 2. CSS Text 4 §5.3 Paragraph Balancing Line Limits -/

/-- CSS Text 4 §5.3 & Blink ParagraphLineBreaker::kMaxLinesForBalance:
    UAs may limit line balancing for performance reasons (Blink limit is 6 lines).
    Paragraphs exceeding this line count fall back to standard greedy line breaking. -/
def maxLinesForBalance : Nat := 6

/-- CSS Text 4 §5.3: Whether paragraph balancing applies given line count. -/
def shouldBalanceParagraph (lineCount : Nat) (maxLines : Nat := maxLinesForBalance) : Bool :=
  lineCount ≤ maxLines

/-! ## 3. Score Line Breaker Runtime Constraints (CSS Text 4 §5.4 & CSS Text 3 §5.2) -/

/-- CSS Text 4 §5.4 & Blink LineBreaker::ShouldDisableScoreLineBreak:
    Runtime line breaking conditions that disable score line breaking (text-wrap: pretty):
    - Unresolved line overflow (CSS Text 3 §5.2)
    - white-space: break-spaces (CSS Text 3 §3)
    - box-decoration-break: clone (CSS Fragmentation 3 / CSS Inline 3). -/
structure LineBreakRuntimeFeatures where
  hasUnresolvedOverflow : Bool := false
  isBreakSpaces : Bool := false
  isBoxDecorationBreakClone : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Whether score line breaking is disabled by runtime line conditions. -/
def isScoreLineBreakDisabledByRuntime (rf : LineBreakRuntimeFeatures) : Bool :=
  rf.hasUnresolvedOverflow || rf.isBreakSpaces || rf.isBoxDecorationBreakClone

/-! ## 4. General Laws for Paragraph Line Breaking Suitability -/

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

/-- CSS Ruby 1 §3 Law: Ruby container elements always disable score line breaking for all inputs. -/
theorem ruby_disables_score_breaking (f : ParagraphFeatures) (h : f.hasRuby = true) :
    isScoreLineBreakDisabled f = true := by
  unfold isScoreLineBreakDisabled
  simp [h]

/-- CSS Text 4 §5.3 Law: Line count exceeding limit always disables balancing for all inputs. -/
theorem balance_exceeded_law (lines : Nat) (h : ¬ (lines ≤ maxLinesForBalance)) :
    shouldBalanceParagraph lines = false := by
  unfold shouldBalanceParagraph
  simp [h]

/-- CSS Text 4 §5.3 Law: Line count within limit always allows balancing for all inputs. -/
theorem balance_within_law (lines : Nat) (h : lines ≤ maxLinesForBalance) :
    shouldBalanceParagraph lines = true := by
  unfold shouldBalanceParagraph
  simp [h]

/-- CSS Text 3 §5.2 Law: Unresolved line overflow always disables score line breaking. -/
theorem runtime_overflow_disables_score_break (rf : LineBreakRuntimeFeatures) (h : rf.hasUnresolvedOverflow = true) :
    isScoreLineBreakDisabledByRuntime rf = true := by
  unfold isScoreLineBreakDisabledByRuntime
  simp [h]

/-- CSS Text 3 §3 Law: break-spaces always disables score line breaking. -/
theorem runtime_break_spaces_disables_score_break (rf : LineBreakRuntimeFeatures) (h : rf.isBreakSpaces = true) :
    isScoreLineBreakDisabledByRuntime rf = true := by
  unfold isScoreLineBreakDisabledByRuntime
  simp [h]

/-- CSS Fragmentation 3 Law: box-decoration-break: clone always disables score line breaking. -/
theorem runtime_clone_disables_score_break (rf : LineBreakRuntimeFeatures) (h : rf.isBoxDecorationBreakClone = true) :
    isScoreLineBreakDisabledByRuntime rf = true := by
  unfold isScoreLineBreakDisabledByRuntime
  simp [h]

end ChromiumLayout
