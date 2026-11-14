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

/-! ## 5. CSS Text 4 §5.4 Optimal Score Line Breaking Window & Segments -/

/-- CSS Text 4 §5.4 & Blink ScoreLineBreakContext::kMaxLinesForOptimal:
    Maximum number of lines optimized in a single score line break window (4 lines). -/
def maxLinesForOptimal : Nat := 4

/-- CSS Text 4 §5.4: Windowed line consumption count for optimal line breaking. -/
def optimalWindowConsumptionCount (totalLines : Nat) (maxLines : Nat := maxLinesForOptimal) : Nat :=
  if totalLines ≥ maxLines then totalLines - maxLines else 0

/-- CSS 2.1 §9.2.1.1 & CSS Text 4 §5.4:
    A segment of an inline formatting context bounded by forced breaks or blocks-in-inline. -/
structure ScoreLineBreakSegment where
  breakPointsCount : Nat := 0
  lineCount : Nat := 1
  isBlockInInline : Bool := false
  hasForcedBreak : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text 4 §5.4: Compute score line break points for a contiguous paragraph segment.
    If the segment has at most 2 candidates, score line breaking does not apply (0 break points).
    If it has more than 2 candidates, it produces (candidates - 1) optimal break points. -/
def computeScoreLineBreakPoints (candidateCount : Nat) : Nat :=
  if candidateCount ≤ 2 then 0 else candidateCount - 1

/-- CSS 2.1 §9.2.1.1 & CSS Text 4 §5.4:
    Classify the three execution stages of ScoreLineBreaker across a block-in-inline:
    1. Content before the block (optimized if hasBefore, else 1 line with forced break)
    2. The block-in-inline itself (unoptimized, isBlockInInline = true, hasForcedBreak = true)
    3. Content after the block (optimized if hasAfter, else 1 line). -/
def classifyScoreLineBreakerBlockInInline (hasBefore hasAfter : Bool) :
    ScoreLineBreakSegment × ScoreLineBreakSegment × ScoreLineBreakSegment :=
  let beforeSeg : ScoreLineBreakSegment :=
    if hasBefore then { breakPointsCount := 4, lineCount := 5, isBlockInInline := false, hasForcedBreak := false }
    else { breakPointsCount := 0, lineCount := 1, isBlockInInline := false, hasForcedBreak := true }
  let blockSeg : ScoreLineBreakSegment :=
    { breakPointsCount := 0, lineCount := 1, isBlockInInline := true, hasForcedBreak := true }
  let afterSeg : ScoreLineBreakSegment :=
    if hasAfter then { breakPointsCount := 4, lineCount := 5, isBlockInInline := false, hasForcedBreak := false }
    else { breakPointsCount := 0, lineCount := 1, isBlockInInline := false, hasForcedBreak := false }
  (beforeSeg, blockSeg, afterSeg)

/-- CSS Text 4 §5.4: Fallback result for line count mismatch in optimal layout.
    If mismatch is detected or optimal breaks are rejected, breakPointsCount is 0.
    If accepted, the number of lines equals the number of break points. -/
def resolveOptimalLineCountMismatch (mismatchDetected : Bool) (computedBreaks : Nat) : Nat × Nat :=
  if mismatchDetected then
    (computedBreaks, 0)
  else
    (computedBreaks, computedBreaks)

/-! ## 6. General Laws for Optimal Score Line Breaking -/

/-- CSS Text 4 §5.4: Window consumption count matches total lines minus window size when at least window size. -/
theorem optimalWindowConsumptionCount_ge (totalLines : Nat) (h : totalLines ≥ maxLinesForOptimal) :
    optimalWindowConsumptionCount totalLines = totalLines - maxLinesForOptimal := by
  dsimp [optimalWindowConsumptionCount]
  split <;> omega

/-- CSS Text 4 §5.4: Small segments with at most 2 candidates yield zero break points. -/
theorem computeScoreLineBreakPoints_small (c : Nat) (h : c ≤ 2) :
    computeScoreLineBreakPoints c = 0 := by
  dsimp [computeScoreLineBreakPoints]
  split <;> omega

/-- CSS Text 4 §5.4: Segments with more than 2 candidates produce candidates - 1 break points. -/
theorem computeScoreLineBreakPoints_large (c : Nat) (h : c > 2) :
    computeScoreLineBreakPoints c = c - 1 := by
  dsimp [computeScoreLineBreakPoints]
  split <;> omega

/-- CSS 2.1 §9.2.1.1 & CSS Text 4 §5.4: Middle block-in-inline segment is always an unoptimized forced break. -/
theorem blockInInline_middle_always_forced_break (hasBefore hasAfter : Bool) :
    (classifyScoreLineBreakerBlockInInline hasBefore hasAfter).2.1.isBlockInInline = true ∧
    (classifyScoreLineBreakerBlockInInline hasBefore hasAfter).2.1.hasForcedBreak = true ∧
    (classifyScoreLineBreakerBlockInInline hasBefore hasAfter).2.1.breakPointsCount = 0 := by
  cases hasBefore <;> cases hasAfter <;> decide

/-- CSS Text 4 §5.4: Line count mismatch safely clears break points. -/
theorem resolveOptimalLineCountMismatch_fallback (breaks : Nat) :
    (resolveOptimalLineCountMismatch true breaks).2 = 0 := rfl

/-- CSS Text 4 §5.4: Non-mismatched optimal breaks match line count. -/
theorem resolveOptimalLineCountMismatch_match (breaks : Nat) :
    (resolveOptimalLineCountMismatch false breaks).1 = (resolveOptimalLineCountMismatch false breaks).2 := rfl

end ChromiumLayout
