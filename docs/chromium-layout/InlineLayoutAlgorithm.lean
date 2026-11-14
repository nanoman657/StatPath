/-
  docs/chromium-layout/InlineLayoutAlgorithm.lean

  Formal model for Blink InlineLayoutAlgorithm
  (`third_party/blink/renderer/core/layout/inline/inline_layout_algorithm.h`,
   `inline_layout_algorithm.cc`).

  Formalizes general layout rules verified in `inline_layout_algorithm_test.cc`:
  1. Inline box border/padding partitioning across fragment lines.
  2. Break token chaining across line layout passes.
  3. Float exclusions and line offset computation.
  4. Hanging spaces and line alignment (RTL / Center / Right).
  5. CSS Text Box Trim (`text-box-trim: trim-both`).
  6. Ink overflow from half-leading and font metrics.
  7. Ellipsis fallback selection for fonts lacking U+2026.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 1. Physical Box Strut & Inline Box Fragmentation -/

/-- Physical box strut representing borders or paddings on four sides (`PhysicalBoxStrut`).
    Tested in `InlineLayoutAlgorithmTest.InlineBoxBorderPadding`. -/
structure PhysicalBoxStrut where
  left : Nat := 0
  top : Nat := 0
  right : Nat := 0
  bottom : Nat := 0
  deriving DecidableEq, Repr

/-- Partition an inline box's border or padding strut across line fragments.
    In LTR: the first fragment retains the left edge, the last retains the right edge.
    All fragments retain top and bottom edges.
    Tested in `InlineLayoutAlgorithmTest.InlineBoxBorderPadding`. -/
def partitionInlineStrut (s : PhysicalBoxStrut) (isStart : Bool) (isEnd : Bool) : PhysicalBoxStrut :=
  { left := if isStart then s.left else 0,
    top := s.top,
    right := if isEnd then s.right else 0,
    bottom := s.bottom }

/-- Content offset derived from border and padding struts.
    Tested in `InlineLayoutAlgorithmTest.InlineBoxBorderPadding`. -/
def strutContentOffset (border : PhysicalBoxStrut) (padding : PhysicalBoxStrut) : Nat × Nat :=
  (border.left + padding.left, border.top + padding.top)

/-- General Law: Vertical borders and paddings are invariant across all line fragments. -/
theorem physicalBoxStrut_partition_vertical_preserved (s : PhysicalBoxStrut) (isStart isEnd : Bool) :
    (partitionInlineStrut s isStart isEnd).top = s.top ∧
    (partitionInlineStrut s isStart isEnd).bottom = s.bottom := by
  dsimp [partitionInlineStrut]
  exact ⟨rfl, rfl⟩

/-- General Law: Horizontal strut partition between start fragment (line 1) and end fragment (line 2)
    conserves total horizontal borders/paddings. -/
theorem physicalBoxStrut_partition_horizontal_sum (s : PhysicalBoxStrut) :
    (partitionInlineStrut s true false).left + (partitionInlineStrut s false true).left = s.left ∧
    (partitionInlineStrut s true false).right + (partitionInlineStrut s false true).right = s.right := by
  dsimp [partitionInlineStrut]
  omega

/-! ## 2. Break Token Chaining -/

/-- Break token recording progress through inline items across layouts.
    Tested in `InlineLayoutAlgorithmTest.BreakToken`. -/
structure InlineBreakToken where
  itemIndex : Nat
  textOffset : Nat
  deriving DecidableEq, Repr

/-- Advance layout to produce the next line break token.
    Returns `none` when all items are consumed. -/
def advanceBreakToken (totalItems : Nat) (current : Option InlineBreakToken) (step : Nat) :
    Option InlineBreakToken :=
  let nextIdx := (current.map (·.itemIndex)).getD 0 + step
  if nextIdx ≥ totalItems then none
  else some { itemIndex := nextIdx, textOffset := nextIdx * 4 }

/-- General Law: When nextIdx reaches or exceeds totalItems, break token is none. -/
theorem advanceBreakToken_done (totalItems : Nat) (current : Option InlineBreakToken) (step : Nat)
    (h : (current.map (·.itemIndex)).getD 0 + step ≥ totalItems) :
    advanceBreakToken totalItems current step = none := by
  dsimp [advanceBreakToken]
  split
  · rfl
  · contradiction

/-! ## 3. Float Exclusions & Line Left Offset -/

/-- Float exclusion affecting inline line positioning.
    Tested in `InlineLayoutAlgorithmTest.TextFloatsAroundFloatsBefore`,
    `PositionFloatsWithMargins`. -/
structure FloatExclusion where
  isLeft : Bool
  width : Nat
  height : Nat
  marginInlineStart : Nat := 0
  marginInlineEnd : Nat := 0
  deriving DecidableEq, Repr

def FloatExclusion.totalWidth (f : FloatExclusion) : Nat :=
  f.marginInlineStart + f.width + f.marginInlineEnd

/-- Sum of total widths of active left floats. -/
def sumLeftFloatWidths : List FloatExclusion → Nat
  | [] => 0
  | f :: fs => (if f.isLeft then f.totalWidth else 0) + sumLeftFloatWidths fs

/-- Compute line left offset accounting for left float exclusions and container padding. -/
def lineLeftOffset (floats : List FloatExclusion) (containerPaddingLeft : Nat) : Nat :=
  containerPaddingLeft + sumLeftFloatWidths floats

/-- General Law: Adding a left float increases the line left offset by its total width. -/
theorem lineLeftOffset_cons_left (f : FloatExclusion) (floats : List FloatExclusion) (pad : Nat)
    (h : f.isLeft = true) :
    lineLeftOffset (f :: floats) pad = lineLeftOffset floats pad + f.totalWidth := by
  dsimp [lineLeftOffset, sumLeftFloatWidths]
  rw [h]
  dsimp
  omega

/-! ## 4. Hanging Spaces & Line Alignment -/

/-- Mode of space hanging at line end (`css-text-3`).
    Tested in `InlineLayoutAlgorithmTest.LineBoxWithHangingWidthRTLRightAligned`,
    `LineBoxWithHangingWidthRTLCenterAligned`. -/
inductive HangingMode where
  | unconditional
  | conditional
  deriving DecidableEq, Repr

/-- Text alignment options. -/
inductive TextAlign where
  | left
  | right
  | center
  deriving DecidableEq, Repr

/-- Effective line width after applying space hanging rules. -/
def effectiveLineWidth (textWidth : Nat) (spaceWidth : Nat) (containerWidth : Nat) (mode : HangingMode) : Nat :=
  match mode with
  | .unconditional => textWidth
  | .conditional =>
    let total := textWidth + spaceWidth
    if total ≤ containerWidth then total else containerWidth

/-- General Law: Unconditional hanging spaces never affect the effective line width. -/
theorem hanging_spaces_unconditional_invariant (tw sw cw : Nat) :
    effectiveLineWidth tw sw cw .unconditional = tw := by
  rfl

/-- Compute line rectangle given alignment and space hanging mode. -/
def computeHangingLineRect (containerWidth : Nat) (textWidth : Nat) (spaceWidth : Nat) (lineHeight : Nat)
    (mode : HangingMode) (align : TextAlign) : PhysicalRect :=
  let w := effectiveLineWidth textWidth spaceWidth containerWidth mode
  let x := match align with
    | .right => containerWidth - w
    | .center => (containerWidth - w) / 2
    | .left => 0
  { x := x, y := 0, width := w, height := lineHeight }

/-! ## 5. CSS Text Box Trim -/

/-- Child node for text-box-trim evaluation.
    Tested in `InlineLayoutAlgorithmTest.TextBoxTrimConstraintSpace*`. -/
structure TrimChild where
  id : String := ""
  isInFlow : Bool := true
  deriving DecidableEq, Repr, Inhabited

structure TextBoxTrimResult where
  shouldTrimStart : Bool := false
  shouldTrimEnd : Bool := false
  deriving DecidableEq, Repr

/-- Compute `text-box-trim: trim-both` flags for child blocks. -/
def computeTextBoxTrim (children : List TrimChild) (trimBoth : Bool) : List (String × TextBoxTrimResult) :=
  if !trimBoth then
    children.map (fun c => (c.id, { shouldTrimStart := false, shouldTrimEnd := false }))
  else
    let inFlow := children.filter (·.isInFlow)
    match inFlow with
    | [] => children.map (fun c => (c.id, { shouldTrimStart := false, shouldTrimEnd := false }))
    | [single] =>
      children.map (fun c =>
        (c.id, if c.id == single.id then { shouldTrimStart := true, shouldTrimEnd := true }
               else { shouldTrimStart := false, shouldTrimEnd := false }))
    | first :: rest =>
      let last := rest.reverse.head!
      children.map (fun c =>
        (c.id, if c.id == first.id then { shouldTrimStart := true, shouldTrimEnd := false }
               else if c.id == last.id then { shouldTrimStart := false, shouldTrimEnd := true }
               else { shouldTrimStart := false, shouldTrimEnd := false }))

/-- General Law: When text-box-trim is disabled, no child is trimmed. -/
theorem textBoxTrim_disabled (children : List TrimChild) :
    computeTextBoxTrim children false =
      children.map (fun c => (c.id, { shouldTrimStart := false, shouldTrimEnd := false })) := by
  rfl

/-- General Law: When there are no in-flow children, no child is trimmed. -/
theorem textBoxTrim_no_inflow (children : List TrimChild) (h : children.filter (·.isInFlow) = []) :
    computeTextBoxTrim children true =
      children.map (fun c => (c.id, { shouldTrimStart := false, shouldTrimEnd := false })) := by
  dsimp [computeTextBoxTrim]
  rw [h]

/-- General Law: When there is exactly one in-flow child, it receives both start and end trim. -/
theorem textBoxTrim_single_inflow (children : List TrimChild) (single : TrimChild)
    (h : children.filter (·.isInFlow) = [single]) :
    computeTextBoxTrim children true =
      children.map (fun c => (c.id, if c.id == single.id then { shouldTrimStart := true, shouldTrimEnd := true }
                                     else { shouldTrimStart := false, shouldTrimEnd := false })) := by
  dsimp [computeTextBoxTrim]
  rw [h]

/-! ## 6. Ink Overflow & Ellipsis Fallback -/

/-- Ink overflow vertical bounds from line height and font size.
    Tested in `InlineLayoutAlgorithmTest.InkOverflow`. -/
def inkOverflowVertical (lineHeight : Nat) (fontSize : Nat) : Int × Nat :=
  let top : Int := (Int.ofNat lineHeight - Int.ofNat fontSize) / 2
  (top, fontSize)

/-- Fallback string for ellipsis when font lacks horizontal ellipsis (U+2026).
    Tested in `InlineLayoutAlgorithmTest.EllipsisFallbackToDots`. -/
def selectEllipsisString (fontHasEllipsisGlyph : Bool) : String :=
  if fontHasEllipsisGlyph then "…" else "..."

/-- General Law: When horizontal ellipsis glyph is missing, fallback is always "...". -/
theorem ellipsisFallback_missing_glyph : selectEllipsisString false = "..." := by
  rfl

/-! ## 7. Block-in-Inline Line Box Classification (CSS 2.1 §9.2.1.1) -/

structure LineBoxFragmentInfo where
  isEmptyLineBox : Bool := false
  isBlockInInline : Bool := false
  blockCount : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- CSS 2.1 §9.2.1.1: Classify line box fragments around and for a block-in-inline. -/
def classifyBlockInInline (isBlockEmpty : Bool) (hasHeight : Bool) : List LineBoxFragmentInfo :=
  let preLine : LineBoxFragmentInfo := { isEmptyLineBox := true, isBlockInInline := false }
  let blockLine : LineBoxFragmentInfo := {
    isEmptyLineBox := isBlockEmpty && !hasHeight,
    isBlockInInline := true,
    blockCount := 1
  }
  let postLine : LineBoxFragmentInfo := { isEmptyLineBox := true, isBlockInInline := false }
  [preLine, blockLine, postLine]

/-- CSS 2.1 §9.2.1.1 Law: Block-in-inline split produces exactly 3 line boxes where
    the middle line box represents the block-in-inline. -/
theorem blockInInline_middle_is_block (empty height : Bool) :
    let lines := classifyBlockInInline empty height
    lines.length = 3 ∧
    lines[0]!.isBlockInInline = false ∧
    lines[1]!.isBlockInInline = true ∧
    lines[2]!.isBlockInInline = false := by
  dsimp [classifyBlockInInline]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 8. Empty Inline Containing Blocks and Fragment Generation (CSS 2.1 §10.6.1, §9.4.2) -/

/-- CSS 2.1 §10.6.1 & CSS 2.1 §9.4.2:
    Layout for an empty inline containing block whose descendants are all out-of-flow positioned.
    Because there is no in-flow content, the container height, line box size, and inline box fragment
    size are all zero, yet a box fragment is generated for positioning out-of-flow children. -/
def layoutEmptyInlineContainingBlock (hasOutOfFlowDescendants : Bool) : (Nat × Nat) × (Nat × Nat) :=
  if hasOutOfFlowDescendants then
    ((0, 0), (0, 0)) -- (lineBoxSize, inlineBoxFragmentSize)
  else
    ((0, 0), (0, 0))

/-- CSS 2.1 §9.4.2 & Blink InlineLayoutAlgorithm:
    Determine whether an inline box generates box fragments across fragmented lines.
    If an inline box has borders or padding on any fragment (e.g. `border-right`),
    it generates a box fragment for EVERY line it fragments across. -/
def shouldGenerateBoxFragmentsAcrossLines (hasBorderOrPaddingOnAnyFragment : Bool) (lineCount : Nat) : List Bool :=
  if hasBorderOrPaddingOnAnyFragment then
    List.replicate lineCount true
  else
    List.replicate lineCount false

/-- CSS 2.1 §10.6.1 Law: Empty inline containing block with out-of-flow content has zero line and fragment dimensions. -/
theorem emptyInlineContainingBlock_zero_size (oof : Bool) :
    layoutEmptyInlineContainingBlock oof = ((0, 0), (0, 0)) := by
  dsimp [layoutEmptyInlineContainingBlock]
  split <;> rfl

/-- CSS 2.1 §9.4.2 Law: When an inline box has border/padding on any line, all fragmented lines generate box fragments. -/
theorem shouldGenerateBoxFragments_consistent (hasBorder : Bool) (n : Nat) (h : hasBorder = true) :
    (shouldGenerateBoxFragmentsAcrossLines hasBorder n).all (fun b => b == true) = true := by
  dsimp [shouldGenerateBoxFragmentsAcrossLines]
  rw [h]
  simp

end ChromiumLayout
