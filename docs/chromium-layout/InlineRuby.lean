/-
  docs/chromium-layout/InlineRuby.lean

  Formal model for CSS Ruby Annotation Layout Level 1 (CSS Ruby 1)
  and Blink RubyBlockPositionCalculator (`third_party/blink/renderer/core/layout/inline/ruby_utils.h`).
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout

/-! ## 1. CSS Ruby 1 Annotation Level Types -/

/-- CSS Ruby 1 §4.1: ruby-position property (over vs under). -/
inductive RubyPosition where
  | over
  | under
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §2.3.1: Ruby level representing base or annotation depth path.
    Base level is represented by the empty list `[]`. -/
abbrev RubyLevel := List Int

/-- CSS Ruby 1 §2.3.1: Check whether a ruby level represents the base text level. -/
def isBaseLevel (lvl : RubyLevel) : Bool :=
  lvl.isEmpty

/-- CSS Ruby 1 §2.3: A ruby column pairing base items with annotation items. -/
structure LogicalRubyColumn where
  startIndex : Nat := 0
  size : Nat := 0
  rubyPosition : RubyPosition := .over
  subColumns : List LogicalRubyColumn := []
  deriving Inhabited

/-- CSS Ruby 1 §2.3: The end index of a logical ruby column in the inline sequence. -/
def LogicalRubyColumn.endIndex (c : LogicalRubyColumn) : Nat :=
  c.startIndex + c.size

/-- CSS Ruby 1 §3.1: A line of ruby annotations at a particular ruby level. -/
structure RubyLine where
  level : RubyLevel := []
  columns : List LogicalRubyColumn := []
  deriving Inhabited

/-- CSS Ruby 1 §2.3.1: Check whether a ruby line is at the base text level. -/
def RubyLine.isBaseLevel (line : RubyLine) : Bool :=
  line.level.isEmpty

/-! ## 2. CSS Ruby 1 §2.3.1 Segment Pairing and Level Grouping -/

/-- CSS Ruby 1 §2.3.1: Check if column a encloses column b in the base inline progression. -/
def encloses (a b : LogicalRubyColumn) : Bool :=
  a.startIndex ≤ b.startIndex && b.endIndex ≤ a.endIndex

/-- CSS Ruby 1 §2.3.1: Compute the annotation depth of a column given enclosing columns on the same side. -/
def computeColumnDepth (pos : RubyPosition) (col : LogicalRubyColumn) (allCols : List LogicalRubyColumn) : Int :=
  let enclosed := allCols.filter (fun c => c.startIndex ≠ col.startIndex && encloses col c && c.rubyPosition == pos)
  let baseDepth : Int := if pos == .under then -1 else 1
  if pos == .under then
    baseDepth - (enclosed.length : Int)
  else
    baseDepth + (enclosed.length : Int)

/-- CSS Ruby 1 §3.1.2: Order depths (under annotations inner-to-outer, then over inner-to-outer). -/
def isDepthLe (d1 d2 : Int) : Bool :=
  if d1 < 0 && d2 ≥ 0 then true
  else if d1 ≥ 0 && d2 < 0 then false
  else if d1 < 0 && d2 < 0 then d2 ≤ d1
  else d1 ≤ d2

/-- CSS Ruby 1 §3.1.2: Lexicographic ordering on ruby levels. -/
def isLevelLe : RubyLevel → RubyLevel → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x ≠ y then isDepthLe x y
    else isLevelLe xs ys

/-- Insert a ruby level in sorted order. -/
def insertLevel (lvl : RubyLevel) : List RubyLevel → List RubyLevel
  | [] => [lvl]
  | x :: xs => if isLevelLe lvl x then lvl :: x :: xs else x :: insertLevel lvl xs

/-- Sort ruby levels by closing order. -/
def sortLevels : List RubyLevel → List RubyLevel
  | [] => []
  | x :: xs => insertLevel x (sortLevels xs)

/-- CSS Ruby 1 §2.3.1: Group columns sharing a parent level into lines by their computed ruby levels. -/
def groupColumnsToLines (parentLevel : RubyLevel) (cols : List LogicalRubyColumn) : List RubyLine :=
  let assignedLevels := cols.map (fun c =>
    let d := computeColumnDepth c.rubyPosition c cols
    (parentLevel ++ [d], c)
  )
  let rawLevels := assignedLevels.foldl (fun acc (lvl, _) => if acc.contains lvl then acc else acc ++ [lvl]) []
  let sortedLevels := sortLevels rawLevels
  sortedLevels.map (fun lvl =>
    let matchingCols := (assignedLevels.filter (fun (l, _) => l == lvl)).map Prod.snd
    { level := lvl, columns := matchingCols }
  )

/-- CSS Ruby 1 §3.1.2: Group a list of ruby columns into ruby lines starting from the base line. -/
def groupLines (cols : List LogicalRubyColumn) : List RubyLine :=
  let baseLine : RubyLine := { level := [], columns := [] }
  if cols.isEmpty then [baseLine]
  else
    let topLines := groupColumnsToLines [] cols
    let subLines := cols.foldl (fun acc col =>
      match col.subColumns with
      | [] => acc
      | subs =>
        let colDepth := computeColumnDepth col.rubyPosition col cols
        let colLevel := [colDepth]
        acc ++ groupColumnsToLines colLevel subs
    ) []
    baseLine :: (topLines ++ subLines)

/-! ## 3. CSS Ruby 1 §3.1 Primary Line Progression and Inflow End Offset -/

/-- CSS Ruby 1 §3.1: An inline item on a formatted line.
    Includes regular inflow items (text, control, atomic inline) and ruby columns
    whose base text participates in primary line progression. -/
inductive LineResultItem where
  | text (startOffset endOffset : Nat)
  | control (startOffset endOffset : Nat)
  | atomicInline (startOffset endOffset : Nat)
  | openRubyColumn (startOffset endOffset : Nat)
  | rubyColumn (baseStartOffset baseEndOffset : Nat) (annotationEndOffset : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Scan reversed line items to find the last inflow item's end offset. -/
def scanInflowEndOffset (startOffset : Nat) : List LineResultItem → Nat
  | [] => startOffset
  | item :: rest =>
    match item with
    | .text _ endOff => endOff
    | .control _ endOff => endOff
    | .atomicInline _ endOff => endOff
    | .openRubyColumn _ endOff => endOff
    | .rubyColumn baseStart baseEnd _ =>
      if baseEnd ≠ baseStart then baseEnd
      else scanInflowEndOffset startOffset rest

/-- CSS Ruby 1 §3.1 / Blink LineInfo::InflowEndOffset:
    The end offset of inflow content on the line. For a ruby column, inflow content
    is determined by the primary line progression in the base line, excluding annotation lines. -/
def lineInflowEndOffset (startOffset : Nat) (results : List LineResultItem) : Nat :=
  scanInflowEndOffset startOffset results.reverse

/-! ## 4. General Laws -/

/-- General Law: LogicalRubyColumn end index is the sum of startIndex and size for all inputs. -/
theorem logicalRubyColumn_endIndex (start sz : Nat) (pos : RubyPosition) (subs : List LogicalRubyColumn) :
    (LogicalRubyColumn.mk start sz pos subs).endIndex = start + sz := by
  rfl

/-- General Law: A RubyLevel is base level if and only if it is empty for all inputs. -/
theorem rubyLevel_isBaseLevel_iff (lvl : RubyLevel) :
    isBaseLevel lvl = true ↔ lvl = [] := by
  dsimp [isBaseLevel]
  cases lvl <;> simp

/-- General Law: A RubyLine is at the base level if and only if its level is empty for all inputs. -/
theorem rubyLine_isBaseLevel_iff (line : RubyLine) :
    line.isBaseLevel = true ↔ line.level = [] := by
  dsimp [RubyLine.isBaseLevel]
  cases line.level <;> simp

/-- CSS Ruby 1 §3.1: Inflow end offset of an empty line is its start offset. -/
theorem lineInflowEndOffset_empty (startOffset : Nat) :
    lineInflowEndOffset startOffset [] = startOffset := rfl

/-- CSS Ruby 1 §3.1: A ruby column's inflow end offset is determined by its base line. -/
theorem lineInflowEndOffset_ruby_base (startOffset baseStart baseEnd annoEnd : Nat) (h : baseEnd ≠ baseStart) :
    lineInflowEndOffset startOffset [.rubyColumn baseStart baseEnd annoEnd] = baseEnd := by
  dsimp [lineInflowEndOffset, scanInflowEndOffset, List.reverse]
  split <;> rename_i h2
  · rfl
  · contradiction

/-- CSS Ruby 1 §3.1: Inflow end offset of a text item is its end offset. -/
theorem lineInflowEndOffset_text (startOffset s e : Nat) :
    lineInflowEndOffset startOffset [.text s e] = e := rfl

/-- CSS Ruby 1 §3.1: Inflow end offset of an open ruby column marker is its end offset. -/
theorem lineInflowEndOffset_openRubyColumn (startOffset s e : Nat) :
    lineInflowEndOffset startOffset [.openRubyColumn s e] = e := rfl

/-! ## 5. CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5: Ruby Annotation Metrics and Text Emphasis -/

/-- CSS Text Decoration 3 §3.5: The position of text emphasis marks relative to text. -/
inductive TextEmphasisPosition where
  | over
  | under
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Annotation metrics describing the distances from the line-over and line-under of an inline
    fragment to the exterior boundaries of ruby annotations and text-emphasis marks.
    (Matches Blink `FontHeight FragmentItem::AnnotationMetrics() const`). -/
structure AnnotationMetrics where
  ascent : Nat := 0
  descent : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- CSS Text Decoration 3 §3.5: Default text emphasis mark height is 50% of the font size. -/
def computeTextEmphasisHeight (fontSize : Nat) : Nat :=
  fontSize / 2

/-- CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    A specification of ruby annotation and emphasis parameters for a text fragment. -/
structure TextAnnotationSpec where
  hasRuby : Bool := false
  rubyPosition : RubyPosition := .over
  rubyAnnoHeight : Nat := 0
  hasEmphasis : Bool := false
  emphasisPosition : TextEmphasisPosition := .over
  fontSize : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Compute annotation metrics for a text item.
    - If the item is not in a ruby container (hasRuby = false), metrics are {0, 0}.
    - If ruby is over, ascent is determined by ruby annotation height or over-emphasis height.
    - If ruby is under, descent is determined by ruby annotation height or under-emphasis height. -/
def computeAnnotationMetrics (spec : TextAnnotationSpec) : AnnotationMetrics :=
  if !spec.hasRuby then
    { ascent := 0, descent := 0 }
  else
    let empHeight := if spec.hasEmphasis then computeTextEmphasisHeight spec.fontSize else 0
    let ascentVal :=
      if spec.rubyPosition == .over then
        if spec.rubyAnnoHeight > 0 then spec.rubyAnnoHeight
        else if spec.hasEmphasis && spec.emphasisPosition == .over then empHeight
        else 0
      else 0
    let descentVal :=
      if spec.rubyPosition == .under then
        if spec.rubyAnnoHeight > 0 then spec.rubyAnnoHeight
        else if spec.hasEmphasis && spec.emphasisPosition == .under then empHeight
        else 0
      else 0
    { ascent := ascentVal, descent := descentVal }

/-- CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    A nested ruby annotation layer with text height and emphasis mark. -/
structure NestedRubyAnnotation where
  textHeight : Nat
  emphasisHeight : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    Total ascent for nested ruby annotations stacked outside a base item.
    Each layer contributes its text height and any associated emphasis mark height. -/
def computeNestedRubyAscent : List NestedRubyAnnotation → Nat
  | [] => 0
  | l :: ls => l.textHeight + l.emphasisHeight + computeNestedRubyAscent ls

/-- CSS Ruby 1 §3.2, CSS Text Decoration 3 §3.5, CSS 2.1 §10.8:
    Line box height for a line containing text with ruby annotations and text emphasis. -/
def computeAnnotatedLineHeight (baseHeight rubyAnnoOver empOver rubyAnnoUnder empUnder : Nat) : Nat :=
  baseHeight + max rubyAnnoOver empOver + max rubyAnnoUnder empUnder

/-! ## 6. General Laws for Annotation Metrics and Ruby Stacking -/

/-- CSS Ruby 1 §3.2: Non-ruby text fragments always have zero annotation metrics. -/
theorem computeAnnotationMetrics_noRuby (spec : TextAnnotationSpec) (h : spec.hasRuby = false) :
    computeAnnotationMetrics spec = { ascent := 0, descent := 0 } := by
  dsimp [computeAnnotationMetrics]
  rw [h]
  rfl

/-- CSS Text Decoration 3 §3.5: Text emphasis mark height is monotonic in font size. -/
theorem computeTextEmphasisHeight_monotonic (s1 s2 : Nat) (h : s1 ≤ s2) :
    computeTextEmphasisHeight s1 ≤ computeTextEmphasisHeight s2 := by
  dsimp [computeTextEmphasisHeight]
  exact Nat.div_le_div_right h

/-- CSS Ruby 1 §3.2: Stacking nested ruby annotations preserves total ascent additivity. -/
theorem computeNestedRubyAscent_append (l1 l2 : List NestedRubyAnnotation) :
    computeNestedRubyAscent (l1 ++ l2) = computeNestedRubyAscent l1 + computeNestedRubyAscent l2 := by
  induction l1 with
  | nil =>
    dsimp [computeNestedRubyAscent]
    omega
  | cons head tail ih =>
    dsimp [computeNestedRubyAscent]
    rw [ih]
    omega

/-- CSS Ruby 1 §3.2 & CSS Text Decoration 3 §3.5:
    When ruby annotation height matches emphasis height, line height is invariant
    between ruby-only, emphasis-only, and ruby-with-emphasis. -/
theorem computeAnnotatedLineHeight_ruby_emphasis_invariant (baseHeight H : Nat) :
    computeAnnotatedLineHeight baseHeight 0 H 0 0 = computeAnnotatedLineHeight baseHeight H H 0 0 ∧
    computeAnnotatedLineHeight baseHeight H H 0 0 = computeAnnotatedLineHeight baseHeight H 0 0 0 := by
  dsimp [computeAnnotatedLineHeight]
  constructor
  · omega
  · omega

/-! ## 7. CSS Ruby 1 §2.1 Ruby Formatting Context and Inlinification -/

/-- CSS Display 3 §2 / CSS Ruby 1 §2.1: Display types relevant to ruby layout. -/
inductive RubyChildDisplay where
  | inline
  | block
  | tableCell
  | tableCaption
  | tableColumn
  | inlineTable
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §2.1:
    The contents of a ruby container are inlinified.
    - table-cell children are wrapped in inline-table.
    - table-caption and table-column children become inline-level table elements.
    - block-level children are inlinified into inline boxes.
    - inline-level children remain inline. -/
def inlinifyRubyChildDisplay : RubyChildDisplay → RubyChildDisplay
  | .tableCell => .inlineTable
  | .tableCaption => .tableCaption
  | .tableColumn => .tableColumn
  | .block => .inline
  | .inline => .inline
  | .inlineTable => .inlineTable

/-- CSS Ruby 1 §2.1: Whether a child in a ruby container is inline-level.
    All children in a ruby container are inlinified, so every child is inline-level. -/
def isRubyChildInline (_child : RubyChildDisplay) : Bool :=
  true

/-- CSS Ruby 1 §2.1 & CSS 2.1 §9.2.1.1:
    Whether a child inside a ruby base causes the prior text to move to an anonymous block.
    Because all children of a ruby base are inlinified, no anonymous block is ever created around prior text. -/
def movesPriorTextToAnonymousBlock (_child : RubyChildDisplay) : Bool :=
  false

/-- CSS Ruby 1 §2.1 Law: All ruby children are inline-level for any child display. -/
theorem ruby_child_always_inline (d : RubyChildDisplay) :
    isRubyChildInline d = true := rfl

/-- CSS Ruby 1 §2.1 Law: Adding any child to a ruby base never moves prior text to an anonymous block. -/
theorem ruby_child_never_moves_prior_text (d : RubyChildDisplay) :
    movesPriorTextToAnonymousBlock d = false := rfl

/-- CSS Ruby 1 §2.1 Law: A table-cell child in a ruby container is inlinified to inline-table. -/
theorem inlinifyRubyChildDisplay_tableCell :
    inlinifyRubyChildDisplay .tableCell = .inlineTable := rfl

/-- CSS Ruby 1 §2.1 Law: A block child in a ruby container is inlinified to inline. -/
theorem inlinifyRubyChildDisplay_block :
    inlinifyRubyChildDisplay .block = .inline := rfl

/-- CSS Ruby 1 §2.1 Law: Table caption remains table-caption display. -/
theorem inlinifyRubyChildDisplay_tableCaption :
    inlinifyRubyChildDisplay .tableCaption = .tableCaption := rfl

/-- CSS Ruby 1 §2.1 Law: Table column remains table-column display. -/
theorem inlinifyRubyChildDisplay_tableColumn :
    inlinifyRubyChildDisplay .tableColumn = .tableColumn := rfl

/-! ## 8. CSS Ruby 1 §4 Ruby Sizing and Min-Max Sizes -/

/-- CSS Ruby 1 §4: Intrinsic min/max sizes for ruby base and annotations. -/
structure RubyColumnSizes where
  baseMin : Nat := 0
  baseMax : Nat := 0
  annotationMins : List Nat := []
  annotationMaxs : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §4: Compute the min-content inline size of a ruby column.
    The min-content size of a ruby column is the maximum of the base min-content size
    and the min-content sizes of all its associated annotations. -/
def computeRubyColumnMinSize (col : RubyColumnSizes) : Nat :=
  col.annotationMins.foldl Nat.max col.baseMin

/-- CSS Ruby 1 §4: Compute the max-content inline size of a ruby column.
    The max-content size of a ruby column is the maximum of the base max-content size
    and the max-content sizes of all its associated annotations. -/
def computeRubyColumnMaxSize (col : RubyColumnSizes) : Nat :=
  col.annotationMaxs.foldl Nat.max col.baseMax

/-- CSS Ruby 1 §4 Law: When a ruby column has no annotations, its min size equals its base min size. -/
theorem computeRubyColumnMinSize_empty_annotations (b : Nat) :
    computeRubyColumnMinSize { baseMin := b, annotationMins := [] } = b := rfl

/-- CSS Ruby 1 §4 Law: When a ruby column has no annotations, its max size equals its base max size. -/
theorem computeRubyColumnMaxSize_empty_annotations (b : Nat) :
    computeRubyColumnMaxSize { baseMax := b, annotationMaxs := [] } = b := rfl

/-- CSS Ruby 1 §4 Law: When ruby base is empty (size 0), column min size is the annotation min size. -/
theorem computeRubyColumnMinSize_empty_base (m : Nat) :
    computeRubyColumnMinSize { baseMin := 0, annotationMins := [m] } = m := by
  dsimp [computeRubyColumnMinSize]
  exact Nat.zero_max m

/-- CSS Ruby 1 §4 Law: Adding an atomic inline with size w to ruby base establishes minimum column size. -/
theorem computeRubyColumnMinSize_with_base (w : Nat) :
    computeRubyColumnMinSize { baseMin := w, annotationMins := [0] } = w := by
  dsimp [computeRubyColumnMinSize]
  exact Nat.max_zero w

/-! ## 9. CSS Text 3 §7.3 & CSS Ruby 1 §3: Ruby Justification Opportunities -/

/-- CSS Text 3 §7.3 & CSS Ruby 1 §3:
    Whether a justification opportunity can occur between inline items in a ruby container.
    Ruby annotations and non-text atomic inlines do not create spurious justification opportunities. -/
def hasRubyJustificationOpportunity (isAnnotation : Bool) (hasText : Bool) : Bool :=
  !isAnnotation && hasText

/-- CSS Text 3 §7.3 Law: Ruby annotations never receive line justification expansion. -/
theorem ruby_annotation_no_justification (hasText : Bool) :
    hasRubyJustificationOpportunity true hasText = false := rfl

/-- CSS Text 3 §7.3 Law: Atomic items without text do not generate justification opportunities. -/
theorem ruby_atomic_inline_no_text_no_justification :
    hasRubyJustificationOpportunity false false = false := rfl

end ChromiumLayout
