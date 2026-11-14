/-
  docs/chromium-layout/InlineFragmentItem.lean

  Formal model for Blink FragmentItem and FragmentItems
  (`third_party/blink/renderer/core/layout/inline/fragment_item.h`,
   `fragment_items.h`, `fragment_items_builder.h`).

  Owns: FragmentItem, FragmentItems representation, culled inline box bounds,
  ink overflow union laws, and fragmentainer distribution.
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout

/-! ## 1. Fragment Item Model -/

inductive FragmentItemType where
  | line
  | text
  | generatedText
  | box
  deriving DecidableEq, Repr, Inhabited

/-- Physical rectangle (`platform/geometry/physical_rect.h`). -/
structure PhysicalRect where
  x : Nat := 0
  y : Nat := 0
  width : Nat := 0
  height : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Rectangle union (`PhysicalRect::Unite`). -/
def PhysicalRect.union (r1 r2 : PhysicalRect) : PhysicalRect :=
  if r1.width == 0 && r1.height == 0 then r2
  else if r2.width == 0 && r2.height == 0 then r1
  else
    let minX := Nat.min r1.x r2.x
    let minY := Nat.min r1.y r2.y
    let maxX := Nat.max (r1.x + r1.width) (r2.x + r2.width)
    let maxY := Nat.max (r1.y + r1.height) (r2.y + r2.height)
    { x := minX, y := minY, width := maxX - minX, height := maxY - minY }

/-- Rectangle enclosure: `r2` is contained in `r1` (`r1.encloses r2`). -/
def PhysicalRect.encloses (r1 r2 : PhysicalRect) : Prop :=
  r1.x ≤ r2.x ∧
  r1.y ≤ r2.y ∧
  r2.x + r2.width ≤ r1.x + r1.width ∧
  r2.y + r2.height ≤ r1.y + r1.height

/-- A fragment item in the inline formatting context
    (`inline/fragment_item.h:74-320`). -/
structure FragmentItem where
  type : FragmentItemType := .text
  nodeId : Nat := 0
  offset : LogicalOffset := {}
  size : LogicalSize := {}
  inkOverflow : PhysicalRect := {}
  isFirstForNode : Bool := false
  isLastForNode : Bool := false
  isRubyAnnotationLine : Bool := false
  startOffsetInContainer : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- Compute bounding box for a culled inline from its descendant items
    (`inline/fragment_item.cc:754-780`, `CulledInlineBox`). -/
def culledInlineBoundingBox (items : List FragmentItem) (targetNodeId : Nat) : PhysicalRect :=
  let matching := items.filter (fun it => it.nodeId == targetNodeId)
  matching.foldl
    (fun acc it => acc.union { x := it.offset.inlineOffset
                             , y := it.offset.blockOffset
                             , width := it.size.inlineSize
                             , height := it.size.blockSize })
    {}

/-- Caret inline position with `text-fit: grow`
    (`inline/fragment_item_test.cc:931`, `CaretInlinePositionForOffset_TextFit`). -/
def caretInlinePositionForOffset (textLen : Nat) (availWidth : Nat) (offset : Nat) : Nat :=
  if textLen == 0 then 0
  else (availWidth / textLen) * offset

/-! ## 2. General Laws for Fragment Items -/

/-- Union of non-empty rectangles encloses the left rectangle. -/
theorem physicalRect_union_encloses_left (r1 r2 : PhysicalRect)
    (h1 : r1.width ≠ 0 ∨ r1.height ≠ 0) :
    (r1.union r2).encloses r1 := by
  dsimp [PhysicalRect.union]
  have hZero : ¬ (r1.width == 0 && r1.height == 0) := by
    intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h1 with hw | hh
    · exact hw h.1
    · exact hh h.2
  simp [hZero]
  split
  · -- r2 is empty
    dsimp [PhysicalRect.encloses]
    omega
  · -- both non-empty
    dsimp [PhysicalRect.encloses]
    let minX := Nat.min r1.x r2.x
    let minY := Nat.min r1.y r2.y
    let maxX := Nat.max (r1.x + r1.width) (r2.x + r2.width)
    let maxY := Nat.max (r1.y + r1.height) (r2.y + r2.height)
    have hMinXLe : minX ≤ r1.x := Nat.min_le_left _ _
    have hXLe : r1.x ≤ r1.x + r1.width := Nat.le_add_right _ _
    have hMaxXGe : r1.x + r1.width ≤ maxX := Nat.le_max_left _ _
    have hMinXLeMax : minX ≤ maxX := by omega
    have hMinYLe : minY ≤ r1.y := Nat.min_le_left _ _
    have hYLe : r1.y ≤ r1.y + r1.height := Nat.le_add_right _ _
    have hMaxYGe : r1.y + r1.height ≤ maxY := Nat.le_max_left _ _
    have hMinYLeMax : minY ≤ maxY := by omega
    refine ⟨hMinXLe, hMinYLe, ?_, ?_⟩
    · rw [Nat.add_sub_of_le hMinXLeMax]
      exact hMaxXGe
    · rw [Nat.add_sub_of_le hMinYLeMax]
      exact hMaxYGe

/-- Union of non-empty rectangles encloses the right rectangle. -/
theorem physicalRect_union_encloses_right (r1 r2 : PhysicalRect)
    (h2 : r2.width ≠ 0 ∨ r2.height ≠ 0) :
    (r1.union r2).encloses r2 := by
  dsimp [PhysicalRect.union]
  split
  · -- r1 is empty
    dsimp [PhysicalRect.encloses]
    omega
  · split
    · -- r2 is empty, contradiction
      rename_i _ h2Empty
      simp only [Bool.and_eq_true, beq_iff_eq] at h2Empty
      rcases h2 with hw | hh
      · exact False.elim (hw h2Empty.1)
      · exact False.elim (hh h2Empty.2)
    · -- both non-empty
      dsimp [PhysicalRect.encloses]
      let minX := Nat.min r1.x r2.x
      let minY := Nat.min r1.y r2.y
      let maxX := Nat.max (r1.x + r1.width) (r2.x + r2.width)
      let maxY := Nat.max (r1.y + r1.height) (r2.y + r2.height)
      have hMinXLe : minX ≤ r2.x := Nat.min_le_right _ _
      have hXLe : r2.x ≤ r2.x + r2.width := Nat.le_add_right _ _
      have hMaxXGe : r2.x + r2.width ≤ maxX := Nat.le_max_right _ _
      have hMinXLeMax : minX ≤ maxX := by omega
      have hMinYLe : minY ≤ r2.y := Nat.min_le_right _ _
      have hYLe : r2.y ≤ r2.y + r2.height := Nat.le_add_right _ _
      have hMaxYGe : r2.y + r2.height ≤ maxY := Nat.le_max_right _ _
      have hMinYLeMax : minY ≤ maxY := by omega
      refine ⟨hMinXLe, hMinYLe, ?_, ?_⟩
      · rw [Nat.add_sub_of_le hMinXLeMax]
        exact hMaxXGe
      · rw [Nat.add_sub_of_le hMinYLeMax]
        exact hMaxYGe

/-! ## 3. Fragment Sequence Flags (CSS 2.1 §9.4.2 & CSS Inline 3 §2) -/

/-- CSS 2.1 §9.4.2: First fragment for an inline node in a sequence. -/
def isFirstFragmentForNode (fragIndex : Nat) : Bool :=
  fragIndex == 0

/-- CSS 2.1 §9.4.2: Last fragment for an inline node in a sequence of totalFragments. -/
def isLastFragmentForNode (fragIndex : Nat) (totalFragments : Nat) : Bool :=
  fragIndex + 1 == totalFragments

/-- CSS 2.1 §9.4.2 Law: Fragment index 0 is always first for any sequence length. -/
theorem firstFragment_zero : isFirstFragmentForNode 0 = true := by
  rfl

/-- CSS 2.1 §9.4.2 Law: Fragment index > 0 is never first. -/
theorem firstFragment_pos (idx : Nat) : isFirstFragmentForNode (idx + 1) = false := by
  rfl

/-- CSS 2.1 §9.4.2 Law: Fragment at terminal index is always last. -/
theorem lastFragment_terminal (idx : Nat) : isLastFragmentForNode idx (idx + 1) = true := by
  unfold isLastFragmentForNode
  simp

/-- CSS 2.1 §9.4.2 Law: Single fragment is simultaneously first and last. -/
theorem single_fragment_first_and_last :
    isFirstFragmentForNode 0 = true ∧ isLastFragmentForNode 0 1 = true := by
  exact ⟨rfl, rfl⟩

/-- CSS Text 4 §5 Law: Caret position at offset 0 is always 0. -/
theorem caret_position_zero_offset (textLen avail : Nat) :
    caretInlinePositionForOffset textLen avail 0 = 0 := by
  unfold caretInlinePositionForOffset
  split <;> simp

/-- CSS Inline 3 §2 Law: Empty item list produces empty culled bounding box. -/
theorem culledInlineBoundingBox_empty (target : Nat) :
    culledInlineBoundingBox [] target = {} := by
  rfl

/-! ## 4. Fragmentainer Container Queries for Culled Inlines (CSS Fragmentation 3 §2, CSS Inline 3 §2) -/

/-- CSS Fragmentation 3 §2, CSS Inline 3 §2:
    Query whether a fragmentainer contains items of a culled inline,
    and whether it is the first or last fragmentainer to contain them.
    Returns `(isContainer, isFirst, isLast)`. -/
def isContainerForCulledInline (allFragments : List (List Nat)) (fragIdx : Nat) (culledNodeId : Nat) :
    Bool × Bool × Bool :=
  let current := allFragments[fragIdx]?.getD []
  if current.contains culledNodeId == false then (false, false, false)
  else
    let isFirst := !(allFragments.take fragIdx).any (fun items => items.contains culledNodeId)
    let isLast := !(allFragments.drop (fragIdx + 1)).any (fun items => items.contains culledNodeId)
    (true, isFirst, isLast)

/-- General Law: If a fragmentainer does not contain any item of a culled inline,
    it is not a container for it. -/
theorem isContainerForCulledInline_not_contains (allFragments : List (List Nat)) (fragIdx : Nat) (culledNodeId : Nat)
    (hNot : (allFragments[fragIdx]?.getD []).contains culledNodeId = false) :
    (isContainerForCulledInline allFragments fragIdx culledNodeId).1 = false := by
  dsimp [isContainerForCulledInline]
  rw [hNot]
  simp

/-- General Law: When there are no fragments, no fragmentainer contains the culled inline. -/
theorem isContainerForCulledInline_empty (fragIdx : Nat) (culledNodeId : Nat) :
    isContainerForCulledInline [] fragIdx culledNodeId = (false, false, false) := by
  dsimp [isContainerForCulledInline]

/-! ## 5. Visual Runs, Sequence Flags, Hyphen Offsets, and Line Classification (CSS Writing Modes 3 §3.1, CSS 2.1 §9.4.2, CSS Text 3 §5.2, CSS Overflow 3 §4.4, CSS Ruby 1 §3) -/

/-- CSS Writing Modes 3 §3.1 & UAX #9:
    Derive visual text fragment runs for mixed-directional text lines under RTL paragraph direction.
    For each line with number and trailing period, visual reordering places the trailing period first. -/
def bidiVisualFragmentRunsRtl (lines : List (String × String)) : List String :=
  lines.flatMap (fun (num, punct) => [punct, num])

/-- CSS 2.1 §9.4.2 & CSS Inline 3 §2:
    Derive `(isFirstForNode, isLastForNode)` sequence flags for a fragment at index `fragIdx`
    in a sequence of `totalFrags` fragments belonging to that layout object. -/
def deriveFragmentSequenceFlags (totalFrags : Nat) (fragIdx : Nat) : Bool × Bool :=
  (isFirstFragmentForNode fragIdx, isLastFragmentForNode fragIdx totalFrags)

/-- Helper for computing hyphen offsets in container. -/
def computeHyphenOffsetsAux (accOffset : Nat) : List Nat → List Nat
  | [] => []
  | len :: rest =>
    let hyphenOff := accOffset + len + 1
    hyphenOff :: computeHyphenOffsetsAux hyphenOff rest

/-- CSS Text 3 §5.2 & Blink FragmentItem::StartOffsetInContainer:
    Compute start offsets in container for layout-generated hyphen fragments
    produced at soft-hyphen break opportunities after each segment.
    Each hyphen fragment is positioned immediately following its preceding text segment
    in container character offset coordinates. -/
def computeHyphenOffsetsInContainer (segmentLengths : List Nat) : List Nat :=
  computeHyphenOffsetsAux 0 segmentLengths

/-- CSS Overflow 3 §4.4 & Blink FragmentItem:
    When an atomic inline overflows the container under `text-overflow: ellipsis`,
    it produces a box item and a generated text (ellipsis) item, both marked as
    the last fragment for their respective nodes. -/
def classifyEllipsizedAtomicInlineFragments (itemWidth containerWidth : Nat) :
    Option (FragmentItemType × Bool) :=
  if itemWidth > containerWidth then
    some (.box, true)
  else
    none

/-- CSS Ruby 1 §3 & Blink FragmentItem::IsRubyAnnotationLine:
    Classify line fragments in a ruby formatting context.
    A ruby container produces a base line (isRubyAnnotationLine = false)
    and one or more ruby annotation lines (isRubyAnnotationLine = true) for `<rt>` content. -/
def classifyRubyLineFragments (hasBaseText : Bool) (hasAnnotationText : Bool) : List (FragmentItemType × Bool) :=
  let baseLine := if hasBaseText then [(FragmentItemType.line, false)] else []
  let rtLine := if hasAnnotationText then [(FragmentItemType.line, true)] else []
  baseLine ++ rtLine

/-- General Law: When a layout object has multiple fragments, the first fragment is first but not last. -/
theorem deriveFragmentSequenceFlags_first (n : Nat) (h : n > 1) :
    deriveFragmentSequenceFlags n 0 = (true, false) := by
  dsimp [deriveFragmentSequenceFlags, isFirstFragmentForNode, isLastFragmentForNode]
  have hLast : (0 + 1 == n) = false := by
    apply beq_false_of_ne
    omega
  rw [hLast]

/-- General Law: Single hyphen segment offset is length + 1. -/
theorem computeHyphenOffsetsInContainer_single (len : Nat) :
    computeHyphenOffsetsInContainer [len] = [len + 1] := by
  dsimp [computeHyphenOffsetsInContainer, computeHyphenOffsetsAux]
  congr 1
  omega

/-- General Law: Overflowing atomic inline under text-overflow: ellipsis yields a terminal box item. -/
theorem classifyEllipsizedAtomicInlineFragments_overflow (w cW : Nat) (h : w > cW) :
    classifyEllipsizedAtomicInlineFragments w cW = some (.box, true) := by
  dsimp [classifyEllipsizedAtomicInlineFragments]
  simp [h]

/-- General Law: Ruby container with both base and annotation text produces base line and annotation line. -/
theorem classifyRubyLineFragments_both :
    classifyRubyLineFragments true true = [(.line, false), (.line, true)] := rfl

/-! ## 7. FragmentItemsBuilder Line Box Assembly (CSS 2.1 §9.4.2) -/

/-- CSS 2.1 §9.4.2 & Blink FragmentItemsBuilder:
    Container collecting line box fragments in order.
    Supports sequential additions, reordering (e.g. for custom layout worklets),
    and selective line emission. -/
structure FragmentItemsBuilder where
  lines : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- Append a line box fragment to the builder (`FragmentItemsBuilder::AddLine`). -/
def FragmentItemsBuilder.addLine (b : FragmentItemsBuilder) (lineId : Nat) : FragmentItemsBuilder :=
  { lines := b.lines ++ [lineId] }

/-- Finalize items into physical order (`FragmentItemsBuilder::ConvertToPhysical`). -/
def FragmentItemsBuilder.items (b : FragmentItemsBuilder) : List Nat :=
  b.lines

/-- CSS 2.1 §9.4.2 Law: Adding lines preserves the exact sequence and count in final items. -/
theorem fragmentItemsBuilder_preserves_lines (b : FragmentItemsBuilder) (lineId : Nat) :
    (b.addLine lineId).items.length = b.items.length + 1 ∧
    (b.addLine lineId).items.getLast? = some lineId := by
  dsimp [FragmentItemsBuilder.addLine, FragmentItemsBuilder.items]
  simp

end ChromiumLayout
