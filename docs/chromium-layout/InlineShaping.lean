/-
  docs/chromium-layout/InlineShaping.lean

  Formal model for Blink Inline Node item collection, text shaping,
  and Min/Max size computation
  (`third_party/blink/renderer/core/layout/inline/inline_node.h`,
   `third_party/blink/renderer/core/layout/inline/inline_node.cc`,
   `third_party/blink/renderer/core/layout/inline/line_breaker.cc`).

  Owns:
  - Inline item classification (text, control, atomic inline, open/close tags)
  - InlineNode::CollectInlines DOM flattening and item offset attribution
  - Fixed-width font (Ahem 10px) min/max intrinsic inline sizes calculation
  - Grapheme cluster and combining mark segmentation
-/
import LayoutTypes
import LayoutInline
import InlineGeometry

namespace ChromiumLayout

/-! ## 1. Inline Item Types & Collection Tokens -/

inductive InlineItemType where
  | text
  | control
  | atomicInline
  | openTag
  | closeTag
  | floating
  | bidiControl
  deriving DecidableEq, Repr, Inhabited

structure InlineCollectedItem where
  itemType : InlineItemType := .text
  startOffset : Nat := 0
  endOffset : Nat := 0
  bidiLevel : Nat := 0
  isSymbolMarker : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- CSS Writing Modes 3 §2.1: Direction derived from bidi embedding level.
    Even bidi levels are LTR; odd bidi levels are RTL. -/
def InlineCollectedItem.direction (item : InlineCollectedItem) : TextDirection :=
  if item.bidiLevel % 2 == 0 then .ltr else .rtl

/-- CSS Writing Modes 3 §2.1 Law: Even bidi embedding levels produce LTR direction. -/
theorem inlineCollectedItem_direction_even (item : InlineCollectedItem) (h : item.bidiLevel % 2 = 0) :
    item.direction = .ltr := by
  unfold InlineCollectedItem.direction
  simp [h]

/-- CSS Writing Modes 3 §2.1 Law: Odd bidi embedding levels produce RTL direction. -/
theorem inlineCollectedItem_direction_odd (item : InlineCollectedItem) (h : item.bidiLevel % 2 = 1) :
    item.direction = .rtl := by
  unfold InlineCollectedItem.direction
  have h2 : ¬ (item.bidiLevel % 2 = 0) := by omega
  simp [h2]

/-- CSS Writing Modes 3 §2.1 & UAX #9: Split an InlineCollectedItem at a character offset
    if the offset falls strictly inside the item's span. -/
def splitInlineItem (item : InlineCollectedItem) (splitOffset : Nat) : List InlineCollectedItem :=
  if item.startOffset < splitOffset && splitOffset < item.endOffset then
    [{ item with endOffset := splitOffset },
     { item with startOffset := splitOffset }]
  else
    [item]

/-- CSS Writing Modes 3 §2.1 & UAX #9 Law: Splitting an item preserves total character span. -/
theorem splitInlineItem_span (item : InlineCollectedItem) (off : Nat)
    (h1 : item.startOffset < off) (h2 : off < item.endOffset) :
    let pieces := splitInlineItem item off
    pieces.length = 2 ∧
    (pieces[0]!.endOffset - pieces[0]!.startOffset) +
    (pieces[1]!.endOffset - pieces[1]!.startOffset) =
    item.endOffset - item.startOffset := by
  have hcond : (item.startOffset < off && off < item.endOffset) = true := by
    simp [h1, h2]
  unfold splitInlineItem
  simp [hcond]
  omega

inductive InlineCollectionToken where
  | text (content : String)
  | openTag (tag : String)
  | closeTag
  | atomicInline (widthPx : Nat := 10)
  | br
  /-- CSS 2.1 §9.5 Floats: Floating box inside an inline formatting context.
      Floats are out-of-flow and produce a zero-length inline item in the text buffer. -/
  | floating
  /-- CSS Text 3 §4: Preserved newline character (e.g. within pre or pre-wrap). -/
  | newline
  /-- CSS Text 3 §4: Word break opportunity element (<wbr>). -/
  | wbr
  /-- CSS Lists 3 §3: List item symbol marker (e.g. bullet "• "). -/
  | symbolMarker (content : String := "• ")
  deriving DecidableEq, Repr, Inhabited

structure CollectionResult where
  text : String := ""
  items : List InlineCollectedItem := []
  isBidiEnabled : Bool := false
  deriving DecidableEq, Repr

/-! ## 2. Flattening and Item Collection (`InlineNode::CollectInlines`) -/

/-- CSS Writing Modes 3 §2.1: Preliminary bidi detection during CollectInlines.
    Flags true for non-ASCII surrogate pairs or RTL scripts. -/
def detectBidiInCollectInlines (text : String) : Bool :=
  text.toList.any (fun c => c.val > 0xFFFF || (c.val ≥ 0x0590 && c.val ≤ 0x08FF))

/-- CSS Writing Modes 3 §2.1: Resolved bidi enablement during SegmentText.
    Resets to false if no characters are strong RTL. -/
def detectBidiInSegmentText (text : String) : Bool :=
  text.toList.any (fun c => c.val ≥ 0x0590 && c.val ≤ 0x08FF)

/-- CSS 2.1 §9.5, §9.4.2 & CSS Writing Modes 3 §5.1.4: Single step of inline collection
    attributing character offsets, item types, and text buffer emission.
    Within text combine, forced line breaks and newlines are treated as text spaces,
    and wbr is treated as a zero-width space. -/
def collectInlinesStep (offset : Nat) (isTextCombine : Bool := false) : InlineCollectionToken → Nat × InlineCollectedItem × List Char
  | .text s => (offset + s.length, { itemType := .text, startOffset := offset, endOffset := offset + s.length }, s.toList)
  | .openTag _ => (offset, { itemType := .openTag, startOffset := offset, endOffset := offset }, [])
  | .closeTag => (offset, { itemType := .closeTag, startOffset := offset, endOffset := offset }, [])
  | .atomicInline _ => (offset + 1, { itemType := .atomicInline, startOffset := offset, endOffset := offset + 1 }, ['\uFFFC'])
  | .br | .newline =>
    let (t, c) := if isTextCombine then (InlineItemType.text, ' ') else (.control, '\n')
    (offset + 1, { itemType := t, startOffset := offset, endOffset := offset + 1 }, [c])
  | .wbr =>
    if isTextCombine then
      (offset + 1, { itemType := .text, startOffset := offset, endOffset := offset + 1 }, ['\u200B'])
    else
      (offset, { itemType := .control, startOffset := offset, endOffset := offset }, [])
  | .symbolMarker s =>
    (offset + s.length, { itemType := .text, startOffset := offset, endOffset := offset + s.length, isSymbolMarker := true }, s.toList)
  | .floating => (offset, { itemType := .floating, startOffset := offset, endOffset := offset }, [])

/-- CSS 2.1 §9.5 Law: Floating items in an inline formatting context do not advance the inline offset. -/
theorem collectInlinesStep_floating_zero_advance (offset : Nat) :
    (collectInlinesStep offset false .floating).1 = offset := by
  rfl

/-- CSS 2.1 §9.5 Law: Floating items in an inline formatting context produce zero character length. -/
theorem collectInlinesStep_floating_zero_length (offset : Nat) :
    (collectInlinesStep offset false .floating).2.1.startOffset = (collectInlinesStep offset false .floating).2.1.endOffset := by
  rfl

/-- CSS 2.1 §9.5 Law: Floating items in an inline formatting context emit no characters into the text buffer. -/
theorem collectInlinesStep_floating_empty_chars (offset : Nat) :
    (collectInlinesStep offset false .floating).2.2 = [] := by
  rfl

/-- CSS Writing Modes 3 §5.1.4 Law: Forced line breaks in text combine are classified as text items. -/
theorem collectInlinesStep_textCombine_br_is_text (offset : Nat) :
    (collectInlinesStep offset true .br).2.1.itemType = .text := rfl

/-- CSS Writing Modes 3 §5.1.4 Law: Preserved newlines in text combine are classified as text items. -/
theorem collectInlinesStep_textCombine_newline_is_text (offset : Nat) :
    (collectInlinesStep offset true .newline).2.1.itemType = .text := rfl

/-- CSS Writing Modes 3 §5.1.4 Law: Word break opportunities in text combine are classified as text items. -/
theorem collectInlinesStep_textCombine_wbr_is_text (offset : Nat) :
    (collectInlinesStep offset true .wbr).2.1.itemType = .text := rfl

/-- CSS Writing Modes 3 §5.1.4 Law: Forced line breaks in text combine emit a space character into the text buffer. -/
theorem collectInlinesStep_textCombine_br_space (offset : Nat) :
    (collectInlinesStep offset true .br).2.2 = [' '] := rfl

/-- CSS Writing Modes 3 §5.1.4 Law: Preserved newlines in text combine emit a space character into the text buffer. -/
theorem collectInlinesStep_textCombine_newline_space (offset : Nat) :
    (collectInlinesStep offset true .newline).2.2 = [' '] := rfl

/-- CSS Writing Modes 3 §5.1.4 Law: Word break opportunities in text combine emit a zero-width space into the text buffer. -/
theorem collectInlinesStep_textCombine_wbr_zws (offset : Nat) :
    (collectInlinesStep offset true .wbr).2.2 = ['\u200B'] := rfl

/-- Flatten input inline node tokens into character text and classified inline items. -/
def collectInlines (tokens : List InlineCollectionToken) (dir : TextDirection := .ltr) (isTextCombine : Bool := false) : CollectionResult :=
  let baseLevel := match dir with | .ltr => 0 | .rtl => 1
  let rec loop (offset : Nat) (accItems : List InlineCollectedItem) (accChars : List Char) :
      List InlineCollectionToken → Nat × List InlineCollectedItem × List Char
    | [] => (offset, accItems, accChars)
    | tok :: rest =>
      let (nxtOffset, item, chars) := collectInlinesStep offset isTextCombine tok
      let itemWithLevel := { item with bidiLevel := baseLevel }
      loop nxtOffset (itemWithLevel :: accItems) (accChars ++ chars) rest
  let (_, revItems, chars) := loop 0 [] [] tokens
  let textStr := String.ofList chars
  { text := textStr, items := revItems.reverse, isBidiEnabled := detectBidiInCollectInlines textStr }

/-! ## 3. Grapheme Cluster & Combining Mark Segmentation -/

def utf16Length (c : Char) : Nat :=
  if c.val > 0xFFFF then 2 else 1

def isCombiningMark (c : Char) : Bool :=
  c == '\u05B4' || c == '\u0343'

/-- Compute UTF-16 code unit lengths for grapheme clusters respecting combining marks. -/
def clusterUtf16Lengths (cs : List Char) : List Nat :=
  let rec loop (acc : List Nat) (prevLen : Option Nat) : List Char → List Nat
    | [] =>
      match prevLen with
      | some l => (l :: acc).reverse
      | none => acc.reverse
    | c :: rest =>
      if isCombiningMark c then
        match prevLen with
        | some l => loop acc (some (l + utf16Length c)) rest
        | none => loop (utf16Length c :: acc) none rest
      else
        match prevLen with
        | some l => loop (l :: acc) (some (utf16Length c)) rest
        | none => loop acc (some (utf16Length c)) rest
  loop [] none cs

/-- Segment text into grapheme cluster UTF-16 lengths. -/
def graphemeLengths (s : String) : List Nat :=
  clusterUtf16Lengths s.toList

/-! ## 4. Intrinsic Min/Max Size Computation (`InlineNode::ComputeMinMaxSizes`) -/

/-- CSS Values and Units 3 §6 & Blink LayoutUnit::kIntMax:
    Finite numeric limit for layout coordinates and sizes in LayoutUnit (1/64 px fixed point).
    kIntMax = (1 << 25) - 1 = 33554431. -/
def layoutUnitMaxInt : Nat := 33554431

/-- CSS Values and Units 3 §6: Values exceeding UA finite limits are clamped to the nearest supported value. -/
def clampLayoutUnit (v : Nat) : Nat :=
  if v > layoutUnitMaxInt then layoutUnitMaxInt else v

structure MinMaxSizes where
  minSize : Nat := 0
  maxSize : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Compute min/max content sizes for 10px fixed-width (Ahem) font. -/
def computeMinMaxSizesAhem (tokens : List InlineCollectionToken) : MinMaxSizes :=
  let rec toSegments (curWordLen : Nat) (words : List Nat) (totalChars : Nat) : List InlineCollectionToken → List Nat × Nat
    | [] =>
      let finalWords := if curWordLen > 0 then curWordLen :: words else words
      (finalWords, totalChars)
    | .text s :: rest =>
      let chars := s.toList
      let rec processChars (wLen : Nat) (accW : List Nat) (tot : Nat) : List Char → Nat × List Nat × Nat
        | [] => (wLen, accW, tot)
        | ' ' :: cs =>
          let nextAccW := if wLen > 0 then wLen :: accW else accW
          processChars 0 nextAccW (tot + 1) cs
        | _ :: cs =>
          processChars (wLen + 1) accW (tot + 1) cs
      let (endW, midWords, nextTot) := processChars curWordLen words totalChars chars
      toSegments endW midWords nextTot rest
    | .openTag _ :: rest | .closeTag :: rest | .floating :: rest | .wbr :: rest =>
      toSegments curWordLen words totalChars rest
    | .atomicInline wPx :: rest =>
      let wordsAfterPrev := if curWordLen > 0 then curWordLen :: words else words
      let wordsWithAtomic := (wPx / 10) :: wordsAfterPrev
      toSegments 0 wordsWithAtomic (totalChars + (wPx / 10)) rest
    | .br :: rest | .newline :: rest =>
      let wordsAfterPrev := if curWordLen > 0 then curWordLen :: words else words
      toSegments 0 wordsAfterPrev totalChars rest
    | .symbolMarker s :: rest =>
      toSegments (curWordLen + s.length) words (totalChars + s.length) rest
  let (wordLengths, totalCharCount) := toSegments 0 [] 0 tokens
  let maxWord := wordLengths.foldl Nat.max 0
  { minSize := clampLayoutUnit (maxWord * 10), maxSize := clampLayoutUnit (totalCharCount * 10) }

/-! ## 5. General Laws for LayoutUnit Saturation (CSS Values and Units 3 §6) -/

/-- CSS Values and Units 3 §6 Law: Values exceeding layoutUnitMaxInt clamp to layoutUnitMaxInt. -/
theorem clampLayoutUnit_overflow (v : Nat) (h : v > layoutUnitMaxInt) :
    clampLayoutUnit v = layoutUnitMaxInt := by
  unfold clampLayoutUnit
  simp [h]

/-- CSS Values and Units 3 §6 Law: Values within layoutUnitMaxInt are preserved. -/
theorem clampLayoutUnit_within (v : Nat) (h : ¬ (v > layoutUnitMaxInt)) :
    clampLayoutUnit v = v := by
  unfold clampLayoutUnit
  simp [h]

/-- CSS Values and Units 3 §6 Law: Clamped value never exceeds layoutUnitMaxInt. -/
theorem clampLayoutUnit_le_max (v : Nat) :
    clampLayoutUnit v ≤ layoutUnitMaxInt := by
  unfold clampLayoutUnit
  split
  · exact Nat.le_refl _
  · omega

/-! ## 6. Inline Tree Mutation & Invalidation (CSS 2.1 §9.4.2 & CSS Inline 3 §2) -/

/-- DOM node mutation or style change operation affecting inline layout invalidation. -/
inductive InlineMutation where
  | insertNode (isOutOfFlowIndependent : Bool := false)
  | removeNode
  | changeStyle (affectsInlines : Bool := true)
  deriving DecidableEq, Repr, Inhabited

/-- CSS 2.1 §9.4.2 & Blink InlineNode::SetNeedsCollectInlines:
    Determine `needsCollectInlines` flags for modified target, parent, container, and sibling nodes.
    - Ancestors up to the containing block flow (target, parent, container) are invalidated (marked true)
      when an inline-affecting mutation occurs within the formatting context.
    - Sibling nodes outside the ancestor path are unaffected (marked false).
    - Modifications inside an independent out-of-flow formatting context do not invalidate the container. -/
def computeNeedsCollectInlines (op : InlineMutation) : Bool × Bool × Bool × Bool :=
  match op with
  | .insertNode true => (false, false, false, false)
  | .insertNode false => (true, true, true, false)
  | .removeNode => (true, true, true, false)
  | .changeStyle true => (true, true, true, false)
  | .changeStyle false => (false, false, false, false)

/-- CSS 2.1 §9.4.2 Law: Siblings outside the modified ancestor chain never need inline recolletion. -/
theorem siblings_never_need_collect_inlines (op : InlineMutation) :
    (computeNeedsCollectInlines op).2.2.2 = false := by
  cases op with
  | insertNode b => cases b <;> rfl
  | removeNode => rfl
  | changeStyle b => cases b <;> rfl

/-- CSS 2.1 §9.4.2 Law: In-flow insertion or removal always marks parent and container for inline collection. -/
theorem inflow_mutation_invalidates_ancestors (isInsert : Bool) :
    let (_, p, c, _) := computeNeedsCollectInlines (if isInsert then .insertNode false else .removeNode)
    p = true ∧ c = true := by
  cases isInsert <;> exact ⟨rfl, rfl⟩

end ChromiumLayout
