/-
  docs/chromium-layout/Layout.lean

  Formal model of Chromium Blink LayoutNG's CSS 2.1 in-flow block and inline
  formatting contexts in Lean 4.34.0 (core only, no Mathlib).

  Pinned Chromium revision: 36c121be58126ddbb0686965897b8c8ff9b246fb
  Subtree: third_party/blink/renderer/core/layout/

  This file defines the types, layout functions, and hypotheses referenced by
  Laws 1–5 in `docs/chromium-layout/SCOPE.md` §4, with file:line references to
  the Blink C++ source at the pinned revision.
-/

namespace ChromiumLayout

/-! ## 1. Geometry, `BoxStrut`, and Signed `MarginStrut` (M1)
    Source:
    - `geometry/box_strut.h:33-114`, `geometry/box_strut.cc:14-54`
    - `geometry/margin_strut.h:16-58`, `geometry/margin_strut.cc:11-46`
    - `geometry/logical_size.h:19-65`, `geometry/logical_offset.h:19-68`
    - `platform/fonts/font_height.h:42-95`
-/

/-- `BoxStrut` (`geometry/box_strut.h:33-114`): logical box-model widths
    (margins, borders, or padding) on all four edges, in `LayoutUnit` quanta (`1/64` px). -/
structure BoxStrut where
  inlineStart : Nat := 0
  inlineEnd   : Nat := 0
  blockStart  : Nat := 0
  blockEnd    : Nat := 0
  deriving DecidableEq, Repr

namespace BoxStrut

/-- `BoxStrut::InlineSum()` (`geometry/box_strut.h:62`). -/
def inlineSum (s : BoxStrut) : Nat :=
  s.inlineStart + s.inlineEnd

/-- `BoxStrut::BlockSum()` (`geometry/box_strut.h:63`). -/
def blockSum (s : BoxStrut) : Nat :=
  s.blockStart + s.blockEnd

/-- `BoxStrut::IsEmpty()` (`geometry/box_strut.h:68`). -/
def isEmpty (s : BoxStrut) : Bool :=
  s.inlineStart == 0 && s.inlineEnd == 0 && s.blockStart == 0 && s.blockEnd == 0

end BoxStrut

/-- `MarginStrut` (`geometry/margin_strut.h:16-58`, `geometry/margin_strut.cc:11-46`):
    stores the largest positive margin (`pos`) and largest negative margin magnitude (`neg`)
    participating in CSS 2.1 §8.3.1 margin collapsing (non-quirky mode). -/
structure MarginStrut where
  pos : Nat := 0
  neg : Nat := 0
  deriving DecidableEq, Repr

namespace MarginStrut

/-- Empty `MarginStrut` (`geometry/margin_strut.h:17-18`). -/
def empty : MarginStrut :=
  { pos := 0, neg := 0 }

/-- `MarginStrut::Append` (`geometry/margin_strut.cc:11-30`, non-quirky case):
    combines two margin struts by taking the maximum positive margin and maximum
    negative margin magnitude. -/
def append (s1 s2 : MarginStrut) : MarginStrut :=
  { pos := Nat.max s1.pos s2.pos, neg := Nat.max s1.neg s2.neg }

/-- `MarginStrut::Sum` (`geometry/margin_strut.h:40-44`, non-quirky case):
    net collapsed margin (`positive_margin + negative_margin`, clamped to `Nat`). -/
def sum (s : MarginStrut) : Nat :=
  s.pos - s.neg

/-- Apply a signed `MarginStrut` offset (`+ s.pos - s.neg`) to a block offset `y`
    (`geometry/margin_strut.h:40-44`). -/
def applyOffset (y : Nat) (s : MarginStrut) : Nat :=
  (y + s.pos) - s.neg

/-- `MarginStrut::IsEmpty()` (`geometry/margin_strut.cc:32-37`). -/
def isEmpty (s : MarginStrut) : Bool :=
  s.pos == 0 && s.neg == 0

end MarginStrut

/-- `FontHeight` (`platform/fonts/font_height.h:42-95`, used in `inline/inline_box_state.h:52`):
    baseline-relative ascent and descent in `LayoutUnit`s. -/
structure FontHeight where
  ascent  : Nat := 0
  descent : Nat := 0
  deriving DecidableEq, Repr

namespace FontHeight

/-- `FontHeight::LineHeight()` (`platform/fonts/font_height.h:61`). -/
def lineHeight (h : FontHeight) : Nat :=
  h.ascent + h.descent

/-- `FontHeight::Merge` (`platform/fonts/font_height.h:85`, `inline/inline_box_state.cc:295`):
    enclosing ascent and descent of two baseline-aligned metrics. -/
def merge (h1 h2 : FontHeight) : FontHeight :=
  { ascent := Nat.max h1.ascent h2.ascent, descent := Nat.max h1.descent h2.descent }

end FontHeight

/-- `LogicalSize` (`geometry/logical_size.h:19-65`). -/
structure LogicalSize where
  inlineSize : Nat := 0
  blockSize  : Nat := 0
  deriving DecidableEq, Repr

/-- `LogicalOffset` (`geometry/logical_offset.h:19-68`). -/
structure LogicalOffset where
  inlineOffset : Nat := 0
  blockOffset  : Nat := 0
  deriving DecidableEq, Repr

/-- `ConstraintSpace` (`constraint_space.h:47-180`): top-down layout constraints passed
    into `BlockLayoutAlgorithm` and `InlineLayoutAlgorithm`. -/
structure ConstraintSpace where
  availableInlineSize : Nat := 0
  bfcLineOffset       : Nat := 0
  bfcBlockOffset      : Nat := 0
  marginStrut         : MarginStrut := MarginStrut.empty
  isNewBfc            : Bool := true
  deriving DecidableEq, Repr

/-! ## 2. Inline Items, Greedy Line Breaking, and Line Box Construction (M3 & M4)
    Source:
    - `inline/inline_item.h:35-190`, `inline/inline_items_builder.cc:110-320`
    - `inline/line_breaker.h:67-287`, `inline/line_breaker.cc:897-1130, 1337-1450, 2432-2515`
    - `inline/line_info.h:38-185`, `inline/inline_box_state.cc:277-445`
    - `inline/inline_layout_algorithm.cc:345-430`
-/

/-- `InlineItem` (`inline/inline_item.h:35-190`, `SCOPE.md` §3):
    flat item representation of an inline formatting context. -/
inductive InlineItem where
  | TextSeg
      (itemId : Nat)
      (inlineSize : Nat)
      (metrics : FontHeight)
      (canBreakAfter : Bool)
      (isCollapsibleSpace : Bool)
  | AtomicInline
      (itemId : Nat)
      (borderSize : LogicalSize)
      (margins : BoxStrut)
      (baselineAscent : Nat)
  | OpenTag
      (itemId : Nat)
      (inlineStartEdge : Nat)
      (strut : FontHeight)
  | CloseTag
      (itemId : Nat)
      (inlineEndEdge : Nat)
  | ForcedBreak
      (itemId : Nat)
  deriving DecidableEq, Repr

namespace InlineItem

abbrev TextSegment := TextSeg
abbrev OpenSpan := OpenTag
abbrev CloseSpan := CloseTag
abbrev HardBreak := ForcedBreak

/-- Item identifier (`SCOPE.md` §3). -/
def itemId : InlineItem → Nat
  | TextSeg id _ _ _ _ => id
  | AtomicInline id _ _ _ => id
  | OpenTag id _ _ => id
  | CloseTag id _ => id
  | ForcedBreak id => id

/-- Advance width of an `InlineItem` before trailing-space collapse
    (`inline/line_breaker.cc:1337, 3060, 3984, 4037`). -/
def rawInlineSize : InlineItem → Nat
  | TextSeg _ w _ _ _ => w
  | AtomicInline _ sz m _ => m.inlineStart + sz.inlineSize + m.inlineEnd
  | OpenTag _ w _ => w
  | CloseTag _ w => w
  | ForcedBreak _ => 0

/-- Whether an `InlineItem` is a collapsible space token
    (`inline/line_breaker.cc:2440`). -/
def isCollapsible : InlineItem → Bool
  | TextSeg _ _ _ _ isSpace => isSpace
  | _ => false

/-- Whether an `InlineItem` is a forced line break (`<br>` / `\n`,
    `inline/line_breaker.cc:1076`). -/
def isForcedBreak : InlineItem → Bool
  | ForcedBreak _ => true
  | _ => false

/-- Baseline-aligned `FontHeight` contributed by an `InlineItem`
    (`inline/inline_box_state.cc:295, 396`, `inline/logical_line_builder.cc`). -/
def fontHeight : InlineItem → FontHeight
  | TextSeg _ _ m _ _ => m
  | AtomicInline _ sz m asc =>
      { ascent := m.blockStart + asc
      , descent := (sz.blockSize - asc) + m.blockEnd }
  | OpenTag _ _ s => s
  | CloseTag _ _ => { ascent := 0, descent := 0 }
  | ForcedBreak _ => { ascent := 0, descent := 0 }

end InlineItem

/-- `LineInfo` (`inline/line_info.h:38-185`, `SCOPE.md` §4):
    per-line output of `LineBreaker::NextLine`. -/
structure LineInfo where
  items             : List InlineItem := []
  inlineSize        : Nat := 0
  nonBreakItemCount : Nat := 0
  deriving DecidableEq, Repr

/-- `PlacedInlineItem` (`inline/logical_line_item.h:35-140`, `SCOPE.md` §3):
    an inline item positioned within a `LineBoxFragment`. -/
structure PlacedInlineItem where
  itemId       : Nat := 0
  inlineOffset : Nat := 0
  blockOffset  : Nat := 0
  inlineSize   : Nat := 0
  blockSize    : Nat := 0
  deriving DecidableEq, Repr

/-- `LineBoxFragment` (`inline/physical_line_box_fragment.h:28-95`, `SCOPE.md` §3). -/
structure LineBoxFragment where
  bfcOffset  : LogicalOffset := {}
  inlineSize : Nat := 0
  metrics    : FontHeight := {}
  items      : List PlacedInlineItem := []
  deriving DecidableEq, Repr

/-- Auxiliary greedy line-breaking loop after the first item on a line has been consumed
    (`LineBreaker::BreakLine` and `LineBreaker::HandleTrailingSpaces`,
    `inline/line_breaker.cc:1024-1130, 2432-2515`).
    Returns `(tailItems, finalCommittedWidth, finalNonBreakCount, remainingItems)`. -/
def takeLineAux (avail curWidth pendingSpace nonBreakCount : Nat) :
    List InlineItem → List InlineItem × Nat × Nat × List InlineItem
  | [] => ([], curWidth, nonBreakCount, [])
  | next :: more =>
    match next with
    | .ForcedBreak _ =>
      -- A forced break is consumed onto the current line and immediately ends the line.
      ([next], curWidth, nonBreakCount, more)
    | .TextSeg _ w _ _ true =>
      -- Trailing collapsible space hangs without increasing `curWidth` until a non-space item follows.
      if curWidth ≤ avail then
        let (subItems, finalW, finalCnt, rem) :=
          takeLineAux avail curWidth (pendingSpace + w) (nonBreakCount + 1) more
        (next :: subItems, finalW, finalCnt, rem)
      else
        ([], curWidth, nonBreakCount, next :: more)
    | _ =>
      let w := next.rawInlineSize
      let newWidth := curWidth + pendingSpace + w
      if newWidth ≤ avail then
        let (subItems, finalW, finalCnt, rem) :=
          takeLineAux avail newWidth 0 (nonBreakCount + 1) more
        (next :: subItems, finalW, finalCnt, rem)
      else
        ([], curWidth, nonBreakCount, next :: more)

/-- `LineBreaker::NextLine` (`inline/line_breaker.cc:897-925`):
    always consumes `first` (guaranteeing progress even when `first` overflows `avail`)
    and greedily packs subsequent items from `rest` via `takeLineAux`. -/
def takeLine (avail : Nat) (first : InlineItem) (rest : List InlineItem) :
    LineInfo × List InlineItem :=
  match first with
  | .ForcedBreak _ =>
    ({ items := [first], inlineSize := 0, nonBreakItemCount := 0 }, rest)
  | .TextSeg _ w _ _ true =>
    let (tailItems, finalW, finalCnt, rem) := takeLineAux avail 0 w 1 rest
    ({ items := first :: tailItems, inlineSize := finalW, nonBreakItemCount := finalCnt }, rem)
  | _ =>
    let w := first.rawInlineSize
    let (tailItems, finalW, finalCnt, rem) := takeLineAux avail w 0 1 rest
    ({ items := first :: tailItems, inlineSize := finalW, nonBreakItemCount := finalCnt }, rem)

/-- Fuel-driven line-breaking loop (`inline/inline_layout_algorithm.cc:1340-1410`),
    with explicit termination measure `fuel = items.length`. -/
def breakLinesFuel : Nat → Nat → List InlineItem → List LineInfo
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, avail, first :: rest =>
    let (line, rem) := takeLine avail first rest
    line :: breakLinesFuel fuel avail rem

/-- `breakLines` (`inline/line_breaker.cc:897`, `SCOPE.md` §4 Law 4):
    packs `items` into lines of width at most `avail` (with single-item fallback on overflow). -/
def breakLines (avail : Nat) (items : List InlineItem) : List LineInfo :=
  breakLinesFuel items.length avail items

/-- Accumulate `FontHeight` across all items on a line, starting from the line strut
    (`InlineLayoutStateStack::OnBeginPlaceItems` / `OnOpenTag` / `OnEndPlaceItems`,
    `inline/inline_box_state.cc:277-445`). -/
def accumulateLineMetrics (strut : FontHeight) : List InlineItem → FontHeight
  | [] => strut
  | it :: rest => FontHeight.merge it.fontHeight (accumulateLineMetrics strut rest)

/-- Position each item on a line box relative to the line's baseline `lineMetrics.ascent`
    (`InlineLayoutStateStack::OnEndPlaceItems` and `ComputeInlinePositions`,
    `inline/inline_box_state.cc:426-445, 855-910`). -/
def placeLineItems (lineMetrics : FontHeight) (inlineOffset : Nat) :
    List InlineItem → List PlacedInlineItem
  | [] => []
  | it :: rest =>
    let fh := it.fontHeight
    let w := it.rawInlineSize
    let placed : PlacedInlineItem :=
      { itemId := it.itemId
      , inlineOffset := inlineOffset
      , blockOffset := lineMetrics.ascent - fh.ascent
      , inlineSize := w
      , blockSize := fh.ascent + fh.descent }
    placed :: placeLineItems lineMetrics (inlineOffset + w) rest

/-- `InlineLayoutAlgorithm::CreateLine` (`inline/inline_layout_algorithm.cc:378-430`,
    `SCOPE.md` §4 Law 5): constructs a `LineBoxFragment` from the line strut and `LineInfo`. -/
def createLineBox (strut : FontHeight) (lineInfo : LineInfo) : LineBoxFragment :=
  let metrics := accumulateLineMetrics strut lineInfo.items
  { bfcOffset := { inlineOffset := 0, blockOffset := 0 }
  , inlineSize := lineInfo.inlineSize
  , metrics := metrics
  , items := placeLineItems metrics 0 lineInfo.items }

/-! ## 3. In-Flow Block Layout (`BlockLayoutAlgorithm`, M2)
    Source:
    - `block_layout_algorithm.h:34-430`, `block_layout_algorithm.cc:555-576, 800-935, 1172-1500, 2385-3137, 3851-3915`
    - `physical_box_fragment.h:40-160`, `layout_result.h:45-210`
-/

/-- `ChildBoxFragment` (`physical_box_fragment.h:40-160`, `SCOPE.md` §3):
    a placed child box fragment inside a block container's fragment. -/
structure ChildBoxFragment where
  nodeId        : Nat := 0
  offset        : LogicalOffset := {}
  borderBoxSize : LogicalSize := {}
  lines         : List LineBoxFragment := []
  deriving DecidableEq, Repr

/-- `PhysicalBoxFragment` (`physical_box_fragment.h:40-160`, `SCOPE.md` §3). -/
structure PhysicalBoxFragment where
  nodeId        : Nat := 0
  offset        : LogicalOffset := {}
  borderBoxSize : LogicalSize := {}
  children      : List ChildBoxFragment := []
  lines         : List LineBoxFragment := []
  deriving DecidableEq, Repr

/-- `LayoutResult` (`layout_result.h:45-210`, `SCOPE.md` §3). -/
structure LayoutResult where
  fragment           : PhysicalBoxFragment := {}
  bfcBlockOffset     : Option Nat := none
  endMarginStrut     : MarginStrut := MarginStrut.empty
  intrinsicBlockSize : Nat := 0
  deriving DecidableEq, Repr

/-- `LayoutInputNode` (`block_node.h:31-145`, `inline/inline_node.h:34-126`, `SCOPE.md` §3):
    an in-flow child inside a block formatting context. -/
inductive LayoutInputNode where
  | blockChild
      (nodeId : Nat)
      (border : BoxStrut)
      (padding : BoxStrut)
      (margin : BoxStrut)
      (explicitInlineSize : Option Nat)
      (explicitBlockSize : Option Nat)
      (isNewBfc : Bool)
      (contentBlockSize : Nat)
      (hasInflowContent : Bool)
      (innerStartMargin : MarginStrut)
      (innerEndMargin : MarginStrut)
  | inlineChild
      (nodeId : Nat)
      (border : BoxStrut)
      (padding : BoxStrut)
      (margin : BoxStrut)
      (explicitInlineSize : Option Nat)
      (explicitBlockSize : Option Nat)
      (lineStrut : FontHeight)
      (items : List InlineItem)
  deriving DecidableEq, Repr

/-- `BlockContainerNode` (`block_node.h:31-145`, `SCOPE.md` §3 & §4):
    a block container with a list of in-flow children. -/
structure BlockContainerNode where
  nodeId             : Nat := 0
  border             : BoxStrut := {}
  padding            : BoxStrut := {}
  margin             : BoxStrut := {}
  explicitInlineSize : Option Nat := none
  explicitBlockSize  : Option Nat := none
  isNewBfc           : Bool := true
  children           : List LayoutInputNode := []
  deriving DecidableEq, Repr

namespace LayoutInputNode

def nodeId : LayoutInputNode → Nat
  | blockChild id _ _ _ _ _ _ _ _ _ _ => id
  | inlineChild id _ _ _ _ _ _ _ => id

def border : LayoutInputNode → BoxStrut
  | blockChild _ b _ _ _ _ _ _ _ _ _ => b
  | inlineChild _ b _ _ _ _ _ _ => b

def padding : LayoutInputNode → BoxStrut
  | blockChild _ _ p _ _ _ _ _ _ _ _ => p
  | inlineChild _ _ p _ _ _ _ _ => p

def margin : LayoutInputNode → BoxStrut
  | blockChild _ _ _ m _ _ _ _ _ _ _ => m
  | inlineChild _ _ _ m _ _ _ _ => m

def explicitInlineSize : LayoutInputNode → Option Nat
  | blockChild _ _ _ _ w _ _ _ _ _ _ => w
  | inlineChild _ _ _ _ w _ _ _ => w

def explicitBlockSize : LayoutInputNode → Option Nat
  | blockChild _ _ _ _ _ h _ _ _ _ _ => h
  | inlineChild _ _ _ _ _ h _ _ => h

/-- Whether a child has a block-start edge (border, padding, or new BFC) separating
    its block-start margin from its own descendants (`block_layout_algorithm.cc:846, 882-883`). -/
def hasBlockStartEdge : LayoutInputNode → Bool
  | blockChild _ b p _ _ _ isBfc _ _ _ _ => isBfc || (b.blockStart + p.blockStart > 0)
  | inlineChild _ b p _ _ _ _ _ => b.blockStart + p.blockStart > 0

/-- Whether a child has a block-end edge (border, padding, explicit block size, or new BFC)
    preventing its descendants' trailing margin from collapsing out (`block_layout_algorithm.cc:1286, 1443`). -/
def hasBlockEndEdge : LayoutInputNode → Bool
  | blockChild _ b p _ _ h isBfc _ _ _ _ => isBfc || (b.blockEnd + p.blockEnd > 0) || h.isSome
  | inlineChild _ b p _ _ h _ _ => (b.blockEnd + p.blockEnd > 0) || h.isSome

/-- Whether a child is self-collapsing (`LayoutResult::IsSelfCollapsing`,
    `block_layout_algorithm.cc:1480-1484, 2406, 2941`): zero border-box block size and no
    in-flow content or BFC boundary. -/
def isSelfCollapsing : LayoutInputNode → Bool
  | blockChild _ b p _ _ h isBfc contentSz hasContent _ _ =>
      !isBfc && (b.blockSum + p.blockSum == 0) && h.isNone && !hasContent && (contentSz == 0)
  | inlineChild _ b p _ _ h _ items =>
      (b.blockSum + p.blockSum == 0) && h.isNone && items.isEmpty

/-- Effective block-start `MarginStrut` of a child (`block_layout_algorithm.cc:2879-2906`),
    including parent-child block-start collapse when `!hasBlockStartEdge`. -/
def startMarginStrut (c : LayoutInputNode) : MarginStrut :=
  let ownStart : MarginStrut := { pos := c.margin.blockStart, neg := 0 }
  match c with
  | blockChild _ _ _ _ _ _ _ _ _ innerStart _ =>
      if c.hasBlockStartEdge then ownStart else MarginStrut.append ownStart innerStart
  | inlineChild _ _ _ _ _ _ _ _ => ownStart

/-- Effective block-end `MarginStrut` of a child (`block_layout_algorithm.cc:3030-3038`),
    including parent-child block-end collapse when `!hasBlockEndEdge`. -/
def endMarginStrut (c : LayoutInputNode) : MarginStrut :=
  let ownEnd : MarginStrut := { pos := c.margin.blockEnd, neg := 0 }
  match c with
  | blockChild _ _ _ _ _ _ _ _ _ _ innerEnd =>
      if c.hasBlockEndEdge then ownEnd else MarginStrut.append innerEnd ownEnd
  | inlineChild _ _ _ _ _ _ _ _ => ownEnd

/-- Line boxes produced by an `inlineChild` (`inline/inline_layout_algorithm.cc:1340-1410`). -/
def inlineChildLines : LayoutInputNode → List LineBoxFragment
  | blockChild _ _ _ _ _ _ _ _ _ _ _ => []
  | inlineChild _ b p _ expW _ strut items =>
      let avail := expW.getD 0 - (b.inlineSum + p.inlineSum)
      (breakLines avail items).map (createLineBox strut)

/-- Total block size of a list of line boxes stacked vertically. -/
def linesTotalBlockSize : List LineBoxFragment → Nat
  | [] => 0
  | l :: rest => (l.metrics.ascent + l.metrics.descent) + linesTotalBlockSize rest

/-- Border-box block size of a child (`block_layout_algorithm.cc:1401-1406`). -/
def borderBoxBlockSize (c : LayoutInputNode) : Nat :=
  if c.isSelfCollapsing then
    0
  else
    match c with
    | blockChild _ b p _ _ expH _ contentSz _ _ innerEnd =>
        let trailing := if c.hasBlockEndEdge then innerEnd.sum else 0
        let intrinsic := b.blockStart + p.blockStart + contentSz + trailing + p.blockEnd + b.blockEnd
        expH.getD intrinsic
    | inlineChild _ b p _ _ expH _ _ =>
        let linesSz := linesTotalBlockSize c.inlineChildLines
        let intrinsic := b.blockStart + p.blockStart + linesSz + p.blockEnd + b.blockEnd
        expH.getD intrinsic

/-- Resolve a child's border-box inline size (`CSS 2.1 §10.3.3`, `length_utils.cc`). -/
def resolveInlineSize (availInline : Nat) (c : LayoutInputNode) : Nat :=
  match c.explicitInlineSize with
  | some w => w
  | none => availInline - c.margin.inlineSum

end LayoutInputNode

/-- State returned by the recursive child-layout pass `layoutChildren`
    (`PreviousInflowPosition` in `block_layout_algorithm.h:34-44`). -/
structure ChildrenLayoutState where
  fragments          : List ChildBoxFragment := []
  bfcResolved        : Bool := false
  firstResolvedStrut : MarginStrut := MarginStrut.empty
  logicalBlockOffset : Nat := 0
  marginStrut        : MarginStrut := MarginStrut.empty
  deriving DecidableEq, Repr

/-- Recursive in-flow child layout loop over `List LayoutInputNode`
    (`BlockLayoutAlgorithm::Layout`, `HandleInflow`, `ComputeInflowPosition`,
    `block_layout_algorithm.cc:986-1117, 2385-2805, 2927-3060`). -/
def layoutChildren
    (availInline : Nat)
    (bfcResolved : Bool)
    (pos : Nat)
    (strut : MarginStrut) :
    List LayoutInputNode → ChildrenLayoutState
  | [] =>
      { fragments := []
      , bfcResolved := bfcResolved
      , firstResolvedStrut := strut
      , logicalBlockOffset := pos
      , marginStrut := strut }
  | c :: rest =>
      let startStrut := MarginStrut.append strut c.startMarginStrut
      let endStrut := c.endMarginStrut
      let inlineSz := c.resolveInlineSize availInline
      let inlineOff := c.margin.inlineStart
      if c.isSelfCollapsing then
        let blockOff := if bfcResolved then pos + startStrut.sum else 0
        let frag : ChildBoxFragment :=
          { nodeId := c.nodeId
          , offset := { inlineOffset := inlineOff, blockOffset := blockOff }
          , borderBoxSize := { inlineSize := inlineSz, blockSize := 0 }
          , lines := [] }
        let nextStrut := MarginStrut.append startStrut endStrut
        let tailState := layoutChildren availInline bfcResolved pos nextStrut rest
        { tailState with fragments := frag :: tailState.fragments }
      else
        let blockOff := if bfcResolved then pos + startStrut.sum else 0
        let blkSz := c.borderBoxBlockSize
        let frag : ChildBoxFragment :=
          { nodeId := c.nodeId
          , offset := { inlineOffset := inlineOff, blockOffset := blockOff }
          , borderBoxSize := { inlineSize := inlineSz, blockSize := blkSz }
          , lines := c.inlineChildLines }
        let nextPos := blockOff + blkSz
        let tailState := layoutChildren availInline true nextPos endStrut rest
        { tailState with
          fragments := frag :: tailState.fragments
          firstResolvedStrut := if bfcResolved then strut else startStrut }

/-- `BlockLayoutAlgorithm::Layout` and `FinishLayout`
    (`block_layout_algorithm.cc:800-1500`, `SCOPE.md` §4 Laws 2 & 3). -/
def layoutBlock (space : ConstraintSpace) (node : BlockContainerNode) : LayoutResult :=
  let borderBoxInline :=
    match node.explicitInlineSize with
    | some w => w
    | none => space.availableInlineSize - node.margin.inlineSum
  let childAvailInline := borderBoxInline - (node.border.inlineSum + node.padding.inlineSum)
  let contentStart := node.border.blockStart + node.padding.blockStart
  let hasStartEdge := (contentStart > 0) || space.isNewBfc || node.isNewBfc
  let initResolved := hasStartEdge
  let initPos := if hasStartEdge then contentStart else 0
  let initStrut := if hasStartEdge then MarginStrut.empty else space.marginStrut
  let st := layoutChildren childAvailInline initResolved initPos initStrut node.children
  let contentEnd := node.padding.blockEnd + node.border.blockEnd
  let hasEndEdge := (contentEnd > 0) || space.isNewBfc || node.isNewBfc
  if !st.bfcResolved then
    if contentEnd == 0 && node.explicitBlockSize.isNone then
      -- Self-collapsing container (`block_layout_algorithm.cc:1480-1484`).
      { fragment :=
          { nodeId := node.nodeId
          , offset := { inlineOffset := space.bfcLineOffset, blockOffset := space.bfcBlockOffset }
          , borderBoxSize := { inlineSize := borderBoxInline, blockSize := 0 }
          , children := st.fragments
          , lines := [] }
      , bfcBlockOffset := none
      , endMarginStrut := st.marginStrut
      , intrinsicBlockSize := 0 }
    else
      let resolvedBfc := space.bfcBlockOffset + st.marginStrut.sum
      let intrinsic := contentEnd
      let finalBlock := node.explicitBlockSize.getD intrinsic
      { fragment :=
          { nodeId := node.nodeId
          , offset := { inlineOffset := space.bfcLineOffset, blockOffset := resolvedBfc }
          , borderBoxSize := { inlineSize := borderBoxInline, blockSize := finalBlock }
          , children := st.fragments
          , lines := [] }
      , bfcBlockOffset := some resolvedBfc
      , endMarginStrut := MarginStrut.empty
      , intrinsicBlockSize := intrinsic }
  else
    let resolvedBfc :=
      if hasStartEdge then
        space.bfcBlockOffset + space.marginStrut.sum
      else
        space.bfcBlockOffset + st.firstResolvedStrut.sum
    let (intrinsic, outStrut) :=
      if hasEndEdge then
        (st.logicalBlockOffset + st.marginStrut.sum + contentEnd, MarginStrut.empty)
      else
        match node.explicitBlockSize with
        | none => (st.logicalBlockOffset, st.marginStrut)
        | some _ => (st.logicalBlockOffset, MarginStrut.empty)
    let finalBlock := node.explicitBlockSize.getD intrinsic
    { fragment :=
        { nodeId := node.nodeId
        , offset := { inlineOffset := space.bfcLineOffset, blockOffset := resolvedBfc }
        , borderBoxSize := { inlineSize := borderBoxInline, blockSize := finalBlock }
        , children := st.fragments
        , lines := [] }
    , bfcBlockOffset := some resolvedBfc
    , endMarginStrut := outStrut
    , intrinsicBlockSize := intrinsic }

/-! ## 4. Hypotheses and Specification Functions for Laws 2 & 3 (`SCOPE.md` §4) -/

/-- Whether a `LayoutInputNode`'s inner margin struts have zero negative margin components. -/
def ChildMarginsNonNegative : LayoutInputNode → Prop
  | .blockChild _ _ _ _ _ _ _ _ _ innerStart innerEnd =>
      innerStart.neg = 0 ∧ innerEnd.neg = 0
  | .inlineChild _ _ _ _ _ _ _ _ => True

/-- Explicit hypothesis for Law 2 (`SCOPE.md` §4): all children of `node` have non-negative margins. -/
def AllMarginsNonNegative (node : BlockContainerNode) : Prop :=
  ∀ c ∈ node.children, ChildMarginsNonNegative c

/-- Explicit hypothesis for Law 3 (`SCOPE.md` §4): all children of `node` are non-self-collapsing
    with non-negative margins. -/
def AllChildrenNonSelfCollapsing (node : BlockContainerNode) : Prop :=
  ∀ c ∈ node.children, c.isSelfCollapsing = false ∧ ChildMarginsNonNegative c

/-- Total in-flow block size of a sequence of children starting from an incoming `MarginStrut`
    (`SCOPE.md` §4 Law 3). -/
def collapsedFlowBlockSizeFrom (strut : MarginStrut) : List LayoutInputNode → Nat
  | [] => strut.sum
  | c :: rest =>
      (MarginStrut.append strut c.startMarginStrut).sum +
      c.borderBoxBlockSize +
      collapsedFlowBlockSizeFrom c.endMarginStrut rest

/-- Total collapsed in-flow block size of `children` inside a BFC root (`SCOPE.md` §4 Law 3):
    the sum of all children's border-box block sizes plus the collapsed margins before the
    first child, between each adjacent pair `(k, k+1)`, and after the last child. -/
def totalCollapsedFlowBlockSize (children : List LayoutInputNode) : Nat :=
  collapsedFlowBlockSizeFrom MarginStrut.empty children

/-! ## 5. Kernel-Checked Statements of Laws 1–5 (`SCOPE.md` §4) -/

/-- Statement of Law 1 (`margin_strut_semilattice`, `SCOPE.md` §4). -/
def margin_strut_semilattice_stmt : Prop :=
  ∀ (s1 s2 s3 : MarginStrut),
    MarginStrut.append (MarginStrut.append s1 s2) s3 =
      MarginStrut.append s1 (MarginStrut.append s2 s3) ∧
    MarginStrut.append s1 s2 = MarginStrut.append s2 s1 ∧
    MarginStrut.append s1 s1 = s1

/-- Statement of Law 2 (`block_siblings_monotonic_non_overlapping`, `SCOPE.md` §4). -/
def block_siblings_monotonic_non_overlapping_stmt : Prop :=
  ∀ (space : ConstraintSpace) (node : BlockContainerNode)
    (_hNonNeg : AllMarginsNonNegative node)
    (i j : Nat) (hij : i < j)
    (hj : j < (layoutBlock space node).fragment.children.length),
    let cs := (layoutBlock space node).fragment.children
    let ci := cs[i]'(Nat.lt_trans hij hj)
    let cj := cs[j]'hj
    ci.offset.blockOffset + ci.borderBoxSize.blockSize ≤ cj.offset.blockOffset

/-- Statement of Law 3 (`bfc_intrinsic_block_size_conservation`, `SCOPE.md` §4). -/
def bfc_intrinsic_block_size_conservation_stmt : Prop :=
  ∀ (space : ConstraintSpace) (node : BlockContainerNode)
    (_hBfc : node.isNewBfc = true) (_hAuto : node.explicitBlockSize = none)
    (_hNonSelf : AllChildrenNonSelfCollapsing node),
    (layoutBlock space node).intrinsicBlockSize =
      node.border.blockStart + node.padding.blockStart +
      totalCollapsedFlowBlockSize node.children +
      node.padding.blockEnd + node.border.blockEnd

/-- Statement of Law 4 (`line_breaker_progress_and_partition`, `SCOPE.md` §4). -/
def line_breaker_progress_and_partition_stmt : Prop :=
  ∀ (avail : Nat) (items : List InlineItem),
    (breakLines avail items).length ≤ items.length ∧
    (breakLines avail items).flatMap LineInfo.items = items ∧
    ∀ line ∈ breakLines avail items,
      line.nonBreakItemCount ≤ 1 ∨ line.inlineSize ≤ avail

/-- Statement of Law 5 (`line_box_height_encloses_items`, `SCOPE.md` §4). -/
def line_box_height_encloses_items_stmt : Prop :=
  ∀ (strut : FontHeight) (lineInfo : LineInfo)
    (item : PlacedInlineItem)
    (_hMem : item ∈ (createLineBox strut lineInfo).items),
    let line := createLineBox strut lineInfo
    item.blockOffset + item.blockSize ≤ line.metrics.ascent + line.metrics.descent

/-! ## 6. M1 Proofs: `BoxStrut`, Signed `MarginStrut`, Law 1, and Blink Test Vectors -/

theorem MarginStrut.append_assoc (s1 s2 s3 : MarginStrut) :
    MarginStrut.append (MarginStrut.append s1 s2) s3 =
      MarginStrut.append s1 (MarginStrut.append s2 s3) := by
  cases s1
  cases s2
  cases s3
  simp [MarginStrut.append, Nat.max_assoc]

theorem MarginStrut.append_comm (s1 s2 : MarginStrut) :
    MarginStrut.append s1 s2 = MarginStrut.append s2 s1 := by
  cases s1
  cases s2
  simp [MarginStrut.append, Nat.max_comm]

theorem MarginStrut.append_idem (s : MarginStrut) :
    MarginStrut.append s s = s := by
  cases s
  simp [MarginStrut.append]

/-- Law 1 (`margin_strut_semilattice`, `SCOPE.md` §4):
    `MarginStrut.append` (modeling `MarginStrut::Append` in `geometry/margin_strut.cc:11-30`
    for non-quirky margins) is associative, commutative, and idempotent, so
    `MarginStrut.sum` produces the same collapsed margin regardless of how
    adjacent self-collapsing boxes are grouped. -/
theorem margin_strut_semilattice (s1 s2 s3 : MarginStrut) :
    MarginStrut.append (MarginStrut.append s1 s2) s3 =
      MarginStrut.append s1 (MarginStrut.append s2 s3) ∧
    MarginStrut.append s1 s2 = MarginStrut.append s2 s1 ∧
    MarginStrut.append s1 s1 = s1 := by
  exact ⟨MarginStrut.append_assoc s1 s2 s3, MarginStrut.append_comm s1 s2, MarginStrut.append_idem s1⟩

/-- Transcribed Blink unit test vectors for `MarginStrut` and `BoxStrut`
    (`block_layout_algorithm_test.cc:568-1025`, `geometry/box_strut_test.cc:16-135`). -/
def blinkM1TestVectors : List (Nat × Nat) :=
  [ -- CollapsingMarginsCase3 (`block_layout_algorithm_test.cc:605`): max(20, 200) = 200
    ((MarginStrut.append ⟨20, 0⟩ ⟨200, 0⟩).sum, 200)
  , -- CollapsingMarginsCase4 (`block_layout_algorithm_test.cc:662`): max(8, 30) = 30
    ((MarginStrut.append ⟨8, 0⟩ ⟨30, 0⟩).sum, 30)
  , -- CollapsingMarginsCase6 (`block_layout_algorithm_test.cc:810`): max(10, 40) = 40
    ((MarginStrut.append ⟨10, 0⟩ ⟨40, 0⟩).sum, 40)
  , -- CollapsingMarginsEmptyBlockWithClearance (`block_layout_algorithm_test.cc:968-983`):
    -- offset 90 with signed strut {50, 70} gives (90 + 50) - 70 = 70
    (MarginStrut.applyOffset 90 (MarginStrut.append ⟨50, 0⟩ ⟨0, 70⟩), 70)
  , -- CollapsingMarginsEmptyBlockWithClearance (`block_layout_algorithm_test.cc:991-1006`):
    -- {70, 0} appended with {0, 10} -> sum 60; with {0, 20} -> sum 50; with {80, 0} -> sum 60
    ((MarginStrut.append ⟨70, 0⟩ ⟨0, 10⟩).sum, 60)
  , ((MarginStrut.append ⟨70, 10⟩ ⟨0, 20⟩).sum, 50)
  , ((MarginStrut.append ⟨70, 20⟩ ⟨80, 0⟩).sum, 60)
  , -- GeometryUnitsTest (`geometry/box_strut_test.cc:18-24`): BoxStrut(5, 10, 15, 20)
    ((BoxStrut.mk 5 10 15 20).inlineSum, 15)
  , ((BoxStrut.mk 5 10 15 20).blockSum, 35)
  ]

theorem blink_m1_test_vectors_pass :
    ∀ p ∈ blinkM1TestVectors, p.1 = p.2 := by
  decide

#print axioms MarginStrut.append_assoc
#print axioms MarginStrut.append_comm
#print axioms MarginStrut.append_idem
#print axioms margin_strut_semilattice
#print axioms blink_m1_test_vectors_pass

end ChromiumLayout
