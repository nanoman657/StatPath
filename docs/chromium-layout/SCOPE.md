# Formal Model Scope: Chromium Blink LayoutNG Block and Inline Layout in Bend 2 and Lean 4

This document scopes a formal model of Chromium's Blink LayoutNG block and inline formatting contexts in **Bend 2** (`2.0.39`+) and **Lean 4.34.0** (core only, no Mathlib, compiled directly with `lean <file>`), following the verification architecture established in [`bend-engine/`](../../bend-engine/README.md) and [`bend-tls/browser/`](../../bend-tls/browser/README.md).

---

## 1. Pinned Chromium Revision and Verified Source Paths

- **Repository:** `https://github.com/chromium/chromium.git`
- **Pinned Revision:** `36c121be58126ddbb0686965897b8c8ff9b246fb` (`2026-11-06 23:57:42 -0800`, *"Ash: Migrate CellularSetupServiceTest off RunUntilIdle"*)
- **Checkout Method:** Shallow blobless sparse checkout (`git fetch --depth 1 --filter=blob:none` with `git sparse-checkout set third_party/blink/renderer/core/layout`) into `/root/agy-scratch/chromium-layout/chromium` (occupying 111 MB on disk).

Every path listed below under `third_party/blink/renderer/core/layout/` was verified to exist at revision `36c121be58126ddbb0686965897b8c8ff9b246fb` (Note: in current Blink, the `ng_` filename prefix from the LayoutNG migration has been retired; LayoutNG is now the sole layout engine in `core/layout/`):

### 1.1 Block Layout and Core Geometry (`third_party/blink/renderer/core/layout/`)
- `block_layout_algorithm.h`, `block_layout_algorithm.cc` — `BlockLayoutAlgorithm`: in-flow block child layout, BFC block-offset resolution, `ComputeInflowPosition`, `NextBorderEdge`, `CalculateMargins`, `FinishLayout`.
- `block_layout_algorithm_utils.h`, `block_layout_algorithm_utils.cc` — helper routines for block layout and clearance/BFC offset calculations.
- `block_node.h`, `block_node.cc` — `BlockNode`: input node interface for block layout (`Layout`, `ComputeMinMaxSizes`, `FirstChild`).
- `block_child_iterator.h`, `block_child_iterator.cc` — `BlockChildIterator`: iteration over in-flow children.
- `box_fragment_builder.h`, `box_fragment_builder.cc` — `BoxFragmentBuilder`: accumulator for child fragments, BFC offsets, intrinsic block size, and margin struts.
- `constraint_space.h`, `constraint_space.cc`, `constraint_space_builder.h` — `ConstraintSpace` and `ConstraintSpaceBuilder`: available size, percentage resolution size, BFC offset, and margin-strut inputs passed top-down.
- `fragment_builder.h`, `fragment_builder.cc` — `FragmentBuilder`: base builder for box and line-box fragments.
- `layout_result.h`, `layout_result.cc` — `LayoutResult`: immutable output of a layout pass (`GetPhysicalFragment`, `BfcBlockOffset`, `EndMarginStrut`, `IntrinsicBlockSize`, `EStatus`).
- `physical_box_fragment.h`, `physical_box_fragment.cc`, `physical_fragment.h`, `physical_fragment.cc` — `PhysicalBoxFragment` and `PhysicalFragment`: output fragment tree nodes.
- `simplified_layout_algorithm.h`, `simplified_layout_algorithm.cc` — `SimplifiedLayoutAlgorithm`: fast-path relayout preserving child geometry.
- `length_utils.h`, `length_utils.cc`, `space_utils.h`, `space_utils.cc` — `ResolveMainBlockLength`, `ResolveMainInlineLength`, `ComputeBorders`, `ComputePadding`, `ComputeMarginsFor`.
- `geometry/bfc_offset.h`, `geometry/bfc_rect.h` — `BfcOffset` (`line_offset`, `block_offset`) and `BfcRect`.
- `geometry/box_strut.h`, `geometry/box_strut.cc` — `BoxStrut` (`line_left`, `line_right`, `inline_start`, `inline_end`, `block_start`, `block_end`, `InlineSum()`, `BlockSum()`) and `LineBoxStrut`.
- `geometry/fragment_geometry.h` — `FragmentGeometry` (`border_box_size`, `border`, `scrollbar`, `padding`).
- `geometry/logical_offset.h`, `geometry/logical_rect.h`, `geometry/logical_size.h` — `LogicalOffset`, `LogicalRect`, `LogicalSize`.
- `geometry/margin_strut.h`, `geometry/margin_strut.cc` — `MarginStrut` (`positive_margin`, `negative_margin`, `Append`, `Sum`, `IsEmpty`).

### 1.2 Inline Layout (`third_party/blink/renderer/core/layout/inline/`)
- `inline/inline_layout_algorithm.h`, `inline/inline_layout_algorithm.cc` — `InlineLayoutAlgorithm`: constructs line boxes from `LineBreaker` output (`Layout`, `CreateLine`, `PrepareBoxStates`).
- `inline/inline_node.h`, `inline/inline_node.cc`, `inline/inline_node_data.h`, `inline/inline_node_data.cc` — `InlineNode` and `InlineNodeData`: inline formatting context root (`CollectInlines`, `ShapeText`, `ComputeMinMaxSizes`).
- `inline/inline_item.h`, `inline/inline_item.cc` — `InlineItem`: flat representation of inline content (`kText`, `kControl`, `kOpenTag`, `kCloseTag`, `kAtomicInline`).
- `inline/inline_item_result.h`, `inline/inline_item_result.cc` — `InlineItemResult`: measured inline item on a single line (`inline_size`, `margins`, `borders`, `padding`, `can_break_after`).
- `inline/inline_items_builder.h`, `inline/inline_items_builder.cc` — `InlineItemsBuilder`: flattens the DOM/layout inline tree into a sequence of `InlineItem`s and a normalized text buffer.
- `inline/inline_box_state.h`, `inline/inline_box_state.cc` — `InlineBoxState` and `InlineLayoutStateStack`: box-state stack computing `FontHeight` (`ascent`, `descent`), `vertical-align`, inline borders/padding/margins (`OnBeginPlaceItems`, `OnOpenTag`, `OnCloseTag`, `OnEndPlaceItems`).
- `inline/line_breaker.h`, `inline/line_breaker.cc` — `LineBreaker`: greedy line-breaking state machine (`NextLine`, `BreakLine`, `HandleText`, `HandleAtomicInline`, `HandleOpenTag`, `HandleCloseTag`, `HandleTrailingSpaces`).
- `inline/line_info.h`, `inline/line_info.cc` — `LineInfo`: per-line intermediate output (`Results()`, `Width()`, `AvailableWidth()`, `BfcOffset()`, `LineStyle()`).
- `inline/line_widths.h`, `inline/line_widths.cc` — `LineWidths`: line inline-size budget computation.
- `inline/logical_line_builder.h`, `inline/logical_line_builder.cc`, `inline/logical_line_item.h`, `inline/logical_line_item.cc` — `LogicalLineBuilder` and `LogicalLineItem`: converts `LineInfo` results into logical line items and positions them along the inline and block axes.
- `inline/line_box_fragment_builder.h`, `inline/line_box_fragment_builder.cc`, `inline/physical_line_box_fragment.h`, `inline/physical_line_box_fragment.cc` — `LineBoxFragmentBuilder` and `PhysicalLineBoxFragment`: output line-box fragment construction.
- `inline/inline_child_layout_context.h`, `inline/inline_child_layout_context.cc` — `InlineChildLayoutContext`: context shared across adjacent line boxes within a block container.

---

## 2. The First Fragment: CSS 2.1 In-Flow Block and Inline Layout

The first formal fragment covers **CSS 2.1 Section 9.4.1 (Block Formatting Contexts), Section 9.4.2 (Inline Formatting Contexts), Section 8.3.1 (Collapsing Margins — non-negative and signed variants), Section 10.3.3 (Block-level, non-replaced elements in normal flow), Section 10.6.3 (Block-level non-replaced elements in normal flow when `overflow` computes to `visible`), and Section 10.8 (Line height calculations)**, restricted to:

1. **In-Flow Normal Flow Only:**
   - No floats (`float: none`, `clear: none`; `ExclusionSpace` is empty and `unpositioned_floats` is empty).
   - No out-of-flow positioning (`position: static`; no `absolute`, `fixed`, `relative`, or `sticky` offsets; no anchor positioning).
   - No Flexbox, Grid, Table, Multicol, Ruby, SVG text, or Custom layout.
   - No block fragmentation / pagination (`BlockBreakToken` is `None`; `InlineBreakToken` is used solely as a line-to-line cursor index into the `InlineItem` list).
2. **Single Writing Mode and Direction:**
   - Horizontal top-to-bottom (`writing-mode: horizontal-tb`) and left-to-right (`direction: ltr`), so logical coordinates (`inline_offset`, `block_offset`, `inline_size`, `block_size`) coincide with physical `(x, y, width, height)` without bidirectional reordering (UAX #9 Bidi is out of scope for the first fragment).
3. **Fixed-Point Layout Arithmetic (`LayoutUnit` as `Nat` / Signed Pairs):**
   - Blink's `LayoutUnit` is a 32-bit signed fixed-point integer with 6 fractional bits (`1/64` px). In the first fragment, sizes, offsets, borders, padding, and non-negative margins are represented in Bend and Lean as `Nat` (in `1/64`-px units), with signed margins represented as a pair `(pos: Nat, neg: Nat)` matching `MarginStrut { positive_margin, negative_margin }` in `geometry/margin_strut.h`.
4. **Block Formatting Context (BFC) Rules:**
   - Block containers either establish a new BFC (`is_bfc_root: Bool`) or participate in their parent's BFC.
   - Inline-size resolution (`10.3.3`): a child block's border-box inline-size fills `available_inline_size - (margin_inline_start + margin_inline_end)` when `auto`, or takes an explicit border-box inline-size.
   - Block-axis margin collapsing (`MarginStrut::Append` and `MarginStrut::Sum` in `geometry/margin_strut.cc`): adjacent vertical margins collapse between previous siblings (`PreviousInflowPosition`), across parent block-start / first-child when the parent has zero block-start border and padding (`!has_block_start_edge`), across parent block-end / last-child when the parent has `auto` block-size and zero block-end border and padding, and through self-collapsing boxes (zero border-box block-size and no in-flow content).
5. **Inline Formatting Context (IFC) Rules:**
   - An `InlineNode` contains a flat list of `InlineItem`s (`TextSegment`, `AtomicInline`, `OpenSpan`, `CloseSpan`, `HardBreak`).
   - Text shaping and break opportunities are pre-segmented into indivisible `TextSegment` tokens with known `(inline_size, ascent, descent, can_break_after, is_collapsible_space)`.
   - `LineBreaker` packs items greedily into lines of width at most `available_inline_size`, collapsing trailing collapsible spaces and always consuming at least one item per line to guarantee termination even on overflow.
   - `InlineBoxState` computes each line box's `FontHeight` (`ascent = max_i ascent_i`, `descent = max_i descent_i`, `line_height = ascent + descent`) for baseline-aligned (`vertical-align: baseline`) items, and stacks the resulting line boxes vertically in the enclosing block container.

---

## 3. Bend Types for Layout Input and Output

In Bend 2, recursive and algebraic types use `type Name is Data:`. All numerical fields are `Nat` (in `1/64`-px `LayoutUnit` quanta):

```python
import Base

# 1. Box-model struts (geometry/box_strut.h, geometry/margin_strut.h)
type BoxStrut is Data:
  Strut{inline_start: Nat, inline_end: Nat, block_start: Nat, block_end: Nat}

type MarginStrut is Data:
  MStrut{pos: Nat, neg: Nat}

type FontHeight is Data:
  FHeight{ascent: Nat, descent: Nat}

type LogicalSize is Data:
  LSize{inline_size: Nat, block_size: Nat}

type LogicalOffset is Data:
  LOffset{inline_offset: Nat, block_offset: Nat}

type MaybeNat is Data:
  NoneNat{}
  SomeNat{val: Nat}

# 2. Top-down constraint space (constraint_space.h)
type ConstraintSpace is Data:
  CSpace{
    available_inline_size: Nat,
    bfc_line_offset: Nat,
    bfc_block_offset: Nat,
    margin_strut: MarginStrut,
    is_new_bfc: Bool
  }

# 3. Inline Formatting Context input items (inline/inline_item.h)
type InlineItem is Data:
  # Pre-shaped text segment between break opportunities
  TextSeg{
    item_id: Nat,
    inline_size: Nat,
    metrics: FontHeight,
    can_break_after: Bool,
    is_collapsible_space: Bool
  }
  # Atomic inline-level box (e.g. inline-block or replaced inline element)
  AtomicInline{
    item_id: Nat,
    border_size: LogicalSize,
    margins: BoxStrut,
    baseline_ascent: Nat
  }
  # Inline box start/end tags (<span> borders, padding, margins, strut metrics)
  OpenTag{
    item_id: Nat,
    inline_start_edge: Nat,
    strut: FontHeight
  }
  CloseTag{
    item_id: Nat,
    inline_end_edge: Nat
  }
  # Forced line break (<br>)
  ForcedBreak{
    item_id: Nat
  }

# 4. Block Formatting Context input tree (block_node.h, inline/inline_node.h)
type LayoutInputNode is Data:
  # Block container with block-level children
  BlockContainer{
    node_id: Nat,
    border: BoxStrut,
    padding: BoxStrut,
    margin: BoxStrut,
    explicit_inline_size: MaybeNat,
    explicit_block_size: MaybeNat,
    is_new_bfc: Bool,
    children: List<LayoutInputNode>
  }
  # Block container establishing an Inline Formatting Context
  InlineContainer{
    node_id: Nat,
    border: BoxStrut,
    padding: BoxStrut,
    margin: BoxStrut,
    explicit_inline_size: MaybeNat,
    explicit_block_size: MaybeNat,
    line_strut: FontHeight,
    items: List<InlineItem>
  }

# 5. Output Fragment Tree (physical_box_fragment.h, inline/physical_line_box_fragment.h)
type PlacedInlineItem is Data:
  PlacedItem{
    item_id: Nat,
    inline_offset: Nat,
    block_offset: Nat,
    inline_size: Nat,
    block_size: Nat
  }

type LineBoxFragment is Data:
  LineFrag{
    bfc_offset: LogicalOffset,
    inline_size: Nat,
    metrics: FontHeight,
    items: List<PlacedInlineItem>
  }

type PhysicalBoxFragment is Data:
  BoxFrag{
    node_id: Nat,
    offset: LogicalOffset,
    border_box_size: LogicalSize,
    children: List<PhysicalBoxFragment>,
    lines: List<LineBoxFragment>
  }

# 6. LayoutResult (layout_result.h)
type LayoutResult is Data:
  LResult{
    fragment: PhysicalBoxFragment,
    bfc_block_offset: MaybeNat,
    end_margin_strut: MarginStrut,
    intrinsic_block_size: Nat
  }
```

---

## 4. Lean 4 Statements for the First Five Laws

All five laws are stated in Lean 4.34.0 (core only, no Mathlib) over the model types corresponding 1-to-1 to Section 3 (defined and kernel-checked in [`Layout.lean`](./Layout.lean) with no changes to the five statements below):

```lean
namespace ChromiumLayout

/-- Law 1 (`margin_strut_semilattice`):
    `MarginStrut.append` (modeling `MarginStrut::Append` in `geometry/margin_strut.cc`
    for non-quirky margins) is associative, commutative, and idempotent, so
    `MarginStrut.sum` produces the same collapsed margin regardless of how
    adjacent self-collapsing boxes are grouped. -/
theorem margin_strut_semilattice (s1 s2 s3 : MarginStrut) :
    MarginStrut.append (MarginStrut.append s1 s2) s3 =
      MarginStrut.append s1 (MarginStrut.append s2 s3) ∧
    MarginStrut.append s1 s2 = MarginStrut.append s2 s1 ∧
    MarginStrut.append s1 s1 = s1

/-- Law 2 (`block_siblings_monotonic_non_overlapping`):
    In `BlockLayoutAlgorithm::Layout` (`block_layout_algorithm.cc`), for any
    block container laid out with non-negative margins, the placed child box
    fragments `c_0, c_1, ..., c_{n-1}` have monotonically non-decreasing
    block offsets and pairwise disjoint border-box block intervals:
    for all `i < j`, `c_i.offset.blockOffset + c_i.borderBoxSize.blockSize ≤ c_j.offset.blockOffset`. -/
theorem block_siblings_monotonic_non_overlapping
    (space : ConstraintSpace) (node : BlockContainerNode)
    (hNonNeg : AllMarginsNonNegative node)
    (i j : Nat) (hij : i < j)
    (hj : j < (layoutBlock space node).fragment.children.length) :
    let cs := (layoutBlock space node).fragment.children
    let ci := cs[i]'(Nat.lt_trans hij hj)
    let cj := cs[j]'hj
    ci.offset.blockOffset + ci.borderBoxSize.blockSize ≤ cj.offset.blockOffset

/-- Law 3 (`bfc_intrinsic_block_size_conservation`):
    For a BFC-root block container with `explicitBlockSize = none` and `n`
    non-self-collapsing children with non-negative margins, the container's
    `intrinsicBlockSize` equals its block-start border+padding, plus the sum
    of all children's border-box block sizes, plus the collapsed margins before
    the first child, between each adjacent pair `(k, k+1)`, and after the last
    child, plus its block-end border+padding. -/
theorem bfc_intrinsic_block_size_conservation
    (space : ConstraintSpace) (node : BlockContainerNode)
    (hBfc : node.isNewBfc = true) (hAuto : node.explicitBlockSize = none)
    (hNonSelf : AllChildrenNonSelfCollapsing node) :
    (layoutBlock space node).intrinsicBlockSize =
      node.border.blockStart + node.padding.blockStart +
      totalCollapsedFlowBlockSize node.children +
      node.padding.blockEnd + node.border.blockEnd

/-- Law 4 (`line_breaker_progress_and_partition`):
    `LineBreaker::NextLine` (`inline/line_breaker.cc`) makes strict forward
    progress on any non-empty input `items : List InlineItem` (consuming at
    least one item per line even when the first item overflows `availableInlineSize`),
    terminates in at most `items.length` lines, and partitions the input
    items in exact order (`(breakLines avail items).flatMap LineInfo.items = items`). -/
theorem line_breaker_progress_and_partition
    (avail : Nat) (items : List InlineItem) :
    (breakLines avail items).length ≤ items.length ∧
    (breakLines avail items).flatMap LineInfo.items = items ∧
    ∀ line ∈ breakLines avail items,
      line.nonBreakItemCount ≤ 1 ∨ line.inlineSize ≤ avail

/-- Law 5 (`line_box_height_encloses_items`):
    For every line box constructed by `InlineLayoutAlgorithm::CreateLine` and
    `InlineBoxState::OnEndPlaceItems` (`inline/inline_layout_algorithm.cc`,
    `inline/inline_box_state.cc`) from baseline-aligned items, the line box's
    total block size `line.metrics.ascent + line.metrics.descent` is at least
    every placed item's block size, and each item's block interval
    `[item.blockOffset, item.blockOffset + item.blockSize]` lies within
    `[0, line.metrics.ascent + line.metrics.descent]`. -/
theorem line_box_height_encloses_items
    (strut : FontHeight) (lineInfo : LineInfo)
    (item : PlacedInlineItem)
    (hMem : item ∈ (createLineBox strut lineInfo).items) :
    let line := createLineBox strut lineInfo
    item.blockOffset + item.blockSize ≤ line.metrics.ascent + line.metrics.descent
```

---

## 5. Assumptions Taken as Axioms (Input Boundaries)

Following the pattern in `bend-engine` and `bend-tls/browser`, the formal model does **not** add `axiom` declarations to Lean's kernel (`#print axioms` must report only `propext`, `Classical.choice`, `Quot.sound`). Instead, lower-level subsystems outside `core/layout/` are factored out as **typed input parameters with explicit structural preconditions** (what the model takes as given from the caller):

1. **Font Metrics (`platform/fonts/font_height.h`, `SimpleFontData`):**
   - FreeType / Skia font tables and `FontMetrics::Ascent()` / `Descent()` / `LineGap()` are not modelled.
   - Each `InlineItem` and `InlineContainer` carries a pre-computed `FontHeight { ascent : Nat, descent : Nat }` in `LayoutUnit`s (`1/64` px).
   - **Precondition:** `ascent ≥ 0` and `descent ≥ 0` (guaranteed by `Nat` representation).
2. **Text Shaping (`platform/fonts/shaping/harfbuzz_shaper.h`, `ShapeResult`):**
   - HarfBuzz glyph shaping, OpenType kerning/ligatures, font fallback cascades, and sub-run slicing (`ShapingLineBreaker`) are not modelled.
   - Text is provided as a list of atomic `TextSeg` tokens between candidate break opportunities, each carrying its shaped advance width `inline_size : Nat`.
   - **Precondition (Sub-additivity / Monotonicity):** Joining two adjacent unsplit text runs without hyphenation has width equal to the sum of their segment widths (`width(s_1 ++ s_2) = width(s_1) + width(s_2)`).
3. **Unicode Line Breaking and Bidirectional Reordering (ICU `TextBreakIterator`, `BidiParagraph`):**
   - ICU UAX #14 line-break iteration (`platform/text/text_break_iterator.h`) and UAX #9 bidirectional reordering (`inline/inline_items_builder.cc`) are abstracted into boolean flags on each `TextSeg` (`can_break_after : Bool`, `is_collapsible_space : Bool`) and `ForcedBreak` items.
4. **Computed Style and Length Resolution (`core/style/computed_style.h`, `length_utils.cc`):**
   - CSS cascade, inheritance, `calc()`, `em`/`rem`/`vw`/`vh`, and percentage resolution up to `LayoutUnit` values are assumed already resolved into `BoxStrut` and `MaybeNat` (`explicit_inline_size`, `explicit_block_size`) before entering the pure layout functions.

---

## 6. Size of the Source Being Modelled and Counting Method

### 6.1 Counting Method
All counts were computed at Chromium revision `36c121be58126ddbb0686965897b8c8ff9b246fb` under `third_party/blink/renderer/core/layout/` using a deterministic Python line counter (`wc -l` for **Total Lines**, and a C/C++ comment-and-blank stripper for **SLOC** that removes empty/whitespace-only lines, `//` single-line comments, and `/* ... */` multi-line block comments). Unit tests (`*_test.cc`, `*_test.h`) and benchmarks (`*_perftest.cc`) are excluded.

For context, the entire `third_party/blink/renderer/core/layout/` directory (including Flex, Grid, Table, MathML, SVG, Custom, Exclusions, and Forms) contains:
- `core/layout/` top-level (267 non-test `.h`/`.cc` files): **91,660 total lines** (**63,094 SLOC**)
- `core/layout/geometry/` (29 non-test `.h`/`.cc` files): **3,146 total lines** (**2,234 SLOC**)
- `core/layout/inline/` (94 non-test `.h`/`.cc` files): **35,439 total lines** (**25,909 SLOC**)

### 6.2 Files Directly in the Block & Inline Layout Scope (67 files)

| Subsystem | Files (`.h` + `.cc`) | Total Lines | Non-Blank Non-Comment SLOC | Core In-Scope Slice SLOC (Estimated) |
|---|---:|---:|---:|---:|
| **Block Layout Algorithm** (`block_layout_algorithm.*`, `block_layout_algorithm_utils.*`, `block_node.*`, `block_child_iterator.*`, `simplified_layout_algorithm.*`) | 10 | 7,536 | 4,889 | ~1,450 |
| **Fragments, Builders & Spaces** (`box_fragment_builder.*`, `fragment_builder.*`, `constraint_space.*`, `constraint_space_builder.h`, `layout_result.*`, `physical_box_fragment.*`, `physical_fragment.*`, `length_utils.*`, `space_utils.*`) | 17 | 15,863 | 11,455 | ~1,800 |
| **Core Geometry & Margin Struts** (`geometry/bfc_offset.h`, `bfc_rect.h`, `box_strut.*`, `fragment_geometry.h`, `logical_offset.h`, `logical_rect.h`, `logical_size.h`, `margin_strut.*`) | 10 | 909 | 629 | ~450 |
| **Block & Geometry Subtotal** | **37** | **24,308** | **16,947** | **~3,700** |
| **Inline Layout & Box State** (`inline/inline_layout_algorithm.*`, `inline_node.*`, `inline_node_data.*`, `inline_box_state.*`, `inline_child_layout_context.*`) | 10 | 7,113 | 5,267 | ~1,200 |
| **Line Breaker & Line Info** (`inline/line_breaker.*`, `line_info.*`, `line_widths.*`) | 6 | 6,472 | 4,669 | ~1,100 |
| **Inline Items & Line Builders** (`inline/inline_item.*`, `inline_item_result.*`, `inline_items_builder.*`, `logical_line_builder.*`, `logical_line_item.*`, `line_box_fragment_builder.*`, `physical_line_box_fragment.*`) | 14 | 5,152 | 3,768 | ~850 |
| **Inline Subtotal** | **30** | **18,737** | **13,704** | **~3,150** |
| **Total (Block + Geometry + Inline)** | **67** | **43,045** | **30,651** | **~6,850** |

*Why the in-scope slice is ~6,850 SLOC out of 30,651 SLOC:* Approximately 77% of the SLOC in those 67 C++ files handles features excluded from the first fragment: floats and `ExclusionSpace` opportunities, out-of-flow positioned descendants, fragmentation (`BlockBreakToken` / column spanners / page breaks), ruby annotations, `line-clamp` / ellipsis relayout, `text-box-trim`, bidirectional text runs, SVG text scaling, layout cache invalidation, and Blink Oilpan garbage-collection tracing (`Trace(Visitor*)`).

---

## 7. Effort Estimates per Milestone and Basis

### 7.1 Calibration Basis from Existing Repository Developments
Our effort estimates are anchored to the two completed formal developments in this repository:
1. **`bend-engine/`** (Learning-data merge):
   - **Code size:** `merge.bend` (286 lines), `LAWS.bend` + `ORDER.bend` + `KEYS.bend` + `SORTED.bend` + `SORTMAP.bend` (1,319 lines), `PROOF.bend` (2,604 lines), `Merge.lean` (796 lines), plus `model_vectors.py` and differential tests.
   - **Ratio:** ~14.7x total Bend proof + spec lines per line of executable Bend; ~2.8x Lean lines per line of executable Bend.
2. **`bend-tls/browser/`** (TCP relay & page flow control):
   - **Code size:** `tcp_transitions.bend` (59 lines) + `frame.bend` (76 lines) → `tcp_contract_proof.bend` + `tcp_model.bend` + `frame_proof.bend` + `frame_arith.bend` + `frame_lists.bend` (1,028 lines), `Transitions.lean` (220 lines), `CompilerCheck.lean` (1,226 lines), `Relay.lean` (3,086 lines), and `induct/*.lean` (14,152 lines across 30 files).
   - **Empirical productivity:** Pure arithmetic and record-transform models with Lean `omega`/`simp` proofs and Bend inductive proofs take ~1–2 engineer-days per 100 lines of executable Bend when both `lean <file>` and `bend <file> --verdict` are required.

### 7.2 Milestones

| Milestone | Deliverables | Est. Bend LOC (Code + Proofs) | Est. Lean 4 LOC | Effort (Eng-Days) | Basis |
|---|---|---:|---:|---:|---|
| **M1: Geometry, `BoxStrut`, & Signed `MarginStrut`** | `BoxStrut`, `MarginStrut` (`pos`, `neg`), `Append`, `Sum`, Law 1 (`margin_strut_semilattice`) in Bend (`--verdict`) and Lean (`lean`). | 120 code / 450 proof | 300 | **2–3 days** | Directly extends the `stack.bend` / `Spike.lean` vertical stacking spike (144 Bend lines / 118 Lean lines) to signed `(pos, neg)` pairs; comparable to `LP` and `Nat.max` laws in `bend-engine/PROOF.bend`. |
| **M2: In-Flow Block Layout (`BlockLayoutAlgorithm`)** | Recursive `layout_block` over `List<LayoutInputNode>`, BFC offset resolution, self-collapsing boxes, parent-child margin collapsing, Laws 2 & 3 in Lean and Bend. | 350 code / 1,800 proof | 900 | **6–9 days** | Comparable in structural complexity to `bend-engine/merge.bend` (286 lines) + `Merge.lean` (796 lines) + `PROOF.bend` (2,604 lines), using list-induction over children instead of sorted association lists. |
| **M3: Greedy Line Breaking (`LineBreaker`)** | `break_lines` over `List<InlineItem>`, trailing collapsible space removal, forced breaks, overflow single-item fallback, Law 4 in Lean and Bend. | 300 code / 1,600 proof | 850 | **6–8 days** | Stateful accumulator loop over a list with fuel/termination measure (`items.length`); complexity matches `Relay.lean`'s `pump_props`/`pump_reach`/`pump_done` proofs and `frame_lists.bend`. |
| **M4: Inline Box State & Line Box Construction (`InlineLayoutAlgorithm`)** | `create_line_box`, `FontHeight` max-accumulation across baseline items and `OpenTag`/`CloseTag` spans, block-Container IFC integration, Law 5 in Lean and Bend. | 250 code / 1,200 proof | 650 | **4–6 days** | Tree/stack fold over `PlacedInlineItem`s and `FontHeight` records; uses the same `Nat.max` congruence and list-membership patterns as M1–M2. |
| **M5: Differential Conformance & Translation Check** | Bounded test-vector generator (`model_vectors.py` pattern), compiled `.mjs` differential test suite against reference vectors/WPT fixtures, and `CompilerCheck.lean` extension for `Nat.max` / records. | 150 code / 400 scripts | 600 | **3–5 days** | Mirrors `bend-engine/model_vectors.py` (1,137 vectors) and `bend-tls/browser/core/check/CompilerCheck.lean` (adding `>` / `Nat.max` and record constructors noted in `bend-engine/README.md`). |
| **Total** | **Full CSS 2.1 In-Flow Block + Inline Model** | **~1,020 code / ~5,050 proof** | **~3,300** | **21–31 days** | **~4 to 6 engineer-weeks total** |

---

## 8. Where the Model Stops Matching the Engine

Because the link between the Bend/Lean model and Chromium's C++ in `third_party/blink/renderer/core/layout/` is a **hand-written transcription** (exactly as `Merge.lean` / `merge.bend` is a hand transcription of `merge.ts`), the formal proofs stop at specific boundaries:

1. **Hand Transcription from C++ to Bend and from Bend to Lean:**
   - No mechanized C++ frontend parses Blink's `block_layout_algorithm.cc` or `line_breaker.cc` into Bend or Lean, and no tool automatically proves that the Bend definitions and Lean definitions are identical (unless `CompilerCheck.lean` is extended from flat arithmetic transitions to recursive algebraic data types).
   - **Mitigation:** Differential testing on bounded exhaustive domains (`model_vectors.txt`) and WPT (Web Platform Tests) layout geometry dumps (`offsetTop`, `offsetLeft`, `offsetWidth`, `offsetHeight`, `getClientRects()`).
2. **Unbounded `Nat` vs. 32-Bit Saturating `LayoutUnit` (`platform/geometry/layout_unit.h`):**
   - The Bend and Lean models use unbounded `Nat`. Blink's `LayoutUnit` uses 32-bit signed saturating arithmetic (`base::ClampedNumeric<int32_t>`) with `kLayoutUnitMax = (2^31 - 1) / 64 ≈ 33,554,431.98` px.
   - The model matches Blink's arithmetic **only when all intermediate positions, sizes, and sums stay strictly below `2^31 - 1` layout units** (and below `2^48 - 1` in compiled Bend JavaScript due to `nat_chk`, as proved in `Transitions.lean`). Near `LayoutUnit::Max()`, Blink saturates whereas `Nat` does not.
3. **Subpixel Rounding, Pixel Snapping, and Zoom:**
   - Blink performs `LayoutUnit` division/rounding during percentage resolution, `text-fit` scaling, and post-layout physical pixel snapping (`ToRoundedPoint`, `SnapSizeToPixel`). The model operates purely in exact `LayoutUnit` integers after lengths have been resolved.
4. **Stateful/Incremental Layout and Caching (`TryReuseFragmentsFromCache`, `SimplifiedLayoutAlgorithm`):**
   - Blink reuses previous `PhysicalFragment`s and `InlineNodeData` across DOM mutations when constraint spaces match. The model is a pure functional single-pass evaluator from `ConstraintSpace × LayoutInputNode` to `LayoutResult`; cache hit/invalidation equivalence is outside the first fragment.
5. **Compiler Check Limitations (`CompilerCheck.lean`):**
   - As documented in `bend-engine/README.md`, `CompilerCheck.lean` currently validates flat `Nat` expressions (`var`, `add`, `sub`, `min` with `<` guards) and rejects `>` guards (`Nat.max`) and record constructors (`Stacked{...}`). Until extended in M5, translation from `.bend` to `.mjs` is checked via bounded vector testing rather than kernel translation validation.

---

## 9. Open Questions

1. **Signed Margins Representation (`Int` vs. `(pos: Nat, neg: Nat)`):**
   - Bend 2's standard library (`Base`) provides rich inductive support and kernel proof ergonomics for `Nat`, whereas `MarginStrut` in Blink naturally splits signed margins into `positive_margin >= 0` and `negative_margin <= 0`. Should negative margins in `BoxStrut` be represented as a `(pos: Nat, neg: Nat)` pair throughout the Bend model, or should negative margins be deferred to Milestone 2 while keeping `BoxStrut` non-negative (`Nat`) in Milestone 1?
2. **Parent-Child Margin Collapsing vs. BFC-Root-Only in Milestone 2:**
   - Collapsing margins between adjacent siblings (`ComputeInflowPosition`) is local to a single loop, whereas collapsing a child's margin through a parent with zero border/padding (`BfcBlockOffset()` resolution on first inflow child) requires Blink's "abort and relayout once BFC block offset is resolved" (`LayoutResult::kBfcBlockOffsetResolved`) two-pass state. Should Milestone 2 model the two-pass BFC-offset resolution explicitly, or compute the equivalent closed-form functional specification?
3. **Inline Box Nesting Depth (`InlineLayoutStateStack`):**
   - Does the first inline fragment need arbitrary nesting of `OpenTag`/`CloseTag` (`<span>` inside `<span>` with inline borders/padding), or is a single level of inline boxes plus `TextSeg` and `AtomicInline` sufficient for the first five laws?
4. **Differential Oracle Harness:**
   - Because installing browsers or running `playwright install` is out of scope on this machine, should the differential test oracle for M2–M5 use pre-recorded JSON geometry fixtures from Chromium `blink_unittests` (`block_layout_algorithm_test.cc`, `inline_layout_algorithm_test.cc`), or a standalone reference evaluator in TypeScript/Lean?
5. **BendTT `--verdict` Stack Virtual Memory in Constrained Cgroups:**
   - `bend <file> --verdict` spawns the compiled Lean `bendtt` binary with `LEAN_STACK_SIZE_KB=4194304` (4 GB virtual stack reservation), which triggers `SIGABRT` inside a 900 MB memory-capped container unless `LEAN_STACK_SIZE_KB` is unset or capped. Should we document a `BENDTT` wrapper script for CI environments with strict virtual-memory caps?
