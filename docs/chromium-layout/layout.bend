# docs/chromium-layout/layout.bend
#
# Executable Bend 2 model of Chromium Blink LayoutNG's CSS 2.1 in-flow block and inline
# formatting contexts.
#
# Pinned Chromium revision: 36c121be58126ddbb0686965897b8c8ff9b246fb
# Subtree: third_party/blink/renderer/core/layout/

import Base

# ==============================================================================
# 1. Geometry, BoxStrut, and Signed MarginStrut (M1)
#    Source:
#    - geometry/box_strut.h:33-114, geometry/box_strut.cc:14-54
#    - geometry/margin_strut.h:16-58, geometry/margin_strut.cc:11-46
#    - geometry/logical_size.h:19-65, geometry/logical_offset.h:19-68
#    - platform/fonts/font_height.h:42-95
# ==============================================================================

# Conditional helpers (scrutinizing a Bool parameter directly)
def bool_ite(cond: Bool, +t: Bool, +f: Bool) -> Bool:
  match cond:
    case True{}:
      t
    case False{}:
      f

def nat_ite(cond: Bool, +t: Nat, +f: Nat) -> Nat:
  match cond:
    case True{}:
      t
    case False{}:
      f

# BoxStrut (geometry/box_strut.h:33-114)
type BoxStrut is Data:
  Strut{inline_start: Nat, inline_end: Nat, block_start: Nat, block_end: Nat}

def box_strut_zero() -> BoxStrut:
  Strut{0n, 0n, 0n, 0n}

def box_strut_inline_start(s: BoxStrut) -> Nat:
  match s:
    case Strut{istart, +ie, +bs, +be}:
      istart

def box_strut_inline_end(s: BoxStrut) -> Nat:
  match s:
    case Strut{+istart, ie, +bs, +be}:
      ie

def box_strut_block_start(s: BoxStrut) -> Nat:
  match s:
    case Strut{+istart, +ie, bs, +be}:
      bs

def box_strut_block_end(s: BoxStrut) -> Nat:
  match s:
    case Strut{+istart, +ie, +bs, be}:
      be

# BoxStrut::InlineSum() (geometry/box_strut.h:62)
def box_strut_inline_sum(s: BoxStrut) -> Nat:
  match s:
    case Strut{inline_start, inline_end, +block_start, +block_end}:
      Nat.add(inline_start, inline_end)

# BoxStrut::BlockSum() (geometry/box_strut.h:63)
def box_strut_block_sum(s: BoxStrut) -> Nat:
  match s:
    case Strut{+inline_start, +inline_end, block_start, block_end}:
      Nat.add(block_start, block_end)

# BoxStrut::operator+ (geometry/box_strut.h:74-85)
def box_strut_add(a: BoxStrut, b: BoxStrut) -> BoxStrut:
  match a b:
    case Strut{is1, ie1, bs1, be1} Strut{is2, ie2, bs2, be2}:
      Strut{Nat.add(is1, is2), Nat.add(ie1, ie2), Nat.add(bs1, bs2), Nat.add(be1, be2)}

# MarginStrut (geometry/margin_strut.h:16-58, geometry/margin_strut.cc:11-46)
type MarginStrut is Data:
  MStrut{pos: Nat, neg: Nat}

def margin_strut_ite(cond: Bool, +t: MarginStrut, +f: MarginStrut) -> MarginStrut:
  match cond:
    case True{}:
      t
    case False{}:
      f

# Empty MarginStrut (geometry/margin_strut.h:17-18)
def margin_strut_empty() -> MarginStrut:
  MStrut{0n, 0n}

# MarginStrut::Append (geometry/margin_strut.cc:11-30, non-quirky case)
def margin_strut_append(s1: MarginStrut, s2: MarginStrut) -> MarginStrut:
  match s1 s2:
    case MStrut{p1, n1} MStrut{p2, n2}:
      MStrut{Nat.max(p1, p2), Nat.max(n1, n2)}

# MarginStrut::Sum (geometry/margin_strut.h:40-44, non-quirky case, clamped to Nat)
def margin_strut_sum(s: MarginStrut) -> Nat:
  match s:
    case MStrut{pos, neg}:
      Nat.sub(pos, neg)

# Apply a signed MarginStrut offset (+ s.pos - s.neg) to a block offset y (geometry/margin_strut.h:40-44)
def margin_strut_apply_offset(y: Nat, s: MarginStrut) -> Nat:
  match s:
    case MStrut{pos, neg}:
      Nat.sub(Nat.add(y, pos), neg)

# FontHeight (platform/fonts/font_height.h:42-95, inline/inline_box_state.h:52)
type FontHeight is Data:
  FHeight{ascent: Nat, descent: Nat}

def font_height_zero() -> FontHeight:
  FHeight{0n, 0n}

def font_height_ascent(h: FontHeight) -> Nat:
  match h:
    case FHeight{ascent, +descent}:
      ascent

def font_height_descent(h: FontHeight) -> Nat:
  match h:
    case FHeight{+ascent, descent}:
      descent

# FontHeight::LineHeight() (platform/fonts/font_height.h:61)
def font_height_line_height(h: FontHeight) -> Nat:
  match h:
    case FHeight{ascent, descent}:
      Nat.add(ascent, descent)

# FontHeight::Merge (platform/fonts/font_height.h:85, inline/inline_box_state.cc:295)
def font_height_merge(h1: FontHeight, h2: FontHeight) -> FontHeight:
  match h1 h2:
    case FHeight{a1, d1} FHeight{a2, d2}:
      FHeight{Nat.max(a1, a2), Nat.max(d1, d2)}

# LogicalSize (geometry/logical_size.h:19-65)
type LogicalSize is Data:
  LSize{inline_size: Nat, block_size: Nat}

# LogicalOffset (geometry/logical_offset.h:19-68)
type LogicalOffset is Data:
  LOffset{inline_offset: Nat, block_offset: Nat}

# MaybeNat (SCOPE.md §3)
type MaybeNat is Data:
  NoneNat{}
  SomeNat{val: Nat}

def maybe_nat_ite(cond: Bool, +t: MaybeNat, +f: MaybeNat) -> MaybeNat:
  match cond:
    case True{}:
      t
    case False{}:
      f

def maybe_nat_get_or(m: MaybeNat, +fallback: Nat) -> Nat:
  match m:
    case NoneNat{}:
      fallback
    case SomeNat{val}:
      val

def maybe_nat_is_some(m: MaybeNat) -> Bool:
  match m:
    case NoneNat{}:
      False{}
    case SomeNat{+val}:
      True{}

def maybe_nat_is_none(m: MaybeNat) -> Bool:
  match m:
    case NoneNat{}:
      True{}
    case SomeNat{+val}:
      False{}

# Boolean <= on Nat
def nat_le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nat_le(p, q)

# Boolean == 0 on Nat
def nat_is_zero(a: Nat) -> Bool:
  match a:
    case 0n:
      True{}
    case 1n+p:
      False{}

# Boolean > 0 on Nat
def nat_pos(a: Nat) -> Bool:
  match a:
    case 0n:
      False{}
    case 1n+p:
      True{}

# ==============================================================================
# 2. Inline Formatting Context: Line Breaking & Line Boxes (M3 & M4)
#    Source:
#    - inline/inline_item.h:42-220
#    - inline/line_info.h:35-180
#    - inline/line_breaker.h:45-210, inline/line_breaker.cc:740-925
#    - inline/inline_box_state.h:40-235, inline/inline_box_state.cc:277-445
#    - inline/inline_layout_algorithm.cc:378-430, 1340-1410
# ==============================================================================

# InlineItem (inline/inline_item.h:42-220, SCOPE.md §3)
type InlineItem is Data:
  TextSeg{
    item_id: Nat,
    inline_size: Nat,
    font_height: FontHeight,
    can_break_after: Bool,
    is_trailing_space: Bool
  }
  AtomicInline{
    item_id: Nat,
    inline_size: Nat,
    block_size: Nat,
    font_height: FontHeight
  }
  OpenTag{
    item_id: Nat,
    border_inline_start: Nat,
    padding_inline_start: Nat,
    margin_inline_start: Nat,
    font_height: FontHeight
  }
  CloseTag{
    item_id: Nat,
    border_inline_end: Nat,
    padding_inline_end: Nat,
    margin_inline_end: Nat
  }
  ForcedBreak{
    item_id: Nat
  }

def inline_item_id(it: InlineItem) -> Nat:
  match it:
    case TextSeg{id, +w, +fh, +cb, +ts}:
      id
    case AtomicInline{id, +w, +bs, +fh}:
      id
    case OpenTag{id, +b, +p, +m, +fh}:
      id
    case CloseTag{id, +b, +p, +m}:
      id
    case ForcedBreak{id}:
      id

def inline_item_raw_inline_size(it: InlineItem) -> Nat:
  match it:
    case TextSeg{+id, w, +fh, +cb, +ts}:
      w
    case AtomicInline{+id, w, +bs, +fh}:
      w
    case OpenTag{+id, b, p, m, +fh}:
      Nat.add(Nat.add(b, p), m)
    case CloseTag{+id, b, p, m}:
      Nat.add(Nat.add(b, p), m)
    case ForcedBreak{+id}:
      0n

def inline_item_font_height(it: InlineItem) -> FontHeight:
  match it:
    case TextSeg{+id, +w, fh, +cb, +ts}:
      fh
    case AtomicInline{+id, +w, +bs, fh}:
      fh
    case OpenTag{+id, +b, +p, +m, fh}:
      fh
    case CloseTag{+id, +b, +p, +m}:
      FHeight{0n, 0n}
    case ForcedBreak{+id}:
      FHeight{0n, 0n}

def inline_item_is_empty_list(items: List<&2, InlineItem>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case +h <> +t:
      False{}

# PlacedInlineItem (inline/logical_line_item.h:35-140, SCOPE.md §3)
type PlacedInlineItem is Data:
  PlacedItem{
    item_id: Nat,
    inline_offset: Nat,
    block_offset: Nat,
    inline_size: Nat,
    block_size: Nat
  }

# LineBoxFragment (inline/physical_line_box_fragment.h:30-95, SCOPE.md §3)
type LineBoxFragment is Data:
  LineFrag{
    bfc_offset: LogicalOffset,
    inline_size: Nat,
    metrics: FontHeight,
    items: List<&2, PlacedInlineItem>
  }

# LineInfo (inline/line_info.h:35-180, SCOPE.md §3)
type LineInfo is Data:
  LInfo{
    items: List<&2, InlineItem>,
    inline_size: Nat,
    non_break_item_count: Nat
  }

# Result tuple for take_line_aux and take_line
type TakeLineAuxResult is Data:
  TakeAuxRes{
    items: List<&2, InlineItem>,
    inline_size: Nat,
    non_break_count: Nat,
    remaining: List<&2, InlineItem>
  }

type TakeLineResult is Data:
  TakeRes{
    line: LineInfo,
    remaining: List<&2, InlineItem>
  }

def take_line_aux_choose(
  fits: Bool,
  +next: InlineItem,
  +cur_width: Nat,
  +non_break_count: Nat,
  +more: List<&2, InlineItem>,
  +rec: TakeLineAuxResult
) -> TakeLineAuxResult:
  match fits:
    case True{}:
      match rec:
        case TakeAuxRes{sub_items, final_w, final_cnt, rem}:
          TakeAuxRes{next <> sub_items, final_w, final_cnt, rem}
    case False{}:
      TakeAuxRes{Nil{}, cur_width, non_break_count, next <> more}

# Greedy line-packing auxiliary pass (inline/line_breaker.cc:740-925)
def take_line_aux(
  items: List<&2, InlineItem>,
  +avail: Nat,
  +cur_width: Nat,
  +pending_space: Nat,
  +non_break_count: Nat
) -> TakeLineAuxResult:
  match items:
    case Nil{}:
      TakeAuxRes{Nil{}, cur_width, non_break_count, Nil{}}
    case +next <> +more:
      match next:
        case ForcedBreak{+id}:
          TakeAuxRes{next <> Nil{}, cur_width, non_break_count, more}
        case TextSeg{+id, +w, +fh, +cb, is_ts}:
          match is_ts:
            case True{}:
              take_line_aux_choose(
                nat_le(cur_width, avail),
                next,
                cur_width,
                non_break_count,
                more,
                take_line_aux(more, avail, cur_width, Nat.add(pending_space, w), Nat.add(non_break_count, 1n)))
            case False{}:
              +new_w = Nat.add(Nat.add(cur_width, pending_space), w)
              take_line_aux_choose(
                nat_le(new_w, avail),
                next,
                cur_width,
                non_break_count,
                more,
                take_line_aux(more, avail, new_w, 0n, Nat.add(non_break_count, 1n)))
        case _:
          +w = inline_item_raw_inline_size(next)
          +new_w = Nat.add(Nat.add(cur_width, pending_space), w)
          take_line_aux_choose(
            nat_le(new_w, avail),
            next,
            cur_width,
            non_break_count,
            more,
            take_line_aux(more, avail, new_w, 0n, Nat.add(non_break_count, 1n)))

def take_line_wrap(+first: InlineItem, aux: TakeLineAuxResult) -> TakeLineResult:
  match aux:
    case TakeAuxRes{tail_items, final_w, final_cnt, rem}:
      TakeRes{LInfo{first <> tail_items, final_w, final_cnt}, rem}

# LineBreaker::NextLine (inline/line_breaker.cc:897-925)
def take_line(+avail: Nat, +first: InlineItem, +rest: List<&2, InlineItem>) -> TakeLineResult:
  match first:
    case ForcedBreak{+id}:
      TakeRes{LInfo{first <> Nil{}, 0n, 0n}, rest}
    case TextSeg{+id, +w, +fh, +cb, is_ts}:
      match is_ts:
        case True{}:
          take_line_wrap(first, take_line_aux(rest, avail, 0n, w, 1n))
        case False{}:
          take_line_wrap(first, take_line_aux(rest, avail, w, 0n, 1n))
    case _:
      +w = inline_item_raw_inline_size(first)
      take_line_wrap(first, take_line_aux(rest, avail, w, 0n, 1n))

def take_line_info(r: TakeLineResult) -> LineInfo:
  match r:
    case TakeRes{line, +rem}:
      line

def take_line_rem(r: TakeLineResult) -> List<&2, InlineItem>:
  match r:
    case TakeRes{+line, rem}:
      rem

def inline_item_list_len(items: List<&2, InlineItem>) -> Nat:
  match items:
    case Nil{}:
      0n
    case +h <> t:
      Nat.add(1n, inline_item_list_len(t))

# Fuel-driven line-breaking loop (inline/inline_layout_algorithm.cc:1340-1410)
def break_lines_fuel(fuel: Nat, +avail: Nat, items: List<&2, InlineItem>) -> List<&2, LineInfo>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match items:
        case Nil{}:
          Nil{}
        case +first <> +rest:
          +step = take_line(avail, first, rest)
          take_line_info(step) <> break_lines_fuel(p, avail, take_line_rem(step))

# breakLines (inline/line_breaker.cc:897, SCOPE.md §4 Law 4)
def break_lines(+avail: Nat, +items: List<&2, InlineItem>) -> List<&2, LineInfo>:
  break_lines_fuel(inline_item_list_len(items), avail, items)

# Accumulate FontHeight across all items on a line (inline/inline_box_state.cc:277-445)
def accumulate_line_metrics(items: List<&2, InlineItem>, +strut: FontHeight) -> FontHeight:
  match items:
    case Nil{}:
      strut
    case +it <> rest:
      font_height_merge(inline_item_font_height(it), accumulate_line_metrics(rest, strut))

# Place each item on a line box relative to baseline line_metrics.ascent (inline/inline_box_state.cc:426-445)
def place_line_items(items: List<&2, InlineItem>, +line_metrics: FontHeight, +inline_off: Nat) -> List<&2, PlacedInlineItem>:
  match items:
    case Nil{}:
      Nil{}
    case +it <> rest:
      +fh = inline_item_font_height(it)
      +w = inline_item_raw_inline_size(it)
      PlacedItem{
        inline_item_id(it),
        inline_off,
        Nat.sub(font_height_ascent(line_metrics), font_height_ascent(fh)),
        w,
        font_height_line_height(fh)
      } <> place_line_items(rest, line_metrics, Nat.add(inline_off, w))

# InlineLayoutAlgorithm::CreateLine (inline/inline_layout_algorithm.cc:378-430, SCOPE.md §4 Law 5)
def create_line_box(+strut: FontHeight, +line_info: LineInfo) -> LineBoxFragment:
  match line_info:
    case LInfo{+items, +inline_sz, +cnt}:
      +metrics = accumulate_line_metrics(items, strut)
      LineFrag{
        LOffset{0n, 0n},
        inline_sz,
        metrics,
        place_line_items(items, metrics, 0n)
      }

def line_frag_list_ite(cond: Bool, +t: List<&2, LineBoxFragment>, +f: List<&2, LineBoxFragment>) -> List<&2, LineBoxFragment>:
  match cond:
    case True{}:
      t
    case False{}:
      f

def line_frag_with_block_offset(+block_off: Nat, lf: LineBoxFragment) -> LineBoxFragment:
  match lf:
    case LineFrag{+off, isz, metrics, placed}:
      LineFrag{LOffset{0n, block_off}, isz, metrics, placed}

def line_frag_line_height(lf: LineBoxFragment) -> Nat:
  match lf:
    case LineFrag{+off, +isz, metrics, +placed}:
      font_height_line_height(metrics)

type StackedLinesResult is Data:
  StackedLines{lines: List<&2, LineBoxFragment>, total_block_size: Nat}

def stacked_lines_list(r: StackedLinesResult) -> List<&2, LineBoxFragment>:
  match r:
    case StackedLines{lines, +tbs}:
      lines

def stacked_lines_block_size(r: StackedLinesResult) -> Nat:
  match r:
    case StackedLines{+lines, tbs}:
      tbs

def stack_line_boxes(lines: List<&2, LineInfo>, +strut: FontHeight, +block_off: Nat) -> StackedLinesResult:
  match lines:
    case Nil{}:
      StackedLines{Nil{}, block_off}
    case +li <> rest:
      +lb = create_line_box(strut, li)
      +lh = line_frag_line_height(lb)
      +positioned = line_frag_with_block_offset(block_off, lb)
      +tail = stack_line_boxes(rest, strut, Nat.add(block_off, lh))
      StackedLines{positioned <> stacked_lines_list(tail), stacked_lines_block_size(tail)}

# ==============================================================================
# 3. In-Flow Block Layout (BlockLayoutAlgorithm, M2)
#    Source:
#    - constraint_space.h:42-180
#    - block_node.h:35-160, layout_input_node.h:38-190
#    - block_layout_algorithm.h:34-430, block_layout_algorithm.cc:555-576, 800-1500, 2385-3137
#    - physical_box_fragment.h:40-160, layout_result.h:45-210
# ==============================================================================

# ConstraintSpace (constraint_space.h:42-180, SCOPE.md §3)
type ConstraintSpace is Data:
  CSpace{
    available_inline_size: Nat,
    available_block_size: MaybeNat,
    bfc_line_offset: Nat,
    bfc_block_offset: Nat,
    margin_strut: MarginStrut,
    is_new_bfc: Bool
  }

# ChildBoxFragment (physical_box_fragment.h:40-160, SCOPE.md §3)
type ChildBoxFragment is Data:
  ChildBoxFrag{
    node_id: Nat,
    offset: LogicalOffset,
    border_box_size: LogicalSize,
    lines: List<&2, LineBoxFragment>
  }

# PhysicalBoxFragment (physical_box_fragment.h:40-160, SCOPE.md §3)
type PhysicalBoxFragment is Data:
  BoxFrag{
    node_id: Nat,
    offset: LogicalOffset,
    border_box_size: LogicalSize,
    children: List<&2, ChildBoxFragment>,
    lines: List<&2, LineBoxFragment>
  }

# LayoutResult (layout_result.h:45-210, SCOPE.md §3)
type LayoutResult is Data:
  LResult{
    fragment: PhysicalBoxFragment,
    bfc_block_offset: MaybeNat,
    end_margin_strut: MarginStrut,
    intrinsic_block_size: Nat
  }

# LayoutInputNode (layout_input_node.h:38-190, block_node.h:35-160, SCOPE.md §3)
type LayoutInputNode is Data:
  BlockChild{
    node_id: Nat,
    border: BoxStrut,
    padding: BoxStrut,
    margin: BoxStrut,
    explicit_inline_size: MaybeNat,
    explicit_block_size: MaybeNat,
    is_new_bfc: Bool,
    content_block_size: Nat,
    has_inflow_content: Bool,
    inner_start_strut: MarginStrut,
    inner_end_strut: MarginStrut
  }
  InlineChild{
    node_id: Nat,
    border: BoxStrut,
    padding: BoxStrut,
    margin: BoxStrut,
    explicit_inline_size: MaybeNat,
    explicit_block_size: MaybeNat,
    line_strut: FontHeight,
    items: List<&2, InlineItem>
  }

# BlockContainerNode (block_node.h:35-160, SCOPE.md §3)
type BlockContainerNode is Data:
  BlockContainer{
    node_id: Nat,
    border: BoxStrut,
    padding: BoxStrut,
    margin: BoxStrut,
    explicit_inline_size: MaybeNat,
    explicit_block_size: MaybeNat,
    is_new_bfc: Bool,
    children: List<&2, LayoutInputNode>
  }

def child_node_id(c: LayoutInputNode) -> Nat:
  match c:
    case BlockChild{id, +b, +p, +m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      id
    case InlineChild{id, +b, +p, +m, +ew, +eh, +st, +items}:
      id

def child_margin(c: LayoutInputNode) -> BoxStrut:
  match c:
    case BlockChild{+id, +b, +p, m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      m
    case InlineChild{+id, +b, +p, m, +ew, +eh, +st, +items}:
      m

def child_resolve_inline_size(+avail_inline: Nat, c: LayoutInputNode) -> Nat:
  match c:
    case BlockChild{+id, +b, +p, +m, ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      maybe_nat_get_or(ew, Nat.sub(avail_inline, box_strut_inline_sum(m)))
    case InlineChild{+id, +b, +p, +m, ew, +eh, +st, +items}:
      maybe_nat_get_or(ew, Nat.sub(avail_inline, box_strut_inline_sum(m)))

def child_is_self_collapsing(c: LayoutInputNode) -> Bool:
  match c:
    case BlockChild{+id, +b, +p, +m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      Bool.and(
        Bool.and(
          Bool.and(
            nat_is_zero(Nat.add(box_strut_block_sum(b), box_strut_block_sum(p))),
            maybe_nat_is_none(eh)),
          Bool.not(has_c)),
        Bool.not(bfc))
    case InlineChild{+id, +b, +p, +m, +ew, +eh, +st, +items}:
      Bool.and(
        Bool.and(
          nat_is_zero(Nat.add(box_strut_block_sum(b), box_strut_block_sum(p))),
          maybe_nat_is_none(eh)),
        inline_item_is_empty_list(items))

def margin_strut_pos(p: Nat) -> MarginStrut:
  MStrut{p, 0n}

def child_start_margin_strut(c: LayoutInputNode) -> MarginStrut:
  match c:
    case BlockChild{+id, +b, +p, +m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      +outer = margin_strut_pos(box_strut_block_start(m))
      margin_strut_ite(
        Bool.or(nat_pos(Nat.add(box_strut_block_start(b), box_strut_block_start(p))), bfc),
        outer,
        margin_strut_append(outer, ist))
    case InlineChild{+id, +b, +p, +m, +ew, +eh, +st, +items}:
      MStrut{box_strut_block_start(m), 0n}

def child_end_margin_strut(c: LayoutInputNode) -> MarginStrut:
  match c:
    case BlockChild{+id, +b, +p, +m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      +outer = margin_strut_pos(box_strut_block_end(m))
      margin_strut_ite(
        Bool.or(
          Bool.or(nat_pos(Nat.add(box_strut_block_end(b), box_strut_block_end(p))), bfc),
          maybe_nat_is_some(eh)),
        outer,
        margin_strut_append(ien, outer))
    case InlineChild{+id, +b, +p, +m, +ew, +eh, +st, +items}:
      MStrut{box_strut_block_end(m), 0n}

def child_inline_lines(+avail_inline: Nat, c: LayoutInputNode) -> StackedLinesResult:
  match c:
    case BlockChild{+id, +b, +p, +m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      StackedLines{Nil{}, 0n}
    case InlineChild{+id, +b, +p, +m, +ew, +eh, +st, +items}:
      +box_inline = maybe_nat_get_or(ew, Nat.sub(avail_inline, box_strut_inline_sum(m)))
      +content_inline = Nat.sub(box_inline, Nat.add(box_strut_inline_sum(b), box_strut_inline_sum(p)))
      +start_off = Nat.add(box_strut_block_start(b), box_strut_block_start(p))
      stack_line_boxes(break_lines(content_inline, items), st, start_off)

def child_border_box_block_size(+avail_inline: Nat, +c: LayoutInputNode) -> Nat:
  match c:
    case BlockChild{+id, +b, +p, +m, +ew, +eh, +bfc, +csz, +has_c, +ist, +ien}:
      +bp = Nat.add(box_strut_block_sum(b), box_strut_block_sum(p))
      maybe_nat_get_or(
        eh,
        nat_ite(child_is_self_collapsing(c), 0n, Nat.add(bp, csz)))
    case InlineChild{+id, +b, +p, +m, +ew, +eh, +st, +items}:
      +stacked = child_inline_lines(avail_inline, c)
      maybe_nat_get_or(
        eh,
        nat_ite(
          child_is_self_collapsing(c),
          0n,
          Nat.add(stacked_lines_block_size(stacked), Nat.add(box_strut_block_end(p), box_strut_block_end(b)))))

# ChildrenLayoutState (PreviousInflowPosition in block_layout_algorithm.h:34-44)
type ChildrenLayoutState is Data:
  ChildState{
    fragments: List<&2, ChildBoxFragment>,
    bfc_resolved: Bool,
    first_resolved_strut: MarginStrut,
    logical_block_offset: Nat,
    margin_strut: MarginStrut
  }

def child_state_fragments(st: ChildrenLayoutState) -> List<&2, ChildBoxFragment>:
  match st:
    case ChildState{frags, +res, +first, +pos, +strut}:
      frags

def child_state_bfc_resolved(st: ChildrenLayoutState) -> Bool:
  match st:
    case ChildState{+frags, res, +first, +pos, +strut}:
      res

def child_state_first_resolved_strut(st: ChildrenLayoutState) -> MarginStrut:
  match st:
    case ChildState{+frags, +res, first, +pos, +strut}:
      first

def child_state_logical_block_offset(st: ChildrenLayoutState) -> Nat:
  match st:
    case ChildState{+frags, +res, +first, pos, +strut}:
      pos

def child_state_margin_strut(st: ChildrenLayoutState) -> MarginStrut:
  match st:
    case ChildState{+frags, +res, +first, +pos, strut}:
      strut

# Recursive in-flow child layout pass (block_layout_algorithm.cc:986-1117, 2385-2805)
def layout_children(
  cs: List<&2, LayoutInputNode>,
  +avail_inline: Nat,
  +bfc_resolved: Bool,
  +pos: Nat,
  +strut: MarginStrut
) -> ChildrenLayoutState:
  match cs:
    case Nil{}:
      ChildState{Nil{}, bfc_resolved, strut, pos, strut}
    case +c <> rest:
      +is_self = child_is_self_collapsing(c)
      +start_strut = margin_strut_append(strut, child_start_margin_strut(c))
      +end_strut = child_end_margin_strut(c)
      +inline_sz = child_resolve_inline_size(avail_inline, c)
      +inline_off = box_strut_inline_start(child_margin(c))
      +block_off = nat_ite(bfc_resolved, Nat.add(pos, margin_strut_sum(start_strut)), 0n)
      +blk_sz = nat_ite(is_self, 0n, child_border_box_block_size(avail_inline, c))
      +lines = line_frag_list_ite(is_self, Nil{}, stacked_lines_list(child_inline_lines(avail_inline, c)))
      +next_bfc = bool_ite(is_self, bfc_resolved, True{})
      +next_pos = nat_ite(is_self, pos, Nat.add(block_off, blk_sz))
      +next_strut = margin_strut_ite(is_self, margin_strut_append(start_strut, end_strut), end_strut)
      +tail_st = layout_children(rest, avail_inline, next_bfc, next_pos, next_strut)
      +first_res =
        margin_strut_ite(
          is_self,
          child_state_first_resolved_strut(tail_st),
          margin_strut_ite(bfc_resolved, strut, start_strut))
      ChildState{
        ChildBoxFrag{
          child_node_id(c),
          LOffset{inline_off, block_off},
          LSize{inline_sz, blk_sz},
          lines
        } <> child_state_fragments(tail_st),
        child_state_bfc_resolved(tail_st),
        first_res,
        child_state_logical_block_offset(tail_st),
        child_state_margin_strut(tail_st)
      }

# BlockLayoutAlgorithm::Layout and FinishLayout (block_layout_algorithm.cc:800-1500, SCOPE.md §4 Laws 2 & 3)
def layout_block(+space: ConstraintSpace, +node: BlockContainerNode) -> LayoutResult:
  match space node:
    case CSpace{+avail_inline, +avail_block, +bfc_line_off, +bfc_block_off, +space_strut, +space_bfc} BlockContainer{+node_id, +border, +padding, +margin, +exp_inline, +exp_block, +node_bfc, +children}:
      +border_box_inline = maybe_nat_get_or(exp_inline, Nat.sub(avail_inline, box_strut_inline_sum(margin)))
      +child_avail_inline = Nat.sub(border_box_inline, Nat.add(box_strut_inline_sum(border), box_strut_inline_sum(padding)))
      +content_start = Nat.add(box_strut_block_start(border), box_strut_block_start(padding))
      +has_start_edge = Bool.or(Bool.or(nat_pos(content_start), space_bfc), node_bfc)
      +init_pos = nat_ite(has_start_edge, content_start, 0n)
      +init_strut = margin_strut_ite(has_start_edge, margin_strut_empty(), space_strut)
      +st = layout_children(children, child_avail_inline, has_start_edge, init_pos, init_strut)
      +st_resolved = child_state_bfc_resolved(st)
      +st_first_strut = child_state_first_resolved_strut(st)
      +st_pos = child_state_logical_block_offset(st)
      +st_strut = child_state_margin_strut(st)
      +content_end = Nat.add(box_strut_block_end(padding), box_strut_block_end(border))
      +has_end_edge = Bool.or(Bool.or(nat_pos(content_end), space_bfc), node_bfc)
      +is_self_collapsing_container = Bool.and(
        Bool.and(Bool.not(st_resolved), nat_is_zero(content_end)),
        maybe_nat_is_none(exp_block))
      +block_off =
        nat_ite(
          st_resolved,
          nat_ite(
            has_start_edge,
            Nat.add(bfc_block_off, margin_strut_sum(space_strut)),
            Nat.add(bfc_block_off, margin_strut_sum(st_first_strut))),
          nat_ite(
            is_self_collapsing_container,
            bfc_block_off,
            Nat.add(bfc_block_off, margin_strut_sum(st_strut))))
      +intrinsic =
        nat_ite(
          st_resolved,
          nat_ite(
            has_end_edge,
            Nat.add(Nat.add(st_pos, margin_strut_sum(st_strut)), content_end),
            st_pos),
          nat_ite(is_self_collapsing_container, 0n, content_end))
      +final_block =
        nat_ite(is_self_collapsing_container, 0n, maybe_nat_get_or(exp_block, intrinsic))
      +bfc_off =
        maybe_nat_ite(is_self_collapsing_container, NoneNat{}, SomeNat{block_off})
      +out_strut =
        margin_strut_ite(
          st_resolved,
          margin_strut_ite(
            Bool.or(has_end_edge, maybe_nat_is_some(exp_block)),
            margin_strut_empty(),
            st_strut),
          margin_strut_ite(is_self_collapsing_container, st_strut, margin_strut_empty()))
      LResult{
        BoxFrag{
          node_id,
          LOffset{bfc_line_off, block_off},
          LSize{border_box_inline, final_block},
          child_state_fragments(st),
          Nil{}
        },
        bfc_off,
        out_strut,
        intrinsic
      }

def layout_result_intrinsic_block_size(r: LayoutResult) -> Nat:
  match r:
    case LResult{+frag, +bfc_off, +end_strut, intrinsic}:
      intrinsic

def layout_result_bfc_block_offset_or(r: LayoutResult, +fallback: Nat) -> Nat:
  match r:
    case LResult{+frag, bfc_off, +end_strut, +intrinsic}:
      maybe_nat_get_or(bfc_off, fallback)

def layout_result_end_margin_pos(r: LayoutResult) -> Nat:
  match r:
    case LResult{+frag, +bfc_off, end_strut, +intrinsic}:
      match end_strut:
        case MStrut{pos, +neg}:
          pos

# Specification helper for Law 3 (bfc_intrinsic_block_size_conservation, SCOPE.md §4)
def collapsed_flow_block_size_from(cs: List<&2, LayoutInputNode>, +avail_inline: Nat, +prev_strut: MarginStrut) -> Nat:
  match cs:
    case Nil{}:
      margin_strut_sum(prev_strut)
    case +c <> rest:
      +collapsed = margin_strut_sum(margin_strut_append(prev_strut, child_start_margin_strut(c)))
      Nat.add(
        Nat.add(collapsed, child_border_box_block_size(avail_inline, c)),
        collapsed_flow_block_size_from(rest, avail_inline, child_end_margin_strut(c)))

def total_collapsed_flow_block_size(+avail_inline: Nat, cs: List<&2, LayoutInputNode>) -> Nat:
  collapsed_flow_block_size_from(cs, avail_inline, margin_strut_empty())
