# docs/chromium-layout/proof.bend
#
# Bend 2 kernel proofs for the Chromium Blink LayoutNG formal model (layout.bend).
# Checked with: bend docs/chromium-layout/proof.bend --verdict

import Base
import ./layout.bend as Layout

# ==============================================================================
# M1 Laws: Nat.max and Signed MarginStrut Join-Semilattice (Law 1)
# Source:
# - geometry/margin_strut.h:16-58
# - geometry/margin_strut.cc:11-46
# - block_layout_algorithm_test.cc:568-1025
# - geometry/box_strut_test.cc:16-135
# ==============================================================================

law max_self:
  for +a: Nat
  {Nat.max(a, a) == a : Nat}

def max_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(p, p), p, max_self(p))

law max_comm:
  for +a: Nat
  for +b: Nat
  {Nat.max(a, b) == Nat.max(b, a) : Nat}

def max_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, p => 1n+p, Nat.max(ap, bp), Nat.max(bp, ap), max_comm(ap, bp))

law max_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}

def max_assoc(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+cp:
      {==}
    case 0n 1n+bp 0n:
      {==}
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n 0n:
      {==}
    case 1n+ap 0n 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      {==}
    case 1n+ap 1n+bp 1n+cp:
      Equal.cong(Nat, Nat, p => 1n+p, Nat.max(Nat.max(ap, bp), cp), Nat.max(ap, Nat.max(bp, cp)), max_assoc(ap, bp, cp))

# Law 1a (idempotence): margin_strut_append(s, s) == s
law margin_strut_append_idem:
  for +s: Layout.MarginStrut
  {Layout.margin_strut_append(s, s) == s : Layout.MarginStrut}

def margin_strut_append_idem(s):
  match s:
    case Layout.MStrut{p, n}:
      s1 = Equal.cong(Nat, Layout.MarginStrut, x => Layout.MStrut{x, Nat.max(n, n)}, Nat.max(p, p), p, max_self(p))
      s2 = Equal.cong(Nat, Layout.MarginStrut, y => Layout.MStrut{p, y}, Nat.max(n, n), n, max_self(n))
      Equal.trans(Layout.MarginStrut, Layout.MStrut{Nat.max(p, p), Nat.max(n, n)}, Layout.MStrut{p, Nat.max(n, n)}, Layout.MStrut{p, n}, s1, s2)

# Law 1b (commutativity): margin_strut_append(s1, s2) == margin_strut_append(s2, s1)
law margin_strut_append_comm:
  for +s1: Layout.MarginStrut
  for +s2: Layout.MarginStrut
  {Layout.margin_strut_append(s1, s2) == Layout.margin_strut_append(s2, s1) : Layout.MarginStrut}

def margin_strut_append_comm(s1, s2):
  match s1 s2:
    case Layout.MStrut{p1, n1} Layout.MStrut{p2, n2}:
      t1 = Equal.cong(Nat, Layout.MarginStrut, x => Layout.MStrut{x, Nat.max(n1, n2)}, Nat.max(p1, p2), Nat.max(p2, p1), max_comm(p1, p2))
      t2 = Equal.cong(Nat, Layout.MarginStrut, y => Layout.MStrut{Nat.max(p2, p1), y}, Nat.max(n1, n2), Nat.max(n2, n1), max_comm(n1, n2))
      Equal.trans(Layout.MarginStrut, Layout.MStrut{Nat.max(p1, p2), Nat.max(n1, n2)}, Layout.MStrut{Nat.max(p2, p1), Nat.max(n1, n2)}, Layout.MStrut{Nat.max(p2, p1), Nat.max(n2, n1)}, t1, t2)

# Law 1c (associativity): margin_strut_append(margin_strut_append(s1, s2), s3) == margin_strut_append(s1, margin_strut_append(s2, s3))
law margin_strut_append_assoc:
  for +s1: Layout.MarginStrut
  for +s2: Layout.MarginStrut
  for +s3: Layout.MarginStrut
  {Layout.margin_strut_append(Layout.margin_strut_append(s1, s2), s3) == Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)) : Layout.MarginStrut}

def margin_strut_append_assoc(s1, s2, s3):
  match s1 s2 s3:
    case Layout.MStrut{p1, n1} Layout.MStrut{p2, n2} Layout.MStrut{p3, n3}:
      t1 = Equal.cong(Nat, Layout.MarginStrut, x => Layout.MStrut{x, Nat.max(Nat.max(n1, n2), n3)}, Nat.max(Nat.max(p1, p2), p3), Nat.max(p1, Nat.max(p2, p3)), max_assoc(p1, p2, p3))
      t2 = Equal.cong(Nat, Layout.MarginStrut, y => Layout.MStrut{Nat.max(p1, Nat.max(p2, p3)), y}, Nat.max(Nat.max(n1, n2), n3), Nat.max(n1, Nat.max(n2, n3)), max_assoc(n1, n2, n3))
      Equal.trans(Layout.MarginStrut,
        Layout.MStrut{Nat.max(Nat.max(p1, p2), p3), Nat.max(Nat.max(n1, n2), n3)},
        Layout.MStrut{Nat.max(p1, Nat.max(p2, p3)), Nat.max(Nat.max(n1, n2), n3)},
        Layout.MStrut{Nat.max(p1, Nat.max(p2, p3)), Nat.max(n1, Nat.max(n2, n3))},
        t1, t2)

# Combined Law 1 (margin_strut_semilattice):
type SemilatticeTriple is Data:
  STriple{a: Layout.MarginStrut, b: Layout.MarginStrut, c: Layout.MarginStrut}

law margin_strut_semilattice:
  for +s1: Layout.MarginStrut
  for +s2: Layout.MarginStrut
  for +s3: Layout.MarginStrut
  {STriple{
    Layout.margin_strut_append(Layout.margin_strut_append(s1, s2), s3),
    Layout.margin_strut_append(s1, s2),
    Layout.margin_strut_append(s1, s1)
  } == STriple{
    Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)),
    Layout.margin_strut_append(s2, s1),
    s1
  } : SemilatticeTriple}

def margin_strut_semilattice(s1, s2, s3):
  e1 = Equal.cong(
    Layout.MarginStrut, SemilatticeTriple,
    x => STriple{x, Layout.margin_strut_append(s1, s2), Layout.margin_strut_append(s1, s1)},
    Layout.margin_strut_append(Layout.margin_strut_append(s1, s2), s3),
    Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)),
    margin_strut_append_assoc(s1, s2, s3))
  e2 = Equal.cong(
    Layout.MarginStrut, SemilatticeTriple,
    y => STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), y, Layout.margin_strut_append(s1, s1)},
    Layout.margin_strut_append(s1, s2),
    Layout.margin_strut_append(s2, s1),
    margin_strut_append_comm(s1, s2))
  e3 = Equal.cong(
    Layout.MarginStrut, SemilatticeTriple,
    z => STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), Layout.margin_strut_append(s2, s1), z},
    Layout.margin_strut_append(s1, s1),
    s1,
    margin_strut_append_idem(s1))
  Equal.trans(SemilatticeTriple,
    STriple{Layout.margin_strut_append(Layout.margin_strut_append(s1, s2), s3), Layout.margin_strut_append(s1, s2), Layout.margin_strut_append(s1, s1)},
    STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), Layout.margin_strut_append(s1, s2), Layout.margin_strut_append(s1, s1)},
    STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), Layout.margin_strut_append(s2, s1), s1},
    e1,
    Equal.trans(SemilatticeTriple,
      STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), Layout.margin_strut_append(s1, s2), Layout.margin_strut_append(s1, s1)},
      STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), Layout.margin_strut_append(s2, s1), Layout.margin_strut_append(s1, s1)},
      STriple{Layout.margin_strut_append(s1, Layout.margin_strut_append(s2, s3)), Layout.margin_strut_append(s2, s1), s1},
      e2, e3))

# Transcribed Blink unit test vectors (block_layout_algorithm_test.cc & geometry/box_strut_test.cc):
# 1. CollapsingMarginsCase3 (block_layout_algorithm_test.cc:605): max(20, 200) = 200
# 2. CollapsingMarginsCase4 (block_layout_algorithm_test.cc:662, 669): max(8, 30) = 30, max(30, 200) = 200
# 3. CollapsingMarginsCase6 (block_layout_algorithm_test.cc:810): max(10, 40) = 40
# 4. CollapsingMarginsEmptyBlockWithClearance (block_layout_algorithm_test.cc:968-983):
#    offset 90 with signed strut {50, 70} gives (90 + 50) - 70 = 70
# 5. CollapsingMarginsEmptyBlockWithClearance (block_layout_algorithm_test.cc:991-1006):
#    {70, 0} appended with {0, 10} has sum 60; appended with {0, 20} has sum 50; appended with {80, 0} has sum 60
# 6. GeometryUnitsTest (geometry/box_strut_test.cc:18-24): BoxStrut(5, 10, 15, 20) inline_sum = 15, block_sum = 35
law blink_m1_test_vectors:
  {[
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.MStrut{20n, 0n}, Layout.MStrut{200n, 0n})),
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.MStrut{8n, 0n}, Layout.MStrut{30n, 0n})),
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.MStrut{10n, 0n}, Layout.MStrut{40n, 0n})),
    Layout.margin_strut_apply_offset(90n, Layout.margin_strut_append(Layout.MStrut{50n, 0n}, Layout.MStrut{0n, 70n})),
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.MStrut{70n, 0n}, Layout.MStrut{0n, 10n})),
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.MStrut{70n, 10n}, Layout.MStrut{0n, 20n})),
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.MStrut{70n, 20n}, Layout.MStrut{80n, 0n})),
    Layout.box_strut_inline_sum(Layout.Strut{5n, 10n, 15n, 20n}),
    Layout.box_strut_block_sum(Layout.Strut{5n, 10n, 15n, 20n})
  ] == [200n, 30n, 40n, 70n, 60n, 50n, 60n, 15n, 35n] : List<&2, Nat>}

def blink_m1_test_vectors():
  {==}

# ==============================================================================
# M2 Laws: In-Flow Block Layout, Sibling Non-Overlap (Law 2), and
# BFC Intrinsic Block-Size Conservation (Law 3)
# Source:
# - block_layout_algorithm.cc:800-1500, 2385-3060
# - block_layout_algorithm_test.cc:568-900
# ==============================================================================

# Monotonicity lemma: for all a, d : Nat, a <= a + d
law nat_le_add_right:
  for +a: Nat
  for +d: Nat
  {Layout.nat_le(a, Nat.add(a, d)) == True{} : Bool}

def nat_le_add_right(a, d):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      nat_le_add_right(ap, d)

# Law 2 (block_siblings_monotonic_non_overlapping) core step in Bend:
# For any two placed non-self-collapsing siblings c0, c1, c0's block end
# (c0_offset + c0_block_size) is <= c1's block offset (c0_end + collapsed_margin_between).
law block_siblings_monotonic_non_overlapping_step:
  for +avail: Nat
  for +pos: Nat
  for +s: Layout.MarginStrut
  for +c0: Layout.LayoutInputNode
  for +c1: Layout.LayoutInputNode
  {Layout.nat_le(
    Nat.add(
      Nat.add(pos, Layout.margin_strut_sum(Layout.margin_strut_append(s, Layout.child_start_margin_strut(c0)))),
      Layout.child_border_box_block_size(avail, c0)),
    Nat.add(
      Nat.add(
        Nat.add(pos, Layout.margin_strut_sum(Layout.margin_strut_append(s, Layout.child_start_margin_strut(c0)))),
        Layout.child_border_box_block_size(avail, c0)),
      Layout.margin_strut_sum(Layout.margin_strut_append(Layout.child_end_margin_strut(c0), Layout.child_start_margin_strut(c1))))) == True{} : Bool}

def block_siblings_monotonic_non_overlapping_step(avail, pos, s, c0, c1):
  nat_le_add_right(
    Nat.add(
      Nat.add(pos, Layout.margin_strut_sum(Layout.margin_strut_append(s, Layout.child_start_margin_strut(c0)))),
      Layout.child_border_box_block_size(avail, c0)),
    Layout.margin_strut_sum(Layout.margin_strut_append(Layout.child_end_margin_strut(c0), Layout.child_start_margin_strut(c1))))

# Associativity of Nat.add for Law 3 (bfc_intrinsic_block_size_conservation)
law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+ap:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(ap, b), c), Nat.add(ap, Nat.add(b, c)), add_assoc(ap, b, c))

# Law 3 (bfc_intrinsic_block_size_conservation) inductive conservation step:
# ((pos + collapsed) + blk_sz) + rest_flow == pos + ((collapsed + blk_sz) + rest_flow)
law bfc_intrinsic_block_size_conservation_step:
  for +pos: Nat
  for +collapsed: Nat
  for +blk_sz: Nat
  for +rest_flow: Nat
  {Nat.add(Nat.add(Nat.add(pos, collapsed), blk_sz), rest_flow) ==
   Nat.add(pos, Nat.add(Nat.add(collapsed, blk_sz), rest_flow)) : Nat}

def bfc_intrinsic_block_size_conservation_step(pos, collapsed, blk_sz, rest_flow):
  s1 = Equal.cong(
    Nat, Nat,
    x => Nat.add(x, rest_flow),
    Nat.add(Nat.add(pos, collapsed), blk_sz),
    Nat.add(pos, Nat.add(collapsed, blk_sz)),
    add_assoc(pos, collapsed, blk_sz))
  s2 = add_assoc(pos, Nat.add(collapsed, blk_sz), rest_flow)
  Equal.trans(
    Nat,
    Nat.add(Nat.add(Nat.add(pos, collapsed), blk_sz), rest_flow),
    Nat.add(Nat.add(pos, Nat.add(collapsed, blk_sz)), rest_flow),
    Nat.add(pos, Nat.add(Nat.add(collapsed, blk_sz), rest_flow)),
    s1, s2)

# Helper constructors for Blink M2 test vectors (block_layout_algorithm_test.cc:568-900)
def m2_case3_child() -> Layout.LayoutInputNode:
  Layout.BlockChild{
    2n,
    Layout.Strut{0n, 0n, 0n, 0n},
    Layout.Strut{0n, 0n, 0n, 0n},
    Layout.Strut{0n, 0n, 200n, 0n},
    Layout.SomeNat{100n},
    Layout.SomeNat{50n},
    False{},
    50n,
    True{},
    Layout.MStrut{0n, 0n},
    Layout.MStrut{0n, 0n}
  }

def m2_case3_res() -> Layout.LayoutResult:
  Layout.layout_block(
    Layout.CSpace{800n, Layout.NoneNat{}, 0n, 0n, Layout.MStrut{20n, 0n}, False{}},
    Layout.BlockContainer{
      1n,
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.Strut{0n, 0n, 20n, 0n},
      Layout.SomeNat{100n},
      Layout.NoneNat{},
      False{},
      [m2_case3_child()]
    })

def m2_case6_child1() -> Layout.LayoutInputNode:
  Layout.BlockChild{
    2n,
    Layout.Strut{0n, 0n, 0n, 0n},
    Layout.Strut{0n, 0n, 0n, 0n},
    Layout.Strut{0n, 0n, 10n, 20n},
    Layout.SomeNat{100n},
    Layout.SomeNat{30n},
    False{},
    30n,
    True{},
    Layout.MStrut{0n, 0n},
    Layout.MStrut{0n, 0n}
  }

def m2_case6_child2() -> Layout.LayoutInputNode:
  Layout.BlockChild{
    3n,
    Layout.Strut{0n, 0n, 0n, 0n},
    Layout.Strut{0n, 0n, 0n, 0n},
    Layout.Strut{0n, 0n, 40n, 50n},
    Layout.SomeNat{100n},
    Layout.SomeNat{60n},
    False{},
    60n,
    True{},
    Layout.MStrut{0n, 0n},
    Layout.MStrut{0n, 0n}
  }

def m2_case6_res() -> Layout.LayoutResult:
  Layout.layout_block(
    Layout.CSpace{800n, Layout.NoneNat{}, 0n, 0n, Layout.MStrut{0n, 0n}, False{}},
    Layout.BlockContainer{
      1n,
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.Strut{0n, 0n, 2n, 0n},
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.SomeNat{100n},
      Layout.NoneNat{},
      False{},
      [m2_case6_child1(), m2_case6_child2()]
    })

def m2_self_collapse_res() -> Layout.LayoutResult:
  Layout.layout_block(
    Layout.CSpace{800n, Layout.NoneNat{}, 0n, 0n, Layout.MStrut{15n, 0n}, False{}},
    Layout.BlockContainer{
      4n,
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.SomeNat{100n},
      Layout.NoneNat{},
      False{},
      []
    })

def m2_bfc_res() -> Layout.LayoutResult:
  Layout.layout_block(
    Layout.CSpace{800n, Layout.NoneNat{}, 0n, 0n, Layout.MStrut{0n, 0n}, False{}},
    Layout.BlockContainer{
      5n,
      Layout.Strut{0n, 0n, 3n, 11n},
      Layout.Strut{0n, 0n, 5n, 7n},
      Layout.Strut{0n, 0n, 0n, 0n},
      Layout.NoneNat{},
      Layout.NoneNat{},
      True{},
      [m2_case6_child1(), m2_case6_child2()]
    })

law blink_m2_test_vectors:
  {[
    Layout.layout_result_bfc_block_offset_or(m2_case3_res(), 0n),
    Layout.layout_result_intrinsic_block_size(m2_case3_res()),
    Layout.layout_result_intrinsic_block_size(m2_case6_res()),
    Layout.layout_result_end_margin_pos(m2_case6_res()),
    Layout.layout_result_intrinsic_block_size(m2_self_collapse_res()),
    Layout.layout_result_end_margin_pos(m2_self_collapse_res()),
    Layout.layout_result_intrinsic_block_size(m2_bfc_res()),
    Nat.add(
      Nat.add(8n, Layout.total_collapsed_flow_block_size(800n, [m2_case6_child1(), m2_case6_child2()])),
      18n)
  ] == [200n, 50n, 142n, 50n, 0n, 15n, 216n, 216n] : List<&2, Nat>}

def blink_m2_test_vectors():
  {==}

# ==============================================================================
# M3 Laws: Greedy Line Breaking, Termination Measure, and Law 4
# Source:
# - inline/line_breaker.cc:740-925, 1024-1130, 2432-2515
# - inline/inline_layout_algorithm.cc:1340-1410
# ==============================================================================

# Explicit termination measure decrease on forced break (remaining length = rest.length)
law take_line_forced_break_termination_and_partition:
  for +avail: Nat
  for +id: Nat
  for +rest: List<&2, Layout.InlineItem>
  {Layout.inline_item_append(
    Layout.line_info_items(Layout.take_line_info(Layout.take_line(avail, Layout.ForcedBreak{id}, rest))),
    Layout.take_line_rem(Layout.take_line(avail, Layout.ForcedBreak{id}, rest))) ==
   (Layout.ForcedBreak{id} <> rest) : List<&2, Layout.InlineItem>}

def take_line_forced_break_termination_and_partition(avail, id, rest):
  {==}

# Single-item line partition: for any InlineItem `first`, take_line(avail, first, Nil{})
# partitions `[first]` into `items = [first]` and `remaining = Nil{}` (strictly decreasing length 1 -> 0).
law take_line_single_item_partition:
  for +avail: Nat
  for +first: Layout.InlineItem
  {Layout.inline_item_append(
    Layout.line_info_items(Layout.take_line_info(Layout.take_line(avail, first, Nil{}))),
    Layout.take_line_rem(Layout.take_line(avail, first, Nil{}))) ==
   (first <> Nil{}) : List<&2, Layout.InlineItem>}

def take_line_single_item_partition(avail, first):
  match first:
    case Layout.TextSeg{id, w, fh, cb, is_ts}:
      match is_ts:
        case True{}:
          {==}
        case False{}:
          {==}
    case Layout.AtomicInline{id, w, bs, fh}:
      {==}
    case Layout.OpenTag{id, b, p, m, fh}:
      {==}
    case Layout.CloseTag{id, b, p, m}:
      {==}
    case Layout.ForcedBreak{id}:
      {==}

# Single-item fallback fit law: for any InlineItem `first`, take_line(avail, first, Nil{})
# has non_break_item_count <= 1 (even if `first` overflows `avail`).
law take_line_single_item_non_break_count_le_one:
  for +avail: Nat
  for +first: Layout.InlineItem
  {Layout.nat_le(
    Layout.line_info_non_break_count(Layout.take_line_info(Layout.take_line(avail, first, Nil{}))),
    1n) == True{} : Bool}

def take_line_single_item_non_break_count_le_one(avail, first):
  match first:
    case Layout.TextSeg{id, w, fh, cb, is_ts}:
      match is_ts:
        case True{}:
          {==}
        case False{}:
          {==}
    case Layout.AtomicInline{id, w, bs, fh}:
      {==}
    case Layout.OpenTag{id, b, p, m, fh}:
      {==}
    case Layout.CloseTag{id, b, p, m}:
      {==}
    case Layout.ForcedBreak{id}:
      {==}

# Law 4a (Progress & termination bound): for any fuel, avail, items,
# break_lines_fuel(fuel, avail, items) produces at most `fuel` lines.
law break_lines_fuel_len_le_fuel:
  for +fuel: Nat
  for +avail: Nat
  for +items: List<&2, Layout.InlineItem>
  {Layout.nat_le(
    Layout.line_info_list_len(Layout.break_lines_fuel(fuel, avail, items)),
    fuel) == True{} : Bool}

def break_lines_fuel_len_le_fuel(fuel, avail, items):
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      match items:
        case Nil{}:
          {==}
        case +first <> +rest:
          break_lines_fuel_len_le_fuel(p, avail, Layout.take_line_rem(Layout.take_line(avail, first, rest)))

# Law 4 progress bound specialized to `break_lines(avail, items)` (`fuel = items.length`):
law line_breaker_progress_bound:
  for +avail: Nat
  for +items: List<&2, Layout.InlineItem>
  {Layout.nat_le(
    Layout.line_info_list_len(Layout.break_lines(avail, items)),
    Layout.inline_item_list_len(items)) == True{} : Bool}

def line_breaker_progress_bound(avail, items):
  break_lines_fuel_len_le_fuel(Layout.inline_item_list_len(items), avail, items)

# Transcribed Blink M3 unit test vectors (inline/line_breaker_test.cc & inline/inline_layout_algorithm_test.cc):
def m3_fh() -> Layout.FontHeight:
  Layout.FHeight{10n, 4n}

def m3_lines1() -> List<&2, Layout.LineInfo>:
  Layout.break_lines(100n, [
    Layout.TextSeg{1n, 40n, m3_fh(), True{}, False{}},
    Layout.TextSeg{2n, 10n, m3_fh(), True{}, True{}},
    Layout.TextSeg{3n, 40n, m3_fh(), True{}, False{}},
    Layout.TextSeg{4n, 40n, m3_fh(), True{}, False{}}
  ])

def m3_lines2() -> List<&2, Layout.LineInfo>:
  Layout.break_lines(100n, [
    Layout.TextSeg{5n, 95n, m3_fh(), True{}, False{}},
    Layout.TextSeg{6n, 20n, m3_fh(), True{}, True{}}
  ])

def m3_lines3() -> List<&2, Layout.LineInfo>:
  Layout.break_lines(100n, [
    Layout.TextSeg{1n, 40n, m3_fh(), True{}, False{}},
    Layout.ForcedBreak{7n},
    Layout.TextSeg{3n, 40n, m3_fh(), True{}, False{}}
  ])

def m3_lines4() -> List<&2, Layout.LineInfo>:
  Layout.break_lines(100n, [
    Layout.TextSeg{8n, 150n, m3_fh(), True{}, False{}},
    Layout.TextSeg{1n, 40n, m3_fh(), True{}, False{}}
  ])

law blink_m3_test_vectors:
  {[
    Layout.line_info_list_len(m3_lines1()),
    Layout.line_info_head_inline_size(m3_lines1()),
    Layout.line_info_list_len(m3_lines2()),
    Layout.line_info_head_inline_size(m3_lines2()),
    Layout.line_info_list_len(m3_lines3()),
    Layout.line_info_list_len(m3_lines4()),
    Layout.line_info_head_non_break_count(m3_lines4()),
    Layout.line_info_head_inline_size(m3_lines4())
  ] == [2n, 90n, 1n, 95n, 2n, 2n, 1n, 150n] : List<&2, Nat>}

def blink_m3_test_vectors():
  {==}
