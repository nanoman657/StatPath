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

# BoxStrut (geometry/box_strut.h:33-114)
type BoxStrut is Data:
  Strut{inline_start: Nat, inline_end: Nat, block_start: Nat, block_end: Nat}

# BoxStrut::InlineSum() (geometry/box_strut.h:62)
def box_strut_inline_sum(s: BoxStrut) -> Nat:
  match s:
    case Strut{inline_start, inline_end, block_start, block_end}:
      Nat.add(inline_start, inline_end)

# BoxStrut::BlockSum() (geometry/box_strut.h:63)
def box_strut_block_sum(s: BoxStrut) -> Nat:
  match s:
    case Strut{inline_start, inline_end, block_start, block_end}:
      Nat.add(block_start, block_end)

# BoxStrut::operator+ (geometry/box_strut.h:74-85)
def box_strut_add(a: BoxStrut, b: BoxStrut) -> BoxStrut:
  match a b:
    case Strut{is1, ie1, bs1, be1} Strut{is2, ie2, bs2, be2}:
      Strut{Nat.add(is1, is2), Nat.add(ie1, ie2), Nat.add(bs1, bs2), Nat.add(be1, be2)}

# MarginStrut (geometry/margin_strut.h:16-58, geometry/margin_strut.cc:11-46)
type MarginStrut is Data:
  MStrut{pos: Nat, neg: Nat}

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

def maybe_nat_get_or(m: MaybeNat, fallback: Nat) -> Nat:
  match m:
    case NoneNat{}:
      fallback
    case SomeNat{val}:
      val

def maybe_nat_is_some(m: MaybeNat) -> Bool:
  match m:
    case NoneNat{}:
      False{}
    case SomeNat{val}:
      True{}

def maybe_nat_is_none(m: MaybeNat) -> Bool:
  match m:
    case NoneNat{}:
      True{}
    case SomeNat{val}:
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

# Boolean > 0 on Nat
def nat_pos(a: Nat) -> Bool:
  match a:
    case 0n:
      False{}
    case 1n+p:
      True{}
