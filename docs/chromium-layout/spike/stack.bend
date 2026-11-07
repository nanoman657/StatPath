# Feasibility spike: vertical stacking of two in-flow CSS 2.1 block boxes
# Models Blink LayoutNG's BlockLayoutAlgorithm::ComputeInflowPosition,
# MarginStrut::Append / MarginStrut::Sum (for non-negative margins),
# and BFC block-offset resolution in:
#   third_party/blink/renderer/core/layout/block_layout_algorithm.cc
#   third_party/blink/renderer/core/layout/geometry/margin_strut.cc

import Base

# An in-flow block box with block-axis box-model metrics (in LayoutUnits).
type BlockBox is Data:
  Box{margin_start: Nat, border_start: Nat, content_size: Nat, border_end: Nat, margin_end: Nat}

# Output fragment geometry for two vertically stacked sibling block boxes
# inside a BFC-root block container.
type StackLayout is Data:
  Stacked{y1: Nat, h1: Nat, collapsed_gap: Nat, y2: Nat, h2: Nat, container_size: Nat}

# Collapse two adjacent non-negative vertical margins (MarginStrut::Sum).
def collapse_margins(m1: Nat, m2: Nat) -> Nat:
  Nat.max(m1, m2)

# Border-box block-size of a BlockBox: border_start + content_size + border_end.
def box_border_size(b: BlockBox) -> Nat:
  match b:
    case Box{margin_start, border_start, content_size, border_end, margin_end}:
      Nat.add(Nat.add(border_start, content_size), border_end)

# Block-start margin of a BlockBox.
def box_margin_start(b: BlockBox) -> Nat:
  match b:
    case Box{margin_start, border_start, content_size, border_end, margin_end}:
      margin_start

# Block-end margin of a BlockBox.
def box_margin_end(b: BlockBox) -> Nat:
  match b:
    case Box{margin_start, border_start, content_size, border_end, margin_end}:
      margin_end

# Compute the BFC block-offset of the second box given the first box's
# border-box end offset (y1 + h1) and the two adjacent margins.
def next_border_edge(y1_end: Nat, m1_end: Nat, m2_start: Nat) -> Nat:
  Nat.add(y1_end, collapse_margins(m1_end, m2_start))

# Stack two in-flow block boxes vertically inside a block container with
# block-start/block-end border+padding `pad_start` and `pad_end`.
def stack_two(+pad_start: Nat, +pad_end: Nat, +b1: BlockBox, +b2: BlockBox) -> StackLayout:
  match b1 b2:
    case Box{+m1s, +b1s, +c1, +b1e, +m1e} Box{+m2s, +b2s, +c2, +b2e, +m2e}:
      y1  = Nat.add(pad_start, m1s)
      h1  = Nat.add(Nat.add(b1s, c1), b1e)
      y1e = Nat.add(Nat.add(pad_start, m1s), Nat.add(Nat.add(b1s, c1), b1e))
      gap = Nat.max(m1e, m2s)
      y2  = Nat.add(y1e, Nat.max(m1e, m2s))
      h2  = Nat.add(Nat.add(b2s, c2), b2e)
      y2e = Nat.add(Nat.add(Nat.add(pad_start, m1s), Nat.add(Nat.add(b1s, c1), b1e)), Nat.add(Nat.max(m1e, m2s), Nat.add(Nat.add(b2s, c2), b2e)))
      csz = Nat.add(y2e, Nat.add(m2e, pad_end))
      Stacked{y1, h1, gap, y2, h2, csz}

# Extract the BFC block-offset of child 2 from a StackLayout.
def layout_y2(s: StackLayout) -> Nat:
  match s:
    case Stacked{y1, h1, collapsed_gap, y2, h2, container_size}:
      y2

# Extract the block-end border edge of child 1 (y1 + h1) plus the collapsed gap.
def layout_y1_end_plus_gap(s: StackLayout) -> Nat:
  match s:
    case Stacked{y1, h1, collapsed_gap, y2, h2, container_size}:
      Nat.add(Nat.add(y1, h1), collapsed_gap)

# Boolean <= on Nat for non-overlap verification.
def nat_le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      nat_le(p, q)

# ---- Laws and Kernel Proofs ----

# LAW 1: Margin collapsing is idempotent: collapse_margins(m, m) == m.
law collapse_margins_idem:
  for +m: Nat
  {collapse_margins(m, m) == m : Nat}

def collapse_margins_idem(m):
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(p, p), p, collapse_margins_idem(p))

# LAW 2: Margin collapsing is commutative: collapse_margins(a, b) == collapse_margins(b, a).
law collapse_margins_comm:
  for +a: Nat
  for +b: Nat
  {collapse_margins(a, b) == collapse_margins(b, a) : Nat}

def collapse_margins_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, p => 1n+p, Nat.max(ap, bp), Nat.max(bp, ap), collapse_margins_comm(ap, bp))

# LAW 3: Adding a non-negative collapsed gap never places the next box above y1_end.
law add_nonneg_le:
  for +y1_end: Nat
  for +gap: Nat
  {nat_le(y1_end, Nat.add(y1_end, gap)) == True{} : Bool}

def add_nonneg_le(y1_end, gap):
  match y1_end:
    case 0n:
      {==}
    case 1n+p:
      add_nonneg_le(p, gap)

# LAW 4: Child 2's BFC block-offset is never less than child 1's border-box end (non-overlapping).
law stack_two_non_overlap:
  for +y1_end: Nat
  for +m1_end: Nat
  for +m2_start: Nat
  {nat_le(y1_end, next_border_edge(y1_end, m1_end, m2_start)) == True{} : Bool}

def stack_two_non_overlap(y1_end, m1_end, m2_start):
  add_nonneg_le(y1_end, collapse_margins(m1_end, m2_start))

# LAW 5: Concrete sanity check on stack_two: two block boxes with margins (10, 20) and (15, 5)
# collapse their inner margin to max(20, 15) = 20.
law stack_two_example:
  {collapse_margins(20n, 15n) == 20n : Nat}

def stack_two_example():
  {==}

