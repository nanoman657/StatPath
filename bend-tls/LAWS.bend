# LAWS.bend: what the branch-free selects compute. PROOF.bend proves each law.
#
# A select picks one of two operands with arithmetic on a bit s, so the code takes the same
# path whatever s is. These laws say the arithmetic picks the right operand for s = 0 and s = 1:
#   sel_nat_*   the scalar form a * (1 - s) + b * s used by fe.sel, pl.sel and similar
#   bi_sel_*    bi.sel, limb by limb, on two lists of the same length (SPEC.bend's same_shape)
# The laws are stated as x == f(...) so that the proofs can rewrite the right-hand side.

import Base
import ./SPEC.bend as Spec
import ./bigint.bend as B

law sel_nat_zero:
  for +a: Nat
  for +b: Nat
  {a == Nat.add(Nat.mul(a, Nat.sub(1n, 0n)), Nat.mul(b, 0n)) : Nat}

law sel_nat_one:
  for +a: Nat
  for +b: Nat
  {b == Nat.add(Nat.mul(a, Nat.sub(1n, 1n)), Nat.mul(b, 1n)) : Nat}

# bi.sel with s = 1 returns x
law bi_sel_one:
  for +x: List<&2, Nat>
  for +y: List<&2, Nat>
  for h: {Spec.same_shape(x, y) == True{} : Bool}
  {x == B.bi.sel(1n, x, y) : List<&2, Nat>}

# bi.sel with s = 0 returns y
law bi_sel_zero:
  for +x: List<&2, Nat>
  for +y: List<&2, Nat>
  for h: {Spec.same_shape(x, y) == True{} : Bool}
  {y == B.bi.sel(0n, x, y) : List<&2, Nat>}
