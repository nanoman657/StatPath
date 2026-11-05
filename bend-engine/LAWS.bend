# The merge laws that have Bend kernel proofs so far. Each law is proven by a def of the same name in PROOF.bend.
# Not stated yet: the sorted-map laws (lessons, SRS, XP, state) and the general card-order law. See README.md.

import Base
import ./merge.bend as Merge

# LAW: Nat.max is commutative
law max_comm:
  for +a: Nat
  for +b: Nat
  {Nat.max(a, b) == Nat.max(b, a) : Nat}

# LAW: Nat.max of a value with itself is that value
law max_self:
  for +a: Nat
  {Nat.max(a, a) == a : Nat}

# LAW: the lesson merge is commutative: each field takes the larger value
law lp_max_comm:
  for +a: Merge.Lesson
  for +b: Merge.Lesson
  {Merge.lp_max(a, b) == Merge.lp_max(b, a) : Merge.Lesson}

# LAW: the lesson merge of a lesson with itself is that lesson
law lp_max_self:
  for +a: Merge.Lesson
  {Merge.lp_max(a, a) == a : Merge.Lesson}

# LAW: two cards tie on review time, reps and due date and differ in ease: the larger ease is kept, whatever the order
law tie_ease:
  {Merge.card_merge(Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, Some{7n}}, Merge.Card{"c1", "l1", 1n, 250n, 5n, 0n, 1n, Some{7n}}) == Merge.Card{"c1", "l1", 1n, 250n, 5n, 0n, 1n, Some{7n}} : Merge.Card}

# LAW: an absent review time sorts before a review time of 0
law tie_absent:
  {Merge.card_merge(Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, None{}}, Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, Some{0n}}) == Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, Some{0n}} : Merge.Card}

# ---- the order of strings flips when its two arguments are swapped: the step toward antisymmetry ----
# Cmp.flip is defined here, since the laws below state it.

def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# LAW: flipping twice gives back the comparison
law Cmp.flip_flip:
  for c: Cmp
  {Cmp.flip(Cmp.flip(c)) == c : Cmp}

# LAW: swapping the two Bool arguments flips Bool.cmp
law Bool.cmp_flip:
  for a: Bool
  for b: Bool
  {Bool.cmp(b, a) == Cmp.flip(Bool.cmp(a, b)) : Cmp}

# LAW: the Word comparison step flips
law Word.cmp.fin_flip:
  for ab: Bool
  for bb: Bool
  for c: Cmp
  {Word.cmp.fin(bb, ab, Cmp.flip(c)) == Cmp.flip(Word.cmp.fin(ab, bb, c)) : Cmp}

# LAW: swapping the two Word arguments flips Word.cmp
law Word.cmp_flip:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.cmp(n, b, a) == Cmp.flip(Word.cmp(n, a, b)) : Cmp}

# LAW: swapping the two U32 arguments flips U32.cmp
law U32.cmp_flip:
  for a: U32
  for b: U32
  {U32.cmp(b, a) == Cmp.flip(U32.cmp(a, b)) : Cmp}

# LAW: swapping the two strings flips String.order.go, for any starting comparison
law String.order.go_flip:
  for a: String
  for b: String
  for c: Cmp
  {String.order.go(b, a, Cmp.flip(c)) == Cmp.flip(String.order.go(a, b, c)) : Cmp}

# LAW: swapping the two strings flips String.order
law String.order_flip:
  for a: String
  for b: String
  {String.order(b, a) == Cmp.flip(String.order(a, b)) : Cmp}
