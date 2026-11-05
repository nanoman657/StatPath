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

