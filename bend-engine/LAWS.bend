# The merge laws that have Bend kernel proofs so far. Each law is proven by a def of the same name in PROOF.bend.
# Not stated yet: the XP, SRS and state laws. See README.md.

import Base
import ./merge.bend as Merge
import ./ORDER.bend as Ord
import ./SORTED.bend as S

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

# LAW: Nat.max is associative
law max_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.max(a, Nat.max(b, c)) == Nat.max(Nat.max(a, b), c) : Nat}

# LAW: the lesson merge is associative
law lp_max_assoc:
  for +a: Merge.Lesson
  for +b: Merge.Lesson
  for +c: Merge.Lesson
  {Merge.lp_max(a, Merge.lp_max(b, c)) == Merge.lp_max(Merge.lp_max(a, b), c) : Merge.Lesson}

# LAW: two cards tie on review time, reps and due date and differ in ease: the larger ease is kept, whatever the order
law tie_ease:
  {Merge.card_merge(Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, Some{7n}}, Merge.Card{"c1", "l1", 1n, 250n, 5n, 0n, 1n, Some{7n}}) == Merge.Card{"c1", "l1", 1n, 250n, 5n, 0n, 1n, Some{7n}} : Merge.Card}

# LAW: an absent review time sorts before a review time of 0
law tie_absent:
  {Merge.card_merge(Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, None{}}, Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, Some{0n}}) == Merge.Card{"c1", "l1", 1n, 200n, 5n, 0n, 1n, Some{0n}} : Merge.Card}


# ---- the card order: helper laws for cardMerge_comm ----

# LAW: swapping the two strings of a skey comparison flips it
law skey_cmp_flip:
  for +a: String
  for +b: String
  {Merge.skey_cmp(b, a) == Ord.Cmp.flip(Merge.skey_cmp(a, b)) : Cmp}

# LAW: an EQ skey comparison means the two strings are equal
law skey_eq_of:
  for +a: String
  for +b: String
  for h: Ord.IsEQ(Merge.skey_cmp(a, b))
  {a == b : String}

# LAW: cmp_then flips when both of its arguments flip
law cmp_then_flip:
  for +c: Cmp
  for +d: Cmp
  {Merge.cmp_then(Ord.Cmp.flip(c), Ord.Cmp.flip(d)) == Ord.Cmp.flip(Merge.cmp_then(c, d)) : Cmp}

# LAW: cmp_then flips when each of its arguments is replaced by its flip
law cmp_then_swap:
  for +c: Cmp
  for +c2: Cmp
  for +d: Cmp
  for +d2: Cmp
  for ec: {c2 == Ord.Cmp.flip(c) : Cmp}
  for ed: {d2 == Ord.Cmp.flip(d) : Cmp}
  {Merge.cmp_then(c2, d2) == Ord.Cmp.flip(Merge.cmp_then(c, d)) : Cmp}

# LAW: swapping the two cards flips the whole-card comparison
law full_cmp_flip:
  for +A: Merge.Card
  for +B: Merge.Card
  {Merge.full_cmp(B, A) == Ord.Cmp.flip(Merge.full_cmp(A, B)) : Cmp}

# LAW: lastReview values whose keys compare EQ are equal
law last_key_eq:
  for +t1: Maybe<&2, Nat>
  for +t2: Maybe<&2, Nat>
  for h: Ord.IsEQ(Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))
  {t1 == t2 : Maybe<&2, Nat>}

# LAW: a whole-card EQ comparison means the two cards are equal
law full_eq_card:
  for +A: Merge.Card
  for +B: Merge.Card
  for h: Ord.IsEQ(Merge.full_cmp(A, B))
  {A == B : Merge.Card}

# LAW: card_pick with every comparison flipped and the cards swapped picks the same card; a full tie needs the cards equal
law card_pick_flip:
  for +x: Cmp
  for +r: Cmp
  for +d: Cmp
  for +f: Cmp
  for +A: Merge.Card
  for +B: Merge.Card
  for tie: Ord.IsEQ(f) -> {A == B : Merge.Card}
  {Merge.card_pick(Ord.Cmp.flip(x), Ord.Cmp.flip(r), Ord.Cmp.flip(d), Ord.Cmp.flip(f), B, A) == Merge.card_pick(x, r, d, f, A, B) : Merge.Card}

# LAW: cardMerge_comm: the card merge is commutative
law card_merge_comm:
  for +a: Merge.Card
  for +b: Merge.Card
  {Merge.card_merge(a, b) == Merge.card_merge(b, a) : Merge.Card}

# ---- the sorted-map laws: the key order is transitive, and the sorted-map operations keep it ----

# LAW: the key order is transitive: a < b and b < c give a < c
law skey_lt_trans:
  for +a: String
  for +b: String
  for +c: String
  for h1: {Merge.skey_cmp(a, b) == LT{} : Cmp}
  for h2: {Merge.skey_cmp(b, c) == LT{} : Cmp}
  {Merge.skey_cmp(a, c) == LT{} : Cmp}

# LAW: the lesson merge is commutative on any two lists. Lean's lessons_comm assumes both maps are sorted; this
# statement drops that hypothesis, because the proof (lf_comm) does not use it.
law lessons_comm:
  for +a: List<&2, Merge.LEntry>
  for +b: List<&2, Merge.LEntry>
  {Merge.merge_lessons(a, b) == Merge.merge_lessons(b, a) : List<&2, Merge.LEntry>}

# LAW: the lesson merge is idempotent on a sorted map: merging a map with itself gives the map back
law lessons_idem:
  for +a: List<&2, Merge.LEntry>
  for sa: S.SortedL(a)
  {Merge.merge_lessons(a, a) == a : List<&2, Merge.LEntry>}
