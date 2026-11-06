# The sorted-map layer for the lessons map (LEntry): the lookup spec of the insertion and of the fold, and
# eq_of_sorted_lookup, the Bend side of Merge.lean's ins and fold lemmas. A map is a list of entries strictly
# increasing by key (SortedL in SORTED.bend). The proofs are in PROOF.bend, as def SM.<name>.
#
# eq_of_sorted_lookup takes SameLook in place of Lean's hypothesis "for every key k, the two lookups agree".
# SameLook only speaks about the entries the two maps hold: each entry of a is in b with the same value, and
# each entry of b is in a. Lean's hypothesis implies SameLook, so the law here is at least as strong as Lean's.

import Base
import ./merge.bend as Merge
import ./SORTED.bend as S

# Agree(s, b): every entry of s is in b with the same value (its lookup in b is Some of that value)
def Agree(s: List<&2, Merge.LEntry>, b: List<&2, Merge.LEntry>) -> Type:
  match s:
    case Nil{}:
      Unit
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          {S.lookup_l(b, kh) == Some{vh} : Maybe<&2, Merge.Lesson>} & Agree(t, b)

# SameLook(a, b): each map's entries are in the other with the same values
def SameLook(a: List<&2, Merge.LEntry>, b: List<&2, Merge.LEntry>) -> Type:
  Agree(a, b) & Agree(b, a)

# LAW: the lookup after inserting the entry (ke, ve) into a sorted map is the insertion spec ins_look_l
law lookup_ins:
  for +ke: String
  for +ve: Merge.Lesson
  for +k: String
  for +s: List<&2, Merge.LEntry>
  for ws: S.SortedL(s)
  {S.lookup_l(Merge.lins(Merge.LEntry{ke, ve}, s), k) == S.ins_look_l(Merge.skey_cmp(ke, k), S.lookup_l(s, k), ve) : Maybe<&2, Merge.Lesson>}

# LAW: the lookup after folding xs into a sorted acc combines the two lookups
law lookup_fold:
  for +xs: List<&2, Merge.LEntry>
  for +acc: List<&2, Merge.LEntry>
  for +k: String
  for sx: S.SortedL(xs)
  for sa: S.SortedL(acc)
  {S.lookup_l(Merge.lfold(xs, acc), k) == S.comb_opt_l(S.lookup_l(acc, k), S.lookup_l(xs, k)) : Maybe<&2, Merge.Lesson>}

# LAW: two sorted maps with the same entry lookups are equal (Merge.lean's eq_of_sorted_lookup, for lessons)
law eq_of_sorted_lookup:
  for +a: List<&2, Merge.LEntry>
  for +b: List<&2, Merge.LEntry>
  for sa: S.SortedL(a)
  for sb: S.SortedL(b)
  for hl: SameLook(a, b)
  {a == b : List<&2, Merge.LEntry>}
