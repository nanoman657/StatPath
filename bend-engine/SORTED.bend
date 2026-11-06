# The sorted-map layer: the Bend side of the sorted association lists in Merge.lean.
# Each map is a list of entries strictly increasing by key (skey_cmp, the same order as merge.bend).
# Sortedness is a Type (a witness, in the style of ORDER.bend's IsLT), so a proof can take it apart.
# Three families: lessons (LEntry, combined by lp_max), XP per day (XEntry, Nat.max) and SRS cards (CEntry, card_merge).

import Base
import ./merge.bend as Merge
import ./ORDER.bend as Ord

# ---- lessons (LEntry) ----

# KAllL(s, k): every key of s comes after k. Unit for an empty list.
def KAllL(s: List<&2, Merge.LEntry>, +k: String) -> Type:
  match s:
    case Nil{}:
      Unit
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          Ord.IsLT(Merge.skey_cmp(k, kh)) & KAllL(t, k)

# SortedL(s): s is strictly increasing by key
def SortedL(s: List<&2, Merge.LEntry>) -> Type:
  match s:
    case Nil{}:
      Unit
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          KAllL(t, kh) & SortedL(t)

# the answer when the head entry compares c with k: EQ takes this entry, otherwise the rest
def pick_l(c: Cmp, +v: Merge.Lesson, rest: Maybe<&2, Merge.Lesson>) -> Maybe<&2, Merge.Lesson>:
  match c:
    case LT{}:
      rest
    case EQ{}:
      Some{v}
    case GT{}:
      rest

# lookup k s: the value of the entry whose key is k (Merge.lean's lookup)
def lookup_l(s: List<&2, Merge.LEntry>, +k: String) -> Maybe<&2, Merge.Lesson>:
  match s:
    case Nil{}:
      None{}
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          pick_l(Merge.skey_cmp(kh, k), vh, lookup_l(t, k))

# combOpt: the value when both maps have the key is lp_max of the two values
def comb_opt_l(m: Maybe<&2, Merge.Lesson>, n: Maybe<&2, Merge.Lesson>) -> Maybe<&2, Merge.Lesson>:
  match m n:
    case Some{v} Some{w}:
      Some{Merge.lp_max(v, w)}
    case Some{v} None{}:
      Some{v}
    case None{} Some{w}:
      Some{w}
    case None{} None{}:
      None{}

# the lookup after inserting an entry with key ke and value w: c = skey_cmp(ke, k)
def ins_look_l(c: Cmp, m: Maybe<&2, Merge.Lesson>, +w: Merge.Lesson) -> Maybe<&2, Merge.Lesson>:
  match c:
    case LT{}:
      m
    case EQ{}:
      comb_opt_l(m, Some{w})
    case GT{}:
      m
