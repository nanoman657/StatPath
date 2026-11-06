# The sorted-map layer: the Bend side of the sorted association lists in Merge.lean.
# Each map is a list of entries strictly increasing by key (skey_cmp, the same order as merge.bend).
# Sortedness is a Bool, so a sortedness fact can be reused as a `+` equation hypothesis.
# The three families are the lesson map (LEntry), the XP map (XEntry) and the SRS map (CEntry).

import Base
import ./merge.bend as Merge

# true exactly when the comparison is LT
def is_lt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

# Sorted (h :: t), read as: t is strictly increasing and every key of t is after k
# (the chain form of Merge.lean's Sorted: transitivity of < makes the two agree)
def sorted_from_l(t: List<&2, Merge.LEntry>, +k: String) -> Bool:
  match t:
    case Nil{}:
      True{}
    case h <> r:
      match h:
        case Merge.LEntry{+kh, +vh}:
          Bool.and(is_lt(Merge.skey_cmp(k, kh)), sorted_from_l(r, kh))

# Sorted s, for the lesson map
def sorted_l(s: List<&2, Merge.LEntry>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          sorted_from_l(t, kh)

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

# the lookup after inserting an entry with value w: combOpt with (some w) when the keys are EQ
def ins_look_l(c: Cmp, m: Maybe<&2, Merge.Lesson>, +w: Merge.Lesson) -> Maybe<&2, Merge.Lesson>:
  match c:
    case LT{}:
      m
    case EQ{}:
      comb_opt_l(m, Some{w})
    case GT{}:
      m
