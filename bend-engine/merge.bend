import Base

# The learning-data merge of src/engine/merge.ts: mergeLesson, mergeCard, and the lesson, card and XP maps.
#
# Representation. Each map is a list of entries strictly increasing by key (String.cmp), so a key appears
# once. A key in both maps is combined: lessons take the larger of each field, XP takes the larger day
# total, and cards take mergeCard(a, b) with the first map's card first. Numbers are Nat. A lastReview
# that is absent is None, which the comparisons read as 0 (the TypeScript's "?? 0") and the output keeps
# as None.

type Lesson is Data:
  Lp{crowns: Nat, attempts: Nat, best: Nat, played: Nat}

type Card is Data:
  Card{id: String, lessonId: String, interval: Nat, ease: Nat, due: Nat, lapses: Nat, reps: Nat, last: Maybe<&2, Nat>}

type LEntry is Data:
  LEntry{key: String, val: Lesson}

type CEntry is Data:
  CEntry{key: String, val: Card}

type XEntry is Data:
  XEntry{key: String, val: Nat}

type State is Data:
  St{lessons: List<&2, LEntry>, srs: List<&2, CEntry>, xpByDay: List<&2, XEntry>}

type Out is Data:
  Out{lessons: List<&2, LEntry>, srs: List<&2, CEntry>, xpByDay: List<&2, XEntry>, xp: Nat}

# the order of two keys: String.cmp returns the two strings with the order
def cmp_of(p: (String & String) & Cmp) -> Cmp:
  ((x, y), c) = p
  c

def skey_cmp(a: String, b: String) -> Cmp:
  cmp_of(String.cmp(a, b))

# ---- the combines ----

def lp_max(a: Lesson, b: Lesson) -> Lesson:
  match a b:
    case Lp{c1, n1, b1, p1} Lp{c2, n2, b2, p2}:
      Lp{Nat.max(c1, c2), Nat.max(n1, n2), Nat.max(b1, b2), Nat.max(p1, p2)}

def last_or0(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

# the number a lastReview sorts by in the whole-card order: an absent one first, then the time plus one
def last_key(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      Nat.add(x, 1n)

# lexicographic: the first comparison that is not EQ decides
def cmp_then(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case GT{}:
      GT{}
    case EQ{}:
      d

# the whole card, field by field, in the order of compareCards in merge.ts
def full_cmp(+a: Card, +b: Card) -> Cmp:
  match a b:
    case Card{+i1, +l1, +v1, +e1, +d1, +s1, +r1, +t1} Card{+i2, +l2, +v2, +e2, +d2, +s2, +r2, +t2}:
      cmp_then(skey_cmp(i1, i2),
      cmp_then(skey_cmp(l1, l2),
      cmp_then(Nat.cmp(v1, v2),
      cmp_then(Nat.cmp(e1, e2),
      cmp_then(Nat.cmp(d1, d2),
      cmp_then(Nat.cmp(s1, s2),
      cmp_then(Nat.cmp(r1, r2),
      Nat.cmp(last_key(t1), last_key(t2)))))))))

# the card mergeCard keeps: the later review, then more reps, then the later due date, then the card with
# the larger content; a full tie keeps a
def card_pick(c_last: Cmp, c_reps: Cmp, c_due: Cmp, c_full: Cmp, a: Card, b: Card) -> Card:
  match c_last:
    case LT{}:
      b
    case GT{}:
      a
    case EQ{}:
      match c_reps:
        case LT{}:
          b
        case GT{}:
          a
        case EQ{}:
          match c_due:
            case LT{}:
              b
            case GT{}:
              a
            case EQ{}:
              match c_full:
                case LT{}:
                  b
                case GT{}:
                  a
                case EQ{}:
                  a

def card_merge(+a: Card, +b: Card) -> Card:
  match a b:
    case Card{+i1, +l1, +v1, +e1, +d1, +s1, +r1, +t1} Card{+i2, +l2, +v2, +e2, +d2, +s2, +r2, +t2}:
      card_pick(Nat.cmp(last_or0(t1), last_or0(t2)), Nat.cmp(r1, r2), Nat.cmp(d1, d2),
        full_cmp(a, b), a, b)

# ---- lessons ----

def lins_c(t: List<&2, LEntry>, c: Cmp, e: LEntry, h: LEntry) -> List<&2, LEntry>:
  match t:
    case Nil{}:
      match c:
        case LT{}:
          e <> (h <> Nil{})
        case EQ{}:
          match e h:
            case LEntry{+ke, +ve} LEntry{kh, vh}:
              LEntry{kh, lp_max(vh, ve)} <> Nil{}
        case GT{}:
          h <> (e <> Nil{})
    case h2 <> t2:
      match h2:
        case LEntry{+k2, +v2}:
          match c:
            case LT{}:
              e <> (h <> (LEntry{k2, v2} <> t2))
            case EQ{}:
              match e h:
                case LEntry{+ke, +ve} LEntry{kh, vh}:
                  LEntry{kh, lp_max(vh, ve)} <> (LEntry{k2, v2} <> t2)
            case GT{}:
              match e:
                case LEntry{+ke, +ve}:
                  h <> lins_c(t2, skey_cmp(ke, k2), LEntry{ke, ve}, LEntry{k2, v2})

def lins(e: LEntry, s: List<&2, LEntry>) -> List<&2, LEntry>:
  match e:
    case LEntry{+ke, +ve}:
      match s:
        case Nil{}:
          LEntry{ke, ve} <> Nil{}
        case h <> t:
          match h:
            case LEntry{+kh, +vh}:
              lins_c(t, skey_cmp(ke, kh), LEntry{ke, ve}, LEntry{kh, vh})

def lfold(xs: List<&2, LEntry>, acc: List<&2, LEntry>) -> List<&2, LEntry>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      lfold(t, lins(h, acc))

def merge_lessons(a: List<&2, LEntry>, b: List<&2, LEntry>) -> List<&2, LEntry>:
  lfold(b, lfold(a, Nil{}))

# ---- cards: the existing entry is from the first map, so the combine is mergeCard(a, b) ----

def cins_c(t: List<&2, CEntry>, c: Cmp, e: CEntry, h: CEntry) -> List<&2, CEntry>:
  match t:
    case Nil{}:
      match c:
        case LT{}:
          e <> (h <> Nil{})
        case EQ{}:
          match e h:
            case CEntry{+ke, +ve} CEntry{kh, vh}:
              CEntry{kh, card_merge(vh, ve)} <> Nil{}
        case GT{}:
          h <> (e <> Nil{})
    case h2 <> t2:
      match h2:
        case CEntry{+k2, +v2}:
          match c:
            case LT{}:
              e <> (h <> (CEntry{k2, v2} <> t2))
            case EQ{}:
              match e h:
                case CEntry{+ke, +ve} CEntry{kh, vh}:
                  CEntry{kh, card_merge(vh, ve)} <> (CEntry{k2, v2} <> t2)
            case GT{}:
              match e:
                case CEntry{+ke, +ve}:
                  h <> cins_c(t2, skey_cmp(ke, k2), CEntry{ke, ve}, CEntry{k2, v2})

def cins(e: CEntry, s: List<&2, CEntry>) -> List<&2, CEntry>:
  match e:
    case CEntry{+ke, +ve}:
      match s:
        case Nil{}:
          CEntry{ke, ve} <> Nil{}
        case h <> t:
          match h:
            case CEntry{+kh, +vh}:
              cins_c(t, skey_cmp(ke, kh), CEntry{ke, ve}, CEntry{kh, vh})

def cfold(xs: List<&2, CEntry>, acc: List<&2, CEntry>) -> List<&2, CEntry>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      cfold(t, cins(h, acc))

def merge_srs(a: List<&2, CEntry>, b: List<&2, CEntry>) -> List<&2, CEntry>:
  cfold(b, cfold(a, Nil{}))

# ---- XP per day: the larger value for each day ----

def xins_c(t: List<&2, XEntry>, c: Cmp, e: XEntry, h: XEntry) -> List<&2, XEntry>:
  match t:
    case Nil{}:
      match c:
        case LT{}:
          e <> (h <> Nil{})
        case EQ{}:
          match e h:
            case XEntry{+ke, +ve} XEntry{kh, vh}:
              XEntry{kh, Nat.max(vh, ve)} <> Nil{}
        case GT{}:
          h <> (e <> Nil{})
    case h2 <> t2:
      match h2:
        case XEntry{+k2, +v2}:
          match c:
            case LT{}:
              e <> (h <> (XEntry{k2, v2} <> t2))
            case EQ{}:
              match e h:
                case XEntry{+ke, +ve} XEntry{kh, vh}:
                  XEntry{kh, Nat.max(vh, ve)} <> (XEntry{k2, v2} <> t2)
            case GT{}:
              match e:
                case XEntry{+ke, +ve}:
                  h <> xins_c(t2, skey_cmp(ke, k2), XEntry{ke, ve}, XEntry{k2, v2})

def xins(e: XEntry, s: List<&2, XEntry>) -> List<&2, XEntry>:
  match e:
    case XEntry{+ke, +ve}:
      match s:
        case Nil{}:
          XEntry{ke, ve} <> Nil{}
        case h <> t:
          match h:
            case XEntry{+kh, +vh}:
              xins_c(t, skey_cmp(ke, kh), XEntry{ke, ve}, XEntry{kh, vh})

def xfold(xs: List<&2, XEntry>, acc: List<&2, XEntry>) -> List<&2, XEntry>:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      xfold(t, xins(h, acc))

def merge_xp(a: List<&2, XEntry>, b: List<&2, XEntry>) -> List<&2, XEntry>:
  xfold(b, xfold(a, Nil{}))

# the total XP: the sum of the day values
def xsum(xs: List<&2, XEntry>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      match h:
        case XEntry{+k, +v}:
          Nat.add(v, xsum(t))

# ---- the learning data of two copies ----

def merge_state(a: State, b: State) -> Out:
  match a b:
    case St{la, ca, xa} St{lb, cb, xb}:
      +mx = merge_xp(xa, xb)
      Out{merge_lessons(la, lb), merge_srs(ca, cb), mx, xsum(mx)}
