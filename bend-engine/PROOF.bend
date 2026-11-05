# Proofs of the laws in LAWS.bend. Check with: bend bend-engine/PROOF.bend, and bend bend-engine/PROOF.bend --verdict.
import Base
import ./merge.bend as Merge
import ./LAWS.bend as Laws
import ./ORDER.bend as Ord

def Laws.max_comm(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, p => 1n+p, Nat.max(ap, bp), Nat.max(bp, ap), Laws.max_comm(ap, bp))

def Laws.max_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(p, p), p, Laws.max_self(p))

def Laws.lp_max_comm(a, b):
  match a b:
    case Merge.Lp{c1, n1, b1, p1} Merge.Lp{c2, n2, b2, p2}:
      s1 = Equal.cong(Nat, Merge.Lesson, x => Merge.Lp{x, Nat.max(n1, n2), Nat.max(b1, b2), Nat.max(p1, p2)}, Nat.max(c1, c2), Nat.max(c2, c1), Laws.max_comm(c1, c2))
      s2 = Equal.cong(Nat, Merge.Lesson, y => Merge.Lp{Nat.max(c2, c1), y, Nat.max(b1, b2), Nat.max(p1, p2)}, Nat.max(n1, n2), Nat.max(n2, n1), Laws.max_comm(n1, n2))
      s3 = Equal.cong(Nat, Merge.Lesson, z => Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), z, Nat.max(p1, p2)}, Nat.max(b1, b2), Nat.max(b2, b1), Laws.max_comm(b1, b2))
      s4 = Equal.cong(Nat, Merge.Lesson, w => Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b2, b1), w}, Nat.max(p1, p2), Nat.max(p2, p1), Laws.max_comm(p1, p2))
      Equal.trans(Merge.Lesson,
        Merge.Lp{Nat.max(c1, c2), Nat.max(n1, n2), Nat.max(b1, b2), Nat.max(p1, p2)},
        Merge.Lp{Nat.max(c2, c1), Nat.max(n1, n2), Nat.max(b1, b2), Nat.max(p1, p2)},
        Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b2, b1), Nat.max(p2, p1)},
        s1,
        Equal.trans(Merge.Lesson,
          Merge.Lp{Nat.max(c2, c1), Nat.max(n1, n2), Nat.max(b1, b2), Nat.max(p1, p2)},
          Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b1, b2), Nat.max(p1, p2)},
          Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b2, b1), Nat.max(p2, p1)},
          s2,
          Equal.trans(Merge.Lesson,
            Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b1, b2), Nat.max(p1, p2)},
            Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b2, b1), Nat.max(p1, p2)},
            Merge.Lp{Nat.max(c2, c1), Nat.max(n2, n1), Nat.max(b2, b1), Nat.max(p2, p1)},
            s3, s4)))

def Laws.lp_max_self(a):
  match a:
    case Merge.Lp{c, n, b, p}:
      t1 = Equal.cong(Nat, Merge.Lesson, x => Merge.Lp{x, Nat.max(n, n), Nat.max(b, b), Nat.max(p, p)}, Nat.max(c, c), c, Laws.max_self(c))
      t2 = Equal.cong(Nat, Merge.Lesson, y => Merge.Lp{c, y, Nat.max(b, b), Nat.max(p, p)}, Nat.max(n, n), n, Laws.max_self(n))
      t3 = Equal.cong(Nat, Merge.Lesson, z => Merge.Lp{c, n, z, Nat.max(p, p)}, Nat.max(b, b), b, Laws.max_self(b))
      t4 = Equal.cong(Nat, Merge.Lesson, w => Merge.Lp{c, n, b, w}, Nat.max(p, p), p, Laws.max_self(p))
      Equal.trans(Merge.Lesson,
        Merge.Lp{Nat.max(c, c), Nat.max(n, n), Nat.max(b, b), Nat.max(p, p)},
        Merge.Lp{c, Nat.max(n, n), Nat.max(b, b), Nat.max(p, p)},
        Merge.Lp{c, n, b, p},
        t1,
        Equal.trans(Merge.Lesson,
          Merge.Lp{c, Nat.max(n, n), Nat.max(b, b), Nat.max(p, p)},
          Merge.Lp{c, n, Nat.max(b, b), Nat.max(p, p)},
          Merge.Lp{c, n, b, p},
          t2,
          Equal.trans(Merge.Lesson,
            Merge.Lp{c, n, Nat.max(b, b), Nat.max(p, p)},
            Merge.Lp{c, n, b, Nat.max(p, p)},
            Merge.Lp{c, n, b, p},
            t3, t4)))

def Laws.tie_ease():
  {==}

def Laws.tie_absent():
  {==}

# ---- the string order's swap law: the flip laws ----

def Laws.Cmp.flip_flip(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.Bool.cmp_flip(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Laws.Word.cmp.fin_flip(ab, bb, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Laws.Bool.cmp_flip(ab, bb)
    case GT{}:
      {==}

def Laws.Word.cmp_flip(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(Cmp,
            Word.cmp.fin(bb, ab, Word.cmp(p, bt, at)),
            Word.cmp.fin(bb, ab, Laws.Cmp.flip(Word.cmp(p, at, bt))),
            Laws.Cmp.flip(Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))),
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(bb, ab, c), Word.cmp(p, bt, at), Laws.Cmp.flip(Word.cmp(p, at, bt)), Laws.Word.cmp_flip(p, at, bt)),
            Laws.Word.cmp.fin_flip(ab, bb, Word.cmp(p, at, bt)))

def Laws.U32.cmp_flip(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Laws.Word.cmp_flip(32n, x, y)

def Laws.String.order.go_flip(a, b, c):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{_}, +t}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SCon{Chr{_}, +t} SNil{}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          {==}
        case EQ{}:
          Equal.trans(Cmp,
            String.order.go(t2, t1, U32.cmp(y, x)),
            String.order.go(t2, t1, Laws.Cmp.flip(U32.cmp(x, y))),
            Laws.Cmp.flip(String.order.go(t1, t2, U32.cmp(x, y))),
            Equal.cong(Cmp, Cmp, c2 => String.order.go(t2, t1, c2), U32.cmp(y, x), Laws.Cmp.flip(U32.cmp(x, y)), Laws.U32.cmp_flip(x, y)),
            Laws.String.order.go_flip(t1, t2, U32.cmp(x, y)))
        case GT{}:
          {==}

def Laws.String.order_flip(a, b):
  Laws.String.order.go_flip(a, b, EQ{})
