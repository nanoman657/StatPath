# Proofs of the laws in LAWS.bend. Check with: bend bend-engine/PROOF.bend, and bend bend-engine/PROOF.bend --verdict.
import Base
import ./merge.bend as Merge
import ./LAWS.bend as Laws
import ./ORDER.bend as Ord
import ./SORTED.bend as S
import ./KEYS.bend as Key

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

def Laws.max_assoc(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+cp:
      {==}
    case 0n 1n+bp 0n:
      {==}
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n 0n:
      {==}
    case 1n+ap 0n 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      {==}
    case 1n+ap 1n+bp 1n+cp:
      Equal.cong(Nat, Nat, p => 1n+p, Nat.max(ap, Nat.max(bp, cp)), Nat.max(Nat.max(ap, bp), cp), Laws.max_assoc(ap, bp, cp))

def Laws.lp_max_assoc(a, b, c):
  match a b c:
    case Merge.Lp{c1, n1, b1, p1} Merge.Lp{c2, n2, b2, p2} Merge.Lp{c3, n3, b3, p3}:
      s1 = Equal.cong(Nat, Merge.Lesson, x => Merge.Lp{x, Nat.max(n1, Nat.max(n2, n3)), Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))}, Nat.max(c1, Nat.max(c2, c3)), Nat.max(Nat.max(c1, c2), c3), Laws.max_assoc(c1, c2, c3))
      s2 = Equal.cong(Nat, Merge.Lesson, y => Merge.Lp{Nat.max(Nat.max(c1, c2), c3), y, Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))}, Nat.max(n1, Nat.max(n2, n3)), Nat.max(Nat.max(n1, n2), n3), Laws.max_assoc(n1, n2, n3))
      s3 = Equal.cong(Nat, Merge.Lesson, z => Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), z, Nat.max(p1, Nat.max(p2, p3))}, Nat.max(b1, Nat.max(b2, b3)), Nat.max(Nat.max(b1, b2), b3), Laws.max_assoc(b1, b2, b3))
      s4 = Equal.cong(Nat, Merge.Lesson, w => Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(Nat.max(b1, b2), b3), w}, Nat.max(p1, Nat.max(p2, p3)), Nat.max(Nat.max(p1, p2), p3), Laws.max_assoc(p1, p2, p3))
      Equal.trans(Merge.Lesson,
        Merge.Lp{Nat.max(c1, Nat.max(c2, c3)), Nat.max(n1, Nat.max(n2, n3)), Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))},
        Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(n1, Nat.max(n2, n3)), Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))},
        Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(Nat.max(b1, b2), b3), Nat.max(Nat.max(p1, p2), p3)},
        s1,
        Equal.trans(Merge.Lesson,
          Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(n1, Nat.max(n2, n3)), Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))},
          Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))},
          Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(Nat.max(b1, b2), b3), Nat.max(Nat.max(p1, p2), p3)},
          s2,
          Equal.trans(Merge.Lesson,
            Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(b1, Nat.max(b2, b3)), Nat.max(p1, Nat.max(p2, p3))},
            Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(Nat.max(b1, b2), b3), Nat.max(p1, Nat.max(p2, p3))},
            Merge.Lp{Nat.max(Nat.max(c1, c2), c3), Nat.max(Nat.max(n1, n2), n3), Nat.max(Nat.max(b1, b2), b3), Nat.max(Nat.max(p1, p2), p3)},
            s3, s4)))

def Laws.tie_ease():
  {==}

def Laws.tie_absent():
  {==}


# ---- the witnesses of cmp_then: an EQ result is an EQ of its first argument and of its second ----

def cmp_then_l(c: Cmp, d: Cmp, h: Ord.IsEQ(Merge.cmp_then(c, d))) -> Ord.IsEQ(c):
  match c:
    case LT{}:
      Empty.absurd(Ord.IsEQ(LT{}), h)
    case EQ{}:
      Unit{}
    case GT{}:
      Empty.absurd(Ord.IsEQ(GT{}), h)

def cmp_then_r(c: Cmp, d: Cmp, h: Ord.IsEQ(Merge.cmp_then(c, d))) -> Ord.IsEQ(d):
  match c:
    case LT{}:
      Empty.absurd(Ord.IsEQ(d), h)
    case EQ{}:
      h
    case GT{}:
      Empty.absurd(Ord.IsEQ(d), h)

def Laws.skey_cmp_flip(a, b):
  Equal.trans(Cmp,
    Merge.skey_cmp(b, a),
    String.order(b, a),
    Ord.Cmp.flip(Merge.skey_cmp(a, b)),
    Key.Key.skey_eq_order(b, a),
    Equal.trans(Cmp,
      String.order(b, a),
      Ord.Cmp.flip(String.order(a, b)),
      Ord.Cmp.flip(Merge.skey_cmp(a, b)),
      Ord.String.order_flip(a, b),
      Equal.cong(Cmp, Cmp, c => Ord.Cmp.flip(c), String.order(a, b), Merge.skey_cmp(a, b),
        Equal.sym(Cmp, Merge.skey_cmp(a, b), String.order(a, b), Key.Key.skey_eq_order(a, b)))))

def Laws.skey_eq_of(a, b, h):
  Ord.String.order.eq_w(a, b,
    Ord.Cmp.trEQ(String.order(a, b), Merge.skey_cmp(a, b),
      Equal.sym(Cmp, Merge.skey_cmp(a, b), String.order(a, b), Key.Key.skey_eq_order(a, b)), h))

def Laws.cmp_then_flip(c, d):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.cmp_then_swap(c, c2, d, d2, ec, ed):
  Equal.trans(Cmp,
    Merge.cmp_then(c2, d2),
    Merge.cmp_then(Ord.Cmp.flip(c), d2),
    Ord.Cmp.flip(Merge.cmp_then(c, d)),
    Equal.cong(Cmp, Cmp, w => Merge.cmp_then(w, d2), c2, Ord.Cmp.flip(c), ec),
    Equal.trans(Cmp,
      Merge.cmp_then(Ord.Cmp.flip(c), d2),
      Merge.cmp_then(Ord.Cmp.flip(c), Ord.Cmp.flip(d)),
      Ord.Cmp.flip(Merge.cmp_then(c, d)),
      Equal.cong(Cmp, Cmp, w => Merge.cmp_then(Ord.Cmp.flip(c), w), d2, Ord.Cmp.flip(d), ed),
      Laws.cmp_then_flip(c, d)))

def Laws.full_cmp_flip(A, B):
  match A B:
    case Merge.Card{+i1, +l1, +v1, +e1, +d1, +s1, +r1, +t1} Merge.Card{+i2, +l2, +v2, +e2, +d2, +s2, +r2, +t2}:
      Laws.cmp_then_swap(Merge.skey_cmp(i1, i2), Merge.skey_cmp(i2, i1), Merge.cmp_then(Merge.skey_cmp(l1, l2), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))))), Merge.cmp_then(Merge.skey_cmp(l2, l1), Merge.cmp_then(Nat.cmp(v2, v1), Merge.cmp_then(Nat.cmp(e2, e1), Merge.cmp_then(Nat.cmp(d2, d1), Merge.cmp_then(Nat.cmp(s2, s1), Merge.cmp_then(Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1)))))))), Laws.skey_cmp_flip(i1, i2), Laws.cmp_then_swap(Merge.skey_cmp(l1, l2), Merge.skey_cmp(l2, l1), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))), Merge.cmp_then(Nat.cmp(v2, v1), Merge.cmp_then(Nat.cmp(e2, e1), Merge.cmp_then(Nat.cmp(d2, d1), Merge.cmp_then(Nat.cmp(s2, s1), Merge.cmp_then(Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1))))))), Laws.skey_cmp_flip(l1, l2), Laws.cmp_then_swap(Nat.cmp(v1, v2), Nat.cmp(v2, v1), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))), Merge.cmp_then(Nat.cmp(e2, e1), Merge.cmp_then(Nat.cmp(d2, d1), Merge.cmp_then(Nat.cmp(s2, s1), Merge.cmp_then(Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1)))))), Ord.Nat.cmp_flip(v1, v2), Laws.cmp_then_swap(Nat.cmp(e1, e2), Nat.cmp(e2, e1), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))), Merge.cmp_then(Nat.cmp(d2, d1), Merge.cmp_then(Nat.cmp(s2, s1), Merge.cmp_then(Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1))))), Ord.Nat.cmp_flip(e1, e2), Laws.cmp_then_swap(Nat.cmp(d1, d2), Nat.cmp(d2, d1), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))), Merge.cmp_then(Nat.cmp(s2, s1), Merge.cmp_then(Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1)))), Ord.Nat.cmp_flip(d1, d2), Laws.cmp_then_swap(Nat.cmp(s1, s2), Nat.cmp(s2, s1), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))), Merge.cmp_then(Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1))), Ord.Nat.cmp_flip(s1, s2), Laws.cmp_then_swap(Nat.cmp(r1, r2), Nat.cmp(r2, r1), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)), Nat.cmp(Merge.last_key(t2), Merge.last_key(t1)), Ord.Nat.cmp_flip(r1, r2), Ord.Nat.cmp_flip(Merge.last_key(t1), Merge.last_key(t2)))))))))


def Laws.last_key_eq(t1, t2, h):
  match t1 t2:
    case None{} None{}:
      {==}
    case None{} Some{+x}:
      Empty.absurd({None{} == Some{x} : Maybe<&2, Nat>}, Ord.IsEQ.neq_lt(Nat.cmp(0n, Nat.add(x, 1n)), Ord.Nat.cmp_zero_add1(x), h))
    case Some{+x} None{}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, Nat>}, Ord.IsEQ.neq_gt(Nat.cmp(Nat.add(x, 1n), 0n), Ord.Nat.cmp_add1_zero(x), h))
    case Some{+x} Some{+y}:
      Equal.cong(Nat, Maybe<&2, Nat>, w => Some{w}, x, y,
        Ord.Nat.eq_of_cmp_eq(x, y,
          Ord.Cmp.trEQ(Nat.cmp(x, y), Nat.cmp(Nat.add(x, 1n), Nat.add(y, 1n)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(x, 1n), Nat.add(y, 1n)), Nat.cmp(x, y), Ord.Nat.add1_cmp(x, y)), h)))

def cmp_split(c: Cmp, d: Cmp, h: Ord.IsEQ(Merge.cmp_then(c, d))) -> (Ord.IsEQ(c) & Ord.IsEQ(d)):
  match c:
    case LT{}:
      Empty.absurd((Ord.IsEQ(LT{}) & Ord.IsEQ(d)), h)
    case EQ{}:
      (Unit{}, h)
    case GT{}:
      Empty.absurd((Ord.IsEQ(GT{}) & Ord.IsEQ(d)), h)

def G6(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Nat.cmp(r1, r2)) & Ord.IsEQ(Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))) -> {Merge.Card{i2, l2, v2, e2, d2, s2, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (wr, wt):
      Equal.trans(Merge.Card, Merge.Card{i2, l2, v2, e2, d2, s2, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(Nat, Merge.Card, w => Merge.Card{i2, l2, v2, e2, d2, s2, w, t1}, r1, r2, Ord.Nat.eq_of_cmp_eq(r1, r2, wr)), Equal.cong(Maybe<&2, Nat>, Merge.Card, w => Merge.Card{i2, l2, v2, e2, d2, s2, r2, w}, t1, t2, Laws.last_key_eq(t1, t2, wt)))

def F6(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))) -> {Merge.Card{i2, l2, v2, e2, d2, s2, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G6(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)), h))

def G5(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Nat.cmp(s1, s2)) & Ord.IsEQ(Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))) -> {Merge.Card{i2, l2, v2, e2, d2, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (ws, g):
      Equal.trans(Merge.Card, Merge.Card{i2, l2, v2, e2, d2, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(Nat, Merge.Card, w => Merge.Card{i2, l2, v2, e2, d2, w, r1, t1}, s1, s2, Ord.Nat.eq_of_cmp_eq(s1, s2, ws)), F6(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, g))

def F5(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))) -> {Merge.Card{i2, l2, v2, e2, d2, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G5(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))), h))

def G4(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Nat.cmp(d1, d2)) & Ord.IsEQ(Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))) -> {Merge.Card{i2, l2, v2, e2, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (wd, g):
      Equal.trans(Merge.Card, Merge.Card{i2, l2, v2, e2, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(Nat, Merge.Card, w => Merge.Card{i2, l2, v2, e2, w, s1, r1, t1}, d1, d2, Ord.Nat.eq_of_cmp_eq(d1, d2, wd)), F5(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, g))

def F4(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))) -> {Merge.Card{i2, l2, v2, e2, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G4(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))), h))

def G3(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Nat.cmp(e1, e2)) & Ord.IsEQ(Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))))) -> {Merge.Card{i2, l2, v2, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (we, g):
      Equal.trans(Merge.Card, Merge.Card{i2, l2, v2, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(Nat, Merge.Card, w => Merge.Card{i2, l2, v2, w, d1, s1, r1, t1}, e1, e2, Ord.Nat.eq_of_cmp_eq(e1, e2, we)), F4(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, g))

def F3(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))))) -> {Merge.Card{i2, l2, v2, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G3(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))), h))

def G2(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Nat.cmp(v1, v2)) & Ord.IsEQ(Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))))) -> {Merge.Card{i2, l2, v1, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (wv, g):
      Equal.trans(Merge.Card, Merge.Card{i2, l2, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(Nat, Merge.Card, w => Merge.Card{i2, l2, w, e1, d1, s1, r1, t1}, v1, v2, Ord.Nat.eq_of_cmp_eq(v1, v2, wv)), F3(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, g))

def F2(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))))) -> {Merge.Card{i2, l2, v1, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G2(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))), h))

def G1(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Merge.skey_cmp(l1, l2)) & Ord.IsEQ(Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))))))) -> {Merge.Card{i2, l1, v1, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (wl, g):
      Equal.trans(Merge.Card, Merge.Card{i2, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(String, Merge.Card, w => Merge.Card{i2, w, v1, e1, d1, s1, r1, t1}, l1, l2, Laws.skey_eq_of(l1, l2, wl)), F2(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, g))

def F1(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Merge.skey_cmp(l1, l2), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))))))) -> {Merge.Card{i2, l1, v1, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G1(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Merge.skey_cmp(l1, l2), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))), h))

def G0(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, p: (Ord.IsEQ(Merge.skey_cmp(i1, i2)) & Ord.IsEQ(Merge.cmp_then(Merge.skey_cmp(l1, l2), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))))))) -> {Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  match p:
    case (wi, g):
      Equal.trans(Merge.Card, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Equal.cong(String, Merge.Card, w => Merge.Card{w, l1, v1, e1, d1, s1, r1, t1}, i1, i2, Laws.skey_eq_of(i1, i2, wi)), F1(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, g))

def F0(+i1: String, +l1: String, +v1: Nat, +e1: Nat, +d1: Nat, +s1: Nat, +r1: Nat, +t1: Maybe<&2, Nat>, +i2: String, +l2: String, +v2: Nat, +e2: Nat, +d2: Nat, +s2: Nat, +r2: Nat, +t2: Maybe<&2, Nat>, h: Ord.IsEQ(Merge.cmp_then(Merge.skey_cmp(i1, i2), Merge.cmp_then(Merge.skey_cmp(l1, l2), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2))))))))))) -> {Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1} == Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2} : Merge.Card}:
  G0(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, cmp_split(Merge.skey_cmp(i1, i2), Merge.cmp_then(Merge.skey_cmp(l1, l2), Merge.cmp_then(Nat.cmp(v1, v2), Merge.cmp_then(Nat.cmp(e1, e2), Merge.cmp_then(Nat.cmp(d1, d2), Merge.cmp_then(Nat.cmp(s1, s2), Merge.cmp_then(Nat.cmp(r1, r2), Nat.cmp(Merge.last_key(t1), Merge.last_key(t2)))))))), h))

def Laws.full_eq_card(A, B, h):
  match A B:
    case Merge.Card{+i1, +l1, +v1, +e1, +d1, +s1, +r1, +t1} Merge.Card{+i2, +l2, +v2, +e2, +d2, +s2, +r2, +t2}:
      F0(i1, l1, v1, e1, d1, s1, r1, t1, i2, l2, v2, e2, d2, s2, r2, t2, h)


def Laws.card_pick_flip(x, r, d, f, A, B, tie):
  match x:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match r:
        case LT{}:
          {==}
        case GT{}:
          {==}
        case EQ{}:
          match d:
            case LT{}:
              {==}
            case GT{}:
              {==}
            case EQ{}:
              match f:
                case LT{}:
                  {==}
                case GT{}:
                  {==}
                case EQ{}:
                  Equal.sym(Merge.Card, A, B, tie(Unit{}))

def Laws.card_merge_comm(a, b):
  match a b:
    case Merge.Card{+i1, +l1, +v1, +e1, +d1, +s1, +r1, +t1} Merge.Card{+i2, +l2, +v2, +e2, +d2, +s2, +r2, +t2}:
      Equal.sym(Merge.Card, Merge.card_pick(Nat.cmp(Merge.last_or0(t2), Merge.last_or0(t1)), Nat.cmp(r2, r1), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2)), Nat.cmp(r1, r2), Nat.cmp(d1, d2), Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}), Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}), Equal.trans(Merge.Card, Merge.card_pick(Nat.cmp(Merge.last_or0(t2), Merge.last_or0(t1)), Nat.cmp(r2, r1), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Cmp.flip(Nat.cmp(d1, d2)), Ord.Cmp.flip(Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2})), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2)), Nat.cmp(r1, r2), Nat.cmp(d1, d2), Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}), Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}), Equal.trans(Merge.Card, Merge.card_pick(Nat.cmp(Merge.last_or0(t2), Merge.last_or0(t1)), Nat.cmp(r2, r1), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Nat.cmp(r2, r1), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Cmp.flip(Nat.cmp(d1, d2)), Ord.Cmp.flip(Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2})), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Equal.cong(Cmp, Merge.Card, w => Merge.card_pick(w, Nat.cmp(r2, r1), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Nat.cmp(Merge.last_or0(t2), Merge.last_or0(t1)), Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Nat.cmp_flip(Merge.last_or0(t1), Merge.last_or0(t2))), Equal.trans(Merge.Card, Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Nat.cmp(r2, r1), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Cmp.flip(Nat.cmp(d1, d2)), Ord.Cmp.flip(Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2})), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Equal.cong(Cmp, Merge.Card, w => Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), w, Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Nat.cmp(r2, r1), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Nat.cmp_flip(r1, r2)), Equal.trans(Merge.Card, Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Nat.cmp(d2, d1), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Cmp.flip(Nat.cmp(d1, d2)), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Cmp.flip(Nat.cmp(d1, d2)), Ord.Cmp.flip(Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2})), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Equal.cong(Cmp, Merge.Card, w => Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), w, Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Nat.cmp(d2, d1), Ord.Cmp.flip(Nat.cmp(d1, d2)), Ord.Nat.cmp_flip(d1, d2)), Equal.cong(Cmp, Merge.Card, w => Merge.card_pick(Ord.Cmp.flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2))), Ord.Cmp.flip(Nat.cmp(r1, r2)), Ord.Cmp.flip(Nat.cmp(d1, d2)), w, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Merge.full_cmp(Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}), Ord.Cmp.flip(Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2})), Laws.full_cmp_flip(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}))))), Laws.card_pick_flip(Nat.cmp(Merge.last_or0(t1), Merge.last_or0(t2)), Nat.cmp(r1, r2), Nat.cmp(d1, d2), Merge.full_cmp(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}), Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, h => Laws.full_eq_card(Merge.Card{i1, l1, v1, e1, d1, s1, r1, t1}, Merge.Card{i2, l2, v2, e2, d2, s2, r2, t2}, h))))

def Laws.skey_lt_trans(a, b, c, h1, h2):
  e_ab = Equal.sym(Cmp, Merge.skey_cmp(a, b), String.order(a, b), Key.Key.skey_eq_order(a, b))
  w_ab = Equal.trans(Cmp, String.order(a, b), Merge.skey_cmp(a, b), LT{}, e_ab, h1)
  e_bc = Equal.sym(Cmp, Merge.skey_cmp(b, c), String.order(b, c), Key.Key.skey_eq_order(b, c))
  w_bc = Equal.trans(Cmp, String.order(b, c), Merge.skey_cmp(b, c), LT{}, e_bc, h2)
  r = Ord.String.order.lt_trans(a, b, c, Ord.IsLT.to(String.order(a, b), w_ab), Ord.IsLT.to(String.order(b, c), w_bc))
  Equal.trans(Cmp, Merge.skey_cmp(a, c), String.order(a, c), LT{}, Key.Key.skey_eq_order(a, c), r)

# ---- the sorted-map laws, lessons: the layer's lemmas (no function hypotheses; keys are fixed) ----

# a witness that every key of s is after k also holds for any smaller key kx
def kall_trans_l(s: List<&2, Merge.LEntry>, +kx: String, +ky: String, +exy: {Merge.skey_cmp(kx, ky) == LT{} : Cmp}, w: S.KAllL(s, ky)) -> S.KAllL(s, kx):
  match s:
    case Nil{}:
      Unit{}
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (w1, w2) = w
          eyh = Ord.IsLT.of(Merge.skey_cmp(ky, kh), w1)
          exh = Laws.skey_lt_trans(kx, ky, kh, exy, eyh)
          (Ord.IsLT.to(Merge.skey_cmp(kx, kh), exh), kall_trans_l(t, kx, ky, exy, w2))

# every key of s is after k, so k is not in s
def lookup_none_l(s: List<&2, Merge.LEntry>, +k: String, w: S.KAllL(s, k)) -> {S.lookup_l(s, k) == None{} : Maybe<&2, Merge.Lesson>}:
  match s:
    case Nil{}:
      {==}
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (w1, w2) = w
          e1 = Ord.IsLT.of(Merge.skey_cmp(k, kh), w1)
          e2 = Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(k, kh), LT{}, e1)
          e3 = Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(k, kh)), Ord.Cmp.flip(LT{}), GT{}, e2, {==})
          e4 = Equal.trans(Cmp, Merge.skey_cmp(kh, k), Ord.Cmp.flip(Merge.skey_cmp(k, kh)), GT{}, Laws.skey_cmp_flip(k, kh), e3)
          e5 = Equal.cong(Cmp, Maybe<&2, Merge.Lesson>, (c => S.pick_l(c, vh, S.lookup_l(t, k))), Merge.skey_cmp(kh, k), GT{}, e4)
          e6 = lookup_none_l(t, k, w2)
          g1 = Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(h <> t, k), S.pick_l(Merge.skey_cmp(kh, k), vh, S.lookup_l(t, k)), S.lookup_l(t, k), {==}, e5)
          Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(h <> t, k), S.lookup_l(t, k), None{}, g1, e6)

# ---- key facts: an EQ key comparison lets one key stand for the other ----

def key_subst_l(+x: String, +y: String, +z: String, e: {Merge.skey_cmp(x, y) == EQ{} : Cmp}) -> {Merge.skey_cmp(x, z) == Merge.skey_cmp(y, z) : Cmp}:
  Equal.cong(String, Cmp, (s => Merge.skey_cmp(s, z)), x, y, Laws.skey_eq_of(x, y, Ord.IsEQ.to(Merge.skey_cmp(x, y), e)))

def key_subst_r(+x: String, +y: String, +z: String, e: {Merge.skey_cmp(x, y) == EQ{} : Cmp}) -> {Merge.skey_cmp(z, x) == Merge.skey_cmp(z, y) : Cmp}:
  Equal.cong(String, Cmp, (s => Merge.skey_cmp(z, s)), x, y, Laws.skey_eq_of(x, y, Ord.IsEQ.to(Merge.skey_cmp(x, y), e)))

def eq_flip(+x: String, +y: String, e: {Merge.skey_cmp(x, y) == EQ{} : Cmp}) -> {Merge.skey_cmp(y, x) == EQ{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(y, x), Ord.Cmp.flip(Merge.skey_cmp(x, y)), EQ{},
    Laws.skey_cmp_flip(x, y),
    Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(x, y)), Ord.Cmp.flip(EQ{}), EQ{},
      Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(x, y), EQ{}, e),
      {==}))

# if ke and k compare EQ, then kh compares with k as it compares with ke, flipped
def b_of_eq(+ke: String, +kh: String, +k: String, ea: {Merge.skey_cmp(ke, k) == EQ{} : Cmp}) -> {Merge.skey_cmp(kh, k) == Ord.Cmp.flip(Merge.skey_cmp(ke, kh)) : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(kh, k), Merge.skey_cmp(kh, ke), Ord.Cmp.flip(Merge.skey_cmp(ke, kh)),
    Equal.sym(Cmp, Merge.skey_cmp(kh, ke), Merge.skey_cmp(kh, k), key_subst_r(ke, k, kh, ea)),
    Laws.skey_cmp_flip(ke, kh))

# if ke and kh compare EQ, then kh compares with k as ke does
def b_eq_a(+ke: String, +kh: String, +k: String, hc: {Merge.skey_cmp(ke, kh) == EQ{} : Cmp}) -> {Merge.skey_cmp(kh, k) == Merge.skey_cmp(ke, k) : Cmp}:
  key_subst_l(kh, ke, k, eq_flip(ke, kh, hc))

def lt_b_gt(+ke: String, +kh: String, +k: String, ea: {Merge.skey_cmp(ke, k) == EQ{} : Cmp}, hc: {Merge.skey_cmp(ke, kh) == LT{} : Cmp}) -> {Merge.skey_cmp(kh, k) == GT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(kh, k), Ord.Cmp.flip(Merge.skey_cmp(ke, kh)), GT{}, b_of_eq(ke, kh, k, ea),
    Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(ke, kh)), Ord.Cmp.flip(LT{}), GT{},
      Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(ke, kh), LT{}, hc),
      {==}))

def gt_b_lt(+ke: String, +kh: String, +k: String, ea: {Merge.skey_cmp(ke, k) == EQ{} : Cmp}, hc: {Merge.skey_cmp(ke, kh) == GT{} : Cmp}) -> {Merge.skey_cmp(kh, k) == LT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(kh, k), Ord.Cmp.flip(Merge.skey_cmp(ke, kh)), LT{}, b_of_eq(ke, kh, k, ea),
    Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(ke, kh)), Ord.Cmp.flip(GT{}), LT{},
      Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(ke, kh), GT{}, hc),
      {==}))

# every key of s is after x when it is after y and x compares EQ with y
def kall_eq(s: List<&2, Merge.LEntry>, +x: String, +y: String, +e: {Merge.skey_cmp(x, y) == EQ{} : Cmp}, w: S.KAllL(s, y)) -> S.KAllL(s, x):
  match s:
    case Nil{}:
      Unit{}
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (w1, w2) = w
          (Ord.Cmp.trLT(Merge.skey_cmp(x, kh), Merge.skey_cmp(y, kh), key_subst_l(x, y, kh, e), w1), kall_eq(t, x, y, e, w2))

# ---- lins_c keeps every key after x (the new key ke must be after x too) ----

def kall_lins_c(t: List<&2, Merge.LEntry>, c: Cmp, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +x: String, wh: Ord.IsLT(Merge.skey_cmp(x, kh)), wt: S.KAllL(t, x), hk: Ord.IsLT(Merge.skey_cmp(x, ke))) -> S.KAllL(Merge.lins_c(t, c, Merge.LEntry{ke, ve}, Merge.LEntry{kh, vh}), x):
  match t:
    case Nil{}:
      match c:
        case LT{}:
          (hk, (wh, Unit{}))
        case EQ{}:
          (wh, Unit{})
        case GT{}:
          (wh, (hk, Unit{}))
    case h2 <> t2:
      match h2:
        case Merge.LEntry{+k2, +v2}:
          match c:
            case LT{}:
              (hk, (wh, wt))
            case EQ{}:
              (wh, wt)
            case GT{}:
              (wk2, wt2) = wt
              (wh, kall_lins_c(t2, Merge.skey_cmp(ke, k2), ke, ve, k2, v2, x, wk2, wt2, hk))

# ---- a KAllL witness can be copied: each IsLT witness becomes an equation, which can be shared ----

# the copy of a witness for the list whose head is LEntry{kh, vh}: the head's IsLT is shared through e
def kall_dup_cons(+k: String, +kh: String, +vh: Merge.Lesson, t: List<&2, Merge.LEntry>, +e: {Merge.skey_cmp(k, kh) == LT{} : Cmp}, p: (S.KAllL(t, k) & S.KAllL(t, k))) -> (S.KAllL(Merge.LEntry{kh, vh} <> t, k) & S.KAllL(Merge.LEntry{kh, vh} <> t, k)):
  (ta, tb) = p
  ((Ord.IsLT.to(Merge.skey_cmp(k, kh), e), ta), (Ord.IsLT.to(Merge.skey_cmp(k, kh), e), tb))

def kall_dup(s: List<&2, Merge.LEntry>, +k: String, w: S.KAllL(s, k)) -> (S.KAllL(s, k) & S.KAllL(s, k)):
  match s:
    case Nil{}:
      (Unit{}, Unit{})
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (wi, wt) = w
          e = Ord.IsLT.of(Merge.skey_cmp(k, kh), wi)
          kall_dup_cons(k, kh, vh, t, e, kall_dup(t, k, wt))

# an EQ-free reversal: if x compares GT with y, then y compares LT with x
def rev_gt(+x: String, +y: String, e: {Merge.skey_cmp(x, y) == GT{} : Cmp}) -> {Merge.skey_cmp(y, x) == LT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(y, x), Ord.Cmp.flip(Merge.skey_cmp(x, y)), LT{},
    Laws.skey_cmp_flip(x, y),
    Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(x, y)), Ord.Cmp.flip(GT{}), LT{},
      Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(x, y), GT{}, e),
      {==}))

# the LT case of sorted_lins_c: the new entry ke goes before the head kh; p holds two copies of KAllL(t, kh)
def sorted_lt_cons(t: List<&2, Merge.LEntry>, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +ec: {Merge.skey_cmp(ke, kh) == LT{} : Cmp}, p: (S.KAllL(t, kh) & S.KAllL(t, kh)), ws: S.SortedL(t)) -> S.SortedL(Merge.LEntry{ke, ve} <> (Merge.LEntry{kh, vh} <> t)):
  (wa, wb) = p
  ((Ord.IsLT.to(Merge.skey_cmp(ke, kh), ec), kall_trans_l(t, ke, kh, ec, wa)), (wb, ws))

# ---- lins_c keeps the list sorted, when the new key ke compares c with the head key kh ----

def sorted_lins_c(t: List<&2, Merge.LEntry>, c: Cmp, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +ec: {Merge.skey_cmp(ke, kh) == c : Cmp}, w: S.KAllL(t, kh), ws: S.SortedL(t)) -> S.SortedL(Merge.lins_c(t, c, Merge.LEntry{ke, ve}, Merge.LEntry{kh, vh})):
  match t:
    case Nil{}:
      match c:
        case LT{}:
          ((Ord.IsLT.to(Merge.skey_cmp(ke, kh), ec), Unit{}), (Unit{}, Unit{}))
        case EQ{}:
          (Unit{}, Unit{})
        case GT{}:
          ((Ord.IsLT.to(Merge.skey_cmp(kh, ke), rev_gt(ke, kh, ec)), Unit{}), (Unit{}, Unit{}))
    case +h2 <> +t2:
      match h2:
        case Merge.LEntry{+k2, +v2}:
          match c:
            case LT{}:
              sorted_lt_cons(h2 <> t2, ke, ve, kh, vh, ec, kall_dup(h2 <> t2, kh, w), ws)
            case EQ{}:
              (w, ws)
            case GT{}:
              (wkh2, wkh_t2) = w
              (w2, ws2) = ws
              (kall_lins_c(t2, Merge.skey_cmp(ke, k2), ke, ve, k2, v2, kh, wkh2, wkh_t2, Ord.IsLT.to(Merge.skey_cmp(kh, ke), rev_gt(ke, kh, ec))),
               sorted_lins_c(t2, Merge.skey_cmp(ke, k2), ke, ve, k2, v2, {==}, w2, ws2))

# ---- lins keeps a sorted list sorted ----

def sorted_lins(+ke: String, +ve: Merge.Lesson, s: List<&2, Merge.LEntry>, ws: S.SortedL(s)) -> S.SortedL(Merge.lins(Merge.LEntry{ke, ve}, s)):
  match s:
    case Nil{}:
      (Unit{}, Unit{})
    case h <> t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (w, ws2) = ws
          sorted_lins_c(t, Merge.skey_cmp(ke, kh), ke, ve, kh, vh, {==}, w, ws2)

# ---- the lookup of an insertion, lessons: the lemmas by how the new key ke compares with the head kh ----
# c2 is the comparison of ke with k, c3 that of kh with k; the witnesses tie them to the keys.

# pick_l with its comparison replaced by an equal one
def pk_l(x: Cmp, y: Cmp, +v: Merge.Lesson, +r: Maybe<&2, Merge.Lesson>, e: {x == y : Cmp}) -> {S.pick_l(x, v, r) == S.pick_l(y, v, r) : Maybe<&2, Merge.Lesson>}:
  Equal.cong(Cmp, Maybe<&2, Merge.Lesson>, (z => S.pick_l(z, v, r)), x, y, e)

# a new entry into an empty rest: its lookup is its insertion
def sing_l(c2: Cmp, +ve: Merge.Lesson) -> {S.pick_l(c2, ve, None{}) == S.ins_look_l(c2, None{}, ve) : Maybe<&2, Merge.Lesson>}:
  match c2:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# ke before kh: the lookup is the rest, except at ke itself, where the rest has no key k
def lk_lt(+c2: Cmp, +c3: Cmp, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +k: String, +t: List<&2, Merge.LEntry>, w: S.KAllL(t, kh), +ea: {Merge.skey_cmp(ke, k) == c2 : Cmp}, +hb: {Merge.skey_cmp(kh, k) == c3 : Cmp}, +hc: {Merge.skey_cmp(ke, kh) == LT{} : Cmp}) -> {S.pick_l(c2, ve, S.pick_l(c3, vh, S.lookup_l(t, k))) == S.ins_look_l(c2, S.pick_l(c3, vh, S.lookup_l(t, k)), ve) : Maybe<&2, Merge.Lesson>}:
  match c2:
    case LT{}:
      {==}
    case EQ{}:
      e1 = Equal.trans(Cmp, Merge.skey_cmp(k, kh), Merge.skey_cmp(ke, kh), LT{}, key_subst_l(k, ke, kh, eq_flip(ke, k, ea)), hc)
      n1 = lookup_none_l(t, k, kall_trans_l(t, k, kh, e1, w))
      r3 = Equal.trans(Cmp, c3, Merge.skey_cmp(kh, k), GT{}, Equal.sym(Cmp, Merge.skey_cmp(kh, k), c3, hb), lt_b_gt(ke, kh, k, ea, hc))
      rX = Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(c3, vh, S.lookup_l(t, k)), S.pick_l(GT{}, vh, S.lookup_l(t, k)), None{}, pk_l(c3, GT{}, vh, S.lookup_l(t, k), r3), Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(GT{}, vh, S.lookup_l(t, k)), S.lookup_l(t, k), None{}, {==}, n1))
      Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(EQ{}, ve, S.pick_l(c3, vh, S.lookup_l(t, k))), S.comb_opt_l(None{}, Some{ve}), S.comb_opt_l(S.pick_l(c3, vh, S.lookup_l(t, k)), Some{ve}), {==}, Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, (z => S.comb_opt_l(z, Some{ve})), None{}, S.pick_l(c3, vh, S.lookup_l(t, k)), Equal.sym(Maybe<&2, Merge.Lesson>, S.pick_l(c3, vh, S.lookup_l(t, k)), None{}, rX)))
    case GT{}:
      {==}

# ke equal to kh: the entry is combined, and the rest is not consulted, so the lookup is the combined entry
def lk_eq(+c2: Cmp, +c3: Cmp, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +k: String, +t: List<&2, Merge.LEntry>, +rel: {c3 == c2 : Cmp}) -> {S.pick_l(c3, Merge.lp_max(vh, ve), S.lookup_l(t, k)) == S.ins_look_l(c2, S.pick_l(c3, vh, S.lookup_l(t, k)), ve) : Maybe<&2, Merge.Lesson>}:
  match c2:
    case LT{}:
      Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(c3, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(LT{}, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(c3, vh, S.lookup_l(t, k)), pk_l(c3, LT{}, Merge.lp_max(vh, ve), S.lookup_l(t, k), rel), Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(LT{}, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(LT{}, vh, S.lookup_l(t, k)), S.pick_l(c3, vh, S.lookup_l(t, k)), {==}, Equal.sym(Maybe<&2, Merge.Lesson>, S.pick_l(c3, vh, S.lookup_l(t, k)), S.pick_l(LT{}, vh, S.lookup_l(t, k)), pk_l(c3, LT{}, vh, S.lookup_l(t, k), rel))))
    case EQ{}:
      Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(c3, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(EQ{}, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.comb_opt_l(S.pick_l(c3, vh, S.lookup_l(t, k)), Some{ve}), pk_l(c3, EQ{}, Merge.lp_max(vh, ve), S.lookup_l(t, k), rel), Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(EQ{}, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.comb_opt_l(S.pick_l(EQ{}, vh, S.lookup_l(t, k)), Some{ve}), S.comb_opt_l(S.pick_l(c3, vh, S.lookup_l(t, k)), Some{ve}), {==}, Equal.sym(Maybe<&2, Merge.Lesson>, S.comb_opt_l(S.pick_l(c3, vh, S.lookup_l(t, k)), Some{ve}), S.comb_opt_l(S.pick_l(EQ{}, vh, S.lookup_l(t, k)), Some{ve}), Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, (z => S.comb_opt_l(z, Some{ve})), S.pick_l(c3, vh, S.lookup_l(t, k)), S.pick_l(EQ{}, vh, S.lookup_l(t, k)), pk_l(c3, EQ{}, vh, S.lookup_l(t, k), rel)))))
    case GT{}:
      Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(c3, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(GT{}, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(c3, vh, S.lookup_l(t, k)), pk_l(c3, GT{}, Merge.lp_max(vh, ve), S.lookup_l(t, k), rel), Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(GT{}, Merge.lp_max(vh, ve), S.lookup_l(t, k)), S.pick_l(GT{}, vh, S.lookup_l(t, k)), S.pick_l(c3, vh, S.lookup_l(t, k)), {==}, Equal.sym(Maybe<&2, Merge.Lesson>, S.pick_l(c3, vh, S.lookup_l(t, k)), S.pick_l(GT{}, vh, S.lookup_l(t, k)), pk_l(c3, GT{}, vh, S.lookup_l(t, k), rel))))

# kh before ke: the rest gets the insertion, and kh's comparison with k decides which entry shows
def lk_gt(+c2: Cmp, +c3: Cmp, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +k: String, +s: List<&2, Merge.LEntry>, +ea: {Merge.skey_cmp(ke, k) == c2 : Cmp}, +hb: {Merge.skey_cmp(kh, k) == c3 : Cmp}, +hc: {Merge.skey_cmp(ke, kh) == GT{} : Cmp}) -> {S.pick_l(c3, vh, S.ins_look_l(c2, S.lookup_l(s, k), ve)) == S.ins_look_l(c2, S.pick_l(c3, vh, S.lookup_l(s, k)), ve) : Maybe<&2, Merge.Lesson>}:
  match c3:
    case LT{}:
      {==}
    case EQ{}:
      rel2 = Equal.trans(Cmp, c2, Merge.skey_cmp(ke, k), GT{}, Equal.sym(Cmp, Merge.skey_cmp(ke, k), c2, ea), Equal.trans(Cmp, Merge.skey_cmp(ke, k), Merge.skey_cmp(ke, kh), GT{}, Equal.sym(Cmp, Merge.skey_cmp(ke, kh), Merge.skey_cmp(ke, k), key_subst_r(kh, k, ke, hb)), hc))
      rg = Equal.cong(Cmp, Maybe<&2, Merge.Lesson>, (z => S.ins_look_l(z, Some{vh}, ve)), c2, GT{}, rel2)
      Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(EQ{}, vh, S.ins_look_l(c2, S.lookup_l(s, k), ve)), S.ins_look_l(c2, Some{vh}, ve), S.ins_look_l(c2, S.pick_l(EQ{}, vh, S.lookup_l(s, k)), ve), Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(EQ{}, vh, S.ins_look_l(c2, S.lookup_l(s, k), ve)), S.ins_look_l(GT{}, Some{vh}, ve), S.ins_look_l(c2, Some{vh}, ve), {==}, Equal.sym(Maybe<&2, Merge.Lesson>, S.ins_look_l(c2, Some{vh}, ve), S.ins_look_l(GT{}, Some{vh}, ve), rg)), {==})
    case GT{}:
      {==}

# ---- the lookup of lins_c: inserting ke into the list kh <> t, where c compares ke with kh ----

# ke at any position: the lookup after the insertion is the insertion of ke into the lookup of the list
def lins_c_look(t: List<&2, Merge.LEntry>, c: Cmp, +ke: String, +ve: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +k: String, ec: {Merge.skey_cmp(ke, kh) == c : Cmp}, w: S.KAllL(t, kh), ws: S.SortedL(t)) -> {S.lookup_l(Merge.lins_c(t, c, Merge.LEntry{ke, ve}, Merge.LEntry{kh, vh}), k) == S.ins_look_l(Merge.skey_cmp(ke, k), S.pick_l(Merge.skey_cmp(kh, k), vh, S.lookup_l(t, k)), ve) : Maybe<&2, Merge.Lesson>}:
  match t:
    case Nil{}:
      match c:
        case LT{}:
          lk_lt(Merge.skey_cmp(ke, k), Merge.skey_cmp(kh, k), ke, ve, kh, vh, k, Nil{}, w, {==}, {==}, ec)
        case EQ{}:
          lk_eq(Merge.skey_cmp(ke, k), Merge.skey_cmp(kh, k), ke, ve, kh, vh, k, Nil{}, b_eq_a(ke, kh, k, ec))
        case GT{}:
          Equal.trans(Maybe<&2, Merge.Lesson>,
            S.pick_l(Merge.skey_cmp(kh, k), vh, S.pick_l(Merge.skey_cmp(ke, k), ve, None{})),
            S.pick_l(Merge.skey_cmp(kh, k), vh, S.ins_look_l(Merge.skey_cmp(ke, k), None{}, ve)),
            S.ins_look_l(Merge.skey_cmp(ke, k), S.pick_l(Merge.skey_cmp(kh, k), vh, None{}), ve),
            Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, (z => S.pick_l(Merge.skey_cmp(kh, k), vh, z)), S.pick_l(Merge.skey_cmp(ke, k), ve, None{}), S.ins_look_l(Merge.skey_cmp(ke, k), None{}, ve), sing_l(Merge.skey_cmp(ke, k), ve)),
            lk_gt(Merge.skey_cmp(ke, k), Merge.skey_cmp(kh, k), ke, ve, kh, vh, k, Nil{}, {==}, {==}, ec))
    case +h2 <> +t2:
      match h2:
        case Merge.LEntry{+k2, +v2}:
          match c:
            case LT{}:
              lk_lt(Merge.skey_cmp(ke, k), Merge.skey_cmp(kh, k), ke, ve, kh, vh, k, h2 <> t2, w, {==}, {==}, ec)
            case EQ{}:
              lk_eq(Merge.skey_cmp(ke, k), Merge.skey_cmp(kh, k), ke, ve, kh, vh, k, h2 <> t2, b_eq_a(ke, kh, k, ec))
            case GT{}:
              (w2, ws2) = ws
              Equal.trans(Maybe<&2, Merge.Lesson>,
                S.pick_l(Merge.skey_cmp(kh, k), vh, S.lookup_l(Merge.lins_c(t2, Merge.skey_cmp(ke, k2), Merge.LEntry{ke, ve}, Merge.LEntry{k2, v2}), k)),
                S.pick_l(Merge.skey_cmp(kh, k), vh, S.ins_look_l(Merge.skey_cmp(ke, k), S.lookup_l(h2 <> t2, k), ve)),
                S.ins_look_l(Merge.skey_cmp(ke, k), S.pick_l(Merge.skey_cmp(kh, k), vh, S.lookup_l(h2 <> t2, k)), ve),
                Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, (z => S.pick_l(Merge.skey_cmp(kh, k), vh, z)), S.lookup_l(Merge.lins_c(t2, Merge.skey_cmp(ke, k2), Merge.LEntry{ke, ve}, Merge.LEntry{k2, v2}), k), S.ins_look_l(Merge.skey_cmp(ke, k), S.lookup_l(h2 <> t2, k), ve), lins_c_look(t2, Merge.skey_cmp(ke, k2), ke, ve, k2, v2, k, {==}, w2, ws2)),
                lk_gt(Merge.skey_cmp(ke, k), Merge.skey_cmp(kh, k), ke, ve, kh, vh, k, h2 <> t2, {==}, {==}, ec))

# the lookup of a sorted-list insertion: lins puts ke into its place, and the lookup sees the insertion
def lins_look(+ke: String, +ve: Merge.Lesson, +k: String, s: List<&2, Merge.LEntry>, ws: S.SortedL(s)) -> {S.lookup_l(Merge.lins(Merge.LEntry{ke, ve}, s), k) == S.ins_look_l(Merge.skey_cmp(ke, k), S.lookup_l(s, k), ve) : Maybe<&2, Merge.Lesson>}:
  match s:
    case Nil{}:
      sing_l(Merge.skey_cmp(ke, k), ve)
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (w, ws2) = ws
          lins_c_look(t, Merge.skey_cmp(ke, kh), ke, ve, kh, vh, k, {==}, w, ws2)

# ---- the lessons merge: the Maybe values, the lookups of the lists, the fold, and the pointwise laws ----

# None is not Some: a disequality between two Maybe values
def is_none_t(m: Maybe<&2, Merge.Lesson>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+x}:
      Empty

def none_ne_some(+v: Merge.Lesson, p: {None{} == Some{v} : Maybe<&2, Merge.Lesson>}) -> Empty:
  %p : is_none_t(_)
  Unit{}

# combining with None on the right keeps the value
def comb_none_r(+x: Maybe<&2, Merge.Lesson>) -> {S.comb_opt_l(x, None{}) == x : Maybe<&2, Merge.Lesson>}:
  match x:
    case Some{+v}:
      {==}
    case None{}:
      {==}

# combining with None on the left keeps the value
def comb_none_l(+x: Maybe<&2, Merge.Lesson>) -> {S.comb_opt_l(None{}, x) == x : Maybe<&2, Merge.Lesson>}:
  match x:
    case Some{+v}:
      {==}
    case None{}:
      {==}

# the combination of two values is commutative, as lp_max is
def comb_comm(+m: Maybe<&2, Merge.Lesson>, +n: Maybe<&2, Merge.Lesson>) -> {S.comb_opt_l(m, n) == S.comb_opt_l(n, m) : Maybe<&2, Merge.Lesson>}:
  match m n:
    case Some{+v} Some{+w}:
      Equal.cong(Merge.Lesson, Maybe<&2, Merge.Lesson>, x => Some{x}, Merge.lp_max(v, w), Merge.lp_max(w, v), Laws.lp_max_comm(v, w))
    case Some{+v} None{}:
      {==}
    case None{} Some{+w}:
      {==}
    case None{} None{}:
      {==}

# the combination of a value with itself is that value
def comb_idem(+m: Maybe<&2, Merge.Lesson>) -> {S.comb_opt_l(m, m) == m : Maybe<&2, Merge.Lesson>}:
  match m:
    case Some{+v}:
      Equal.cong(Merge.Lesson, Maybe<&2, Merge.Lesson>, x => Some{x}, Merge.lp_max(v, v), v, Laws.lp_max_self(v))
    case None{}:
      {==}

# the lookup at a key that compares EQ with the head key: the head's value
def lk_head(+kb: String, +vb: Merge.Lesson, +t: List<&2, Merge.LEntry>, +k: String, e: {Merge.skey_cmp(kb, k) == EQ{} : Cmp}) -> {S.lookup_l(Merge.LEntry{kb, vb} <> t, k) == Some{vb} : Maybe<&2, Merge.Lesson>}:
  Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.LEntry{kb, vb} <> t, k), S.pick_l(Merge.skey_cmp(kb, k), vb, S.lookup_l(t, k)), Some{vb}, {==},
    Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(Merge.skey_cmp(kb, k), vb, S.lookup_l(t, k)), S.pick_l(EQ{}, vb, S.lookup_l(t, k)), Some{vb},
      pk_l(Merge.skey_cmp(kb, k), EQ{}, vb, S.lookup_l(t, k), e), {==}))

# the lookup at a key before the head key: the head is skipped
def lk_skip(+kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +k: String, wk: Ord.IsLT(Merge.skey_cmp(kh, k))) -> {S.lookup_l(Merge.LEntry{kh, vh} <> t, k) == S.lookup_l(t, k) : Maybe<&2, Merge.Lesson>}:
  Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.LEntry{kh, vh} <> t, k), S.pick_l(Merge.skey_cmp(kh, k), vh, S.lookup_l(t, k)), S.lookup_l(t, k), {==},
    Equal.trans(Maybe<&2, Merge.Lesson>, S.pick_l(Merge.skey_cmp(kh, k), vh, S.lookup_l(t, k)), S.pick_l(LT{}, vh, S.lookup_l(t, k)), S.lookup_l(t, k),
      pk_l(Merge.skey_cmp(kh, k), LT{}, vh, S.lookup_l(t, k), Ord.IsLT.of(Merge.skey_cmp(kh, k), wk)), {==}))

# one step of the fold's lookup: the head key kh is folded into acc; c compares kh with k
def lf_step(c: Cmp, +kh: String, +vh: Merge.Lesson, +k: String, +t: List<&2, Merge.LEntry>, +mv: Maybe<&2, Merge.Lesson>, +pv: Maybe<&2, Merge.Lesson>, +fv: Maybe<&2, Merge.Lesson>, +ec: {Merge.skey_cmp(kh, k) == c : Cmp}, wt: S.KAllL(t, kh), l2: {pv == S.ins_look_l(c, mv, vh) : Maybe<&2, Merge.Lesson>}, ih: {fv == S.comb_opt_l(pv, S.lookup_l(t, k)) : Maybe<&2, Merge.Lesson>}) -> {fv == S.comb_opt_l(mv, S.pick_l(c, vh, S.lookup_l(t, k))) : Maybe<&2, Merge.Lesson>}:
  match c:
    case LT{}:
      p1 = Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, z => S.comb_opt_l(z, S.lookup_l(t, k)), pv, mv, Equal.trans(Maybe<&2, Merge.Lesson>, pv, S.ins_look_l(LT{}, mv, vh), mv, l2, {==}))
      Equal.trans(Maybe<&2, Merge.Lesson>, fv, S.comb_opt_l(pv, S.lookup_l(t, k)), S.comb_opt_l(mv, S.pick_l(LT{}, vh, S.lookup_l(t, k))), ih, p1)
    case EQ{}:
      hn = lookup_none_l(t, k, kall_eq(t, k, kh, eq_flip(kh, k, ec), wt))
      p1 = Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, z => S.comb_opt_l(pv, z), S.lookup_l(t, k), None{}, hn)
      p2 = Equal.trans(Maybe<&2, Merge.Lesson>, S.comb_opt_l(pv, S.lookup_l(t, k)), S.comb_opt_l(pv, None{}), pv, p1, comb_none_r(pv))
      p3 = Equal.trans(Maybe<&2, Merge.Lesson>, fv, S.comb_opt_l(pv, S.lookup_l(t, k)), pv, ih, p2)
      Equal.trans(Maybe<&2, Merge.Lesson>, fv, pv, S.comb_opt_l(mv, S.pick_l(EQ{}, vh, S.lookup_l(t, k))), p3, l2)
    case GT{}:
      p1 = Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, z => S.comb_opt_l(z, S.lookup_l(t, k)), pv, mv, Equal.trans(Maybe<&2, Merge.Lesson>, pv, S.ins_look_l(GT{}, mv, vh), mv, l2, {==}))
      Equal.trans(Maybe<&2, Merge.Lesson>, fv, S.comb_opt_l(pv, S.lookup_l(t, k)), S.comb_opt_l(mv, S.pick_l(GT{}, vh, S.lookup_l(t, k))), ih, p1)

# a sorted list folded into a sorted list stays sorted
def sorted_lfold(+xs: List<&2, Merge.LEntry>, +acc: List<&2, Merge.LEntry>, wacc: S.SortedL(acc)) -> S.SortedL(Merge.lfold(xs, acc)):
  match xs:
    case Nil{}:
      wacc
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          sorted_lfold(t, Merge.lins(Merge.LEntry{kh, vh}, acc), sorted_lins(kh, vh, acc, wacc))

# the two copies of a SortedL witness for a cons, from the copies of its parts
def sd_cons(+kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, dk: (S.KAllL(t, kh) & S.KAllL(t, kh)), dt: (S.SortedL(t) & S.SortedL(t))) -> (S.SortedL(Merge.LEntry{kh, vh} <> t) & S.SortedL(Merge.LEntry{kh, vh} <> t)):
  (wk1, wk2) = dk
  (wt1, wt2) = dt
  ((wk1, wt1), (wk2, wt2))

# a witness of SortedL can be copied, as a witness of KAllL can
def sortedL_dup(s: List<&2, Merge.LEntry>, w: S.SortedL(s)) -> (S.SortedL(s) & S.SortedL(s)):
  match s:
    case Nil{}:
      (Unit{}, Unit{})
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (wk, wt) = w
          sd_cons(kh, vh, t, kall_dup(t, kh, wk), sortedL_dup(t, wt))

# the lookup of a fold: folding a sorted list into a sorted list looks up as the combination of the two.
# The witnesses of acc come in pairs, so each recursive call is given a fresh pair (no matching on a computed value).
def lfold_look(+xs: List<&2, Merge.LEntry>, +acc: List<&2, Merge.LEntry>, +k: String, sx: S.SortedL(xs), pa: (S.SortedL(acc) & S.SortedL(acc))) -> {S.lookup_l(Merge.lfold(xs, acc), k) == S.comb_opt_l(S.lookup_l(acc, k), S.lookup_l(xs, k)) : Maybe<&2, Merge.Lesson>}:
  match xs:
    case Nil{}:
      Equal.sym(Maybe<&2, Merge.Lesson>, S.comb_opt_l(S.lookup_l(acc, k), None{}), S.lookup_l(acc, k), comb_none_r(S.lookup_l(acc, k)))
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (wkt, wt) = sx
          (sa1, sa2) = pa
          lf_step(Merge.skey_cmp(kh, k), kh, vh, k, t, S.lookup_l(acc, k), S.lookup_l(Merge.lins(Merge.LEntry{kh, vh}, acc), k), S.lookup_l(Merge.lfold(t, Merge.lins(Merge.LEntry{kh, vh}, acc)), k), {==}, wkt, lins_look(kh, vh, k, acc, sa1), lfold_look(t, Merge.lins(Merge.LEntry{kh, vh}, acc), k, wt, sortedL_dup(Merge.lins(Merge.LEntry{kh, vh}, acc), sorted_lins(kh, vh, acc, sa2))))

# the pointwise lemma for the merge, with the copies of the witnesses given
def pt_comm_h(+a: List<&2, Merge.LEntry>, +b: List<&2, Merge.LEntry>, +k: String, pa: (S.SortedL(a) & S.SortedL(a)), pb: (S.SortedL(b) & S.SortedL(b))) -> {S.lookup_l(Merge.lfold(b, Merge.lfold(a, Nil{})), k) == S.lookup_l(Merge.lfold(a, Merge.lfold(b, Nil{})), k) : Maybe<&2, Merge.Lesson>}:
  (sa1, sa2) = pa
  (sb1, sb2) = pb
  lfa = Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(a, Nil{}), k), S.comb_opt_l(S.lookup_l(Nil{}, k), S.lookup_l(a, k)), S.lookup_l(a, k), lfold_look(a, Nil{}, k, sa1, (Unit{}, Unit{})), comb_none_l(S.lookup_l(a, k)))
  lfb = Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(b, Nil{}), k), S.comb_opt_l(S.lookup_l(Nil{}, k), S.lookup_l(b, k)), S.lookup_l(b, k), lfold_look(b, Nil{}, k, sb1, (Unit{}, Unit{})), comb_none_l(S.lookup_l(b, k)))
  lab = Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(b, Merge.lfold(a, Nil{})), k), S.comb_opt_l(S.lookup_l(Merge.lfold(a, Nil{}), k), S.lookup_l(b, k)), S.comb_opt_l(S.lookup_l(a, k), S.lookup_l(b, k)), lfold_look(b, Merge.lfold(a, Nil{}), k, sb2, sortedL_dup(Merge.lfold(a, Nil{}), sorted_lfold(a, Nil{}, Unit{}))), Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, z => S.comb_opt_l(z, S.lookup_l(b, k)), S.lookup_l(Merge.lfold(a, Nil{}), k), S.lookup_l(a, k), lfa))
  lba = Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(a, Merge.lfold(b, Nil{})), k), S.comb_opt_l(S.lookup_l(Merge.lfold(b, Nil{}), k), S.lookup_l(a, k)), S.comb_opt_l(S.lookup_l(b, k), S.lookup_l(a, k)), lfold_look(a, Merge.lfold(b, Nil{}), k, sa2, sortedL_dup(Merge.lfold(b, Nil{}), sorted_lfold(b, Nil{}, Unit{}))), Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, z => S.comb_opt_l(z, S.lookup_l(a, k)), S.lookup_l(Merge.lfold(b, Nil{}), k), S.lookup_l(b, k), lfb))
  Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(b, Merge.lfold(a, Nil{})), k), S.comb_opt_l(S.lookup_l(a, k), S.lookup_l(b, k)), S.lookup_l(Merge.lfold(a, Merge.lfold(b, Nil{})), k), lab, Equal.trans(Maybe<&2, Merge.Lesson>, S.comb_opt_l(S.lookup_l(a, k), S.lookup_l(b, k)), S.comb_opt_l(S.lookup_l(b, k), S.lookup_l(a, k)), S.lookup_l(Merge.lfold(a, Merge.lfold(b, Nil{})), k), comb_comm(S.lookup_l(a, k), S.lookup_l(b, k)), Equal.sym(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(a, Merge.lfold(b, Nil{})), k), S.comb_opt_l(S.lookup_l(b, k), S.lookup_l(a, k)), lba)))

# the pointwise lemma for the merge, from the witnesses of a and b
def pt_comm(+a: List<&2, Merge.LEntry>, +b: List<&2, Merge.LEntry>, +k: String, sa: S.SortedL(a), sb: S.SortedL(b)) -> {S.lookup_l(Merge.lfold(b, Merge.lfold(a, Nil{})), k) == S.lookup_l(Merge.lfold(a, Merge.lfold(b, Nil{})), k) : Maybe<&2, Merge.Lesson>}:
  pt_comm_h(a, b, k, sortedL_dup(a, sa), sortedL_dup(b, sb))

# the pointwise lemma for the self-merge, with the copies of the witness given
def pt_idem_h(+a: List<&2, Merge.LEntry>, +k: String, pa: (S.SortedL(a) & S.SortedL(a))) -> {S.lookup_l(Merge.lfold(a, Merge.lfold(a, Nil{})), k) == S.lookup_l(a, k) : Maybe<&2, Merge.Lesson>}:
  (sa1, sa2) = pa
  lfa = Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(a, Nil{}), k), S.comb_opt_l(S.lookup_l(Nil{}, k), S.lookup_l(a, k)), S.lookup_l(a, k), lfold_look(a, Nil{}, k, sa1, (Unit{}, Unit{})), comb_none_l(S.lookup_l(a, k)))
  lap = Equal.trans(Maybe<&2, Merge.Lesson>, S.comb_opt_l(S.lookup_l(Merge.lfold(a, Nil{}), k), S.lookup_l(a, k)), S.comb_opt_l(S.lookup_l(a, k), S.lookup_l(a, k)), S.lookup_l(a, k), Equal.cong(Maybe<&2, Merge.Lesson>, Maybe<&2, Merge.Lesson>, z => S.comb_opt_l(z, S.lookup_l(a, k)), S.lookup_l(Merge.lfold(a, Nil{}), k), S.lookup_l(a, k), lfa), comb_idem(S.lookup_l(a, k)))
  Equal.trans(Maybe<&2, Merge.Lesson>, S.lookup_l(Merge.lfold(a, Merge.lfold(a, Nil{})), k), S.comb_opt_l(S.lookup_l(Merge.lfold(a, Nil{}), k), S.lookup_l(a, k)), S.lookup_l(a, k), lfold_look(a, Merge.lfold(a, Nil{}), k, sa2, sortedL_dup(Merge.lfold(a, Nil{}), sorted_lfold(a, Nil{}, Unit{}))), lap)

# the pointwise lemma for the self-merge, from the witness of a
def pt_idem(+a: List<&2, Merge.LEntry>, +k: String, sa: S.SortedL(a)) -> {S.lookup_l(Merge.lfold(a, Merge.lfold(a, Nil{})), k) == S.lookup_l(a, k) : Maybe<&2, Merge.Lesson>}:
  pt_idem_h(a, k, sortedL_dup(a, sa))

# ---- lins: the walk lemmas. The new entry (ka, va) against the head (kh, vh) and the rest X ----

# lins_c with LT: the new entry goes in front of the head
def lc_lt(+X: List<&2, Merge.LEntry>, +ka: String, +va: Merge.Lesson, +kh: String, +vh: Merge.Lesson) -> {Merge.lins_c(X, LT{}, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}) == Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> X) : List<&2, Merge.LEntry>}:
  match X:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      match h2:
        case Merge.LEntry{+k2, +v2}:
          {==}

# lins_c with EQ: the new entry merges into the head, which keeps its key
def lc_eq(+X: List<&2, Merge.LEntry>, +ka: String, +va: Merge.Lesson, +kh: String, +vh: Merge.Lesson) -> {Merge.lins_c(X, EQ{}, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}) == Merge.LEntry{kh, Merge.lp_max(vh, va)} <> X : List<&2, Merge.LEntry>}:
  match X:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      match h2:
        case Merge.LEntry{+k2, +v2}:
          {==}

# lins_c with GT: the head stays in front, and the new entry goes into the rest
def lc_gt(+X: List<&2, Merge.LEntry>, +ka: String, +va: Merge.Lesson, +kh: String, +vh: Merge.Lesson) -> {Merge.lins_c(X, GT{}, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}) == Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, X) : List<&2, Merge.LEntry>}:
  match X:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      match h2:
        case Merge.LEntry{+k2, +v2}:
          {==}

# insertion of (ka, va) before the head (kh, vh) <> X, when the new key is LT the head's key
def ins_lt(+X: List<&2, Merge.LEntry>, +ka: String, +va: Merge.Lesson, +kh: String, +vh: Merge.Lesson, ec: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> X) == Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> X) : List<&2, Merge.LEntry>}:
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins_c(X, Merge.skey_cmp(ka, kh), Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}), Merge.lins_c(X, LT{}, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> X), Equal.cong(Cmp, List<&2, Merge.LEntry>, (z => Merge.lins_c(X, z, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh})), Merge.skey_cmp(ka, kh), LT{}, ec), lc_lt(X, ka, va, kh, vh))

# insertion of (ka, va) into (kh, vh) <> X, when the keys are EQ: the head is combined
def ins_eq(+X: List<&2, Merge.LEntry>, +ka: String, +va: Merge.Lesson, +kh: String, +vh: Merge.Lesson, ec: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> X) == Merge.LEntry{kh, Merge.lp_max(vh, va)} <> X : List<&2, Merge.LEntry>}:
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins_c(X, Merge.skey_cmp(ka, kh), Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}), Merge.lins_c(X, EQ{}, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> X, Equal.cong(Cmp, List<&2, Merge.LEntry>, (z => Merge.lins_c(X, z, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh})), Merge.skey_cmp(ka, kh), EQ{}, ec), lc_eq(X, ka, va, kh, vh))

# insertion of (ka, va) into (kh, vh) <> X, when the new key is GT the head's key: the head stays in front
def ins_gt(+X: List<&2, Merge.LEntry>, +ka: String, +va: Merge.Lesson, +kh: String, +vh: Merge.Lesson, ec: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> X) == Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, X) : List<&2, Merge.LEntry>}:
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins_c(X, Merge.skey_cmp(ka, kh), Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}), Merge.lins_c(X, GT{}, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh}), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, X), Equal.cong(Cmp, List<&2, Merge.LEntry>, (z => Merge.lins_c(X, z, Merge.LEntry{ka, va}, Merge.LEntry{kh, vh})), Merge.skey_cmp(ka, kh), GT{}, ec), lc_gt(X, ka, va, kh, vh))

# ---- L2: inserting two lessons in either order gives the same list, for every list s ----

# the reverse of an LT comparison is a GT comparison
def rev_lt(+x: String, +y: String, e: {Merge.skey_cmp(x, y) == LT{} : Cmp}) -> {Merge.skey_cmp(y, x) == GT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(y, x), Ord.Cmp.flip(Merge.skey_cmp(x, y)), GT{},
    Laws.skey_cmp_flip(x, y),
    Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(x, y)), Ord.Cmp.flip(LT{}), GT{},
      Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(x, y), LT{}, e),
      {==}))

# key witnesses for the mixed branches: kb after ka, from ka before kh and kb after kh
def w_gl(+ka: String, +kh: String, +kb: String, eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}, eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}) -> {Merge.skey_cmp(kb, ka) == GT{} : Cmp}:
  rev_lt(ka, kb, Laws.skey_lt_trans(ka, kh, kb, eA, rev_gt(kb, kh, eB)))

# ka after kb, from ka after kh and kb before kh
def w_lg(+ka: String, +kh: String, +kb: String, eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}, eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}) -> {Merge.skey_cmp(ka, kb) == GT{} : Cmp}:
  rev_lt(kb, ka, Laws.skey_lt_trans(kb, kh, ka, eB, rev_gt(ka, kh, eA)))

# kb after ka, from ka before kh and kb equal to kh
def w_el(+ka: String, +kh: String, +kb: String, eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}, eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}) -> {Merge.skey_cmp(kb, ka) == GT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(kb, ka), Merge.skey_cmp(kh, ka), GT{}, key_subst_l(kb, kh, ka, eB), rev_lt(ka, kh, eA))

# ka after kb, from ka equal to kh and kb before kh
def w_le(+ka: String, +kh: String, +kb: String, eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}, eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}) -> {Merge.skey_cmp(ka, kb) == GT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(ka, kb), Merge.skey_cmp(kh, kb), GT{}, key_subst_l(ka, kh, kb, eA), rev_lt(kb, kh, eB))

# lp_max is associative and commutative in the order that matters here
def lpac(+x: Merge.Lesson, +y: Merge.Lesson, +z: Merge.Lesson) -> {Merge.lp_max(Merge.lp_max(x, y), z) == Merge.lp_max(Merge.lp_max(x, z), y) : Merge.Lesson}:
  Equal.trans(Merge.Lesson, Merge.lp_max(Merge.lp_max(x, y), z), Merge.lp_max(x, Merge.lp_max(y, z)), Merge.lp_max(Merge.lp_max(x, z), y),
    Equal.sym(Merge.Lesson, Merge.lp_max(x, Merge.lp_max(y, z)), Merge.lp_max(Merge.lp_max(x, y), z), Laws.lp_max_assoc(x, y, z)),
    Equal.trans(Merge.Lesson, Merge.lp_max(x, Merge.lp_max(y, z)), Merge.lp_max(x, Merge.lp_max(z, y)), Merge.lp_max(Merge.lp_max(x, z), y),
      Equal.cong(Merge.Lesson, Merge.Lesson, (w => Merge.lp_max(x, w)), Merge.lp_max(y, z), Merge.lp_max(z, y), Laws.lp_max_comm(y, z)),
      Laws.lp_max_assoc(x, z, y)))

# two entries with EQ keys, in either order, give the same entry before the rest X
def lp_eq_swap(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, e: {Merge.skey_cmp(ka, kb) == EQ{} : Cmp}, +X: List<&2, Merge.LEntry>) -> {Merge.LEntry{kb, Merge.lp_max(vb, va)} <> X == Merge.LEntry{ka, Merge.lp_max(va, vb)} <> X : List<&2, Merge.LEntry>}:
  kq = Equal.sym(String, ka, kb, Laws.skey_eq_of(ka, kb, Ord.IsEQ.to(Merge.skey_cmp(ka, kb), e)))
  s1 = Equal.cong(String, Merge.LEntry, (k => Merge.LEntry{k, Merge.lp_max(vb, va)}), kb, ka, kq)
  s2 = Equal.cong(Merge.Lesson, Merge.LEntry, (v => Merge.LEntry{ka, v}), Merge.lp_max(vb, va), Merge.lp_max(va, vb), Laws.lp_max_comm(vb, va))
  s3 = Equal.trans(Merge.LEntry, Merge.LEntry{kb, Merge.lp_max(vb, va)}, Merge.LEntry{ka, Merge.lp_max(vb, va)}, Merge.LEntry{ka, Merge.lp_max(va, vb)}, s1, s2)
  Equal.cong(Merge.LEntry, List<&2, Merge.LEntry>, (p => p <> X), Merge.LEntry{kb, Merge.lp_max(vb, va)}, Merge.LEntry{ka, Merge.lp_max(va, vb)}, s3)

# congruence for the two places a list appears in lins
def cong_lins(+ka: String, +va: Merge.Lesson, +x: List<&2, Merge.LEntry>, +y: List<&2, Merge.LEntry>, e: {x == y : List<&2, Merge.LEntry>}) -> {Merge.lins(Merge.LEntry{ka, va}, x) == Merge.lins(Merge.LEntry{ka, va}, y) : List<&2, Merge.LEntry>}:
  Equal.cong(List<&2, Merge.LEntry>, List<&2, Merge.LEntry>, (z => Merge.lins(Merge.LEntry{ka, va}, z)), x, y, e)

def cong_cons(+kh: String, +vh: Merge.Lesson, +x: List<&2, Merge.LEntry>, +y: List<&2, Merge.LEntry>, e: {x == y : List<&2, Merge.LEntry>}) -> {Merge.LEntry{kh, vh} <> x == Merge.LEntry{kh, vh} <> y : List<&2, Merge.LEntry>}:
  Equal.cong(List<&2, Merge.LEntry>, List<&2, Merge.LEntry>, (z => Merge.LEntry{kh, vh} <> z), x, y, e)

# ---- the empty list: [A, B] against [B, A] ----

def lins2_nil_c(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +c: Cmp, +ec: {Merge.skey_cmp(ka, kb) == c : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Nil{})) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})) : List<&2, Merge.LEntry>}:
  match c:
    case LT{}:
      s1 = ins_lt(Nil{}, ka, va, kb, vb, ec)
      r1 = ins_gt(Nil{}, kb, vb, ka, va, rev_lt(ka, kb, ec))
      Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Nil{})), Merge.LEntry{ka, va} <> (Merge.LEntry{kb, vb} <> Nil{}), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})), s1, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Nil{}), r1))
    case EQ{}:
      s1 = ins_eq(Nil{}, ka, va, kb, vb, ec)
      r1 = ins_eq(Nil{}, kb, vb, ka, va, eq_flip(ka, kb, ec))
      Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Nil{})), Merge.LEntry{kb, Merge.lp_max(vb, va)} <> Nil{}, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})),
        s1,
        Equal.trans(List<&2, Merge.LEntry>, Merge.LEntry{kb, Merge.lp_max(vb, va)} <> Nil{}, Merge.LEntry{ka, Merge.lp_max(va, vb)} <> Nil{}, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})),
          lp_eq_swap(ka, va, kb, vb, ec, Nil{}),
          Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})), Merge.LEntry{ka, Merge.lp_max(va, vb)} <> Nil{}, r1)))
    case GT{}:
      s1 = ins_gt(Nil{}, ka, va, kb, vb, ec)
      r1 = ins_lt(Nil{}, kb, vb, ka, va, rev_gt(ka, kb, ec))
      Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Nil{})), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> Nil{}), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})),
        Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Nil{})), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Nil{}), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> Nil{}), s1, Equal.cong(List<&2, Merge.LEntry>, List<&2, Merge.LEntry>, (z => Merge.LEntry{kb, vb} <> z), Merge.lins(Merge.LEntry{ka, va}, Nil{}), Merge.LEntry{ka, va} <> Nil{}, {==})),
        Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Nil{})), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> Nil{}), r1))

# ---- the cons case: the branch lemmas, one per pair of comparisons of ka and kb with the head kh ----

# GT, GT: both new entries go past the head, so the head stays in front and the induction hypothesis applies to the rest
def l2_GG(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}, ih: {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, t)) : List<&2, Merge.LEntry>}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_gt(t, kb, vb, kh, vh, eB)
  s2 = ins_gt(Merge.lins(Merge.LEntry{kb, vb}, t), ka, va, kh, vh, eA)
  r1 = ins_gt(t, ka, va, kh, vh, eA)
  r2 = ins_gt(Merge.lins(Merge.LEntry{ka, va}, t), kb, vb, kh, vh, eB)
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, t)), cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t), s1), s2)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, t)), cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t), r1), r2)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L1,
    Equal.trans(List<&2, Merge.LEntry>, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)),
      cong_cons(kh, vh, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, t)), ih),
      Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, t)), R1)))

# GT, EQ: the new a merges into the head, which the new b has just passed
def l2_GE(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_gt(t, kb, vb, kh, vh, eB)
  s2 = ins_eq(Merge.lins(Merge.LEntry{kb, vb}, t), ka, va, kh, vh, eA)
  r1 = ins_eq(t, ka, va, kh, vh, eA)
  r2 = ins_gt(t, kb, vb, kh, Merge.lp_max(vh, va), eB)
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> Merge.lins(Merge.LEntry{kb, vb}, t), cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t), s1), s2)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> Merge.lins(Merge.LEntry{kb, vb}, t), cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t, r1), r2)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> Merge.lins(Merge.LEntry{kb, vb}, t), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> Merge.lins(Merge.LEntry{kb, vb}, t), R1))

# ---- the cons case, continued: the remaining branches ----

# EQ, GT: the new b merges into the head; the new a is past the head
def l2_EG(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_eq(t, kb, vb, kh, vh, eB)
  s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t, s1)
  s3 = ins_gt(t, ka, va, kh, Merge.lp_max(vh, vb), eA)
  r1 = ins_gt(t, ka, va, kh, vh, eA)
  r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t), r1)
  r3 = ins_eq(Merge.lins(Merge.LEntry{ka, va}, t), kb, vb, kh, vh, eB)
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> Merge.lins(Merge.LEntry{ka, va}, t), s2, s3)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> Merge.lins(Merge.LEntry{ka, va}, t), r2, r3)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> Merge.lins(Merge.LEntry{ka, va}, t), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> Merge.lins(Merge.LEntry{ka, va}, t), R1))

# EQ, EQ: both new entries merge into the head; the two combined values agree by lpac
def l2_EE(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_eq(t, kb, vb, kh, vh, eB)
  s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t, s1)
  s3 = ins_eq(t, ka, va, kh, Merge.lp_max(vh, vb), eA)
  m = Equal.cong(Merge.Lesson, List<&2, Merge.LEntry>, (v => Merge.LEntry{kh, v} <> t), Merge.lp_max(Merge.lp_max(vh, vb), va), Merge.lp_max(Merge.lp_max(vh, va), vb), lpac(vh, vb, va))
  r1 = ins_eq(t, ka, va, kh, vh, eA)
  r3 = ins_eq(t, kb, vb, kh, Merge.lp_max(vh, va), eB)
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), Merge.LEntry{kh, Merge.lp_max(Merge.lp_max(vh, vb), va)} <> t, s2, s3)
  L2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(Merge.lp_max(vh, vb), va)} <> t, Merge.LEntry{kh, Merge.lp_max(Merge.lp_max(vh, va), vb)} <> t, L1, m)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), Merge.LEntry{kh, Merge.lp_max(Merge.lp_max(vh, va), vb)} <> t, Equal.cong(List<&2, Merge.LEntry>, List<&2, Merge.LEntry>, (z => Merge.lins(Merge.LEntry{kb, vb}, z)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t, r1), r3)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(Merge.lp_max(vh, va), vb)} <> t, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kh, Merge.lp_max(Merge.lp_max(vh, va), vb)} <> t, R1))

# EQ, LT: the new a is before the head; the new b merges into the head
def l2_EL(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_eq(t, kb, vb, kh, vh, eB)
  s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t, s1)
  s3 = ins_lt(t, ka, va, kh, Merge.lp_max(vh, vb), eA)
  r1 = ins_lt(t, ka, va, kh, vh, eA)
  r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t), r1)
  r3 = ins_gt(Merge.LEntry{kh, vh} <> t, kb, vb, ka, va, w_el(ka, kh, kb, eA, eB))
  r4 = cong_cons(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t, ins_eq(t, kb, vb, kh, vh, eB))
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), s2, s3)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), r2, r3)
  R2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), R1, r4)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, Merge.lp_max(vh, vb)} <> t), R2))

# ---- the cons case, continued: the GT-LT, GT-EQ... branches for the new b past the head and the new a before it ----

# GT, LT: the new a is before the head, so it goes to the front; the new b is past the head and stays behind it
def l2_GL(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_gt(t, kb, vb, kh, vh, eB)
  s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t), s1)
  s3 = ins_lt(Merge.lins(Merge.LEntry{kb, vb}, t), ka, va, kh, vh, eA)
  r1 = ins_lt(t, ka, va, kh, vh, eA)
  r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t), r1)
  r3 = ins_gt(Merge.LEntry{kh, vh} <> t, kb, vb, ka, va, w_gl(ka, kh, kb, eA, eB))
  r4 = cong_cons(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t), ins_gt(t, kb, vb, kh, vh, eB))
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t)), s2, s3)
  L2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), L1, Equal.sym(List<&2, Merge.LEntry>, Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kb, vb}, t)), r4))
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), r2, r3)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), R1))

# LT, GT: the new b is before the head, so it goes to the front; the new a is past the head and stays behind it
def l2_LG(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_lt(t, kb, vb, kh, vh, eB)
  s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t), s1)
  s3 = ins_gt(Merge.LEntry{kh, vh} <> t, ka, va, kb, vb, w_lg(ka, kh, kb, eA, eB))
  s4 = cong_cons(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t), ins_gt(t, ka, va, kh, vh, eA))
  r1 = ins_gt(t, ka, va, kh, vh, eA)
  r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t), r1)
  r3 = ins_lt(Merge.lins(Merge.LEntry{ka, va}, t), kb, vb, kh, vh, eB)
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), s2, s3)
  L2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), L1, s4)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), r2, r3)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{ka, va}, t)), R1))

# LT, EQ: the new b is before the head; the new a merges into the head
def l2_LE(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  s1 = ins_lt(t, kb, vb, kh, vh, eB)
  s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t), s1)
  s3 = ins_gt(Merge.LEntry{kh, vh} <> t, ka, va, kb, vb, w_le(ka, kh, kb, eA, eB))
  s4 = cong_cons(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t, ins_eq(t, ka, va, kh, vh, eA))
  r1 = ins_eq(t, ka, va, kh, vh, eA)
  r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t, r1)
  r3 = ins_lt(t, kb, vb, kh, Merge.lp_max(vh, va), eB)
  L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), s2, s3)
  L2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), L1, s4)
  R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), r2, r3)
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, Merge.lp_max(vh, va)} <> t), R1))

# LT, LT: both new entries are before the head; the order of ka and kb decides the front, and the EQ case joins by lp_eq_swap
def l2_LL(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}, +c3: Cmp, +ec3: {Merge.skey_cmp(ka, kb) == c3 : Cmp}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  match c3:
    case LT{}:
      s1 = ins_lt(t, kb, vb, kh, vh, eB)
      s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t), s1)
      s3 = ins_lt(Merge.LEntry{kh, vh} <> t, ka, va, kb, vb, ec3)
      r1 = ins_lt(t, ka, va, kh, vh, eA)
      r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t), r1)
      r3 = ins_gt(Merge.LEntry{kh, vh} <> t, kb, vb, ka, va, rev_lt(ka, kb, ec3))
      r4 = cong_cons(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t), ins_lt(t, kb, vb, kh, vh, eB))
      L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), s2, s3)
      R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), r2, r3)
      R2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), R1, r4)
      Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, va} <> (Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), R2))
    case EQ{}:
      s1 = ins_lt(t, kb, vb, kh, vh, eB)
      s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t), s1)
      s3 = ins_eq(Merge.LEntry{kh, vh} <> t, ka, va, kb, vb, ec3)
      r1 = ins_lt(t, ka, va, kh, vh, eA)
      r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t), r1)
      r3 = ins_eq(Merge.LEntry{kh, vh} <> t, kb, vb, ka, va, eq_flip(ka, kb, ec3))
      L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, Merge.lp_max(vb, va)} <> (Merge.LEntry{kh, vh} <> t), s2, s3)
      R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, Merge.lp_max(va, vb)} <> (Merge.LEntry{kh, vh} <> t), r2, r3)
      Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, Merge.lp_max(va, vb)} <> (Merge.LEntry{kh, vh} <> t), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, Merge.lp_max(vb, va)} <> (Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, Merge.lp_max(va, vb)} <> (Merge.LEntry{kh, vh} <> t), L1, lp_eq_swap(ka, va, kb, vb, ec3, Merge.LEntry{kh, vh} <> t)), Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{ka, Merge.lp_max(va, vb)} <> (Merge.LEntry{kh, vh} <> t), R1))
    case GT{}:
      s1 = ins_lt(t, kb, vb, kh, vh, eB)
      s2 = cong_lins(ka, va, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t), s1)
      s3 = ins_gt(Merge.LEntry{kh, vh} <> t, ka, va, kb, vb, ec3)
      s4 = cong_cons(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t), ins_lt(t, ka, va, kh, vh, eA))
      r1 = ins_lt(t, ka, va, kh, vh, eA)
      r2 = cong_lins(kb, vb, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t), r1)
      r3 = ins_lt(Merge.LEntry{kh, vh} <> t, kb, vb, ka, va, rev_gt(ka, kb, ec3))
      L1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kb, vb} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), s2, s3)
      L2 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), L1, s4)
      R1 = Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), r2, r3)
      Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)), Merge.LEntry{kb, vb} <> (Merge.LEntry{ka, va} <> (Merge.LEntry{kh, vh} <> t)), R1))

# ---- the cons case dispatch: cb = skey(kb, kh) and ca = skey(ka, kh) choose the branch lemma ----

def lins2_cons(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +cb: Cmp, +ca: Cmp, +eB: {Merge.skey_cmp(kb, kh) == cb : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == ca : Cmp}, +ih: {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, t)) : List<&2, Merge.LEntry>}) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, Merge.LEntry{kh, vh} <> t)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, Merge.LEntry{kh, vh} <> t)) : List<&2, Merge.LEntry>}:
  match cb:
    case LT{}:
      match ca:
        case LT{}:
          l2_LL(ka, va, kb, vb, kh, vh, t, eB, eA, Merge.skey_cmp(ka, kb), {==})
        case EQ{}:
          l2_LE(ka, va, kb, vb, kh, vh, t, eB, eA)
        case GT{}:
          l2_LG(ka, va, kb, vb, kh, vh, t, eB, eA)
    case EQ{}:
      match ca:
        case LT{}:
          l2_EL(ka, va, kb, vb, kh, vh, t, eB, eA)
        case EQ{}:
          l2_EE(ka, va, kb, vb, kh, vh, t, eB, eA)
        case GT{}:
          l2_EG(ka, va, kb, vb, kh, vh, t, eB, eA)
    case GT{}:
      match ca:
        case LT{}:
          l2_GL(ka, va, kb, vb, kh, vh, t, eB, eA)
        case EQ{}:
          l2_GE(ka, va, kb, vb, kh, vh, t, eB, eA)
        case GT{}:
          l2_GG(ka, va, kb, vb, kh, vh, t, eB, eA, ih)

# ---- two lesson insertions commute on any list (no sortedness needed) ----

def lins2(+ka: String, +va: Merge.Lesson, +kb: String, +vb: Merge.Lesson, +s: List<&2, Merge.LEntry>) -> {Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kb, vb}, s)) == Merge.lins(Merge.LEntry{kb, vb}, Merge.lins(Merge.LEntry{ka, va}, s)) : List<&2, Merge.LEntry>}:
  match s:
    case Nil{}:
      lins2_nil_c(ka, va, kb, vb, Merge.skey_cmp(ka, kb), {==})
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          lins2_cons(ka, va, kb, vb, kh, vh, t, Merge.skey_cmp(kb, kh), Merge.skey_cmp(ka, kh), {==}, {==}, lins2(ka, va, kb, vb, t))

# ---- the fold: a fold over b, with the same accumulator changed, is congruent ----

def cong_lfold(+b: List<&2, Merge.LEntry>, +x: List<&2, Merge.LEntry>, +y: List<&2, Merge.LEntry>, e: {x == y : List<&2, Merge.LEntry>}) -> {Merge.lfold(b, x) == Merge.lfold(b, y) : List<&2, Merge.LEntry>}:
  Equal.cong(List<&2, Merge.LEntry>, List<&2, Merge.LEntry>, (z => Merge.lfold(b, z)), x, y, e)

# inserting A into the accumulator before folding b equals inserting it after: the fold passes it along
def lf_lins(+ka: String, +va: Merge.Lesson, +b: List<&2, Merge.LEntry>, +acc: List<&2, Merge.LEntry>) -> {Merge.lfold(b, Merge.lins(Merge.LEntry{ka, va}, acc)) == Merge.lins(Merge.LEntry{ka, va}, Merge.lfold(b, acc)) : List<&2, Merge.LEntry>}:
  match b:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          Equal.trans(List<&2, Merge.LEntry>, Merge.lfold(Merge.LEntry{kh, vh} <> t, Merge.lins(Merge.LEntry{ka, va}, acc)), Merge.lfold(t, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kh, vh}, acc))), Merge.lins(Merge.LEntry{ka, va}, Merge.lfold(Merge.LEntry{kh, vh} <> t, acc)),
            cong_lfold(t, Merge.lins(Merge.LEntry{kh, vh}, Merge.lins(Merge.LEntry{ka, va}, acc)), Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kh, vh}, acc)), Equal.sym(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{ka, va}, Merge.lins(Merge.LEntry{kh, vh}, acc)), Merge.lins(Merge.LEntry{kh, vh}, Merge.lins(Merge.LEntry{ka, va}, acc)), lins2(ka, va, kh, vh, acc))),
            lf_lins(ka, va, t, Merge.lins(Merge.LEntry{kh, vh}, acc)))

# the fold of b over a's entries and the fold of a over b's entries agree: the insertions of one list commute past the other
def lf_comm(+a: List<&2, Merge.LEntry>, +b: List<&2, Merge.LEntry>, +acc: List<&2, Merge.LEntry>) -> {Merge.lfold(b, Merge.lfold(a, acc)) == Merge.lfold(a, Merge.lfold(b, acc)) : List<&2, Merge.LEntry>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          Equal.trans(List<&2, Merge.LEntry>, Merge.lfold(b, Merge.lfold(Merge.LEntry{kh, vh} <> t, acc)), Merge.lfold(t, Merge.lfold(b, Merge.lins(Merge.LEntry{kh, vh}, acc))), Merge.lfold(Merge.LEntry{kh, vh} <> t, Merge.lfold(b, acc)),
            lf_comm(t, b, Merge.lins(Merge.LEntry{kh, vh}, acc)),
            cong_lfold(t, Merge.lfold(b, Merge.lins(Merge.LEntry{kh, vh}, acc)), Merge.lins(Merge.LEntry{kh, vh}, Merge.lfold(b, acc)), lf_lins(kh, vh, b, acc)))

# LAW: lessons_comm: the lesson merge is commutative on any two lists (see LAWS.bend)
def Laws.lessons_comm(a, b):
  lf_comm(a, b, Nil{})

# ---- lessons: idempotence (a sorted map folded into itself gives the map back) ----

# a string compared with itself is EQ
def skey_self(+k: String) -> {Merge.skey_cmp(k, k) == EQ{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(k, k), String.order(k, k), EQ{}, Key.Key.skey_eq_order(k, k), Key.Key.order_self(k))

# inserting an entry whose key is already at the front, with its own value, changes nothing
def lins_self(+kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>) -> {Merge.lins(Merge.LEntry{kh, vh}, Merge.LEntry{kh, vh} <> t) == Merge.LEntry{kh, vh} <> t : List<&2, Merge.LEntry>}:
  Equal.trans(List<&2, Merge.LEntry>, Merge.lins(Merge.LEntry{kh, vh}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, Merge.lp_max(vh, vh)} <> t, Merge.LEntry{kh, vh} <> t,
    ins_eq(t, kh, vh, kh, vh, skey_self(kh)),
    Equal.cong(Merge.Lesson, List<&2, Merge.LEntry>, (u => Merge.LEntry{kh, u} <> t), Merge.lp_max(vh, vh), vh, Laws.lp_max_self(vh)))

# the key order flipped: if kh < kt then kt > kh
def islt_skey_gt(+kh: String, +kt: String, w: Ord.IsLT(Merge.skey_cmp(kh, kt))) -> {Merge.skey_cmp(kt, kh) == GT{} : Cmp}:
  Equal.trans(Cmp, Merge.skey_cmp(kt, kh), Ord.Cmp.flip(Merge.skey_cmp(kh, kt)), GT{}, Laws.skey_cmp_flip(kh, kt),
    Equal.trans(Cmp, Ord.Cmp.flip(Merge.skey_cmp(kh, kt)), Ord.Cmp.flip(LT{}), GT{}, Equal.cong(Cmp, Cmp, Ord.Cmp.flip, Merge.skey_cmp(kh, kt), LT{}, Ord.IsLT.of(Merge.skey_cmp(kh, kt), w)), {==}))

# folding t into an accumulator whose front key is below every key of t: the front entry stays in front
def lf_gt(+kh: String, +vh: Merge.Lesson, +t: List<&2, Merge.LEntry>, +s: List<&2, Merge.LEntry>, w: S.KAllL(t, kh)) -> {Merge.lfold(t, Merge.LEntry{kh, vh} <> s) == Merge.LEntry{kh, vh} <> Merge.lfold(t, s) : List<&2, Merge.LEntry>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +t2:
      match h:
        case Merge.LEntry{+kt, +vt}:
          (wi, wt) = w
          Equal.trans(List<&2, Merge.LEntry>,
            Merge.lfold(t2, Merge.lins(Merge.LEntry{kt, vt}, Merge.LEntry{kh, vh} <> s)),
            Merge.lfold(t2, Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kt, vt}, s)),
            Merge.LEntry{kh, vh} <> Merge.lfold(t2, Merge.lins(Merge.LEntry{kt, vt}, s)),
            cong_lfold(t2, Merge.lins(Merge.LEntry{kt, vt}, Merge.LEntry{kh, vh} <> s), Merge.LEntry{kh, vh} <> Merge.lins(Merge.LEntry{kt, vt}, s), ins_gt(s, kt, vt, kh, vh, islt_skey_gt(kh, kt, wi))),
            lf_gt(kh, vh, t2, Merge.lins(Merge.LEntry{kt, vt}, s), wt))

# a sorted map folded into itself stays itself
def lf_self(+s: List<&2, Merge.LEntry>, ws: S.SortedL(s)) -> {Merge.lfold(s, s) == s : List<&2, Merge.LEntry>}:
  match s:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (wk, wt) = ws
          Equal.trans(List<&2, Merge.LEntry>, Merge.lfold(Merge.LEntry{kh, vh} <> t, Merge.LEntry{kh, vh} <> t), Merge.lfold(t, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> t,
            cong_lfold(t, Merge.lins(Merge.LEntry{kh, vh}, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> t, lins_self(kh, vh, t)),
            Equal.trans(List<&2, Merge.LEntry>, Merge.lfold(t, Merge.LEntry{kh, vh} <> t), Merge.LEntry{kh, vh} <> Merge.lfold(t, t), Merge.LEntry{kh, vh} <> t,
              lf_gt(kh, vh, t, t, wk),
              cong_cons(kh, vh, Merge.lfold(t, t), t, lf_self(t, wt))))

# a sorted map folded into the empty list gives the map back
def lf_nil(+s: List<&2, Merge.LEntry>, ws: S.SortedL(s)) -> {Merge.lfold(s, Nil{}) == s : List<&2, Merge.LEntry>}:
  match s:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.LEntry{+kh, +vh}:
          (wk, wt) = ws
          Equal.trans(List<&2, Merge.LEntry>, Merge.lfold(Merge.LEntry{kh, vh} <> t, Nil{}), Merge.LEntry{kh, vh} <> Merge.lfold(t, Nil{}), Merge.LEntry{kh, vh} <> t,
            lf_gt(kh, vh, t, Nil{}, wk),
            cong_cons(kh, vh, Merge.lfold(t, Nil{}), t, lf_nil(t, wt)))

# a sorted lesson map merged with itself is itself: the fold over a of (a folded into the empty list) gives a.
# The two copies of the witness arrive as a parameter, since a match cannot scrutinize a computed pair.
def idem_pair(+a: List<&2, Merge.LEntry>, dd: (S.SortedL(a) & S.SortedL(a))) -> {Merge.merge_lessons(a, a) == a : List<&2, Merge.LEntry>}:
  (s1, s2) = dd
  Equal.trans(List<&2, Merge.LEntry>, Merge.lfold(a, Merge.lfold(a, Nil{})), Merge.lfold(a, a), a,
    cong_lfold(a, Merge.lfold(a, Nil{}), a, lf_nil(a, s1)),
    lf_self(a, s2))

def idem_lessons(+a: List<&2, Merge.LEntry>, sa: S.SortedL(a)) -> {Merge.merge_lessons(a, a) == a : List<&2, Merge.LEntry>}:
  idem_pair(a, sortedL_dup(a, sa))

# LAW: lessons_idem: merging a sorted lesson map with itself gives the map back (see LAWS.bend)
def Laws.lessons_idem(a, sa):
  idem_lessons(a, sa)
# ---- XP per day: the lessons chains over XEntry, with Nat.max as the combining operation ----
# the copy of a witness for the list whose head is XEntry{kh, vh}: the head's IsLT is shared through e
def kallx_dup_cons(+k: String, +kh: String, +vh: Nat, t: List<&2, Merge.XEntry>, +e: {Merge.skey_cmp(k, kh) == LT{} : Cmp}, p: (S.KAllX(t, k) & S.KAllX(t, k))) -> (S.KAllX(Merge.XEntry{kh, vh} <> t, k) & S.KAllX(Merge.XEntry{kh, vh} <> t, k)):
  (ta, tb) = p
  ((Ord.IsLT.to(Merge.skey_cmp(k, kh), e), ta), (Ord.IsLT.to(Merge.skey_cmp(k, kh), e), tb))

def kallx_dup(s: List<&2, Merge.XEntry>, +k: String, w: S.KAllX(s, k)) -> (S.KAllX(s, k) & S.KAllX(s, k)):
  match s:
    case Nil{}:
      (Unit{}, Unit{})
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          (wi, wt) = w
          e = Ord.IsLT.of(Merge.skey_cmp(k, kh), wi)
          kallx_dup_cons(k, kh, vh, t, e, kallx_dup(t, k, wt))

# the two copies of a SortedX witness for a cons, from the copies of its parts
def sdx_cons(+kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, dk: (S.KAllX(t, kh) & S.KAllX(t, kh)), dt: (S.SortedX(t) & S.SortedX(t))) -> (S.SortedX(Merge.XEntry{kh, vh} <> t) & S.SortedX(Merge.XEntry{kh, vh} <> t)):
  (wk1, wk2) = dk
  (wt1, wt2) = dt
  ((wk1, wt1), (wk2, wt2))

# a witness of SortedX can be copied, as a witness of KAllX can
def sortedx_dup(s: List<&2, Merge.XEntry>, w: S.SortedX(s)) -> (S.SortedX(s) & S.SortedX(s)):
  match s:
    case Nil{}:
      (Unit{}, Unit{})
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          (wk, wt) = w
          sdx_cons(kh, vh, t, kallx_dup(t, kh, wk), sortedx_dup(t, wt))

def xc_lt(+X: List<&2, Merge.XEntry>, +ka: String, +va: Nat, +kh: String, +vh: Nat) -> {Merge.xins_c(X, LT{}, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}) == Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> X) : List<&2, Merge.XEntry>}:
  match X:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      match h2:
        case Merge.XEntry{+k2, +v2}:
          {==}

# lins_c with EQ: the new entry merges into the head, which keeps its key
def xc_eq(+X: List<&2, Merge.XEntry>, +ka: String, +va: Nat, +kh: String, +vh: Nat) -> {Merge.xins_c(X, EQ{}, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}) == Merge.XEntry{kh, Nat.max(vh, va)} <> X : List<&2, Merge.XEntry>}:
  match X:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      match h2:
        case Merge.XEntry{+k2, +v2}:
          {==}

# lins_c with GT: the head stays in front, and the new entry goes into the rest
def xc_gt(+X: List<&2, Merge.XEntry>, +ka: String, +va: Nat, +kh: String, +vh: Nat) -> {Merge.xins_c(X, GT{}, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}) == Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, X) : List<&2, Merge.XEntry>}:
  match X:
    case Nil{}:
      {==}
    case +h2 <> +t2:
      match h2:
        case Merge.XEntry{+k2, +v2}:
          {==}

# insertion of (ka, va) before the head (kh, vh) <> X, when the new key is LT the head's key
def xi_lt(+X: List<&2, Merge.XEntry>, +ka: String, +va: Nat, +kh: String, +vh: Nat, ec: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> X) == Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> X) : List<&2, Merge.XEntry>}:
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins_c(X, Merge.skey_cmp(ka, kh), Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}), Merge.xins_c(X, LT{}, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> X), Equal.cong(Cmp, List<&2, Merge.XEntry>, (z => Merge.xins_c(X, z, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh})), Merge.skey_cmp(ka, kh), LT{}, ec), xc_lt(X, ka, va, kh, vh))

# insertion of (ka, va) into (kh, vh) <> X, when the keys are EQ: the head is combined
def xi_eq(+X: List<&2, Merge.XEntry>, +ka: String, +va: Nat, +kh: String, +vh: Nat, ec: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> X) == Merge.XEntry{kh, Nat.max(vh, va)} <> X : List<&2, Merge.XEntry>}:
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins_c(X, Merge.skey_cmp(ka, kh), Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}), Merge.xins_c(X, EQ{}, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}), Merge.XEntry{kh, Nat.max(vh, va)} <> X, Equal.cong(Cmp, List<&2, Merge.XEntry>, (z => Merge.xins_c(X, z, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh})), Merge.skey_cmp(ka, kh), EQ{}, ec), xc_eq(X, ka, va, kh, vh))

# insertion of (ka, va) into (kh, vh) <> X, when the new key is GT the head's key: the head stays in front
def xi_gt(+X: List<&2, Merge.XEntry>, +ka: String, +va: Nat, +kh: String, +vh: Nat, ec: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> X) == Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, X) : List<&2, Merge.XEntry>}:
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins_c(X, Merge.skey_cmp(ka, kh), Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}), Merge.xins_c(X, GT{}, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh}), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, X), Equal.cong(Cmp, List<&2, Merge.XEntry>, (z => Merge.xins_c(X, z, Merge.XEntry{ka, va}, Merge.XEntry{kh, vh})), Merge.skey_cmp(ka, kh), GT{}, ec), xc_gt(X, ka, va, kh, vh))

# ---- L2: inserting two lessons in either order gives the same list, for every list s ----

# lp_max is associative and commutative in the order that matters here
def xpac(+x: Nat, +y: Nat, +z: Nat) -> {Nat.max(Nat.max(x, y), z) == Nat.max(Nat.max(x, z), y) : Nat}:
  Equal.trans(Nat, Nat.max(Nat.max(x, y), z), Nat.max(x, Nat.max(y, z)), Nat.max(Nat.max(x, z), y),
    Equal.sym(Nat, Nat.max(x, Nat.max(y, z)), Nat.max(Nat.max(x, y), z), Laws.max_assoc(x, y, z)),
    Equal.trans(Nat, Nat.max(x, Nat.max(y, z)), Nat.max(x, Nat.max(z, y)), Nat.max(Nat.max(x, z), y),
      Equal.cong(Nat, Nat, (w => Nat.max(x, w)), Nat.max(y, z), Nat.max(z, y), Laws.max_comm(y, z)),
      Laws.max_assoc(x, z, y)))

# two entries with EQ keys, in either order, give the same entry before the rest X
def xp_eq_swap(+ka: String, +va: Nat, +kb: String, +vb: Nat, e: {Merge.skey_cmp(ka, kb) == EQ{} : Cmp}, +X: List<&2, Merge.XEntry>) -> {Merge.XEntry{kb, Nat.max(vb, va)} <> X == Merge.XEntry{ka, Nat.max(va, vb)} <> X : List<&2, Merge.XEntry>}:
  kq = Equal.sym(String, ka, kb, Laws.skey_eq_of(ka, kb, Ord.IsEQ.to(Merge.skey_cmp(ka, kb), e)))
  s1 = Equal.cong(String, Merge.XEntry, (k => Merge.XEntry{k, Nat.max(vb, va)}), kb, ka, kq)
  s2 = Equal.cong(Nat, Merge.XEntry, (v => Merge.XEntry{ka, v}), Nat.max(vb, va), Nat.max(va, vb), Laws.max_comm(vb, va))
  s3 = Equal.trans(Merge.XEntry, Merge.XEntry{kb, Nat.max(vb, va)}, Merge.XEntry{ka, Nat.max(vb, va)}, Merge.XEntry{ka, Nat.max(va, vb)}, s1, s2)
  Equal.cong(Merge.XEntry, List<&2, Merge.XEntry>, (p => p <> X), Merge.XEntry{kb, Nat.max(vb, va)}, Merge.XEntry{ka, Nat.max(va, vb)}, s3)

# congruence for the two places a list appears in lins
def cong_xins(+ka: String, +va: Nat, +x: List<&2, Merge.XEntry>, +y: List<&2, Merge.XEntry>, e: {x == y : List<&2, Merge.XEntry>}) -> {Merge.xins(Merge.XEntry{ka, va}, x) == Merge.xins(Merge.XEntry{ka, va}, y) : List<&2, Merge.XEntry>}:
  Equal.cong(List<&2, Merge.XEntry>, List<&2, Merge.XEntry>, (z => Merge.xins(Merge.XEntry{ka, va}, z)), x, y, e)

def cong_xcons(+kh: String, +vh: Nat, +x: List<&2, Merge.XEntry>, +y: List<&2, Merge.XEntry>, e: {x == y : List<&2, Merge.XEntry>}) -> {Merge.XEntry{kh, vh} <> x == Merge.XEntry{kh, vh} <> y : List<&2, Merge.XEntry>}:
  Equal.cong(List<&2, Merge.XEntry>, List<&2, Merge.XEntry>, (z => Merge.XEntry{kh, vh} <> z), x, y, e)

# ---- the empty list: [A, B] against [B, A] ----

def xins2_nil_c(+ka: String, +va: Nat, +kb: String, +vb: Nat, +c: Cmp, +ec: {Merge.skey_cmp(ka, kb) == c : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Nil{})) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})) : List<&2, Merge.XEntry>}:
  match c:
    case LT{}:
      s1 = xi_lt(Nil{}, ka, va, kb, vb, ec)
      r1 = xi_gt(Nil{}, kb, vb, ka, va, rev_lt(ka, kb, ec))
      Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Nil{})), Merge.XEntry{ka, va} <> (Merge.XEntry{kb, vb} <> Nil{}), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})), s1, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Nil{}), r1))
    case EQ{}:
      s1 = xi_eq(Nil{}, ka, va, kb, vb, ec)
      r1 = xi_eq(Nil{}, kb, vb, ka, va, eq_flip(ka, kb, ec))
      Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Nil{})), Merge.XEntry{kb, Nat.max(vb, va)} <> Nil{}, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})),
        s1,
        Equal.trans(List<&2, Merge.XEntry>, Merge.XEntry{kb, Nat.max(vb, va)} <> Nil{}, Merge.XEntry{ka, Nat.max(va, vb)} <> Nil{}, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})),
          xp_eq_swap(ka, va, kb, vb, ec, Nil{}),
          Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})), Merge.XEntry{ka, Nat.max(va, vb)} <> Nil{}, r1)))
    case GT{}:
      s1 = xi_gt(Nil{}, ka, va, kb, vb, ec)
      r1 = xi_lt(Nil{}, kb, vb, ka, va, rev_gt(ka, kb, ec))
      Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Nil{})), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> Nil{}), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})),
        Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Nil{})), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Nil{}), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> Nil{}), s1, Equal.cong(List<&2, Merge.XEntry>, List<&2, Merge.XEntry>, (z => Merge.XEntry{kb, vb} <> z), Merge.xins(Merge.XEntry{ka, va}, Nil{}), Merge.XEntry{ka, va} <> Nil{}, {==})),
        Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Nil{})), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> Nil{}), r1))

# ---- the cons case: the branch lemmas, one per pair of comparisons of ka and kb with the head kh ----

# GT, GT: both new entries go past the head, so the head stays in front and the induction hypothesis applies to the rest
def x2_GG(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}, ih: {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, t)) : List<&2, Merge.XEntry>}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_gt(t, kb, vb, kh, vh, eB)
  s2 = xi_gt(Merge.xins(Merge.XEntry{kb, vb}, t), ka, va, kh, vh, eA)
  r1 = xi_gt(t, ka, va, kh, vh, eA)
  r2 = xi_gt(Merge.xins(Merge.XEntry{ka, va}, t), kb, vb, kh, vh, eB)
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, t)), cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t), s1), s2)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, t)), cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t), r1), r2)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L1,
    Equal.trans(List<&2, Merge.XEntry>, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)),
      cong_xcons(kh, vh, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, t)), ih),
      Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, t)), R1)))

# GT, EQ: the new a merges into the head, which the new b has just passed
def x2_GE(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_gt(t, kb, vb, kh, vh, eB)
  s2 = xi_eq(Merge.xins(Merge.XEntry{kb, vb}, t), ka, va, kh, vh, eA)
  r1 = xi_eq(t, ka, va, kh, vh, eA)
  r2 = xi_gt(t, kb, vb, kh, Nat.max(vh, va), eB)
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.XEntry{kh, Nat.max(vh, va)} <> Merge.xins(Merge.XEntry{kb, vb}, t), cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t), s1), s2)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, Nat.max(vh, va)} <> t), Merge.XEntry{kh, Nat.max(vh, va)} <> Merge.xins(Merge.XEntry{kb, vb}, t), cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, va)} <> t, r1), r2)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(vh, va)} <> Merge.xins(Merge.XEntry{kb, vb}, t), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(vh, va)} <> Merge.xins(Merge.XEntry{kb, vb}, t), R1))

# ---- the cons case, continued: the remaining branches ----

# EQ, GT: the new b merges into the head; the new a is past the head
def x2_EG(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_eq(t, kb, vb, kh, vh, eB)
  s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, vb)} <> t, s1)
  s3 = xi_gt(t, ka, va, kh, Nat.max(vh, vb), eA)
  r1 = xi_gt(t, ka, va, kh, vh, eA)
  r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t), r1)
  r3 = xi_eq(Merge.xins(Merge.XEntry{ka, va}, t), kb, vb, kh, vh, eB)
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, Nat.max(vh, vb)} <> t), Merge.XEntry{kh, Nat.max(vh, vb)} <> Merge.xins(Merge.XEntry{ka, va}, t), s2, s3)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), Merge.XEntry{kh, Nat.max(vh, vb)} <> Merge.xins(Merge.XEntry{ka, va}, t), r2, r3)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(vh, vb)} <> Merge.xins(Merge.XEntry{ka, va}, t), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(vh, vb)} <> Merge.xins(Merge.XEntry{ka, va}, t), R1))

# EQ, EQ: both new entries merge into the head; the two combined values agree by xpac
def x2_EE(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_eq(t, kb, vb, kh, vh, eB)
  s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, vb)} <> t, s1)
  s3 = xi_eq(t, ka, va, kh, Nat.max(vh, vb), eA)
  m = Equal.cong(Nat, List<&2, Merge.XEntry>, (v => Merge.XEntry{kh, v} <> t), Nat.max(Nat.max(vh, vb), va), Nat.max(Nat.max(vh, va), vb), xpac(vh, vb, va))
  r1 = xi_eq(t, ka, va, kh, vh, eA)
  r3 = xi_eq(t, kb, vb, kh, Nat.max(vh, va), eB)
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, Nat.max(vh, vb)} <> t), Merge.XEntry{kh, Nat.max(Nat.max(vh, vb), va)} <> t, s2, s3)
  L2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(Nat.max(vh, vb), va)} <> t, Merge.XEntry{kh, Nat.max(Nat.max(vh, va), vb)} <> t, L1, m)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, Nat.max(vh, va)} <> t), Merge.XEntry{kh, Nat.max(Nat.max(vh, va), vb)} <> t, Equal.cong(List<&2, Merge.XEntry>, List<&2, Merge.XEntry>, (z => Merge.xins(Merge.XEntry{kb, vb}, z)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, va)} <> t, r1), r3)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(Nat.max(vh, va), vb)} <> t, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kh, Nat.max(Nat.max(vh, va), vb)} <> t, R1))

# EQ, LT: the new a is before the head; the new b merges into the head
def x2_EL(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == EQ{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_eq(t, kb, vb, kh, vh, eB)
  s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, vb)} <> t, s1)
  s3 = xi_lt(t, ka, va, kh, Nat.max(vh, vb), eA)
  r1 = xi_lt(t, ka, va, kh, vh, eA)
  r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t), r1)
  r3 = xi_gt(Merge.XEntry{kh, vh} <> t, kb, vb, ka, va, w_el(ka, kh, kb, eA, eB))
  r4 = cong_xcons(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, vb)} <> t, xi_eq(t, kb, vb, kh, vh, eB))
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, Nat.max(vh, vb)} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, Nat.max(vh, vb)} <> t), s2, s3)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), r2, r3)
  R2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, Nat.max(vh, vb)} <> t), R1, r4)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, Nat.max(vh, vb)} <> t), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, Nat.max(vh, vb)} <> t), R2))

# ---- the cons case, continued: the GT-LT, GT-EQ... branches for the new b past the head and the new a before it ----

# GT, LT: the new a is before the head, so it goes to the front; the new b is past the head and stays behind it
def x2_GL(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == GT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_gt(t, kb, vb, kh, vh, eB)
  s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t), s1)
  s3 = xi_lt(Merge.xins(Merge.XEntry{kb, vb}, t), ka, va, kh, vh, eA)
  r1 = xi_lt(t, ka, va, kh, vh, eA)
  r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t), r1)
  r3 = xi_gt(Merge.XEntry{kh, vh} <> t, kb, vb, ka, va, w_gl(ka, kh, kb, eA, eB))
  r4 = cong_xcons(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t), xi_gt(t, kb, vb, kh, vh, eB))
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t)), s2, s3)
  L2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), L1, Equal.sym(List<&2, Merge.XEntry>, Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kb, vb}, t)), r4))
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), r2, r3)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), R1))

# LT, GT: the new b is before the head, so it goes to the front; the new a is past the head and stays behind it
def x2_LG(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == GT{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_lt(t, kb, vb, kh, vh, eB)
  s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t), s1)
  s3 = xi_gt(Merge.XEntry{kh, vh} <> t, ka, va, kb, vb, w_lg(ka, kh, kb, eA, eB))
  s4 = cong_xcons(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t), xi_gt(t, ka, va, kh, vh, eA))
  r1 = xi_gt(t, ka, va, kh, vh, eA)
  r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t), r1)
  r3 = xi_lt(Merge.xins(Merge.XEntry{ka, va}, t), kb, vb, kh, vh, eB)
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), s2, s3)
  L2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), L1, s4)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), r2, r3)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{ka, va}, t)), R1))

# LT, EQ: the new b is before the head; the new a merges into the head
def x2_LE(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == EQ{} : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  s1 = xi_lt(t, kb, vb, kh, vh, eB)
  s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t), s1)
  s3 = xi_gt(Merge.XEntry{kh, vh} <> t, ka, va, kb, vb, w_le(ka, kh, kb, eA, eB))
  s4 = cong_xcons(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, va)} <> t, xi_eq(t, ka, va, kh, vh, eA))
  r1 = xi_eq(t, ka, va, kh, vh, eA)
  r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, va)} <> t, r1)
  r3 = xi_lt(t, kb, vb, kh, Nat.max(vh, va), eB)
  L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), s2, s3)
  L2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, Nat.max(vh, va)} <> t), L1, s4)
  R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, Nat.max(vh, va)} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, Nat.max(vh, va)} <> t), r2, r3)
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, Nat.max(vh, va)} <> t), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, Nat.max(vh, va)} <> t), R1))

# LT, LT: both new entries are before the head; the order of ka and kb decides the front, and the EQ case joins by xp_eq_swap
def x2_LL(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +eB: {Merge.skey_cmp(kb, kh) == LT{} : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == LT{} : Cmp}, +c3: Cmp, +ec3: {Merge.skey_cmp(ka, kb) == c3 : Cmp}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  match c3:
    case LT{}:
      s1 = xi_lt(t, kb, vb, kh, vh, eB)
      s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t), s1)
      s3 = xi_lt(Merge.XEntry{kh, vh} <> t, ka, va, kb, vb, ec3)
      r1 = xi_lt(t, ka, va, kh, vh, eA)
      r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t), r1)
      r3 = xi_gt(Merge.XEntry{kh, vh} <> t, kb, vb, ka, va, rev_lt(ka, kb, ec3))
      r4 = cong_xcons(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t), xi_lt(t, kb, vb, kh, vh, eB))
      L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), s2, s3)
      R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), r2, r3)
      R2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), R1, r4)
      Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L1, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, va} <> (Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), R2))
    case EQ{}:
      s1 = xi_lt(t, kb, vb, kh, vh, eB)
      s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t), s1)
      s3 = xi_eq(Merge.XEntry{kh, vh} <> t, ka, va, kb, vb, ec3)
      r1 = xi_lt(t, ka, va, kh, vh, eA)
      r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t), r1)
      r3 = xi_eq(Merge.XEntry{kh, vh} <> t, kb, vb, ka, va, eq_flip(ka, kb, ec3))
      L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, Nat.max(vb, va)} <> (Merge.XEntry{kh, vh} <> t), s2, s3)
      R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, Nat.max(va, vb)} <> (Merge.XEntry{kh, vh} <> t), r2, r3)
      Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, Nat.max(va, vb)} <> (Merge.XEntry{kh, vh} <> t), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, Nat.max(vb, va)} <> (Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, Nat.max(va, vb)} <> (Merge.XEntry{kh, vh} <> t), L1, xp_eq_swap(ka, va, kb, vb, ec3, Merge.XEntry{kh, vh} <> t)), Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{ka, Nat.max(va, vb)} <> (Merge.XEntry{kh, vh} <> t), R1))
    case GT{}:
      s1 = xi_lt(t, kb, vb, kh, vh, eB)
      s2 = cong_xins(ka, va, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t), s1)
      s3 = xi_gt(Merge.XEntry{kh, vh} <> t, ka, va, kb, vb, ec3)
      s4 = cong_xcons(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t), xi_lt(t, ka, va, kh, vh, eA))
      r1 = xi_lt(t, ka, va, kh, vh, eA)
      r2 = cong_xins(kb, vb, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t), r1)
      r3 = xi_lt(Merge.XEntry{kh, vh} <> t, kb, vb, ka, va, rev_gt(ka, kb, ec3))
      L1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kb, vb} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), s2, s3)
      L2 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), L1, s4)
      R1 = Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), r2, r3)
      Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), L2, Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)), Merge.XEntry{kb, vb} <> (Merge.XEntry{ka, va} <> (Merge.XEntry{kh, vh} <> t)), R1))

# ---- the cons case dispatch: cb = skey(kb, kh) and ca = skey(ka, kh) choose the branch lemma ----

def xins2_cons(+ka: String, +va: Nat, +kb: String, +vb: Nat, +kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +cb: Cmp, +ca: Cmp, +eB: {Merge.skey_cmp(kb, kh) == cb : Cmp}, +eA: {Merge.skey_cmp(ka, kh) == ca : Cmp}, +ih: {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, t)) : List<&2, Merge.XEntry>}) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, Merge.XEntry{kh, vh} <> t)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, Merge.XEntry{kh, vh} <> t)) : List<&2, Merge.XEntry>}:
  match cb:
    case LT{}:
      match ca:
        case LT{}:
          x2_LL(ka, va, kb, vb, kh, vh, t, eB, eA, Merge.skey_cmp(ka, kb), {==})
        case EQ{}:
          x2_LE(ka, va, kb, vb, kh, vh, t, eB, eA)
        case GT{}:
          x2_LG(ka, va, kb, vb, kh, vh, t, eB, eA)
    case EQ{}:
      match ca:
        case LT{}:
          x2_EL(ka, va, kb, vb, kh, vh, t, eB, eA)
        case EQ{}:
          x2_EE(ka, va, kb, vb, kh, vh, t, eB, eA)
        case GT{}:
          x2_EG(ka, va, kb, vb, kh, vh, t, eB, eA)
    case GT{}:
      match ca:
        case LT{}:
          x2_GL(ka, va, kb, vb, kh, vh, t, eB, eA)
        case EQ{}:
          x2_GE(ka, va, kb, vb, kh, vh, t, eB, eA)
        case GT{}:
          x2_GG(ka, va, kb, vb, kh, vh, t, eB, eA, ih)

# ---- two lesson insertions commute on any list (no sortedness needed) ----

def xins2(+ka: String, +va: Nat, +kb: String, +vb: Nat, +s: List<&2, Merge.XEntry>) -> {Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kb, vb}, s)) == Merge.xins(Merge.XEntry{kb, vb}, Merge.xins(Merge.XEntry{ka, va}, s)) : List<&2, Merge.XEntry>}:
  match s:
    case Nil{}:
      xins2_nil_c(ka, va, kb, vb, Merge.skey_cmp(ka, kb), {==})
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          xins2_cons(ka, va, kb, vb, kh, vh, t, Merge.skey_cmp(kb, kh), Merge.skey_cmp(ka, kh), {==}, {==}, xins2(ka, va, kb, vb, t))

# ---- the fold: a fold over b, with the same accumulator changed, is congruent ----

def cong_xfold(+b: List<&2, Merge.XEntry>, +x: List<&2, Merge.XEntry>, +y: List<&2, Merge.XEntry>, e: {x == y : List<&2, Merge.XEntry>}) -> {Merge.xfold(b, x) == Merge.xfold(b, y) : List<&2, Merge.XEntry>}:
  Equal.cong(List<&2, Merge.XEntry>, List<&2, Merge.XEntry>, (z => Merge.xfold(b, z)), x, y, e)

# inserting A into the accumulator before folding b equals inserting it after: the fold passes it along
def xf_lins(+ka: String, +va: Nat, +b: List<&2, Merge.XEntry>, +acc: List<&2, Merge.XEntry>) -> {Merge.xfold(b, Merge.xins(Merge.XEntry{ka, va}, acc)) == Merge.xins(Merge.XEntry{ka, va}, Merge.xfold(b, acc)) : List<&2, Merge.XEntry>}:
  match b:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          Equal.trans(List<&2, Merge.XEntry>, Merge.xfold(Merge.XEntry{kh, vh} <> t, Merge.xins(Merge.XEntry{ka, va}, acc)), Merge.xfold(t, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kh, vh}, acc))), Merge.xins(Merge.XEntry{ka, va}, Merge.xfold(Merge.XEntry{kh, vh} <> t, acc)),
            cong_xfold(t, Merge.xins(Merge.XEntry{kh, vh}, Merge.xins(Merge.XEntry{ka, va}, acc)), Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kh, vh}, acc)), Equal.sym(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{ka, va}, Merge.xins(Merge.XEntry{kh, vh}, acc)), Merge.xins(Merge.XEntry{kh, vh}, Merge.xins(Merge.XEntry{ka, va}, acc)), xins2(ka, va, kh, vh, acc))),
            xf_lins(ka, va, t, Merge.xins(Merge.XEntry{kh, vh}, acc)))

# the fold of b over a's entries and the fold of a over b's entries agree: the insertions of one list commute past the other
def xf_comm(+a: List<&2, Merge.XEntry>, +b: List<&2, Merge.XEntry>, +acc: List<&2, Merge.XEntry>) -> {Merge.xfold(b, Merge.xfold(a, acc)) == Merge.xfold(a, Merge.xfold(b, acc)) : List<&2, Merge.XEntry>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          Equal.trans(List<&2, Merge.XEntry>, Merge.xfold(b, Merge.xfold(Merge.XEntry{kh, vh} <> t, acc)), Merge.xfold(t, Merge.xfold(b, Merge.xins(Merge.XEntry{kh, vh}, acc))), Merge.xfold(Merge.XEntry{kh, vh} <> t, Merge.xfold(b, acc)),
            xf_comm(t, b, Merge.xins(Merge.XEntry{kh, vh}, acc)),
            cong_xfold(t, Merge.xfold(b, Merge.xins(Merge.XEntry{kh, vh}, acc)), Merge.xins(Merge.XEntry{kh, vh}, Merge.xfold(b, acc)), xf_lins(kh, vh, b, acc)))

# LAW: xp_comm: the lesson merge is commutative on any two lists (see LAWS.bend)
def Laws.xp_comm(a, b):
  xf_comm(a, b, Nil{})

# ---- lessons: idempotence (a sorted map folded into itself gives the map back) ----

# inserting an entry whose key is already at the front, with its own value, changes nothing
def xins_self(+kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>) -> {Merge.xins(Merge.XEntry{kh, vh}, Merge.XEntry{kh, vh} <> t) == Merge.XEntry{kh, vh} <> t : List<&2, Merge.XEntry>}:
  Equal.trans(List<&2, Merge.XEntry>, Merge.xins(Merge.XEntry{kh, vh}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, Nat.max(vh, vh)} <> t, Merge.XEntry{kh, vh} <> t,
    xi_eq(t, kh, vh, kh, vh, skey_self(kh)),
    Equal.cong(Nat, List<&2, Merge.XEntry>, (u => Merge.XEntry{kh, u} <> t), Nat.max(vh, vh), vh, Laws.max_self(vh)))

# folding t into an accumulator whose front key is below every key of t: the front entry stays in front
def xf_gt(+kh: String, +vh: Nat, +t: List<&2, Merge.XEntry>, +s: List<&2, Merge.XEntry>, w: S.KAllX(t, kh)) -> {Merge.xfold(t, Merge.XEntry{kh, vh} <> s) == Merge.XEntry{kh, vh} <> Merge.xfold(t, s) : List<&2, Merge.XEntry>}:
  match t:
    case Nil{}:
      {==}
    case +h <> +t2:
      match h:
        case Merge.XEntry{+kt, +vt}:
          (wi, wt) = w
          Equal.trans(List<&2, Merge.XEntry>,
            Merge.xfold(t2, Merge.xins(Merge.XEntry{kt, vt}, Merge.XEntry{kh, vh} <> s)),
            Merge.xfold(t2, Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kt, vt}, s)),
            Merge.XEntry{kh, vh} <> Merge.xfold(t2, Merge.xins(Merge.XEntry{kt, vt}, s)),
            cong_xfold(t2, Merge.xins(Merge.XEntry{kt, vt}, Merge.XEntry{kh, vh} <> s), Merge.XEntry{kh, vh} <> Merge.xins(Merge.XEntry{kt, vt}, s), xi_gt(s, kt, vt, kh, vh, islt_skey_gt(kh, kt, wi))),
            xf_gt(kh, vh, t2, Merge.xins(Merge.XEntry{kt, vt}, s), wt))

# a sorted map folded into itself stays itself
def xf_self(+s: List<&2, Merge.XEntry>, ws: S.SortedX(s)) -> {Merge.xfold(s, s) == s : List<&2, Merge.XEntry>}:
  match s:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          (wk, wt) = ws
          Equal.trans(List<&2, Merge.XEntry>, Merge.xfold(Merge.XEntry{kh, vh} <> t, Merge.XEntry{kh, vh} <> t), Merge.xfold(t, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> t,
            cong_xfold(t, Merge.xins(Merge.XEntry{kh, vh}, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> t, xins_self(kh, vh, t)),
            Equal.trans(List<&2, Merge.XEntry>, Merge.xfold(t, Merge.XEntry{kh, vh} <> t), Merge.XEntry{kh, vh} <> Merge.xfold(t, t), Merge.XEntry{kh, vh} <> t,
              xf_gt(kh, vh, t, t, wk),
              cong_xcons(kh, vh, Merge.xfold(t, t), t, xf_self(t, wt))))

# a sorted map folded into the empty list gives the map back
def xf_nil(+s: List<&2, Merge.XEntry>, ws: S.SortedX(s)) -> {Merge.xfold(s, Nil{}) == s : List<&2, Merge.XEntry>}:
  match s:
    case Nil{}:
      {==}
    case +h <> +t:
      match h:
        case Merge.XEntry{+kh, +vh}:
          (wk, wt) = ws
          Equal.trans(List<&2, Merge.XEntry>, Merge.xfold(Merge.XEntry{kh, vh} <> t, Nil{}), Merge.XEntry{kh, vh} <> Merge.xfold(t, Nil{}), Merge.XEntry{kh, vh} <> t,
            xf_gt(kh, vh, t, Nil{}, wk),
            cong_xcons(kh, vh, Merge.xfold(t, Nil{}), t, xf_nil(t, wt)))

# a sorted lesson map merged with itself is itself: the fold over a of (a folded into the empty list) gives a.
# The two copies of the witness arrive as a parameter, since a match cannot scrutinize a computed pair.
def xidem_pair(+a: List<&2, Merge.XEntry>, dd: (S.SortedX(a) & S.SortedX(a))) -> {Merge.merge_xp(a, a) == a : List<&2, Merge.XEntry>}:
  (s1, s2) = dd
  Equal.trans(List<&2, Merge.XEntry>, Merge.xfold(a, Merge.xfold(a, Nil{})), Merge.xfold(a, a), a,
    cong_xfold(a, Merge.xfold(a, Nil{}), a, xf_nil(a, s1)),
    xf_self(a, s2))

def xidem(+a: List<&2, Merge.XEntry>, sa: S.SortedX(a)) -> {Merge.merge_xp(a, a) == a : List<&2, Merge.XEntry>}:
  xidem_pair(a, sortedx_dup(a, sa))

# LAW: xp_idem: merging a sorted lesson map with itself gives the map back (see LAWS.bend)
def Laws.xp_idem(a, sa):
  xidem(a, sa)

# ---- xsum_comm: the total XP is a function of the merged map, so the map's commutation carries over ----

# LAW: xsum_comm, from xp_comm by congruence on xsum
def xsum_comm_h(+a: List<&2, Merge.XEntry>, +b: List<&2, Merge.XEntry>) -> {Merge.xsum(Merge.merge_xp(a, b)) == Merge.xsum(Merge.merge_xp(b, a)) : Nat}:
  Equal.cong(List<&2, Merge.XEntry>, Nat, (z => Merge.xsum(z)), Merge.merge_xp(a, b), Merge.merge_xp(b, a), Laws.xp_comm(a, b))

def Laws.xsum_comm(a, b):
  xsum_comm_h(a, b)


# ---- the card order: level facts for Nat and String, and the lexicographic step ----

# LT is transitive on Nat (the same case split as Word.lt_trans)
def nat_lt_w(+a: Nat, +b: Nat, +c: Nat, h1: Ord.IsLT(Nat.cmp(a, b)), h2: Ord.IsLT(Nat.cmp(b, c))) -> Ord.IsLT(Nat.cmp(a, c)):
  match a b:
    case 0n 0n:
      Empty.absurd(Ord.IsLT(Nat.cmp(0n, c)), h1)
    case 0n 1n+bp:
      match c:
        case 0n:
          Empty.absurd(Ord.IsLT(Nat.cmp(0n, 0n)), h2)
        case 1n+cp:
          Unit{}
    case 1n+ap 0n:
      Empty.absurd(Ord.IsLT(Nat.cmp(1n+ap, c)), h1)
    case 1n+ap 1n+bp:
      match c:
        case 0n:
          Empty.absurd(Ord.IsLT(Nat.cmp(1n+ap, 0n)), h2)
        case 1n+cp:
          nat_lt_w(ap, bp, cp, h1, h2)

# every number compares EQ with itself
def nat_self(+a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nat_self(p)

# the level facts on Nat: LT then EQ, EQ then LT, and EQ then EQ
def nat_le_w(+a: Nat, +b: Nat, +c: Nat, h1: Ord.IsLT(Nat.cmp(a, b)), h2: Ord.IsEQ(Nat.cmp(b, c))) -> Ord.IsLT(Nat.cmp(a, c)):
  Ord.Cmp.trLT(Nat.cmp(a, c), Nat.cmp(a, b),
    Equal.sym(Cmp, Nat.cmp(a, b), Nat.cmp(a, c),
      Equal.cong(Nat, Cmp, w => Nat.cmp(a, w), b, c, Ord.Nat.eq_of_cmp_eq(b, c, h2))),
    h1)

def nat_el_w(+a: Nat, +b: Nat, +c: Nat, h1: Ord.IsEQ(Nat.cmp(a, b)), h2: Ord.IsLT(Nat.cmp(b, c))) -> Ord.IsLT(Nat.cmp(a, c)):
  Ord.Cmp.trLT(Nat.cmp(a, c), Nat.cmp(b, c),
    Equal.cong(Nat, Cmp, w => Nat.cmp(w, c), a, b, Ord.Nat.eq_of_cmp_eq(a, b, h1)),
    h2)

def nat_ee_w(+a: Nat, +b: Nat, +c: Nat, h1: Ord.IsEQ(Nat.cmp(a, b)), h2: Ord.IsEQ(Nat.cmp(b, c))) -> Ord.IsEQ(Nat.cmp(a, c)):
  Ord.IsEQ.to(Nat.cmp(a, c),
    Equal.trans(Cmp, Nat.cmp(a, c), Nat.cmp(a, a), EQ{},
      Equal.cong(Nat, Cmp, w => Nat.cmp(a, w), c, a,
        Equal.sym(Nat, a, c,
          Equal.trans(Nat, a, b, c, Ord.Nat.eq_of_cmp_eq(a, b, h1), Ord.Nat.eq_of_cmp_eq(b, c, h2)))),
      nat_self(a)))

# the level facts on String, through the skey order
def str_ll(+a: String, +b: String, +c: String, h1: Ord.IsLT(Merge.skey_cmp(a, b)), h2: Ord.IsLT(Merge.skey_cmp(b, c))) -> Ord.IsLT(Merge.skey_cmp(a, c)):
  Ord.IsLT.to(Merge.skey_cmp(a, c),
    Laws.skey_lt_trans(a, b, c, Ord.IsLT.of(Merge.skey_cmp(a, b), h1), Ord.IsLT.of(Merge.skey_cmp(b, c), h2)))

def str_le(+a: String, +b: String, +c: String, h1: Ord.IsLT(Merge.skey_cmp(a, b)), h2: Ord.IsEQ(Merge.skey_cmp(b, c))) -> Ord.IsLT(Merge.skey_cmp(a, c)):
  Ord.Cmp.trLT(Merge.skey_cmp(a, c), Merge.skey_cmp(a, b),
    Equal.sym(Cmp, Merge.skey_cmp(a, b), Merge.skey_cmp(a, c),
      Equal.cong(String, Cmp, w => Merge.skey_cmp(a, w), b, c, Laws.skey_eq_of(b, c, h2))),
    h1)

def str_el(+a: String, +b: String, +c: String, h1: Ord.IsEQ(Merge.skey_cmp(a, b)), h2: Ord.IsLT(Merge.skey_cmp(b, c))) -> Ord.IsLT(Merge.skey_cmp(a, c)):
  Ord.Cmp.trLT(Merge.skey_cmp(a, c), Merge.skey_cmp(b, c),
    Equal.cong(String, Cmp, w => Merge.skey_cmp(w, c), a, b, Laws.skey_eq_of(a, b, h1)),
    h2)

def str_ee(+a: String, +b: String, +c: String, h1: Ord.IsEQ(Merge.skey_cmp(a, b)), h2: Ord.IsEQ(Merge.skey_cmp(b, c))) -> Ord.IsEQ(Merge.skey_cmp(a, c)):
  Ord.IsEQ.to(Merge.skey_cmp(a, c),
    Equal.trans(Cmp, Merge.skey_cmp(a, c), Merge.skey_cmp(a, a), EQ{},
      Equal.cong(String, Cmp, w => Merge.skey_cmp(a, w), c, a,
        Equal.sym(String, a, c,
          Equal.trans(String, a, b, c, Laws.skey_eq_of(a, b, h1), Laws.skey_eq_of(b, c, h2)))),
      Equal.trans(Cmp, Merge.skey_cmp(a, a), String.order(a, a), EQ{},
        Key.Key.skey_eq_order(a, a), Key.Key.order_self(a))))

# a comparison that is LT passes the chain through unchanged
def fin_lt(+r: Cmp, +Tr: Cmp, h: Ord.IsLT(r)) -> Ord.IsLT(Merge.cmp_then(r, Tr)):
  match r:
    case LT{}:
      Unit{}
    case EQ{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(EQ{}, Tr)), h)
    case GT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(GT{}, Tr)), h)

# an EQ comparison passes the decision to the rest of the chain
def fin_eq(+r: Cmp, +Tr: Cmp, he: Ord.IsEQ(r), ht: Ord.IsLT(Tr)) -> Ord.IsLT(Merge.cmp_then(r, Tr)):
  match r:
    case LT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(LT{}, Tr)), he)
    case EQ{}:
      ht
    case GT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(GT{}, Tr)), he)

# one level of a lexicographic chain: the level's own facts (LL, LE, EL, EE) and the tail (ih) decide
def lex_step(+p: Cmp, +q: Cmp, +r: Cmp, +Tp: Cmp, +Tq: Cmp, +Tr: Cmp,
    LL: Ord.IsLT(p) -> Ord.IsLT(q) -> Ord.IsLT(r),
    LE: Ord.IsLT(p) -> Ord.IsEQ(q) -> Ord.IsLT(r),
    EL: Ord.IsEQ(p) -> Ord.IsLT(q) -> Ord.IsLT(r),
    EE: Ord.IsEQ(p) -> Ord.IsEQ(q) -> Ord.IsEQ(r),
    ih: Ord.IsLT(Tp) -> Ord.IsLT(Tq) -> Ord.IsLT(Tr),
    hp: Ord.IsLT(Merge.cmp_then(p, Tp)),
    hq: Ord.IsLT(Merge.cmp_then(q, Tq))) -> Ord.IsLT(Merge.cmp_then(r, Tr)):
  match p q:
    case LT{} LT{}:
      fin_lt(r, Tr, LL(Unit{}, Unit{}))
    case LT{} EQ{}:
      fin_lt(r, Tr, LE(Unit{}, Unit{}))
    case LT{} GT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(r, Tr)), hq)
    case EQ{} LT{}:
      fin_lt(r, Tr, EL(Unit{}, Unit{}))
    case EQ{} EQ{}:
      fin_eq(r, Tr, EE(Unit{}, Unit{}), ih(hp, hq))
    case EQ{} GT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(r, Tr)), hq)
    case GT{} LT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(r, Tr)), hp)
    case GT{} EQ{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(r, Tr)), hp)
    case GT{} GT{}:
      Empty.absurd(Ord.IsLT(Merge.cmp_then(r, Tr)), hp)
