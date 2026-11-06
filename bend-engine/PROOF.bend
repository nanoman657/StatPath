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
