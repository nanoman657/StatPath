# Order facts for the sorted-map layer: the word, U32 and string orders are transitive,
# and an EQ comparison of two strings means the strings are equal. Checked by PROOF.bend.
import Base

# ---- witnesses: IsLT(c) is inhabited iff c is LT; IsEQ(c) iff c is EQ ----

def IsLT(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Empty

def IsEQ(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Empty

def Cmp.is_lt_t(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Empty

def Cmp.is_eq_t(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Empty

def Cmp.is_gt_t(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Empty
    case GT{}:
      Unit

# ---- refutations: two distinct constructors are never equal (the != idiom) ----

law Cmp.eq_ne_lt:
  {EQ{} != LT{} : Cmp}

def Cmp.eq_ne_lt(p):
  %p : Cmp.is_eq_t(_)
  Unit{}

law Cmp.lt_ne_eq:
  {LT{} != EQ{} : Cmp}

def Cmp.lt_ne_eq(p):
  %p : Cmp.is_lt_t(_)
  Unit{}

law Cmp.lt_ne_gt:
  {LT{} != GT{} : Cmp}

def Cmp.lt_ne_gt(p):
  %p : Cmp.is_lt_t(_)
  Unit{}

law Cmp.gt_ne_lt:
  {GT{} != LT{} : Cmp}

def Cmp.gt_ne_lt(p):
  %p : Cmp.is_gt_t(_)
  Unit{}

law Cmp.eq_ne_gt:
  {EQ{} != GT{} : Cmp}

def Cmp.eq_ne_gt(p):
  %p : Cmp.is_eq_t(_)
  Unit{}

law Cmp.gt_ne_eq:
  {GT{} != EQ{} : Cmp}

def Cmp.gt_ne_eq(p):
  %p : Cmp.is_gt_t(_)
  Unit{}

# ---- converters between equations and witnesses ----

law IsLT.of:
  for c: Cmp
  for h: IsLT(c)
  {c == LT{} : Cmp}

def IsLT.of(c, h):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, h)
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, h)

law IsEQ.of:
  for c: Cmp
  for h: IsEQ(c)
  {c == EQ{} : Cmp}

def IsEQ.of(c, h):
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, h)
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, h)

def IsLT.to(c: Cmp, e: {c == LT{} : Cmp}) -> IsLT(c):
  match c:
    case LT{}:
      Unit{}
    case EQ{}:
      Empty.absurd(IsLT(EQ{}), Cmp.eq_ne_lt(e))
    case GT{}:
      Empty.absurd(IsLT(GT{}), Cmp.gt_ne_lt(e))

def IsEQ.to(c: Cmp, e: {c == EQ{} : Cmp}) -> IsEQ(c):
  match c:
    case LT{}:
      Empty.absurd(IsEQ(LT{}), Cmp.lt_ne_eq(e))
    case EQ{}:
      Unit{}
    case GT{}:
      Empty.absurd(IsEQ(GT{}), Cmp.gt_ne_eq(e))

# ---- transport of a witness across an equation of comparisons ----

def Cmp.trLT(u: Cmp, v: Cmp, e: {u == v : Cmp}, h: IsLT(v)) -> IsLT(u):
  match u v:
    case LT{} LT{}:
      h
    case LT{} EQ{}:
      Empty.absurd(IsLT(LT{}), Cmp.lt_ne_eq(e))
    case LT{} GT{}:
      Empty.absurd(IsLT(LT{}), Cmp.lt_ne_gt(e))
    case EQ{} LT{}:
      Empty.absurd(IsLT(EQ{}), Cmp.eq_ne_lt(e))
    case EQ{} EQ{}:
      h
    case EQ{} GT{}:
      Empty.absurd(IsLT(EQ{}), Cmp.eq_ne_gt(e))
    case GT{} LT{}:
      Empty.absurd(IsLT(GT{}), Cmp.gt_ne_lt(e))
    case GT{} EQ{}:
      Empty.absurd(IsLT(GT{}), Cmp.gt_ne_eq(e))
    case GT{} GT{}:
      h

def Cmp.trEQ(u: Cmp, v: Cmp, e: {u == v : Cmp}, h: IsEQ(v)) -> IsEQ(u):
  match u v:
    case LT{} LT{}:
      h
    case LT{} EQ{}:
      Empty.absurd(IsEQ(LT{}), Cmp.lt_ne_eq(e))
    case LT{} GT{}:
      Empty.absurd(IsEQ(LT{}), Cmp.lt_ne_gt(e))
    case EQ{} LT{}:
      Empty.absurd(IsEQ(EQ{}), Cmp.eq_ne_lt(e))
    case EQ{} EQ{}:
      h
    case EQ{} GT{}:
      Empty.absurd(IsEQ(EQ{}), Cmp.eq_ne_gt(e))
    case GT{} LT{}:
      Empty.absurd(IsEQ(GT{}), Cmp.gt_ne_lt(e))
    case GT{} EQ{}:
      Empty.absurd(IsEQ(GT{}), Cmp.gt_ne_eq(e))
    case GT{} GT{}:
      h

# ---- Bool facts ----

law Bool.eq_of_cmp_eq:
  for a: Bool
  for b: Bool
  for h: IsEQ(Bool.cmp(a, b))
  {a == b : Bool}

def Bool.eq_of_cmp_eq(a, b, h):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, h)
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, h)
    case True{} True{}:
      {==}

def Bool.cmp_self(a: Bool) -> IsEQ(Bool.cmp(a, a)):
  match a:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law Bool.lt_trans:
  for a: Bool
  for b: Bool
  for c: Bool
  for h1: IsLT(Bool.cmp(a, b))
  for h2: IsLT(Bool.cmp(b, c))
  {Bool.cmp(a, c) == LT{} : Cmp}

def Bool.lt_trans(a, b, c, h1, h2):
  match a b c:
    case False{} False{} False{}:
      Empty.absurd({Bool.cmp(False{}, False{}) == LT{} : Cmp}, h1)
    case False{} False{} True{}:
      Empty.absurd({Bool.cmp(False{}, True{}) == LT{} : Cmp}, h1)
    case False{} True{} False{}:
      Empty.absurd({Bool.cmp(False{}, False{}) == LT{} : Cmp}, h2)
    case False{} True{} True{}:
      Empty.absurd({Bool.cmp(False{}, True{}) == LT{} : Cmp}, h2)
    case True{} False{} False{}:
      Empty.absurd({Bool.cmp(True{}, False{}) == LT{} : Cmp}, h1)
    case True{} False{} True{}:
      Empty.absurd({Bool.cmp(True{}, True{}) == LT{} : Cmp}, h1)
    case True{} True{} False{}:
      Empty.absurd({Bool.cmp(True{}, False{}) == LT{} : Cmp}, h1)
    case True{} True{} True{}:
      Empty.absurd({Bool.cmp(True{}, True{}) == LT{} : Cmp}, h1)

# ---- Word facts ----

def Word.fin_refl(ab: Bool, t: Cmp, h: IsEQ(t)) -> IsEQ(Word.cmp.fin(ab, ab, t)):
  match t:
    case LT{}:
      Empty.absurd(IsEQ(Word.cmp.fin(ab, ab, LT{})), h)
    case EQ{}:
      Bool.cmp_self(ab)
    case GT{}:
      Empty.absurd(IsEQ(Word.cmp.fin(ab, ab, GT{})), h)

def Word.cmp_self(n: Nat, a: Word(n)) -> IsEQ(Word.cmp(n, a, a)):
  match n:
    case 0n:
      Unit{}
    case 1n+(+p):
      match a:
        case WCon{+ab, +at}:
          Word.fin_refl(ab, Word.cmp(p, at, at), Word.cmp_self(p, at))

def Word.fin_eq_t(ab: Bool, bb: Bool, t: Cmp, h: IsEQ(Word.cmp.fin(ab, bb, t))) -> IsEQ(t):
  match t:
    case LT{}:
      Empty.absurd(IsEQ(LT{}), h)
    case EQ{}:
      Unit{}
    case GT{}:
      Empty.absurd(IsEQ(GT{}), h)

def Word.fin_FT(t: Cmp, h: IsEQ(Word.cmp.fin(False{}, True{}, t))) -> Empty:
  match t:
    case LT{}:
      h
    case EQ{}:
      h
    case GT{}:
      h

def Word.fin_TF(t: Cmp, h: IsEQ(Word.cmp.fin(True{}, False{}, t))) -> Empty:
  match t:
    case LT{}:
      h
    case EQ{}:
      h
    case GT{}:
      h

law Word.eq_w:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  for h: IsEQ(Word.cmp(n, a, b))
  {a == b : Word(n)}

def Word.eq_w(n, a, b, h):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, at, bt,
            Word.eq_w(p, at, bt, Word.fin_eq_t(False{}, False{}, Word.cmp(p, at, bt), h)))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Empty.absurd({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)}, Word.fin_FT(Word.cmp(p, at, bt), h))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Empty.absurd({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)}, Word.fin_TF(Word.cmp(p, at, bt), h))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, at, bt,
            Word.eq_w(p, at, bt, Word.fin_eq_t(True{}, True{}, Word.cmp(p, at, bt), h)))

law Word.eq_of_cmp:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for h: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

def Word.eq_of_cmp(n, a, b, h):
  Word.eq_w(n, a, b, IsEQ.to(Word.cmp(n, a, b), h))

# ---- transitivity of the word order: tail cases, then the recursion ----

law Word.lt_cases:
  for +p: Nat
  for +ab: Bool
  for +bb: Bool
  for +cb: Bool
  for +at: Word(p)
  for +bt: Word(p)
  for +ct: Word(p)
  for x: Cmp
  for y: Cmp
  for ex: {Word.cmp(p, at, bt) == x : Cmp}
  for ey: {Word.cmp(p, bt, ct) == y : Cmp}
  for h1: IsLT(Word.cmp.fin(ab, bb, x))
  for h2: IsLT(Word.cmp.fin(bb, cb, y))
  for ih: IsLT(Word.cmp(p, at, bt)) -> IsLT(Word.cmp(p, bt, ct)) -> {Word.cmp(p, at, ct) == LT{} : Cmp}
  {Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}

def Word.lt_cases(p, ab, bb, cb, at, bt, ct, x, y, ex, ey, h1, h2, ih):
  match x:
    case LT{}:
      match y:
        case LT{}:
          Equal.trans(Cmp,
            Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)),
            Word.cmp.fin(ab, cb, LT{}),
            LT{},
            Equal.cong(Cmp, Cmp, w => Word.cmp.fin(ab, cb, w), Word.cmp(p, at, ct), LT{},
              ih(IsLT.to(Word.cmp(p, at, bt), ex), IsLT.to(Word.cmp(p, bt, ct), ey))),
            {==})
        case EQ{}:
          Equal.trans(Cmp,
            Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)),
            Word.cmp.fin(ab, cb, LT{}),
            LT{},
            Equal.cong(Cmp, Cmp, w => Word.cmp.fin(ab, cb, w), Word.cmp(p, at, ct), LT{},
              Equal.trans(Cmp, Word.cmp(p, at, ct), Word.cmp(p, at, bt), LT{},
                Equal.sym(Cmp, Word.cmp(p, at, bt), Word.cmp(p, at, ct),
                  Equal.cong(Word(p), Cmp, w => Word.cmp(p, at, w), bt, ct, Word.eq_of_cmp(p, bt, ct, ey))),
                ex)),
            {==})
        case GT{}:
          Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, h2)
    case EQ{}:
      match y:
        case LT{}:
          Equal.trans(Cmp,
            Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)),
            Word.cmp.fin(ab, cb, LT{}),
            LT{},
            Equal.cong(Cmp, Cmp, w => Word.cmp.fin(ab, cb, w), Word.cmp(p, at, ct), LT{},
              Equal.trans(Cmp, Word.cmp(p, at, ct), Word.cmp(p, bt, ct), LT{},
                Equal.cong(Word(p), Cmp, w => Word.cmp(p, w, ct), at, bt, Word.eq_of_cmp(p, at, bt, ex)),
                ey)),
            {==})
        case EQ{}:
          Equal.trans(Cmp,
            Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)),
            Word.cmp.fin(ab, cb, EQ{}),
            LT{},
            Equal.cong(Cmp, Cmp, w => Word.cmp.fin(ab, cb, w), Word.cmp(p, at, ct), EQ{},
              Equal.trans(Cmp, Word.cmp(p, at, ct), Word.cmp(p, at, at), EQ{},
                Equal.cong(Word(p), Cmp, w => Word.cmp(p, at, w), ct, at,
                  Equal.sym(Word(p), at, ct,
                    Equal.trans(Word(p), at, bt, ct, Word.eq_of_cmp(p, at, bt, ex), Word.eq_of_cmp(p, bt, ct, ey)))),
                IsEQ.of(Word.cmp(p, at, at), Word.cmp_self(p, at)))),
            Bool.lt_trans(ab, bb, cb, h1, h2))
        case GT{}:
          Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, h2)
    case GT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, Word.cmp(p, at, ct)) == LT{} : Cmp}, h1)

law Word.lt_trans:
  for n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  for h1: IsLT(Word.cmp(n, a, b))
  for h2: IsLT(Word.cmp(n, b, c))
  {Word.cmp(n, a, c) == LT{} : Cmp}

def Word.lt_trans(n, a, b, c, h1, h2):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          Empty.absurd({Word.cmp(0n, WNil{}, WNil{}) == LT{} : Cmp}, h1)
    case 1n+(+p):
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          Word.lt_cases(p, ab, bb, cb, at, bt, ct, Word.cmp(p, at, bt), Word.cmp(p, bt, ct), {==}, {==}, h1, h2,
            hx => hy => Word.lt_trans(p, at, bt, ct, hx, hy))

# ---- witness helpers: a witness for one comparison refutes an equation to another ----

def IsLT.neq_gt(u: Cmp, e: {u == GT{} : Cmp}, h: IsLT(u)) -> Empty:
  Cmp.trLT(GT{}, u, Equal.sym(Cmp, u, GT{}, e), h)

def IsEQ.neq_lt(u: Cmp, e: {u == LT{} : Cmp}, h: IsEQ(u)) -> Empty:
  Cmp.trEQ(LT{}, u, Equal.sym(Cmp, u, LT{}, e), h)

def IsEQ.neq_gt(u: Cmp, e: {u == GT{} : Cmp}, h: IsEQ(u)) -> Empty:
  Cmp.trEQ(GT{}, u, Equal.sym(Cmp, u, GT{}, e), h)

# ---- U32: the order is the word order on the payload ----

law U32.lt_trans:
  for +a: U32
  for +b: U32
  for +c: U32
  for h1: IsLT(U32.cmp(a, b))
  for h2: IsLT(U32.cmp(b, c))
  {U32.cmp(a, c) == LT{} : Cmp}

def U32.lt_trans(a, b, c, h1, h2):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      Word.lt_trans(32n, x, y, z, h1, h2)

law U32.eq_w:
  for a: U32
  for b: U32
  for h: IsEQ(U32.cmp(a, b))
  {a == b : U32}

def U32.eq_w(a, b, h):
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, Word.eq_w(32n, x, y, h))

# ---- the string comparison with a starting comparison: a non-EQ start is kept ----

law String.order.go_lt:
  for a: String
  for b: String
  {String.order.go(a, b, LT{}) == LT{} : Cmp}

def String.order.go_lt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{_}, +t}:
      {==}
    case SCon{Chr{_}, +t} SNil{}:
      {==}
    case SCon{Chr{_}, +t1} SCon{Chr{_}, +t2}:
      {==}

law String.order.go_gt:
  for a: String
  for b: String
  {String.order.go(a, b, GT{}) == GT{} : Cmp}

def String.order.go_gt(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{_}, +t}:
      {==}
    case SCon{Chr{_}, +t} SNil{}:
      {==}
    case SCon{Chr{_}, +t1} SCon{Chr{_}, +t2}:
      {==}

# ---- transitivity of the string order ----

law String.order.lt_cases:
  for +x: U32
  for +y: U32
  for +z: U32
  for +t1: String
  for +t2: String
  for +t3: String
  for p: Cmp
  for q: Cmp
  for ep: {U32.cmp(x, y) == p : Cmp}
  for ey: {U32.cmp(y, z) == q : Cmp}
  for h1: IsLT(String.order.go(t1, t2, p))
  for h2: IsLT(String.order.go(t2, t3, q))
  for ih: IsLT(String.order(t1, t2)) -> IsLT(String.order(t2, t3)) -> {String.order(t1, t3) == LT{} : Cmp}
  {String.order.go(t1, t3, U32.cmp(x, z)) == LT{} : Cmp}

def String.order.lt_cases(x, y, z, t1, t2, t3, p, q, ep, ey, h1, h2, ih):
  match p q:
    case LT{} LT{}:
      Equal.trans(Cmp,
        String.order.go(t1, t3, U32.cmp(x, z)),
        String.order.go(t1, t3, LT{}),
        LT{},
        Equal.cong(Cmp, Cmp, c => String.order.go(t1, t3, c), U32.cmp(x, z), LT{},
          U32.lt_trans(x, y, z, IsLT.to(U32.cmp(x, y), ep), IsLT.to(U32.cmp(y, z), ey))),
        String.order.go_lt(t1, t3))
    case LT{} EQ{}:
      Equal.trans(Cmp,
        String.order.go(t1, t3, U32.cmp(x, z)),
        String.order.go(t1, t3, LT{}),
        LT{},
        Equal.cong(Cmp, Cmp, c => String.order.go(t1, t3, c), U32.cmp(x, z), LT{},
          Equal.trans(Cmp, U32.cmp(x, z), U32.cmp(x, y), LT{},
            Equal.sym(Cmp, U32.cmp(x, y), U32.cmp(x, z),
              Equal.cong(U32, Cmp, w => U32.cmp(x, w), y, z, U32.eq_w(y, z, IsEQ.to(U32.cmp(y, z), ey)))),
            ep)),
        String.order.go_lt(t1, t3))
    case LT{} GT{}:
      Empty.absurd({String.order.go(t1, t3, U32.cmp(x, z)) == LT{} : Cmp},
        IsLT.neq_gt(String.order.go(t2, t3, GT{}), String.order.go_gt(t2, t3), h2))
    case EQ{} LT{}:
      Equal.trans(Cmp,
        String.order.go(t1, t3, U32.cmp(x, z)),
        String.order.go(t1, t3, LT{}),
        LT{},
        Equal.cong(Cmp, Cmp, c => String.order.go(t1, t3, c), U32.cmp(x, z), LT{},
          Equal.trans(Cmp, U32.cmp(x, z), U32.cmp(y, z), LT{},
            Equal.cong(U32, Cmp, w => U32.cmp(w, z), x, y, U32.eq_w(x, y, IsEQ.to(U32.cmp(x, y), ep))),
            ey)),
        String.order.go_lt(t1, t3))
    case EQ{} EQ{}:
      Equal.trans(Cmp,
        String.order.go(t1, t3, U32.cmp(x, z)),
        String.order.go(t1, t3, EQ{}),
        LT{},
        Equal.cong(Cmp, Cmp, c => String.order.go(t1, t3, c), U32.cmp(x, z), EQ{},
          Equal.trans(Cmp, U32.cmp(x, z), U32.cmp(y, z), EQ{},
            Equal.cong(U32, Cmp, w => U32.cmp(w, z), x, y, U32.eq_w(x, y, IsEQ.to(U32.cmp(x, y), ep))),
            ey)),
        ih(h1, h2))
    case EQ{} GT{}:
      Empty.absurd({String.order.go(t1, t3, U32.cmp(x, z)) == LT{} : Cmp},
        IsLT.neq_gt(String.order.go(t2, t3, GT{}), String.order.go_gt(t2, t3), h2))
    case GT{} LT{}:
      Empty.absurd({String.order.go(t1, t3, U32.cmp(x, z)) == LT{} : Cmp},
        IsLT.neq_gt(String.order.go(t1, t2, GT{}), String.order.go_gt(t1, t2), h1))
    case GT{} EQ{}:
      Empty.absurd({String.order.go(t1, t3, U32.cmp(x, z)) == LT{} : Cmp},
        IsLT.neq_gt(String.order.go(t1, t2, GT{}), String.order.go_gt(t1, t2), h1))
    case GT{} GT{}:
      Empty.absurd({String.order.go(t1, t3, U32.cmp(x, z)) == LT{} : Cmp},
        IsLT.neq_gt(String.order.go(t1, t2, GT{}), String.order.go_gt(t1, t2), h1))

law String.order.lt_trans:
  for +a: String
  for +b: String
  for +c: String
  for h1: IsLT(String.order(a, b))
  for h2: IsLT(String.order(b, c))
  {String.order(a, c) == LT{} : Cmp}

def String.order.lt_trans(a, b, c, h1, h2):
  match a b c:
    case SNil{} SNil{} SNil{}:
      Empty.absurd({String.order(SNil{}, SNil{}) == LT{} : Cmp}, h1)
    case SNil{} SNil{} SCon{Chr{+z}, +t3}:
      Empty.absurd({String.order(SNil{}, SCon{Chr{z}, t3}) == LT{} : Cmp}, h1)
    case SNil{} SCon{Chr{+y}, +t2} SNil{}:
      Empty.absurd({String.order(SNil{}, SNil{}) == LT{} : Cmp}, h2)
    case SNil{} SCon{Chr{+y}, +t2} SCon{Chr{+z}, +t3}:
      {==}
    case SCon{Chr{+x}, +t1} SNil{} SNil{}:
      Empty.absurd({String.order(SCon{Chr{x}, t1}, SNil{}) == LT{} : Cmp}, h1)
    case SCon{Chr{+x}, +t1} SNil{} SCon{Chr{+z}, +t3}:
      Empty.absurd({String.order(SCon{Chr{x}, t1}, SCon{Chr{z}, t3}) == LT{} : Cmp}, h1)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} SNil{}:
      Empty.absurd({String.order(SCon{Chr{x}, t1}, SNil{}) == LT{} : Cmp}, h2)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2} SCon{Chr{+z}, +t3}:
      String.order.lt_cases(x, y, z, t1, t2, t3, U32.cmp(x, y), U32.cmp(y, z), {==}, {==}, h1, h2,
        hh1 => hh2 => String.order.lt_trans(t1, t2, t3, hh1, hh2))

# ---- EQ means equal: an EQ comparison of two strings makes them equal ----

law String.order.eq_cases:
  for +x: U32
  for +y: U32
  for +t1: String
  for +t2: String
  for p: Cmp
  for ep: {U32.cmp(x, y) == p : Cmp}
  for h: IsEQ(String.order.go(t1, t2, p))
  for ih: IsEQ(String.order(t1, t2)) -> {t1 == t2 : String}
  {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}

def String.order.eq_cases(x, y, t1, t2, p, ep, h, ih):
  match p:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String},
        IsEQ.neq_lt(String.order.go(t1, t2, LT{}), String.order.go_lt(t1, t2), h))
    case EQ{}:
      Equal.trans(String,
        SCon{Chr{x}, t1},
        SCon{Chr{y}, t1},
        SCon{Chr{y}, t2},
        Equal.cong(U32, String, w => SCon{Chr{w}, t1}, x, y, U32.eq_w(x, y, IsEQ.to(U32.cmp(x, y), ep))),
        Equal.cong(String, String, w => SCon{Chr{y}, w}, t1, t2, ih(h)))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String},
        IsEQ.neq_gt(String.order.go(t1, t2, GT{}), String.order.go_gt(t1, t2), h))

law String.order.eq_w:
  for a: String
  for b: String
  for h: IsEQ(String.order(a, b))
  {a == b : String}

def String.order.eq_w(a, b, h):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{+x}, +t}:
      Empty.absurd({SNil{} == SCon{Chr{x}, t} : String}, h)
    case SCon{Chr{+x}, +t} SNil{}:
      Empty.absurd({SCon{Chr{x}, t} == SNil{} : String}, h)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      String.order.eq_cases(x, y, t1, t2, U32.cmp(x, y), {==}, h,
        hh => String.order.eq_w(t1, t2, hh))
