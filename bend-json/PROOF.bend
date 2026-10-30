# PROOF.bend: the proofs of LAWS.bend. Run `bend PROOF.bend`.
#
# A law is a def whose type is its claim: a match is a case split, a
# self-call the induction hypothesis, and %e : P rewrites the goal P[b]
# into P[a] with e : {a == b}. A computed value is split by passing it to
# a lemma beside an equation that names it (b, {f(x) == b}).

import Base
import ./decimal.bend as D
import ./value.bend as V
import ./text.bend as T
import ./parser.bend as P
import ./printer.bend as Pr
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws

# Motives: a type picked by a constructor. A rewrite through one turns a
# clash such as {False{} == True{}} into a goal of Unit.

def BM(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def CM(c: Cmp, lt: Type, eq: Type, gt: Type) -> Type:
  match c:
    case LT{}:
      lt
    case EQ{}:
      eq
    case GT{}:
      gt

def KM(k: T.CKind, p: Type, q: Type, b: Type, c: Type) -> Type:
  match k:
    case T.KPlain{}:
      p
    case T.KQuote{}:
      q
    case T.KBack{}:
      b
    case T.KCtl{}:
      c

# Words
# -----
# U32 is Word(32n), 32 Bools, least significant first; U32.cmp is
# Word.cmp, decided by the highest bit that differs.

def bcmp_eq(a: Bool, b: Bool, e: {Bool.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      %e : CM(_, Unit, {False{} == True{} : Bool}, Unit)
      Unit{}
    case True{} False{}:
      %e : CM(_, Unit, {True{} == False{} : Bool}, Unit)
      Unit{}
    case True{} True{}:
      {==}

def fin_eq(ab: Bool, bb: Bool, t: Cmp, e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}) ->
  {t == EQ{} : Cmp} & {ab == bb : Bool}:
  match t:
    case LT{}:
      %e : CM(_, Unit, {LT{} == EQ{} : Cmp} & {ab == bb : Bool}, Unit)
      Unit{}
    case EQ{}:
      ({==}, bcmp_eq(ab, bb, e))
    case GT{}:
      %e : CM(_, Unit, {GT{} == EQ{} : Cmp} & {ab == bb : Bool}, Unit)
      Unit{}

def wcmp_eq.fin(-p: Nat, -ab: Bool, -at: Word(p), -bb: Bool, -bt: Word(p),
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  h: {Word.cmp(p, at, bt) == EQ{} : Cmp} & {ab == bb : Bool}) ->
  {WCon{ab, at} == WCon{bb, bt} : Word(1n+p)}:
  (e1, e2) = h
  %rec(e1) : {WCon{ab, at} == WCon{bb, _} : Word(1n+p)}
  %e2 : {WCon{ab, at} == WCon{_, at} : Word(1n+p)}
  {==}

# words that compare EQ are equal
def wcmp_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          e => wcmp_eq.fin(p, ab, at, bb, bt, wcmp_eq(p, at, bt),
            fin_eq(ab, bb, Word.cmp(p, at, bt), e))

def ciseq(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      %e : BM(_, {LT{} == EQ{} : Cmp}, Unit)
      Unit{}
    case GT{}:
      %e : BM(_, {GT{} == EQ{} : Cmp}, Unit)
      Unit{}

def ciselt(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      %e : BM(_, {EQ{} == LT{} : Cmp}, Unit)
      Unit{}
    case GT{}:
      %e : BM(_, {GT{} == LT{} : Cmp}, Unit)
      Unit{}

# U32.is_eq(x, y) holds only for x == y
def u32_eq(+x: U32, +y: U32, e: {U32.is_eq(x, y) == True{} : Bool}) -> {x == y : U32}:
  match x y:
    case U32{a} U32{b}:
      %wcmp_eq(32n, a, b, ciseq(Word.cmp(32n, a, b), e)) : {U32{a} == U32{_} : U32}
      {==}

# below a bit 0 of the other word, LT needs LT from the bits under it
def peel(b: Bool, c: Cmp, e: {Word.cmp.fin(b, False{}, c) == LT{} : Cmp}) ->
  {c == LT{} : Cmp}:
  match b c:
    case b0 LT{}:
      {==}
    case False{} EQ{}:
      %e : CM(_, {EQ{} == LT{} : Cmp}, Unit, Unit)
      Unit{}
    case True{} EQ{}:
      %e : CM(_, {EQ{} == LT{} : Cmp}, Unit, Unit)
      Unit{}
    case b0 GT{}:
      %e : CM(_, {GT{} == LT{} : Cmp}, Unit, Unit)
      Unit{}

def cmp_zero_nlt.base(e: {EQ{} == LT{} : Cmp}) -> Empty:
  %e : CM(_, Empty, Unit, Unit)
  Unit{}

# nothing is below the zero word
def cmp_zero_nlt(+n: Nat, +w: Word(n)) ->
  {Word.cmp(n, w, Word.zero(n)) == LT{} : Cmp} -> Empty:
  match n:
    case 0n:
      match w:
        case WNil{}:
          e => cmp_zero_nlt.base(e)
    case 1n+p:
      match w:
        case WCon{a, t}:
          e => cmp_zero_nlt(p, t)(peel(a, Word.cmp(p, t, Word.zero(p)), e))

# at the set bit 5 of 32: LT needs this bit 0 and EQ above it
def top(b: Bool, r: Cmp, nlt: {r == LT{} : Cmp} -> Empty,
  e: {Word.cmp.fin(b, True{}, r) == LT{} : Cmp}) -> {b == False{} : Bool} & {r == EQ{} : Cmp}:
  match b r:
    case b0 LT{}:
      Empty.absurd({b0 == False{} : Bool} & {LT{} == EQ{} : Cmp}, nlt({==}))
    case False{} EQ{}:
      ({==}, {==})
    case True{} EQ{}:
      %e : CM(_, {True{} == False{} : Bool} & {EQ{} == EQ{} : Cmp}, Unit, Unit)
      Unit{}
    case b0 GT{}:
      %e : CM(_, {b0 == False{} : Bool} & {GT{} == EQ{} : Cmp}, Unit, Unit)
      Unit{}

def lt32_bits.fin(+hi: Word(26n), -b5: Bool,
  h: {b5 == False{} : Bool} & {Word.cmp(26n, hi, Word.zero(26n)) == EQ{} : Cmp}) ->
  {b5 == False{} : Bool} & {hi == Word.zero(26n) : Word(26n)}:
  (eb, er) = h
  (eb, wcmp_eq(26n, hi, Word.zero(26n))(er))

def Lo5(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, hi: Word(26n)) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, hi}}}}}}}

# a U32 below 32 has only its five low bits
def lt32_bits(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool,
  +hi: Word(26n), e: {U32.is_lt(Lo5(b0, b1, b2, b3, b4, b5, hi), 32) == True{} : Bool}) ->
  {b5 == False{} : Bool} & {hi == Word.zero(26n) : Word(26n)}:
  +r = Word.cmp(26n, hi, Word.zero(26n))
  +c5 = Word.cmp.fin(b5, True{}, r)
  +c4 = Word.cmp.fin(b4, False{}, c5)
  +c3 = Word.cmp.fin(b3, False{}, c4)
  +c2 = Word.cmp.fin(b2, False{}, c3)
  +c1 = Word.cmp.fin(b1, False{}, c2)
  e0 = ciselt(Word.cmp.fin(b0, False{}, c1), e)
  e5 = peel(b4, c5, peel(b3, c4, peel(b2, c3, peel(b1, c2, peel(b0, c1, e0)))))
  lt32_bits.fin(hi, b5, top(b5, Word.cmp(26n, hi, Word.zero(26n)), cmp_zero_nlt(26n, hi), e5))

# Law 1: escaping
# ---------------

# a raw char decodes to itself after escape: the claim, per char
def CharG(c: Char, acc: String, rest: String) -> Type:
  {T.Str.run(rest, T.SCont{T.StrBody{SCon{c, acc}}})
    == T.Str.run(T.Esc.char(c, rest), T.SCont{T.StrBody{acc}}) : T.SRes}

def CtlG(x: U32, acc: String, rest: String) -> Type:
  {T.Str.run(rest, T.SCont{T.StrBody{SCon{Chr{x}, acc}}})
    == T.Str.run(T.Esc.ctl(x, rest), T.SCont{T.StrBody{acc}}) : T.SRes}

# each of the 32 control chars, by computation
def ctl_case(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, -acc: String, -rest: String) ->
  CtlG(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n)), acc, rest):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# what Esc.kind's verdict says about the char
def kc_not_ctl(b: Bool, e: {T.Esc.kind.c(b) == T.KCtl{} : T.CKind}) -> Empty:
  match b:
    case True{}:
      %e : KM(_, Unit, Unit, Unit, Empty)
      Unit{}
    case False{}:
      %e : KM(_, Unit, Unit, Unit, Empty)
      Unit{}

def kb_not_ctl(+x: U32, q: Bool, e: {T.Esc.kind.b(x, q) == T.KCtl{} : T.CKind}) -> Empty:
  match q:
    case True{}:
      %e : KM(_, Unit, Unit, Unit, Empty)
      Unit{}
    case False{}:
      kc_not_ctl(U32.is_eq(x, 92), e)

def ka_ctl(+x: U32, b: Bool, eb: {U32.is_lt(x, 32) == b : Bool},
  e: {T.Esc.kind.a(x, b) == T.KCtl{} : T.CKind}) -> {U32.is_lt(x, 32) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      Empty.absurd({U32.is_lt(x, 32) == True{} : Bool}, kb_not_ctl(x, U32.is_eq(x, 34), e))

def kind_ctl(+x: U32, e: {T.Esc.kind(x) == T.KCtl{} : T.CKind}) ->
  {U32.is_lt(x, 32) == True{} : Bool}:
  ka_ctl(x, U32.is_lt(x, 32), {==}, e)

def kc_not_q(b: Bool, e: {T.Esc.kind.c(b) == T.KQuote{} : T.CKind}) -> Empty:
  match b:
    case True{}:
      %e : KM(_, Unit, Empty, Unit, Unit)
      Unit{}
    case False{}:
      %e : KM(_, Unit, Empty, Unit, Unit)
      Unit{}

def kb_q(+x: U32, q: Bool, eq: {U32.is_eq(x, 34) == q : Bool},
  e: {T.Esc.kind.b(x, q) == T.KQuote{} : T.CKind}) -> {x == 34 : U32}:
  match q:
    case True{}:
      u32_eq(x, 34, eq)
    case False{}:
      Empty.absurd({x == 34 : U32}, kc_not_q(U32.is_eq(x, 92), e))

def ka_q(+x: U32, b: Bool, e: {T.Esc.kind.a(x, b) == T.KQuote{} : T.CKind}) -> {x == 34 : U32}:
  match b:
    case True{}:
      %e : KM(_, Unit, {x == 34 : U32}, Unit, Unit)
      Unit{}
    case False{}:
      kb_q(x, U32.is_eq(x, 34), {==}, e)

def kind_quote(+x: U32, e: {T.Esc.kind(x) == T.KQuote{} : T.CKind}) -> {x == 34 : U32}:
  ka_q(x, U32.is_lt(x, 32), e)

def kc_back(+x: U32, b: Bool, eb: {U32.is_eq(x, 92) == b : Bool},
  e: {T.Esc.kind.c(b) == T.KBack{} : T.CKind}) -> {x == 92 : U32}:
  match b:
    case True{}:
      u32_eq(x, 92, eb)
    case False{}:
      %e : KM(_, Unit, Unit, {x == 92 : U32}, Unit)
      Unit{}

def kb_back(+x: U32, q: Bool, e: {T.Esc.kind.b(x, q) == T.KBack{} : T.CKind}) -> {x == 92 : U32}:
  match q:
    case True{}:
      %e : KM(_, Unit, Unit, {x == 92 : U32}, Unit)
      Unit{}
    case False{}:
      kc_back(x, U32.is_eq(x, 92), {==}, e)

def ka_back(+x: U32, b: Bool, e: {T.Esc.kind.a(x, b) == T.KBack{} : T.CKind}) -> {x == 92 : U32}:
  match b:
    case True{}:
      %e : KM(_, Unit, Unit, {x == 92 : U32}, Unit)
      Unit{}
    case False{}:
      kb_back(x, U32.is_eq(x, 34), e)

def kind_back(+x: U32, e: {T.Esc.kind(x) == T.KBack{} : T.CKind}) -> {x == 92 : U32}:
  ka_back(x, U32.is_lt(x, 32), e)

def ctl_split.fin(-Q: U32 -> Type, -b0: Bool, -b1: Bool, -b2: Bool, -b3: Bool, -b4: Bool,
  -b5: Bool, -hi: Word(26n), q: Q(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n))),
  h: {b5 == False{} : Bool} & {hi == Word.zero(26n) : Word(26n)}) ->
  Q(Lo5(b0, b1, b2, b3, b4, b5, hi)):
  (eb, eh) = h
  %Equal.sym(Bool, b5, False{}, eb) : Q(Lo5(b0, b1, b2, b3, b4, _, hi))
  %Equal.sym(Word(26n), hi, Word.zero(26n), eh) : Q(Lo5(b0, b1, b2, b3, b4, False{}, _))
  q

# a claim Q about every control char x (Esc.kind(x) == KCtl) follows from
# Q at each of the 32 words with only the five low bits
def ctl_split(-Q: U32 -> Type,
  f: @b0: Bool -> @b1: Bool -> @b2: Bool -> @b3: Bool -> @b4: Bool ->
    Q(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n))),
  +x: U32) -> {T.Esc.kind(x) == T.KCtl{} : T.CKind} -> Q(x):
  match x:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +hi}}}}}}}:
      e => ctl_split.fin(Q, b0, b1, b2, b3, b4, b5, hi, f(b0, b1, b2, b3, b4),
        lt32_bits(b0, b1, b2, b3, b4, b5, hi, kind_ctl(Lo5(b0, b1, b2, b3, b4, b5, hi), e)))

# a control char escapes and decodes to itself
def ctl(+x: U32, -acc: String, -rest: String) ->
  {T.Esc.kind(x) == T.KCtl{} : T.CKind} -> CtlG(x, acc, rest):
  ctl_split(y => CtlG(y, acc, rest),
    b0 => b1 => b2 => b3 => b4 => ctl_case(b0, b1, b2, b3, b4, acc, rest), x)

def char_k(+x: U32, k: T.CKind, e: {T.Esc.kind(x) == k : T.CKind}, -acc: String,
  -rest: String) ->
  {T.Str.run(rest, T.SCont{T.StrBody{SCon{Chr{x}, acc}}})
    == T.Str.run(T.Esc.char.k(x, k, rest), T.SCont{T.StrBody{acc}}) : T.SRes}:
  match k:
    case T.KPlain{}:
      %Equal.sym(T.CKind, T.Esc.kind(x), T.KPlain{}, e) :
        {T.Str.run(rest, T.SCont{T.StrBody{SCon{Chr{x}, acc}}})
          == T.Str.run(rest, T.Str.raw(acc, x, _)) : T.SRes}
      {==}
    case T.KQuote{}:
      %Equal.sym(U32, x, 34, kind_quote(x, e)) :
        {T.Str.run(rest, T.SCont{T.StrBody{SCon{Chr{_}, acc}}})
          == T.Str.run(T.Esc.char.k(x, T.KQuote{}, rest), T.SCont{T.StrBody{acc}}) : T.SRes}
      {==}
    case T.KBack{}:
      %Equal.sym(U32, x, 92, kind_back(x, e)) :
        {T.Str.run(rest, T.SCont{T.StrBody{SCon{Chr{_}, acc}}})
          == T.Str.run(T.Esc.char.k(x, T.KBack{}, rest), T.SCont{T.StrBody{acc}}) : T.SRes}
      {==}
    case T.KCtl{}:
      ctl(x, acc, rest)(e)

def char_l(c: Char, -acc: String, -rest: String) -> CharG(c, acc, rest):
  match c:
    case Chr{+x}:
      char_k(x, T.Esc.kind(x), {==}, acc, rest)

# escaping s and decoding it pushes s's chars onto the decoded ones
def esc_go(s: String, -acc: String, -rest: String) ->
  {T.Str.run(rest, T.SCont{T.StrBody{String.reverse.go(s, acc)}})
    == T.Str.run(T.Esc.go(s, rest), T.SCont{T.StrBody{acc}}) : T.SRes}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      Equal.trans(T.SRes,
        T.Str.run(rest, T.SCont{T.StrBody{String.reverse.go(t, SCon{c, acc})}}),
        T.Str.run(T.Esc.go(t, rest), T.SCont{T.StrBody{SCon{c, acc}}}),
        T.Str.run(T.Esc.char(c, T.Esc.go(t, rest)), T.SCont{T.StrBody{acc}}),
        esc_go(t, SCon{c, acc}, rest), char_l(c, acc, T.Esc.go(t, rest)))

def rev_rev(s: String, -a: String) ->
  {String.reverse.go(a, s) == String.reverse.go(String.reverse.go(s, a), SNil{}) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rev_rev(t, SCon{h, a})

def Laws.escape_roundtrip(s):
  %esc_go(s, SNil{}, SNil{}) : {T.Str.done(_) == Some{s} : Maybe<&2, String>}
  %rev_rev(s, SNil{}) : {Some{_} == Some{s} : Maybe<&2, String>}
  {==}
