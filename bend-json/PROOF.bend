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

# Law 4: no raw control characters
# ---------------------------------

def ge_of_nlt(c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      %e : BM(_, Unit, {Cmp.is_ge(LT{}) == True{} : Bool})
      Unit{}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ka_plain(+x: U32, b: Bool, eb: {U32.is_lt(x, 32) == b : Bool},
  e: {T.Esc.kind.a(x, b) == T.KPlain{} : T.CKind}) -> {U32.is_lt(x, 32) == False{} : Bool}:
  match b:
    case True{}:
      %e : KM(_, {U32.is_lt(x, 32) == False{} : Bool}, Unit, Unit, Unit)
      Unit{}
    case False{}:
      eb

# a plain char is at least U+0020
def plain_ge(+x: U32, e: {T.Esc.kind(x) == T.KPlain{} : T.CKind}) ->
  {U32.is_ge(x, 32) == True{} : Bool}:
  ge_of_nlt(U32.cmp(x, 32), ka_plain(x, U32.is_lt(x, 32), {==}, e))

# Spec.ctl_free: every lemma takes the claim for the text after it (h) and gives it
# for the text with the new chars in front

def ctl_ok(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, -r: String, h: {Spec.ctl_free(r) == True{} : Bool}) ->
  {Spec.ctl_free(T.Esc.ctl(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n)), r)) == True{} : Bool}:
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      h
    case False{} False{} False{} False{} True{}:
      h
    case False{} False{} False{} True{} False{}:
      h
    case False{} False{} False{} True{} True{}:
      h
    case False{} False{} True{} False{} False{}:
      h
    case False{} False{} True{} False{} True{}:
      h
    case False{} False{} True{} True{} False{}:
      h
    case False{} False{} True{} True{} True{}:
      h
    case False{} True{} False{} False{} False{}:
      h
    case False{} True{} False{} False{} True{}:
      h
    case False{} True{} False{} True{} False{}:
      h
    case False{} True{} False{} True{} True{}:
      h
    case False{} True{} True{} False{} False{}:
      h
    case False{} True{} True{} False{} True{}:
      h
    case False{} True{} True{} True{} False{}:
      h
    case False{} True{} True{} True{} True{}:
      h
    case True{} False{} False{} False{} False{}:
      h
    case True{} False{} False{} False{} True{}:
      h
    case True{} False{} False{} True{} False{}:
      h
    case True{} False{} False{} True{} True{}:
      h
    case True{} False{} True{} False{} False{}:
      h
    case True{} False{} True{} False{} True{}:
      h
    case True{} False{} True{} True{} False{}:
      h
    case True{} False{} True{} True{} True{}:
      h
    case True{} True{} False{} False{} False{}:
      h
    case True{} True{} False{} False{} True{}:
      h
    case True{} True{} False{} True{} False{}:
      h
    case True{} True{} False{} True{} True{}:
      h
    case True{} True{} True{} False{} False{}:
      h
    case True{} True{} True{} False{} True{}:
      h
    case True{} True{} True{} True{} False{}:
      h
    case True{} True{} True{} True{} True{}:
      h

def char_k_ok(+x: U32, k: T.CKind, e: {T.Esc.kind(x) == k : T.CKind}, -r: String,
  h: {Spec.ctl_free(r) == True{} : Bool}) -> {Spec.ctl_free(T.Esc.char.k(x, k, r)) == True{} : Bool}:
  match k:
    case T.KPlain{}:
      %Equal.sym(Bool, U32.is_ge(x, 32), True{}, plain_ge(x, e)) : {Bool.and(_, Spec.ctl_free(r)) == True{} : Bool}
      h
    case T.KQuote{}:
      h
    case T.KBack{}:
      h
    case T.KCtl{}:
      ctl_split(y => {Spec.ctl_free(T.Esc.ctl(y, r)) == True{} : Bool},
        b0 => b1 => b2 => b3 => b4 => ctl_ok(b0, b1, b2, b3, b4, r, h), x)(e)

def char_ok(c: Char, -r: String, h: {Spec.ctl_free(r) == True{} : Bool}) -> {Spec.ctl_free(T.Esc.char(c, r)) == True{} : Bool}:
  match c:
    case Chr{+x}:
      char_k_ok(x, T.Esc.kind(x), {==}, r, h)

def esc_ok(s: String, -acc: String, h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(T.Esc.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      h
    case SCon{c, +t}:
      char_ok(c, T.Esc.go(t, acc), esc_ok(t, acc, h))

def digit_ok(d: D.Digit, -acc: String, h: {Spec.ctl_free(acc) == True{} : Bool}) ->
  {Spec.ctl_free(SCon{D.Digit.to_char(d), acc}) == True{} : Bool}:
  match d:
    case D.D0{}:
      h
    case D.D1{}:
      h
    case D.D2{}:
      h
    case D.D3{}:
      h
    case D.D4{}:
      h
    case D.D5{}:
      h
    case D.D6{}:
      h
    case D.D7{}:
      h
    case D.D8{}:
      h
    case D.D9{}:
      h

def dshow_ok(c: List<&2, D.Digit>, -acc: String, h: {Spec.ctl_free(acc) == True{} : Bool}) ->
  {Spec.ctl_free(D.Dec.show(c, acc)) == True{} : Bool}:
  match c:
    case Nil{}:
      h
    case +d <> t:
      dshow_ok(t, SCon{D.Digit.to_char(d), acc}, digit_ok(d, acc, h))

def zeros_ok(n: Nat, -acc: String, h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Str.zeros(n, acc)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+p:
      zeros_ok(p, acc, h)

def sign_ok(neg: Bool, -s: String, h: {Spec.ctl_free(s) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.sign(neg, s)) == True{} : Bool}:
  match neg:
    case True{}:
      h
    case False{}:
      h

def esign_ok(neg: Bool, -s: String, h: {Spec.ctl_free(s) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.esign(neg, s)) == True{} : Bool}:
  match neg:
    case True{}:
      h
    case False{}:
      h

def exp_ok(+c: List<&2, D.Digit>, +eneg: Bool, +e: List<&2, D.Digit>, -acc: String,
  h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.exp(c, eneg, e, acc)) == True{} : Bool}:
  dshow_ok(c, SCon{'e', D.Num.show.esign(eneg, D.Dec.show(e, acc))},
    esign_ok(eneg, D.Dec.show(e, acc), dshow_ok(e, acc, h)))

def pos_fit_ok(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, -acc: String, fit: Bool,
  h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.pos.fit(c, e, acc, fit)) == True{} : Bool}:
  match fit:
    case True{}:
      dshow_ok(c, D.Str.zeros(D.Dec.to_nat(e), acc), zeros_ok(D.Dec.to_nat(e), acc, h))
    case False{}:
      exp_ok(c, False{}, e, acc, h)

def pos_ok(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, -acc: String, small: Bool,
  h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.pos(c, e, acc, small)) == True{} : Bool}:
  match small:
    case True{}:
      pos_fit_ok(c, e, acc, Nat.is_le(Nat.add(List.length(&2, D.Digit, c),
        D.Dec.to_nat(e)), 21n), h)
    case False{}:
      exp_ok(c, False{}, e, acc, h)

def neg_zeros_ok(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat,
  -acc: String, fit: Bool, h: {Spec.ctl_free(acc) == True{} : Bool}) ->
  {Spec.ctl_free(D.Num.show.neg.zeros(c, e, k, l, acc, fit)) == True{} : Bool}:
  match fit:
    case True{}:
      zeros_ok(Nat.sub(k, l), D.Dec.show(c, acc), dshow_ok(c, acc, h))
    case False{}:
      exp_ok(c, True{}, e, acc, h)

def neg_point_ok(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat,
  -acc: String, inside: Bool, h: {Spec.ctl_free(acc) == True{} : Bool}) ->
  {Spec.ctl_free(D.Num.show.neg.point(c, e, k, l, acc, inside)) == True{} : Bool}:
  match inside:
    case True{}:
      dshow_ok(List.drop(&2, D.Digit, c, k),
        SCon{'.', D.Dec.show(List.take(&2, D.Digit, c, k), acc)},
        dshow_ok(List.take(&2, D.Digit, c, k), acc, h))
    case False{}:
      neg_zeros_ok(c, e, k, l, acc, Nat.is_le(Nat.sub(k, l), 5n), h)

def neg_ok(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, -acc: String, small: Bool,
  h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.neg(c, e, acc, small)) == True{} : Bool}:
  match small:
    case True{}:
      neg_point_ok(c, e, D.Dec.to_nat(e), List.length(&2, D.Digit, c), acc,
        Nat.is_lt(D.Dec.to_nat(e), List.length(&2, D.Digit, c)), h)
    case False{}:
      exp_ok(c, True{}, e, acc, h)

def body_ok(+c: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>, -acc: String,
  h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show.body(c, eneg, e, acc)) == True{} : Bool}:
  match eneg e:
    case False{} Nil{}:
      dshow_ok(c, acc, h)
    case False{} Con{+x, +t}:
      pos_ok(c, x <> t, acc, Nat.is_le(List.length(&2, D.Digit, x <> t), 2n), h)
    case True{} +m:
      neg_ok(c, m, acc, Nat.is_le(List.length(&2, D.Digit, m), 6n), h)

def num_ok(n: D.Num, -acc: String, h: {Spec.ctl_free(acc) == True{} : Bool}) -> {Spec.ctl_free(D.Num.show(n, acc)) == True{} : Bool}:
  match n:
    case D.Num{neg, Nil{}, eneg, e}:
      h
    case D.Num{neg, +x <> +t, +eneg, +e}:
      sign_ok(neg, D.Num.show.body(x <> t, eneg, e, acc),
        body_ok(x <> t, eneg, e, acc, h))

# Spec.ctl_free_nl: every lemma takes the claim for the text after it (h) and gives it
# for the text with the new chars in front

def ctl_ok_nl(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, -r: String, h: {Spec.ctl_free_nl(r) == True{} : Bool}) ->
  {Spec.ctl_free_nl(T.Esc.ctl(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n)), r)) == True{} : Bool}:
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      h
    case False{} False{} False{} False{} True{}:
      h
    case False{} False{} False{} True{} False{}:
      h
    case False{} False{} False{} True{} True{}:
      h
    case False{} False{} True{} False{} False{}:
      h
    case False{} False{} True{} False{} True{}:
      h
    case False{} False{} True{} True{} False{}:
      h
    case False{} False{} True{} True{} True{}:
      h
    case False{} True{} False{} False{} False{}:
      h
    case False{} True{} False{} False{} True{}:
      h
    case False{} True{} False{} True{} False{}:
      h
    case False{} True{} False{} True{} True{}:
      h
    case False{} True{} True{} False{} False{}:
      h
    case False{} True{} True{} False{} True{}:
      h
    case False{} True{} True{} True{} False{}:
      h
    case False{} True{} True{} True{} True{}:
      h
    case True{} False{} False{} False{} False{}:
      h
    case True{} False{} False{} False{} True{}:
      h
    case True{} False{} False{} True{} False{}:
      h
    case True{} False{} False{} True{} True{}:
      h
    case True{} False{} True{} False{} False{}:
      h
    case True{} False{} True{} False{} True{}:
      h
    case True{} False{} True{} True{} False{}:
      h
    case True{} False{} True{} True{} True{}:
      h
    case True{} True{} False{} False{} False{}:
      h
    case True{} True{} False{} False{} True{}:
      h
    case True{} True{} False{} True{} False{}:
      h
    case True{} True{} False{} True{} True{}:
      h
    case True{} True{} True{} False{} False{}:
      h
    case True{} True{} True{} False{} True{}:
      h
    case True{} True{} True{} True{} False{}:
      h
    case True{} True{} True{} True{} True{}:
      h

def char_k_ok_nl(+x: U32, k: T.CKind, e: {T.Esc.kind(x) == k : T.CKind}, -r: String,
  h: {Spec.ctl_free_nl(r) == True{} : Bool}) -> {Spec.ctl_free_nl(T.Esc.char.k(x, k, r)) == True{} : Bool}:
  match k:
    case T.KPlain{}:
      %Equal.sym(Bool, U32.is_ge(x, 32), True{}, plain_ge(x, e)) : {Bool.and(Bool.or(_, U32.is_eq(x, 10)), Spec.ctl_free_nl(r)) == True{} : Bool}
      h
    case T.KQuote{}:
      h
    case T.KBack{}:
      h
    case T.KCtl{}:
      ctl_split(y => {Spec.ctl_free_nl(T.Esc.ctl(y, r)) == True{} : Bool},
        b0 => b1 => b2 => b3 => b4 => ctl_ok_nl(b0, b1, b2, b3, b4, r, h), x)(e)

def char_ok_nl(c: Char, -r: String, h: {Spec.ctl_free_nl(r) == True{} : Bool}) -> {Spec.ctl_free_nl(T.Esc.char(c, r)) == True{} : Bool}:
  match c:
    case Chr{+x}:
      char_k_ok_nl(x, T.Esc.kind(x), {==}, r, h)

def esc_ok_nl(s: String, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(T.Esc.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      h
    case SCon{c, +t}:
      char_ok_nl(c, T.Esc.go(t, acc), esc_ok_nl(t, acc, h))

def digit_ok_nl(d: D.Digit, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(SCon{D.Digit.to_char(d), acc}) == True{} : Bool}:
  match d:
    case D.D0{}:
      h
    case D.D1{}:
      h
    case D.D2{}:
      h
    case D.D3{}:
      h
    case D.D4{}:
      h
    case D.D5{}:
      h
    case D.D6{}:
      h
    case D.D7{}:
      h
    case D.D8{}:
      h
    case D.D9{}:
      h

def dshow_ok_nl(c: List<&2, D.Digit>, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(D.Dec.show(c, acc)) == True{} : Bool}:
  match c:
    case Nil{}:
      h
    case +d <> t:
      dshow_ok_nl(t, SCon{D.Digit.to_char(d), acc}, digit_ok_nl(d, acc, h))

def zeros_ok_nl(n: Nat, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Str.zeros(n, acc)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+p:
      zeros_ok_nl(p, acc, h)

def sign_ok_nl(neg: Bool, -s: String, h: {Spec.ctl_free_nl(s) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.sign(neg, s)) == True{} : Bool}:
  match neg:
    case True{}:
      h
    case False{}:
      h

def esign_ok_nl(neg: Bool, -s: String, h: {Spec.ctl_free_nl(s) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.esign(neg, s)) == True{} : Bool}:
  match neg:
    case True{}:
      h
    case False{}:
      h

def exp_ok_nl(+c: List<&2, D.Digit>, +eneg: Bool, +e: List<&2, D.Digit>, -acc: String,
  h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.exp(c, eneg, e, acc)) == True{} : Bool}:
  dshow_ok_nl(c, SCon{'e', D.Num.show.esign(eneg, D.Dec.show(e, acc))},
    esign_ok_nl(eneg, D.Dec.show(e, acc), dshow_ok_nl(e, acc, h)))

def pos_fit_ok_nl(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, -acc: String, fit: Bool,
  h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.pos.fit(c, e, acc, fit)) == True{} : Bool}:
  match fit:
    case True{}:
      dshow_ok_nl(c, D.Str.zeros(D.Dec.to_nat(e), acc), zeros_ok_nl(D.Dec.to_nat(e), acc, h))
    case False{}:
      exp_ok_nl(c, False{}, e, acc, h)

def pos_ok_nl(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, -acc: String, small: Bool,
  h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.pos(c, e, acc, small)) == True{} : Bool}:
  match small:
    case True{}:
      pos_fit_ok_nl(c, e, acc, Nat.is_le(Nat.add(List.length(&2, D.Digit, c),
        D.Dec.to_nat(e)), 21n), h)
    case False{}:
      exp_ok_nl(c, False{}, e, acc, h)

def neg_zeros_ok_nl(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat,
  -acc: String, fit: Bool, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(D.Num.show.neg.zeros(c, e, k, l, acc, fit)) == True{} : Bool}:
  match fit:
    case True{}:
      zeros_ok_nl(Nat.sub(k, l), D.Dec.show(c, acc), dshow_ok_nl(c, acc, h))
    case False{}:
      exp_ok_nl(c, True{}, e, acc, h)

def neg_point_ok_nl(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat,
  -acc: String, inside: Bool, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(D.Num.show.neg.point(c, e, k, l, acc, inside)) == True{} : Bool}:
  match inside:
    case True{}:
      dshow_ok_nl(List.drop(&2, D.Digit, c, k),
        SCon{'.', D.Dec.show(List.take(&2, D.Digit, c, k), acc)},
        dshow_ok_nl(List.take(&2, D.Digit, c, k), acc, h))
    case False{}:
      neg_zeros_ok_nl(c, e, k, l, acc, Nat.is_le(Nat.sub(k, l), 5n), h)

def neg_ok_nl(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, -acc: String, small: Bool,
  h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.neg(c, e, acc, small)) == True{} : Bool}:
  match small:
    case True{}:
      neg_point_ok_nl(c, e, D.Dec.to_nat(e), List.length(&2, D.Digit, c), acc,
        Nat.is_lt(D.Dec.to_nat(e), List.length(&2, D.Digit, c)), h)
    case False{}:
      exp_ok_nl(c, True{}, e, acc, h)

def body_ok_nl(+c: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>, -acc: String,
  h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show.body(c, eneg, e, acc)) == True{} : Bool}:
  match eneg e:
    case False{} Nil{}:
      dshow_ok_nl(c, acc, h)
    case False{} Con{+x, +t}:
      pos_ok_nl(c, x <> t, acc, Nat.is_le(List.length(&2, D.Digit, x <> t), 2n), h)
    case True{} +m:
      neg_ok_nl(c, m, acc, Nat.is_le(List.length(&2, D.Digit, m), 6n), h)

def num_ok_nl(n: D.Num, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) -> {Spec.ctl_free_nl(D.Num.show(n, acc)) == True{} : Bool}:
  match n:
    case D.Num{neg, Nil{}, eneg, e}:
      h
    case D.Num{neg, +x <> +t, +eneg, +e}:
      sign_ok_nl(neg, D.Num.show.body(x <> t, eneg, e, acc),
        body_ok_nl(x <> t, eneg, e, acc, h))

# the compact printer, by the same descent as Pr.go
def go_ok(v: V.Json, mode: Nat, -acc: String, h: {Spec.ctl_free(acc) == True{} : Bool}) ->
  {Spec.ctl_free(Pr.Pr.go(v, mode, acc)) == True{} : Bool}:
  match v mode:
    case V.JNull{} _:
      h
    case V.JBool{True{}} _:
      h
    case V.JBool{False{}} _:
      h
    case V.JNum{n} _:
      num_ok(n, acc, h)
    case V.JStr{s} _:
      esc_ok(s, SCon{'"', acc}, h)
    case V.JArr{xs} 1n+m:
      go_ok(V.JArr{xs}, m, SCon{']', acc}, h)
    case V.JArr{Nil{}} 0n:
      h
    case V.JArr{x <> Nil{}} 0n:
      go_ok(x, 1n, acc, h)
    case V.JArr{x <> (+y <> +t)} 0n:
      go_ok(x, 1n, SCon{',', Pr.Pr.go(V.JArr{y <> t}, 0n, acc)},
        go_ok(V.JArr{y <> t}, 0n, acc, h))
    case V.JObj{ms} 1n+m:
      go_ok(V.JObj{ms}, m, SCon{'}', acc}, h)
    case V.JObj{Nil{}} 0n:
      h
    case V.JObj{V.Mem{k, +x} <> Nil{}} 0n:
      esc_ok(k, SCon{'"', SCon{':', Pr.Pr.go(x, 1n, acc)}}, go_ok(x, 1n, acc, h))
    case V.JObj{V.Mem{k, +x} <> (+y <> +t)} 0n:
      esc_ok(k, SCon{'"', SCon{':', Pr.Pr.go(x, 1n, SCon{',', Pr.Pr.go(V.JObj{y <> t}, 0n, acc)})}},
        go_ok(x, 1n, SCon{',', Pr.Pr.go(V.JObj{y <> t}, 0n, acc)},
          go_ok(V.JObj{y <> t}, 0n, acc, h)))

def Laws.no_control_compact(v):
  go_ok(v, 1n, SNil{}, {==})

def spaces_ok(n: Nat, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(Pr.Pr.spaces(n, acc)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+p:
      spaces_ok(p, acc, h)

def nl_ok(+ind: Nat, +lvl: Nat, -acc: String, h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(Pr.Pr.nl(ind, lvl, acc)) == True{} : Bool}:
  spaces_ok(Nat.mul(lvl, ind), acc, h)

# the pretty printer, by the same descent as Pr.pp
def pp_ok(v: V.Json, mode: Nat, +ind: Nat, +lvl: Nat, -acc: String,
  h: {Spec.ctl_free_nl(acc) == True{} : Bool}) ->
  {Spec.ctl_free_nl(Pr.Pr.pp(v, mode, ind, lvl, acc)) == True{} : Bool}:
  match v mode:
    case V.JNull{} _:
      h
    case V.JBool{True{}} _:
      h
    case V.JBool{False{}} _:
      h
    case V.JNum{n} _:
      num_ok_nl(n, acc, h)
    case V.JStr{s} _:
      esc_ok_nl(s, SCon{'"', acc}, h)
    case V.JArr{Nil{}} 1n+m:
      h
    case V.JArr{+x <> +t} 1n+m:
      pp_ok(V.JArr{x <> t}, m, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{']', acc}),
        nl_ok(ind, lvl, SCon{']', acc}, h))
    case V.JArr{Nil{}} 0n:
      h
    case V.JArr{+x <> Nil{}} 0n:
      nl_ok(ind, lvl, Pr.Pr.pp(x, 1n, ind, lvl, acc), pp_ok(x, 1n, ind, lvl, acc, h))
    case V.JArr{+x <> (+y <> +t)} 0n:
      nl_ok(ind, lvl, Pr.Pr.pp(x, 1n, ind, lvl, SCon{',', Pr.Pr.pp(V.JArr{y <> t}, 0n, ind, lvl, acc)}),
        pp_ok(x, 1n, ind, lvl, SCon{',', Pr.Pr.pp(V.JArr{y <> t}, 0n, ind, lvl, acc)},
          pp_ok(V.JArr{y <> t}, 0n, ind, lvl, acc, h)))
    case V.JObj{Nil{}} 1n+m:
      h
    case V.JObj{+x <> +t} 1n+m:
      pp_ok(V.JObj{x <> t}, m, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{'}', acc}),
        nl_ok(ind, lvl, SCon{'}', acc}, h))
    case V.JObj{Nil{}} 0n:
      h
    case V.JObj{V.Mem{+k, +x} <> Nil{}} 0n:
      nl_ok(ind, lvl, T.quote(k, SCon{':', SCon{' ', Pr.Pr.pp(x, 1n, ind, lvl, acc)}}),
        esc_ok_nl(k, SCon{'"', SCon{':', SCon{' ', Pr.Pr.pp(x, 1n, ind, lvl, acc)}}},
          pp_ok(x, 1n, ind, lvl, acc, h)))
    case V.JObj{V.Mem{+k, +x} <> (+y <> +t)} 0n:
      nl_ok(ind, lvl, T.quote(k, SCon{':', SCon{' ', Pr.Pr.pp(x, 1n, ind, lvl,
          SCon{',', Pr.Pr.pp(V.JObj{y <> t}, 0n, ind, lvl, acc)})}}),
        esc_ok_nl(k, SCon{'"', SCon{':', SCon{' ', Pr.Pr.pp(x, 1n, ind, lvl,
            SCon{',', Pr.Pr.pp(V.JObj{y <> t}, 0n, ind, lvl, acc)})}}},
          pp_ok(x, 1n, ind, lvl, SCon{',', Pr.Pr.pp(V.JObj{y <> t}, 0n, ind, lvl, acc)},
            pp_ok(V.JObj{y <> t}, 0n, ind, lvl, acc, h))))

def Laws.no_control_pretty(ind, v):
  pp_ok(v, 1n, ind, 0n, SNil{}, {==})
