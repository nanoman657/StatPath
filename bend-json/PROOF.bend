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

# Law 2: numbers
# --------------
# The parser reads a number in SNum states; R(s, st) is a run from st.

def R(s: String, st: P.St) -> P.Out:
  P.P.run(s, P.Go{st})

def SN(c: P.Ctx, ns: P.NumSt) -> P.St:
  P.SNum{c, ns}

def NZ(d: D.Digit) -> Data:
  match d:
    case D.D0{}:
      Empty
    case _:
      Unit

# not the lone digit 0, after which a digit is a leading zero
def NotZ(a: List<&2, D.Digit>) -> Data:
  match a:
    case Con{h, Nil{}}:
      NZ(h)
    case _:
      Unit

# a char that the number machine passes on as a step
def num_go(-c: P.Ctx, -ns: P.NumSt, -ch: Char, -ns2: P.NumSt,
  e: {P.N.step(ns, ch) == P.NGo{ns2} : P.NRes}, -rest: String) ->
  {R(rest, SN(c, ns2)) == R(SCon{ch, rest}, SN(c, ns)) : P.Out}:
  %Equal.sym(P.NRes, P.N.step(ns, ch), P.NGo{ns2}, e) :
    {R(rest, SN(c, ns2)) == P.P.run(rest, P.P.num(c, ch, _)) : P.Out}
  {==}

def int_one(neg: Bool, h: D.Digit, -d: D.Digit, nz: NZ(h)) ->
  {P.N.int.one(neg, h, d) == P.NGo{P.NInt{neg, [d, h]}} : P.NRes}:
  match h:
    case D.D0{}:
      Empty.absurd({P.N.int.one(neg, D.D0{}, d) == P.NGo{P.NInt{neg, [d, D.D0{}]}} : P.NRes}, nz)
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

def int_digit(neg: Bool, a: List<&2, D.Digit>, -d: D.Digit, nz: NotZ(a)) ->
  {P.N.int.digit(neg, a, d) == P.NGo{P.NInt{neg, d <> a}} : P.NRes}:
  match a:
    case Nil{}:
      {==}
    case Con{h, Nil{}}:
      int_one(neg, h, d, nz)
    case Con{h, Con{x, y}}:
      {==}

def digit_int(+neg: Bool, +a: List<&2, D.Digit>, d: D.Digit, nz: NotZ(a)) ->
  {P.N.step(P.NInt{neg, a}, D.Digit.to_char(d)) == P.NGo{P.NInt{neg, d <> a}} : P.NRes}:
  match d:
    case D.D0{}:
      int_digit(neg, a, D.D0{}, nz)
    case D.D1{}:
      int_digit(neg, a, D.D1{}, nz)
    case D.D2{}:
      int_digit(neg, a, D.D2{}, nz)
    case D.D3{}:
      int_digit(neg, a, D.D3{}, nz)
    case D.D4{}:
      int_digit(neg, a, D.D4{}, nz)
    case D.D5{}:
      int_digit(neg, a, D.D5{}, nz)
    case D.D6{}:
      int_digit(neg, a, D.D6{}, nz)
    case D.D7{}:
      int_digit(neg, a, D.D7{}, nz)
    case D.D8{}:
      int_digit(neg, a, D.D8{}, nz)
    case D.D9{}:
      int_digit(neg, a, D.D9{}, nz)

def digit_frac(-neg: Bool, -a: List<&2, D.Digit>, -fl: Nat, d: D.Digit) ->
  {P.N.step(P.NFrac{neg, a, fl}, D.Digit.to_char(d)) == P.NGo{P.NFrac{neg, d <> a, 1n+fl}} : P.NRes}:
  match d:
    case D.D0{}:
      {==}
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

def digit_exp(-neg: Bool, -a: List<&2, D.Digit>, -fl: Nat, -eneg: Bool, -e: List<&2, D.Digit>,
  d: D.Digit) ->
  {P.N.step(P.NExpD{neg, a, fl, eneg, e}, D.Digit.to_char(d))
    == P.NGo{P.NExpD{neg, a, fl, eneg, d <> e}} : P.NRes}:
  match d:
    case D.D0{}:
      {==}
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

def notz_app(t: List<&2, D.Digit>, -a0: D.Digit, -a1: List<&2, D.Digit>, nz: NotZ(a0 <> a1)) ->
  NotZ(List.append(&2, D.Digit, t, a0 <> a1)):
  match t:
    case Nil{}:
      nz
    case Con{x, Nil{}}:
      Unit{}
    case Con{x, Con{y, z}}:
      Unit{}

# int digits onto a nonempty acc
def rint(c: List<&2, D.Digit>, +neg: Bool, +a0: D.Digit, +a1: List<&2, D.Digit>,
  +nz: NotZ(a0 <> a1), -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NInt{neg, List.append(&2, D.Digit, c, a0 <> a1)}))
    == R(D.Dec.show(c, rest), SN(ctx, P.NInt{neg, a0 <> a1})) : P.Out}:
  match c:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %rint(t, neg, a0, a1, nz, ctx, SCon{D.Digit.to_char(d), rest}) :
        {R(rest, SN(ctx, P.NInt{neg, List.append(&2, D.Digit, d <> t, a0 <> a1)})) == _ : P.Out}
      num_go(ctx, P.NInt{neg, List.append(&2, D.Digit, t, a0 <> a1)}, D.Digit.to_char(d),
        P.NInt{neg, d <> List.append(&2, D.Digit, t, a0 <> a1)},
        digit_int(neg, List.append(&2, D.Digit, t, a0 <> a1), d, notz_app(t, a0, a1, nz)), rest)

def rfrac(c: List<&2, D.Digit>, +neg: Bool, +a: List<&2, D.Digit>, +fl: Nat, -ctx: P.Ctx,
  -rest: String) ->
  {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, c, a),
    Nat.add(List.length(&2, D.Digit, c), fl)}))
    == R(D.Dec.show(c, rest), SN(ctx, P.NFrac{neg, a, fl})) : P.Out}:
  match c:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %rfrac(t, neg, a, fl, ctx, SCon{D.Digit.to_char(d), rest}) :
        {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, d <> t, a),
          Nat.add(List.length(&2, D.Digit, d <> t), fl)})) == _ : P.Out}
      num_go(ctx, P.NFrac{neg, List.append(&2, D.Digit, t, a), Nat.add(List.length(&2, D.Digit, t), fl)},
        D.Digit.to_char(d), P.NFrac{neg, d <> List.append(&2, D.Digit, t, a),
        1n+Nat.add(List.length(&2, D.Digit, t), fl)},
        digit_frac(neg, List.append(&2, D.Digit, t, a), Nat.add(List.length(&2, D.Digit, t), fl), d),
        rest)

def rexp(c: List<&2, D.Digit>, +neg: Bool, +a: List<&2, D.Digit>, +fl: Nat, +eneg: Bool,
  +e: List<&2, D.Digit>, -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NExpD{neg, a, fl, eneg, List.append(&2, D.Digit, c, e)}))
    == R(D.Dec.show(c, rest), SN(ctx, P.NExpD{neg, a, fl, eneg, e})) : P.Out}:
  match c:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %rexp(t, neg, a, fl, eneg, e, ctx, SCon{D.Digit.to_char(d), rest}) :
        {R(rest, SN(ctx, P.NExpD{neg, a, fl, eneg, List.append(&2, D.Digit, d <> t, e)})) == _ : P.Out}
      num_go(ctx, P.NExpD{neg, a, fl, eneg, List.append(&2, D.Digit, t, e)}, D.Digit.to_char(d),
        P.NExpD{neg, a, fl, eneg, d <> List.append(&2, D.Digit, t, e)},
        digit_exp(neg, a, fl, eneg, List.append(&2, D.Digit, t, e), d), rest)

# n zero digits in front of xs
def Dz(n: Nat, xs: List<&2, D.Digit>) -> List<&2, D.Digit>:
  match n:
    case 0n:
      xs
    case 1n+p:
      D.D0{} <> Dz(p, xs)

def zc(p: Nat, -a: List<&2, D.Digit>) ->
  {D.D0{} <> Dz(p, a) == Dz(p, D.D0{} <> a) : List<&2, D.Digit>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %zc(q, a) : {D.D0{} <> D.D0{} <> Dz(q, a) == D.D0{} <> _ : List<&2, D.Digit>}
      {==}

def add_succ(p: Nat, -q: Nat) -> {1n+Nat.add(p, q) == Nat.add(p, 1n+q) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+r:
      %add_succ(r, q) : {2n+Nat.add(r, q) == 1n+_ : Nat}
      {==}

def rzint(k: Nat, +neg: Bool, +a0: D.Digit, +a1: List<&2, D.Digit>, nz: NotZ(a0 <> a1),
  -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NInt{neg, Dz(k, a0 <> a1)}))
    == R(D.Str.zeros(k, rest), SN(ctx, P.NInt{neg, a0 <> a1})) : P.Out}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      %num_go(ctx, P.NInt{neg, a0 <> a1}, '0', P.NInt{neg, D.D0{} <> a0 <> a1},
        digit_int(neg, a0 <> a1, D.D0{}, nz), D.Str.zeros(p, rest)) :
        {R(rest, SN(ctx, P.NInt{neg, Dz(1n+p, a0 <> a1)})) == _ : P.Out}
      %rzint(p, neg, D.D0{}, a0 <> a1, Unit{}, ctx, rest) :
        {R(rest, SN(ctx, P.NInt{neg, Dz(1n+p, a0 <> a1)})) == _ : P.Out}
      %zc(p, a0 <> a1) :
        {R(rest, SN(ctx, P.NInt{neg, Dz(1n+p, a0 <> a1)})) == R(rest, SN(ctx, P.NInt{neg, _})) : P.Out}
      {==}

def rzfrac(m: Nat, +neg: Bool, +a: List<&2, D.Digit>, +fl: Nat, -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NFrac{neg, Dz(m, a), Nat.add(m, fl)}))
    == R(D.Str.zeros(m, rest), SN(ctx, P.NFrac{neg, a, fl})) : P.Out}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %num_go(ctx, P.NFrac{neg, a, fl}, '0', P.NFrac{neg, D.D0{} <> a, 1n+fl},
        digit_frac(neg, a, fl, D.D0{}), D.Str.zeros(p, rest)) :
        {R(rest, SN(ctx, P.NFrac{neg, Dz(1n+p, a), Nat.add(1n+p, fl)})) == _ : P.Out}
      %rzfrac(p, neg, D.D0{} <> a, 1n+fl, ctx, rest) :
        {R(rest, SN(ctx, P.NFrac{neg, Dz(1n+p, a), Nat.add(1n+p, fl)})) == _ : P.Out}
      %zc(p, a) :
        {R(rest, SN(ctx, P.NFrac{neg, Dz(1n+p, a), Nat.add(1n+p, fl)}))
          == R(rest, SN(ctx, P.NFrac{neg, _, Nat.add(p, 1n+fl)})) : P.Out}
      %add_succ(p, fl) :
        {R(rest, SN(ctx, P.NFrac{neg, Dz(1n+p, a), Nat.add(1n+p, fl)}))
          == R(rest, SN(ctx, P.NFrac{neg, D.D0{} <> Dz(p, a), _})) : P.Out}
      {==}

# where a number's first digit is read: after '-', or as a value's start
def Start(neg: Bool, close: Bool, c: P.Ctx) -> P.St:
  match neg:
    case True{}:
      P.SNum{c, P.NSign{True{}}}
    case False{}:
      P.SVal{close, c}

def start_digit(neg: Bool, -close: Bool, -c: P.Ctx, d: D.Digit) ->
  {P.P.step(Start(neg, close, c), D.Digit.to_char(d)) == P.Go{P.SNum{c, P.NInt{neg, [d]}}} : P.Step}:
  match neg d:
    case True{} D.D0{}:
      {==}
    case True{} D.D1{}:
      {==}
    case True{} D.D2{}:
      {==}
    case True{} D.D3{}:
      {==}
    case True{} D.D4{}:
      {==}
    case True{} D.D5{}:
      {==}
    case True{} D.D6{}:
      {==}
    case True{} D.D7{}:
      {==}
    case True{} D.D8{}:
      {==}
    case True{} D.D9{}:
      {==}
    case False{} D.D0{}:
      {==}
    case False{} D.D1{}:
      {==}
    case False{} D.D2{}:
      {==}
    case False{} D.D3{}:
      {==}
    case False{} D.D4{}:
      {==}
    case False{} D.D5{}:
      {==}
    case False{} D.D6{}:
      {==}
    case False{} D.D7{}:
      {==}
    case False{} D.D8{}:
      {==}
    case False{} D.D9{}:
      {==}

def nz_last(x: D.Digit, h: {D.Dec.is_norm([x]) == True{} : Bool}) -> NZ(x):
  match x:
    case D.D0{}:
      %h : BM(_, Empty, Unit)
      Unit{}
    case D.D1{}:
      Unit{}
    case D.D2{}:
      Unit{}
    case D.D3{}:
      Unit{}
    case D.D4{}:
      Unit{}
    case D.D5{}:
      Unit{}
    case D.D6{}:
      Unit{}
    case D.D7{}:
      Unit{}
    case D.D8{}:
      Unit{}
    case D.D9{}:
      Unit{}

def nz_tail(x: D.Digit, y: List<&2, D.Digit>, h: {D.Dec.is_norm(x <> y) == True{} : Bool}) ->
  NotZ(x <> y):
  match y:
    case Nil{}:
      nz_last(x, h)
    case Con{a, b}:
      Unit{}

# the int digits of a normalized c (top digit nonzero) from the number's start
def rsign(c1: List<&2, D.Digit>, +c0: D.Digit, +neg: Bool, +close: Bool,
  +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NInt{neg, c0 <> c1}))
    == R(D.Dec.show(c0 <> c1, rest), Start(neg, close, ctx)) : P.Out}:
  match c1:
    case Nil{}:
      %Equal.sym(P.Step, P.P.step(Start(neg, close, ctx), D.Digit.to_char(c0)),
        P.Go{SN(ctx, P.NInt{neg, [c0]})}, start_digit(neg, close, ctx, c0)) :
        {R(rest, SN(ctx, P.NInt{neg, [c0]})) == P.P.run(rest, _) : P.Out}
      {==}
    case Con{+x, +y}:
      %rsign(y, x, neg, close, h, ctx, SCon{D.Digit.to_char(c0), rest}) :
        {R(rest, SN(ctx, P.NInt{neg, c0 <> x <> y})) == _ : P.Out}
      num_go(ctx, P.NInt{neg, x <> y}, D.Digit.to_char(c0), P.NInt{neg, c0 <> x <> y},
        digit_int(neg, x <> y, c0, nz_tail(x, y, h)), rest)

# The state the parser is in after each print form
# -------------------------------------------------

def NS.exp(c: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>, neg: Bool) -> P.NumSt:
  P.NExpD{neg, c, 0n, eneg, List.append(&2, D.Digit, e, Nil{})}

def NS.pos.fit(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, neg: Bool, fit: Bool) -> P.NumSt:
  match fit:
    case True{}:
      P.NInt{neg, Dz(D.Dec.to_nat(e), c)}
    case False{}:
      NS.exp(c, False{}, e, neg)

def NS.pos(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, neg: Bool, small: Bool) -> P.NumSt:
  match small:
    case True{}:
      NS.pos.fit(c, e, neg, Nat.is_le(Nat.add(List.length(&2, D.Digit, c), D.Dec.to_nat(e)), 21n))
    case False{}:
      NS.exp(c, False{}, e, neg)

def NS.neg.zeros(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat, neg: Bool,
  fit: Bool) -> P.NumSt:
  match fit:
    case True{}:
      P.NFrac{neg, List.append(&2, D.Digit, c, Dz(Nat.sub(k, l), [D.D0{}])),
        Nat.add(List.length(&2, D.Digit, c), Nat.add(Nat.sub(k, l), 0n))}
    case False{}:
      NS.exp(c, True{}, e, neg)

def NS.neg.point(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat, neg: Bool,
  inside: Bool) -> P.NumSt:
  match inside:
    case True{}:
      P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, c, k), List.drop(&2, D.Digit, c, k)),
        Nat.add(List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)), 0n)}
    case False{}:
      NS.neg.zeros(c, e, k, l, neg, Nat.is_le(Nat.sub(k, l), 5n))

def NS.neg(+c: List<&2, D.Digit>, +e: List<&2, D.Digit>, neg: Bool, small: Bool) -> P.NumSt:
  match small:
    case True{}:
      NS.neg.point(c, e, D.Dec.to_nat(e), List.length(&2, D.Digit, c), neg,
        Nat.is_lt(D.Dec.to_nat(e), List.length(&2, D.Digit, c)))
    case False{}:
      NS.exp(c, True{}, e, neg)

def NS.body(+c: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>, neg: Bool) -> P.NumSt:
  match eneg e:
    case False{} Nil{}:
      P.NInt{neg, c}
    case False{} Con{+x, +t}:
      NS.pos(c, x <> t, neg, Nat.is_le(List.length(&2, D.Digit, x <> t), 2n))
    case True{} +m:
      NS.neg(c, m, neg, Nat.is_le(List.length(&2, D.Digit, m), 6n))

def NS(n: D.Num) -> P.NumSt:
  match n:
    case D.Num{neg, Nil{}, eneg, e}:
      P.NInt{False{}, [D.D0{}]}
    case D.Num{neg, +x <> +t, eneg, e}:
      NS.body(x <> t, eneg, e, neg)

# Each print form runs to its state
# ---------------------------------

def run_esign(+eneg: Bool, +neg: Bool, +c: List<&2, D.Digit>, +e: List<&2, D.Digit>,
  -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NExpD{neg, c, 0n, eneg, List.append(&2, D.Digit, e, Nil{})}))
    == R(D.Num.show.esign(eneg, D.Dec.show(e, rest)), SN(ctx, P.NExp{neg, c, 0n})) : P.Out}:
  match eneg:
    case True{}:
      %num_go(ctx, P.NExp{neg, c, 0n}, '-', P.NExpD{neg, c, 0n, True{}, Nil{}}, {==},
        D.Dec.show(e, rest)) :
        {R(rest, SN(ctx, P.NExpD{neg, c, 0n, True{}, List.append(&2, D.Digit, e, Nil{})})) == _ : P.Out}
      rexp(e, neg, c, 0n, True{}, Nil{}, ctx, rest)
    case False{}:
      %num_go(ctx, P.NExp{neg, c, 0n}, '+', P.NExpD{neg, c, 0n, False{}, Nil{}}, {==},
        D.Dec.show(e, rest)) :
        {R(rest, SN(ctx, P.NExpD{neg, c, 0n, False{}, List.append(&2, D.Digit, e, Nil{})})) == _ : P.Out}
      rexp(e, neg, c, 0n, False{}, Nil{}, ctx, rest)

def run_exp(+c0: D.Digit, +c1: List<&2, D.Digit>, +eneg: Bool, +e: List<&2, D.Digit>, +neg: Bool,
  +close: Bool, +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, NS.exp(c0 <> c1, eneg, e, neg)))
    == R(D.Num.show.exp(c0 <> c1, eneg, e, rest), Start(neg, close, ctx)) : P.Out}:
  %rsign(c1, c0, neg, close, h, ctx, SCon{'e', D.Num.show.esign(eneg, D.Dec.show(e, rest))}) :
    {R(rest, SN(ctx, NS.exp(c0 <> c1, eneg, e, neg))) == _ : P.Out}
  %num_go(ctx, P.NInt{neg, c0 <> c1}, 'e', P.NExp{neg, c0 <> c1, 0n}, {==},
    D.Num.show.esign(eneg, D.Dec.show(e, rest))) :
    {R(rest, SN(ctx, NS.exp(c0 <> c1, eneg, e, neg))) == _ : P.Out}
  run_esign(eneg, neg, c0 <> c1, e, ctx, rest)

def run_pos_fit(+c0: D.Digit, +c1: List<&2, D.Digit>, +e: List<&2, D.Digit>, +neg: Bool,
  +close: Bool, fit: Bool, +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx,
  -rest: String) ->
  {R(rest, SN(ctx, NS.pos.fit(c0 <> c1, e, neg, fit)))
    == R(D.Num.show.pos.fit(c0 <> c1, e, rest, fit), Start(neg, close, ctx)) : P.Out}:
  match fit:
    case True{}:
      %rsign(c1, c0, neg, close, h, ctx, D.Str.zeros(D.Dec.to_nat(e), rest)) :
        {R(rest, SN(ctx, NS.pos.fit(c0 <> c1, e, neg, True{}))) == _ : P.Out}
      rzint(D.Dec.to_nat(e), neg, c0, c1, nz_tail(c0, c1, h), ctx, rest)
    case False{}:
      run_exp(c0, c1, False{}, e, neg, close, h, ctx, rest)

def run_pos(+c0: D.Digit, +c1: List<&2, D.Digit>, +e: List<&2, D.Digit>, +neg: Bool,
  +close: Bool, small: Bool, +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx,
  -rest: String) ->
  {R(rest, SN(ctx, NS.pos(c0 <> c1, e, neg, small)))
    == R(D.Num.show.pos(c0 <> c1, e, rest, small), Start(neg, close, ctx)) : P.Out}:
  match small:
    case True{}:
      run_pos_fit(c0, c1, e, neg, close, Nat.is_le(Nat.add(List.length(&2, D.Digit, c0 <> c1),
        D.Dec.to_nat(e)), 21n), h, ctx, rest)
    case False{}:
      run_exp(c0, c1, False{}, e, neg, close, h, ctx, rest)

def run_neg_zeros(+c0: D.Digit, +c1: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat,
  +neg: Bool, +close: Bool, fit: Bool, +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool},
  -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, NS.neg.zeros(c0 <> c1, e, k, l, neg, fit)))
    == R(D.Num.show.neg.zeros(c0 <> c1, e, k, l, rest, fit), Start(neg, close, ctx)) : P.Out}:
  match fit:
    case True{}:
      %Equal.sym(P.Step, P.P.step(Start(neg, close, ctx), D.Digit.to_char(D.D0{})),
        P.Go{SN(ctx, P.NInt{neg, [D.D0{}]})}, start_digit(neg, close, ctx, D.D0{})) :
        {R(rest, SN(ctx, NS.neg.zeros(c0 <> c1, e, k, l, neg, True{})))
          == P.P.run(SCon{'.', D.Str.zeros(Nat.sub(k, l), D.Dec.show(c0 <> c1, rest))}, _) : P.Out}
      %num_go(ctx, P.NInt{neg, [D.D0{}]}, '.', P.NFrac{neg, [D.D0{}], 0n}, {==},
        D.Str.zeros(Nat.sub(k, l), D.Dec.show(c0 <> c1, rest))) :
        {R(rest, SN(ctx, NS.neg.zeros(c0 <> c1, e, k, l, neg, True{}))) == _ : P.Out}
      %rzfrac(Nat.sub(k, l), neg, [D.D0{}], 0n, ctx, D.Dec.show(c0 <> c1, rest)) :
        {R(rest, SN(ctx, NS.neg.zeros(c0 <> c1, e, k, l, neg, True{}))) == _ : P.Out}
      rfrac(c0 <> c1, neg, Dz(Nat.sub(k, l), [D.D0{}]), Nat.add(Nat.sub(k, l), 0n), ctx, rest)
    case False{}:
      run_exp(c0, c1, True{}, e, neg, close, h, ctx, rest)

def BNil(xs: List<&2, D.Digit>, t: Type, f: Type) -> Type:
  match xs:
    case Nil{}:
      t
    case Con{a, b}:
      f

# below the length, dropping k digits leaves some
law drop_ne:
  for +c: List<&2, D.Digit>
  for +k: Nat
  for hl: {Nat.is_lt(k, List.length(&2, D.Digit, c)) == True{} : Bool}
  exs dh: D.Digit
  exs dt: List<&2, D.Digit>
  {List.drop(&2, D.Digit, c, k) == dh <> dt : List<&2, D.Digit>}

def drop_ne(c, k, hl):
  match c k:
    case Nil{} 0n:
      %hl : BM(_, Sigma<&1, &1, D.Digit, dh => Sigma<&1, &1, List<&2, D.Digit>,
        dt => {List.drop(&2, D.Digit, Nil{}, 0n) == dh <> dt : List<&2, D.Digit>}>>, Unit)
      Unit{}
    case Nil{} 1n+p:
      %hl : BM(_, Sigma<&1, &1, D.Digit, dh => Sigma<&1, &1, List<&2, D.Digit>,
        dt => {List.drop(&2, D.Digit, Nil{}, 1n+p) == dh <> dt : List<&2, D.Digit>}>>, Unit)
      Unit{}
    case Con{x, t} 0n:
      (x, t, {==})
    case Con{x, t} 1n+p:
      drop_ne(t, p, hl)

def drop_norm(c: List<&2, D.Digit>, k: Nat, h: {D.Dec.is_norm(c) == True{} : Bool}) ->
  {D.Dec.is_norm(List.drop(&2, D.Digit, c, k)) == True{} : Bool}:
  match c k:
    case Nil{} k0:
      {==}
    case Con{x, t} 0n:
      h
    case Con{x, Nil{}} 1n+p:
      {==}
    case Con{x, Con{y, z}} 1n+p:
      drop_norm(y <> z, p, h)

def run_point.at(+c: List<&2, D.Digit>, +k: Nat, +dh: D.Digit, +dt: List<&2, D.Digit>,
  +neg: Bool, +close: Bool, +hd: {D.Dec.is_norm(dh <> dt) == True{} : Bool}, -ctx: P.Ctx,
  -rest: String) ->
  {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, c, k), dh <> dt),
    Nat.add(List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)), 0n)}))
    == R(D.Dec.show(dh <> dt, SCon{'.', D.Dec.show(List.take(&2, D.Digit, c, k), rest)}),
      Start(neg, close, ctx)) : P.Out}:
  %rsign(dt, dh, neg, close, hd, ctx, SCon{'.', D.Dec.show(List.take(&2, D.Digit, c, k), rest)}) :
    {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, c, k), dh <> dt),
      Nat.add(List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)), 0n)})) == _ : P.Out}
  %num_go(ctx, P.NInt{neg, dh <> dt}, '.', P.NFrac{neg, dh <> dt, 0n}, {==},
    D.Dec.show(List.take(&2, D.Digit, c, k), rest)) :
    {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, c, k), dh <> dt),
      Nat.add(List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)), 0n)})) == _ : P.Out}
  rfrac(List.take(&2, D.Digit, c, k), neg, dh <> dt, 0n, ctx, rest)

def run_point(+c: List<&2, D.Digit>, +k: Nat, +neg: Bool, +close: Bool,
  +h: {D.Dec.is_norm(c) == True{} : Bool},
  w: Sigma<&1, &1, D.Digit, dh => Sigma<&1, &1, List<&2, D.Digit>,
    dt => {List.drop(&2, D.Digit, c, k) == dh <> dt : List<&2, D.Digit>}>>,
  -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, c, k),
    List.drop(&2, D.Digit, c, k)), Nat.add(List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)), 0n)}))
    == R(D.Dec.show(List.drop(&2, D.Digit, c, k), SCon{'.', D.Dec.show(List.take(&2, D.Digit, c, k), rest)}),
      Start(neg, close, ctx)) : P.Out}:
  (+dh, w2) = w
  (+dt, +eq) = w2
  +hd = Equal.trans(Bool, D.Dec.is_norm(dh <> dt), D.Dec.is_norm(List.drop(&2, D.Digit, c, k)), True{},
    Equal.sym(Bool, D.Dec.is_norm(List.drop(&2, D.Digit, c, k)), D.Dec.is_norm(dh <> dt),
      Equal.cong(List<&2, D.Digit>, Bool, x => D.Dec.is_norm(x), List.drop(&2, D.Digit, c, k), dh <> dt, eq)),
    drop_norm(c, k, h))
  %Equal.sym(List<&2, D.Digit>, List.drop(&2, D.Digit, c, k), dh <> dt, eq) :
    {R(rest, SN(ctx, P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, c, k), _),
      Nat.add(List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)), 0n)}))
      == R(D.Dec.show(_, SCon{'.', D.Dec.show(List.take(&2, D.Digit, c, k), rest)}),
        Start(neg, close, ctx)) : P.Out}
  run_point.at(c, k, dh, dt, neg, close, hd, ctx, rest)

def run_neg_point(+c0: D.Digit, +c1: List<&2, D.Digit>, +e: List<&2, D.Digit>, +k: Nat, +l: Nat,
  +neg: Bool, +close: Bool, inside: Bool,
  ei: {Nat.is_lt(k, List.length(&2, D.Digit, c0 <> c1)) == inside : Bool},
  +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, NS.neg.point(c0 <> c1, e, k, l, neg, inside)))
    == R(D.Num.show.neg.point(c0 <> c1, e, k, l, rest, inside), Start(neg, close, ctx)) : P.Out}:
  match inside:
    case True{}:
      run_point(c0 <> c1, k, neg, close, h, drop_ne(c0 <> c1, k, ei), ctx, rest)
    case False{}:
      run_neg_zeros(c0, c1, e, k, l, neg, close, Nat.is_le(Nat.sub(k, l), 5n), h, ctx, rest)

def run_neg(+c0: D.Digit, +c1: List<&2, D.Digit>, +e: List<&2, D.Digit>, +neg: Bool,
  +close: Bool, small: Bool, +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx,
  -rest: String) ->
  {R(rest, SN(ctx, NS.neg(c0 <> c1, e, neg, small)))
    == R(D.Num.show.neg(c0 <> c1, e, rest, small), Start(neg, close, ctx)) : P.Out}:
  match small:
    case True{}:
      run_neg_point(c0, c1, e, D.Dec.to_nat(e), List.length(&2, D.Digit, c0 <> c1), neg, close,
        Nat.is_lt(D.Dec.to_nat(e), List.length(&2, D.Digit, c0 <> c1)), {==}, h, ctx, rest)
    case False{}:
      run_exp(c0, c1, True{}, e, neg, close, h, ctx, rest)

def run_body(+c0: D.Digit, +c1: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>, +neg: Bool,
  +close: Bool, +h: {D.Dec.is_norm(c0 <> c1) == True{} : Bool}, -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, NS.body(c0 <> c1, eneg, e, neg)))
    == R(D.Num.show.body(c0 <> c1, eneg, e, rest), Start(neg, close, ctx)) : P.Out}:
  match eneg e:
    case False{} Nil{}:
      rsign(c1, c0, neg, close, h, ctx, rest)
    case False{} Con{+x, +t}:
      run_pos(c0, c1, x <> t, neg, close, Nat.is_le(List.length(&2, D.Digit, x <> t), 2n), h, ctx, rest)
    case True{} +m:
      run_neg(c0, c1, m, neg, close, Nat.is_le(List.length(&2, D.Digit, m), 6n), h, ctx, rest)

def run_sign(neg: Bool, -close: Bool, -ctx: P.Ctx, -b: String) ->
  {R(b, Start(neg, close, ctx)) == R(D.Num.show.sign(neg, b), P.SVal{close, ctx}) : P.Out}:
  match neg:
    case True{}:
      {==}
    case False{}:
      {==}

def and_true(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) ->
  {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, e)
    case False{}:
      %e : BM(_, {False{} == True{} : Bool} & {b == True{} : Bool}, Unit)
      Unit{}

# what is_norm says about a nonzero number
def NormF(x: D.Digit, t: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>) -> Type:
  NZ(x) & {D.Dec.is_norm(x <> t) == True{} : Bool} & {D.Num.is_norm.exp(eneg, e) == True{} : Bool}

def norm_split(x: D.Digit, +t: List<&2, D.Digit>, -neg: Bool, +eneg: Bool, +e: List<&2, D.Digit>,
  h: {D.Num.is_norm(D.Num{neg, x <> t, eneg, e}) == True{} : Bool}) -> NormF(x, t, eneg, e):
  match x:
    case D.D0{}:
      %h : BM(_, NormF(D.D0{}, t, eneg, e), Unit)
      Unit{}
    case D.D1{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D1{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D2{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D2{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D3{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D3{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D4{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D4{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D5{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D5{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D6{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D6{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D7{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D7{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D8{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D8{} <> t), D.Num.is_norm.exp(eneg, e), h))
    case D.D9{}:
      (Unit{}, and_true(D.Dec.is_norm(D.D9{} <> t), D.Num.is_norm.exp(eneg, e), h))

def run_num.at(+x: D.Digit, +t: List<&2, D.Digit>, +neg: Bool, +eneg: Bool, +e: List<&2, D.Digit>,
  +close: Bool, f: NormF(x, t, eneg, e), -ctx: P.Ctx, -rest: String) ->
  {R(rest, SN(ctx, NS(D.Num{neg, x <> t, eneg, e}))) == R(D.Num.show(D.Num{neg, x <> t, eneg, e}, rest),
    P.SVal{close, ctx}) : P.Out}:
  (nz, hs) = f
  (hc, he) = hs
  %run_sign(neg, close, ctx, D.Num.show.body(x <> t, eneg, e, rest)) :
    {R(rest, SN(ctx, NS(D.Num{neg, x <> t, eneg, e}))) == _ : P.Out}
  run_body(x, t, eneg, e, neg, close, hc, ctx, rest)

# a normalized number's text runs the parser from a value's start to NS(n)
def run_num(n: D.Num, +close: Bool, h: {D.Num.is_norm(n) == True{} : Bool}, -ctx: P.Ctx,
  -rest: String) ->
  {R(rest, SN(ctx, NS(n))) == R(D.Num.show(n, rest), P.SVal{close, ctx}) : P.Out}:
  match n:
    case D.Num{neg, Nil{}, eneg, e}:
      {==}
    case D.Num{+neg, +x <> +t, +eneg, +e}:
      run_num.at(x, t, neg, eneg, e, close, norm_split(x, t, neg, eneg, e, h), ctx, rest)

# What the state stands for
# -------------------------

def norm_one(d: D.Digit, h: {D.Dec.is_norm([d]) == True{} : Bool}) -> {[d] == D.Dec.norm.one(d) : List<&2, D.Digit>}:
  match d:
    case D.D0{}:
      %h : BM(_, {[D.D0{}] == D.Dec.norm.one(D.D0{}) : List<&2, D.Digit>}, Unit)
      Unit{}
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

def norm_id(c: List<&2, D.Digit>, h: {D.Dec.is_norm(c) == True{} : Bool}) -> {c == D.Dec.norm(c) : List<&2, D.Digit>}:
  match c:
    case Nil{}:
      {==}
    case Con{d, Nil{}}:
      norm_one(d, h)
    case Con{+d, Con{+y, +z}}:
      %norm_id(y <> z, h) : {d <> y <> z == D.Dec.norm.fin(d, _) : List<&2, D.Digit>}
      {==}

def strip_nz(x: D.Digit, -t: List<&2, D.Digit>, nz: NZ(x)) ->
  {(x <> t, 0n) == D.Dec.strip_low(x <> t) : List<&2, D.Digit> & Nat}:
  match x:
    case D.D0{}:
      Empty.absurd({(D.D0{} <> t, 0n) == D.Dec.strip_low(D.D0{} <> t) : List<&2, D.Digit> & Nat}, nz)
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

def strip_dz(k: Nat, -c: List<&2, D.Digit>, h: {(c, 0n) == D.Dec.strip_low(c) : List<&2, D.Digit> & Nat}) ->
  {(c, k) == D.Dec.strip_low(Dz(k, c)) : List<&2, D.Digit> & Nat}:
  match k:
    case 0n:
      h
    case 1n+p:
      %strip_dz(p, c, h) : {(c, 1n+p) == D.Dec.strip_low.inc(_) : List<&2, D.Digit> & Nat}
      {==}

def fin_dz(p: Nat, -x: D.Digit, -t: List<&2, D.Digit>) ->
  {D.D0{} <> Dz(p, x <> t) == D.Dec.norm.fin(D.D0{}, Dz(p, x <> t)) : List<&2, D.Digit>}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

def norm_dz(k: Nat, +x: D.Digit, +t: List<&2, D.Digit>, +h: {x <> t == D.Dec.norm(x <> t) : List<&2, D.Digit>}) ->
  {Dz(k, x <> t) == D.Dec.norm(Dz(k, x <> t)) : List<&2, D.Digit>}:
  match k:
    case 0n:
      h
    case 1n++p:
      %norm_dz(p, x, t, h) : {D.D0{} <> Dz(p, x <> t) == D.Dec.norm.fin(D.D0{}, _) : List<&2, D.Digit>}
      fin_dz(p, x, t)

def norm_zz(m: Nat) -> {Nil{} == D.Dec.norm(Dz(m, [D.D0{}])) : List<&2, D.Digit>}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %norm_zz(p) : {Nil{} == D.Dec.norm.fin(D.D0{}, _) : List<&2, D.Digit>}
      {==}

# zeros above a normalized c vanish
def norm_app(c1: List<&2, D.Digit>, +c0: D.Digit, +z: List<&2, D.Digit>, +hn: {D.Dec.is_norm(c0 <> c1) == True{} : Bool},
  +hz: {Nil{} == D.Dec.norm(z) : List<&2, D.Digit>}) ->
  {c0 <> c1 == D.Dec.norm(List.append(&2, D.Digit, c0 <> c1, z)) : List<&2, D.Digit>}:
  match c1:
    case Nil{}:
      %hz : {[c0] == D.Dec.norm.fin(c0, _) : List<&2, D.Digit>}
      norm_one(c0, hn)
    case Con{+y, +w}:
      %norm_app(w, y, z, hn, hz) : {c0 <> y <> w == D.Dec.norm.fin(c0, _) : List<&2, D.Digit>}
      {==}

def take_drop(c: List<&2, D.Digit>, k: Nat) ->
  {c == List.append(&2, D.Digit, List.take(&2, D.Digit, c, k), List.drop(&2, D.Digit, c, k)) : List<&2, D.Digit>}:
  match c k:
    case Nil{} k0:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n++p:
      %take_drop(t, p) : {x <> t == x <> _ : List<&2, D.Digit>}
      {==}

def len_take(c: List<&2, D.Digit>, k: Nat, h: {Nat.is_lt(k, List.length(&2, D.Digit, c)) == True{} : Bool}) ->
  {k == List.length(&2, D.Digit, List.take(&2, D.Digit, c, k)) : Nat}:
  match c k:
    case Nil{} 0n:
      %h : BM(_, {0n == 0n : Nat}, Unit)
      Unit{}
    case Nil{} 1n+p:
      %h : BM(_, {1n+p == 0n : Nat}, Unit)
      Unit{}
    case Con{x, t} 0n:
      {==}
    case Con{x, +t} 1n++p:
      %len_take(t, p, h) : {1n+p == 1n+_ : Nat}
      {==}

def add_zero(m: Nat) -> {m == Nat.add(m, 0n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_sub(k: Nat, l: Nat, h: {Nat.is_lt(k, l) == False{} : Bool}) ->
  {k == Nat.add(l, Nat.sub(k, l)) : Nat}:
  match k l:
    case 0n 0n:
      {==}
    case 1n+a 0n:
      {==}
    case 0n 1n+q:
      %h : BM(_, Unit, {0n == Nat.add(1n+q, Nat.sub(0n, 1n+q)) : Nat})
      Unit{}
    case 1n++a 1n++q:
      %add_sub(a, q, h) : {1n+a == 1n+_ : Nat}
      {==}

def append_nil(e: List<&2, D.Digit>) -> {e == List.append(&2, D.Digit, e, Nil{}) : List<&2, D.Digit>}:
  match e:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %append_nil(t) : {x <> t == x <> _ : List<&2, D.Digit>}
      {==}

def add_n_pos(k: Nat, -x: List<&2, D.Digit>) ->
  {D.SExp{False{}, D.Dec.iter(k, x)} == D.SExp.add_n(k, D.SExp{False{}, x}) : D.SExp}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      add_n_pos(p, D.Dec.inc(x))

def sub_n_neg(k: Nat, -x: List<&2, D.Digit>) ->
  {D.SExp{True{}, D.Dec.iter(k, x)} == D.SExp.sub_n(k, D.SExp{True{}, x}) : D.SExp}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      sub_n_neg(p, D.Dec.inc(x))

def iter_add(a: Nat, -b: Nat, -x: List<&2, D.Digit>) ->
  {D.Dec.iter(b, D.Dec.iter(a, x)) == D.Dec.iter(Nat.add(a, b), x) : List<&2, D.Digit>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      iter_add(p, b, D.Dec.inc(x))

def iter10(d: D.Digit, -x: List<&2, D.Digit>) -> {d <> D.Dec.inc(x) == D.Dec.iter(10n, d <> x) : List<&2, D.Digit>}:
  match d:
    case D.D0{}:
      {==}
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

def iter_mul(t: Nat, +d: D.Digit, +x: List<&2, D.Digit>) ->
  {d <> D.Dec.iter(t, x) == D.Dec.iter(Nat.mul(t, 10n), d <> x) : List<&2, D.Digit>}:
  match t:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(List<&2, D.Digit>, D.Dec.iter(Nat.mul(p, 10n), D.Dec.iter(10n, d <> x)),
        D.Dec.iter(Nat.add(10n, Nat.mul(p, 10n)), d <> x), iter_add(10n, Nat.mul(p, 10n), d <> x)) :
        {d <> D.Dec.iter(1n+p, x) == _ : List<&2, D.Digit>}
      %iter10(d, x) : {d <> D.Dec.iter(1n+p, x) == D.Dec.iter(Nat.mul(p, 10n), _) : List<&2, D.Digit>}
      iter_mul(p, d, D.Dec.inc(x))

def head0(p: Nat) ->
  {D.D0{} <> D.Dec.iter(1n+p, Nil{}) == D.Dec.iter(Nat.mul(1n+p, 10n), Nil{}) : List<&2, D.Digit>}:
  %Equal.sym(List<&2, D.Digit>, D.Dec.iter(Nat.mul(p, 10n), D.Dec.iter(10n, Nil{})),
    D.Dec.iter(Nat.add(10n, Nat.mul(p, 10n)), Nil{}), iter_add(10n, Nat.mul(p, 10n), Nil{})) :
    {D.D0{} <> D.Dec.iter(1n+p, Nil{}) == _ : List<&2, D.Digit>}
  iter_mul(p, D.D0{}, [D.D1{}])

def head(d: D.Digit, +p: Nat) ->
  {d <> D.Dec.iter(1n+p, Nil{}) == D.Dec.iter(Nat.mul(1n+p, 10n), D.Dec.iter(D.Digit.to_nat(d), Nil{})) : List<&2, D.Digit>}:
  match d:
    case D.D0{}:
      head0(p)
    case D.D1{}:
      iter_mul(1n+p, D.D1{}, Nil{})
    case D.D2{}:
      iter_mul(1n+p, D.D2{}, Nil{})
    case D.D3{}:
      iter_mul(1n+p, D.D3{}, Nil{})
    case D.D4{}:
      iter_mul(1n+p, D.D4{}, Nil{})
    case D.D5{}:
      iter_mul(1n+p, D.D5{}, Nil{})
    case D.D6{}:
      iter_mul(1n+p, D.D6{}, Nil{})
    case D.D7{}:
      iter_mul(1n+p, D.D7{}, Nil{})
    case D.D8{}:
      iter_mul(1n+p, D.D8{}, Nil{})
    case D.D9{}:
      iter_mul(1n+p, D.D9{}, Nil{})

def itn_step(+d: D.Digit, t: Nat, -y: D.Digit, -z: List<&2, D.Digit>, ih: {y <> z == D.Dec.iter(t, Nil{}) : List<&2, D.Digit>}) ->
  {d <> y <> z == D.Dec.iter(Nat.add(D.Digit.to_nat(d), Nat.mul(t, 10n)), Nil{}) : List<&2, D.Digit>}:
  match t:
    case 0n:
      %ih : BNil(_, {d <> y <> z == D.Dec.iter(Nat.add(D.Digit.to_nat(d), Nat.mul(0n, 10n)), Nil{}) : List<&2, D.Digit>}, Unit)
      Unit{}
    case 1n++p:
      %iter_add(D.Digit.to_nat(d), Nat.mul(1n+p, 10n), Nil{}) :
        {d <> y <> z == _ : List<&2, D.Digit>}
      %Equal.sym(List<&2, D.Digit>, y <> z, D.Dec.iter(1n+p, Nil{}), ih) :
        {d <> _ == D.Dec.iter(Nat.mul(1n+p, 10n), D.Dec.iter(D.Digit.to_nat(d), Nil{})) : List<&2, D.Digit>}
      head(d, p)

def itn_one(d: D.Digit, h: {D.Dec.is_norm([d]) == True{} : Bool}) ->
  {[d] == D.Dec.iter(D.Dec.to_nat([d]), Nil{}) : List<&2, D.Digit>}:
  match d:
    case D.D0{}:
      %h : BM(_, {[D.D0{}] == D.Dec.iter(D.Dec.to_nat([D.D0{}]), Nil{}) : List<&2, D.Digit>}, Unit)
      Unit{}
    case D.D1{}:
      {==}
    case D.D2{}:
      {==}
    case D.D3{}:
      {==}
    case D.D4{}:
      {==}
    case D.D5{}:
      {==}
    case D.D6{}:
      {==}
    case D.D7{}:
      {==}
    case D.D8{}:
      {==}
    case D.D9{}:
      {==}

# counting up from 0 to a normalized e's value gives e back
def iter_to_nat(e: List<&2, D.Digit>, h: {D.Dec.is_norm(e) == True{} : Bool}) ->
  {e == D.Dec.iter(D.Dec.to_nat(e), Nil{}) : List<&2, D.Digit>}:
  match e:
    case Nil{}:
      {==}
    case Con{d, Nil{}}:
      itn_one(d, h)
    case Con{+d, Con{+y, +z}}:
      itn_step(d, D.Dec.to_nat(y <> z), y, z, iter_to_nat(y <> z, h))

# the number a state stands for, and whether it may end there
def MK(ns: P.NumSt) -> D.Num:
  match ns:
    case P.NInt{neg, acc}:
      D.Num.make(neg, acc, False{}, Nil{}, 0n)
    case P.NFrac{neg, acc, fl}:
      D.Num.make(neg, acc, False{}, Nil{}, fl)
    case P.NExpD{neg, acc, fl, eneg, e}:
      D.Num.make(neg, acc, eneg, e, fl)
    case _:
      D.Num.zero()

def Ready(ns: P.NumSt) -> Data:
  match ns:
    case P.NInt{neg, acc}:
      Unit
    case P.NFrac{neg, acc, 0n}:
      Empty
    case P.NFrac{neg, acc, 1n+f}:
      Unit
    case P.NExpD{neg, acc, fl, eneg, Nil{}}:
      Empty
    case P.NExpD{neg, acc, fl, eneg, Con{x, t}}:
      Unit
    case _:
      Empty

def fin_ready(ns: P.NumSt, r: Ready(ns)) -> {Some{MK(ns)} == P.N.fin(ns) : Maybe<&2, D.Num>}:
  match ns:
    case P.NSign{neg}:
      Empty.absurd({Some{MK(P.NSign{neg})} == P.N.fin(P.NSign{neg}) : Maybe<&2, D.Num>}, r)
    case P.NInt{neg, acc}:
      {==}
    case P.NFrac{neg, acc, 0n}:
      Empty.absurd({Some{MK(P.NFrac{neg, acc, 0n})} == P.N.fin(P.NFrac{neg, acc, 0n}) : Maybe<&2, D.Num>}, r)
    case P.NFrac{neg, acc, 1n+f}:
      {==}
    case P.NExp{neg, acc, fl}:
      Empty.absurd({Some{MK(P.NExp{neg, acc, fl})} == P.N.fin(P.NExp{neg, acc, fl}) : Maybe<&2, D.Num>}, r)
    case P.NExpD{neg, acc, fl, eneg, Nil{}}:
      Empty.absurd({Some{MK(P.NExpD{neg, acc, fl, eneg, Nil{}})} == P.N.fin(P.NExpD{neg, acc, fl, eneg, Nil{}}) : Maybe<&2, D.Num>}, r)
    case P.NExpD{neg, acc, fl, eneg, Con{x, t}}:
      {==}

# Good(ns, n): the parser may end the number here, and it is n
def Good(ns: P.NumSt, n: D.Num) -> Type:
  Ready(ns) & {n == MK(ns) : D.Num}


# a normalized e is its value counted up from 0
def ez_of(+e: List<&2, D.Digit>, he: {D.Dec.is_norm(e) == True{} : Bool}, -k: Nat,
  ek: {D.Dec.to_nat(e) == k : Nat}) -> {e == D.Dec.iter(k, Nil{}) : List<&2, D.Digit>}:
  %ek : {e == D.Dec.iter(_, Nil{}) : List<&2, D.Digit>}
  iter_to_nat(e, he)

# a number whose digits are already normalized: make only moves the exponent
def mk_clean(-neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, -acc: List<&2, D.Digit>, -eneg: Bool, -e: List<&2, D.Digit>, -fl: Nat, nz: NZ(x),
  hn: {x <> t == D.Dec.norm(acc) : List<&2, D.Digit>}) ->
  {D.Num.make.at(neg, x, t, D.SExp.sub_n(fl, D.SExp.mk(eneg, D.Dec.norm(e))))
    == D.Num.make(neg, acc, eneg, e, fl) : D.Num}:
  %hn : {D.Num.make.at(neg, x, t, D.SExp.sub_n(fl, D.SExp.mk(eneg, D.Dec.norm(e))))
    == D.Num.make.fin(neg, D.Dec.strip_low(_), eneg, e, fl) : D.Num}
  %strip_nz(x, t, nz) : {D.Num.make.at(neg, x, t, D.SExp.sub_n(fl, D.SExp.mk(eneg, D.Dec.norm(e))))
    == D.Num.make.fin(neg, _, eneg, e, fl) : D.Num}
  {==}

def good_int(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, nz: NZ(x), hc: {D.Dec.is_norm(x <> t) == True{} : Bool}) ->
  Good(P.NInt{neg, x <> t}, D.Num{neg, x <> t, False{}, Nil{}}):
  (Unit{}, mk_clean(neg, x, t, x <> t, False{}, Nil{}, 0n, nz, norm_id(x <> t, hc)))

def eq_exp(+neg: Bool, +eneg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}) ->
  {D.Num{neg, x <> t, eneg, e0 <> e1} == MK(NS.exp(x <> t, eneg, e0 <> e1, neg)) : D.Num}:
  %mk_clean(neg, x, t, x <> t, eneg, List.append(&2, D.Digit, e0 <> e1, Nil{}), 0n, nz, norm_id(x <> t, hc)) :
    {D.Num{neg, x <> t, eneg, e0 <> e1} == _ : D.Num}
  %append_nil(e0 <> e1) : {D.Num{neg, x <> t, eneg, e0 <> e1} == D.Num.make.at(neg, x, t, D.SExp.mk(eneg, D.Dec.norm(_))) : D.Num}
  %norm_id(e0 <> e1, he) : {D.Num{neg, x <> t, eneg, e0 <> e1} == D.Num.make.at(neg, x, t, D.SExp.mk(eneg, _)) : D.Num}
  {==}

def good_exp(+neg: Bool, +eneg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}) ->
  Good(NS.exp(x <> t, eneg, e0 <> e1, neg), D.Num{neg, x <> t, eneg, e0 <> e1}):
  (Unit{}, eq_exp(neg, eneg, x, t, e0, e1, nz, hc, he))

def eq_zeros(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}) -> {D.Num{neg, x <> t, False{}, e0 <> e1} == MK(P.NInt{neg, Dz(D.Dec.to_nat(e0 <> e1), x <> t)}) : D.Num}:
  %norm_dz(D.Dec.to_nat(e0 <> e1), x, t, norm_id(x <> t, hc)) :
    {D.Num{neg, x <> t, False{}, e0 <> e1} == D.Num.make.fin(neg, D.Dec.strip_low(_), False{}, Nil{}, 0n) : D.Num}
  %strip_dz(D.Dec.to_nat(e0 <> e1), x <> t, strip_nz(x, t, nz)) :
    {D.Num{neg, x <> t, False{}, e0 <> e1} == D.Num.make.fin(neg, _, False{}, Nil{}, 0n) : D.Num}
  %add_n_pos(D.Dec.to_nat(e0 <> e1), Nil{}) : {D.Num{neg, x <> t, False{}, e0 <> e1} == D.Num.make.at(neg, x, t, _) : D.Num}
  %iter_to_nat(e0 <> e1, he) : {D.Num{neg, x <> t, False{}, e0 <> e1} == D.Num{neg, x <> t, False{}, _} : D.Num}
  {==}

def good_zeros(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}) -> Good(P.NInt{neg, Dz(D.Dec.to_nat(e0 <> e1), x <> t)}, D.Num{neg, x <> t, False{}, e0 <> e1}):
  (Unit{}, eq_zeros(neg, x, t, e0, e1, nz, hc, he))

def eq_frac(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, -acc: List<&2, D.Digit>, hna: {x <> t == D.Dec.norm(acc) : List<&2, D.Digit>}, +p: Nat,
  ek: {D.Dec.to_nat(e0 <> e1) == 1n+p : Nat}) -> {D.Num{neg, x <> t, True{}, e0 <> e1} == MK(P.NFrac{neg, acc, 1n+p}) : D.Num}:
  +ez = ez_of(e0 <> e1, he, 1n+p, ek)
  %mk_clean(neg, x, t, acc, False{}, Nil{}, 1n+p, nz, hna) : {D.Num{neg, x <> t, True{}, e0 <> e1} == _ : D.Num}
  %sub_n_neg(p, [D.D1{}]) : {D.Num{neg, x <> t, True{}, e0 <> e1} == D.Num.make.at(neg, x, t, _) : D.Num}
  %ez : {D.Num{neg, x <> t, True{}, e0 <> e1} == D.Num{neg, x <> t, True{}, _} : D.Num}
  {==}

# a fraction state whose length is the exponent's value
def good_frac(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, -acc: List<&2, D.Digit>, hna: {x <> t == D.Dec.norm(acc) : List<&2, D.Digit>}, k: Nat,
  ek: {D.Dec.to_nat(e0 <> e1) == k : Nat}) -> Good(P.NFrac{neg, acc, k}, D.Num{neg, x <> t, True{}, e0 <> e1}):
  match k:
    case 0n:
      +z = ez_of(e0 <> e1, he, 0n, ek)
      %z : BNil(_, Good(P.NFrac{neg, acc, 0n}, D.Num{neg, x <> t, True{}, e0 <> e1}), Unit)
      Unit{}
    case 1n+p:
      (Unit{}, eq_frac(neg, x, t, e0, e1, nz, hc, he, acc, hna, p, ek))

def good_pt(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, hin: {Nat.is_lt(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)) == True{} : Bool}) ->
  Good(NS.neg.point(x <> t, e0 <> e1, D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t), neg, True{}), D.Num{neg, x <> t, True{}, e0 <> e1}):
  %add_zero(List.length(&2, D.Digit, List.take(&2, D.Digit, x <> t, D.Dec.to_nat(e0 <> e1)))) :
    Good(P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, x <> t, D.Dec.to_nat(e0 <> e1)), List.drop(&2, D.Digit, x <> t, D.Dec.to_nat(e0 <> e1))), _}, D.Num{neg, x <> t, True{}, e0 <> e1})
  %len_take(x <> t, D.Dec.to_nat(e0 <> e1), hin) :
    Good(P.NFrac{neg, List.append(&2, D.Digit, List.take(&2, D.Digit, x <> t, D.Dec.to_nat(e0 <> e1)), List.drop(&2, D.Digit, x <> t, D.Dec.to_nat(e0 <> e1))), _}, D.Num{neg, x <> t, True{}, e0 <> e1})
  %take_drop(x <> t, D.Dec.to_nat(e0 <> e1)) : Good(P.NFrac{neg, _, D.Dec.to_nat(e0 <> e1)}, D.Num{neg, x <> t, True{}, e0 <> e1})
  good_frac(neg, x, t, e0, e1, nz, hc, he, x <> t, norm_id(x <> t, hc), D.Dec.to_nat(e0 <> e1), {==})

def good_z0(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, hin: {Nat.is_lt(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)) == False{} : Bool}) ->
  Good(NS.neg.zeros(x <> t, e0 <> e1, D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t), neg, True{}), D.Num{neg, x <> t, True{}, e0 <> e1}):
  %add_zero(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t))) :
    Good(P.NFrac{neg, List.append(&2, D.Digit, x <> t, Dz(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)), [D.D0{}])), Nat.add(List.length(&2, D.Digit, x <> t), _)}, D.Num{neg, x <> t, True{}, e0 <> e1})
  %add_sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t), hin) :
    Good(P.NFrac{neg, List.append(&2, D.Digit, x <> t, Dz(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)), [D.D0{}])), _}, D.Num{neg, x <> t, True{}, e0 <> e1})
  good_frac(neg, x, t, e0, e1, nz, hc, he, List.append(&2, D.Digit, x <> t, Dz(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)), [D.D0{}])),
    norm_app(t, x, Dz(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)), [D.D0{}]), hc, norm_zz(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)))), D.Dec.to_nat(e0 <> e1), {==})

def good_neg_zeros(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, fit: Bool, hin: {Nat.is_lt(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)) == False{} : Bool}) ->
  Good(NS.neg.zeros(x <> t, e0 <> e1, D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t), neg, fit), D.Num{neg, x <> t, True{}, e0 <> e1}):
  match fit:
    case True{}:
      good_z0(neg, x, t, e0, e1, nz, hc, he, hin)
    case False{}:
      good_exp(neg, True{}, x, t, e0, e1, nz, hc, he)

def good_neg_point(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, inside: Bool, ei: {Nat.is_lt(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)) == inside : Bool}) ->
  Good(NS.neg.point(x <> t, e0 <> e1, D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t), neg, inside), D.Num{neg, x <> t, True{}, e0 <> e1}):
  match inside:
    case True{}:
      good_pt(neg, x, t, e0, e1, nz, hc, he, ei)
    case False{}:
      good_neg_zeros(neg, x, t, e0, e1, nz, hc, he, Nat.is_le(Nat.sub(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)), 5n), ei)

def good_neg(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, small: Bool) -> Good(NS.neg(x <> t, e0 <> e1, neg, small), D.Num{neg, x <> t, True{}, e0 <> e1}):
  match small:
    case True{}:
      good_neg_point(neg, x, t, e0, e1, nz, hc, he, Nat.is_lt(D.Dec.to_nat(e0 <> e1), List.length(&2, D.Digit, x <> t)), {==})
    case False{}:
      good_exp(neg, True{}, x, t, e0, e1, nz, hc, he)

def good_pos_fit(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, fit: Bool) -> Good(NS.pos.fit(x <> t, e0 <> e1, neg, fit), D.Num{neg, x <> t, False{}, e0 <> e1}):
  match fit:
    case True{}:
      good_zeros(neg, x, t, e0, e1, nz, hc, he)
    case False{}:
      good_exp(neg, False{}, x, t, e0, e1, nz, hc, he)

def good_pos(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +e0: D.Digit, +e1: List<&2, D.Digit>, +nz: NZ(x), +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, +he: {D.Dec.is_norm(e0 <> e1) == True{} : Bool}, small: Bool) -> Good(NS.pos(x <> t, e0 <> e1, neg, small), D.Num{neg, x <> t, False{}, e0 <> e1}):
  match small:
    case True{}:
      good_pos_fit(neg, x, t, e0, e1, nz, hc, he, Nat.is_le(Nat.add(List.length(&2, D.Digit, x <> t), D.Dec.to_nat(e0 <> e1)), 21n))
    case False{}:
      good_exp(neg, False{}, x, t, e0, e1, nz, hc, he)

def good_body(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, eneg: Bool, e: List<&2, D.Digit>, +nz: NZ(x),
  +hc: {D.Dec.is_norm(x <> t) == True{} : Bool}, hx: {D.Num.is_norm.exp(eneg, e) == True{} : Bool}) ->
  Good(NS.body(x <> t, eneg, e, neg), D.Num{neg, x <> t, eneg, e}):
  match eneg e:
    case False{} Nil{}:
      good_int(neg, x, t, nz, hc)
    case False{} Con{+e0, +e1}:
      good_pos(neg, x, t, e0, e1, nz, hc, hx, Nat.is_le(List.length(&2, D.Digit, e0 <> e1), 2n))
    case True{} Nil{}:
      %hx : BM(_, Good(NS.body(x <> t, True{}, Nil{}, neg), D.Num{neg, x <> t, True{}, Nil{}}), Unit)
      Unit{}
    case True{} Con{+e0, +e1}:
      good_neg(neg, x, t, e0, e1, nz, hc, hx, Nat.is_le(List.length(&2, D.Digit, e0 <> e1), 6n))

def good_zero(neg: Bool, eneg: Bool, e: List<&2, D.Digit>, h: {D.Num.is_norm(D.Num{neg, Nil{}, eneg, e}) == True{} : Bool}) ->
  Good(P.NInt{False{}, [D.D0{}]}, D.Num{neg, Nil{}, eneg, e}):
  match neg eneg e:
    case False{} False{} Nil{}:
      (Unit{}, {==})
    case True{} b m:
      %h : BM(_, Good(P.NInt{False{}, [D.D0{}]}, D.Num{True{}, Nil{}, b, m}), Unit)
      Unit{}
    case False{} True{} m:
      %h : BM(_, Good(P.NInt{False{}, [D.D0{}]}, D.Num{False{}, Nil{}, True{}, m}), Unit)
      Unit{}
    case False{} False{} Con{y, z}:
      %h : BM(_, Good(P.NInt{False{}, [D.D0{}]}, D.Num{False{}, Nil{}, False{}, y <> z}), Unit)
      Unit{}

def good_num.at(+neg: Bool, +x: D.Digit, +t: List<&2, D.Digit>, +eneg: Bool, +e: List<&2, D.Digit>, f: NormF(x, t, eneg, e)) ->
  Good(NS(D.Num{neg, x <> t, eneg, e}), D.Num{neg, x <> t, eneg, e}):
  (nz, hs) = f
  (hc, hx) = hs
  good_body(neg, x, t, eneg, e, nz, hc, hx)

# a normalized number's state stands for it and may end
def good_num(n: D.Num, h: {D.Num.is_norm(n) == True{} : Bool}) -> Good(NS(n), n):
  match n:
    case D.Num{neg, Nil{}, eneg, e}:
      good_zero(neg, eneg, e, h)
    case D.Num{+neg, +x <> +t, +eneg, +e}:
      good_num.at(neg, x, t, eneg, e, norm_split(x, t, neg, eneg, e, h))

def fin_g(+ns: P.NumSt, -n: D.Num, g: Good(ns, n)) -> {Some{n} == P.N.fin(ns) : Maybe<&2, D.Num>}:
  (r, eq) = g
  %Equal.sym(D.Num, n, MK(ns), eq) : {Some{_} == P.N.fin(ns) : Maybe<&2, D.Num>}
  fin_ready(ns, r)

def Laws.number_roundtrip(n, h):
  %run_num(n, False{}, h, P.Ctx{Nil{}, 512n}, SNil{}) :
    {P.parse_number.of(P.P.out(_, String.length(Pr.print_number(n)))) == Some{n} : Maybe<&2, D.Num>}
  %fin_g(NS(n), n, good_num(n, h)) :
    {P.parse_number.of(P.P.eof.num(_, String.length(Pr.print_number(n)))) == Some{n} : Maybe<&2, D.Num>}
  {==}

# Law 3: values
# -------------

# SVStr: the parser's own loop over an escaped string
def ctl_caseP(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, -c: P.Ctx, -acc: String, -rest: String) ->
  {R(rest, P.SVStr{c, T.StrBody{SCon{Chr{Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n))}, acc}}})
    == R(T.Esc.ctl(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n)), rest), P.SVStr{c, T.StrBody{acc}}) : P.Out}:
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

def char_kP(+x: U32, k: T.CKind, e: {T.Esc.kind(x) == k : T.CKind}, -c: P.Ctx, -acc: String,
  -rest: String) ->
  {R(rest, P.SVStr{c, T.StrBody{SCon{Chr{x}, acc}}})
    == R(T.Esc.char.k(x, k, rest), P.SVStr{c, T.StrBody{acc}}) : P.Out}:
  match k:
    case T.KPlain{}:
      %Equal.sym(T.CKind, T.Esc.kind(x), T.KPlain{}, e) :
        {R(rest, P.SVStr{c, T.StrBody{SCon{Chr{x}, acc}}}) == P.P.run(rest, P.P.vstr(c, T.Str.raw(acc, x, _))) : P.Out}
      {==}
    case T.KQuote{}:
      %Equal.sym(U32, x, 34, kind_quote(x, e)) :
        {R(rest, P.SVStr{c, T.StrBody{SCon{Chr{_}, acc}}})
          == R(T.Esc.char.k(x, T.KQuote{}, rest), P.SVStr{c, T.StrBody{acc}}) : P.Out}
      {==}
    case T.KBack{}:
      %Equal.sym(U32, x, 92, kind_back(x, e)) :
        {R(rest, P.SVStr{c, T.StrBody{SCon{Chr{_}, acc}}})
          == R(T.Esc.char.k(x, T.KBack{}, rest), P.SVStr{c, T.StrBody{acc}}) : P.Out}
      {==}
    case T.KCtl{}:
      ctl_split(y => {R(rest, P.SVStr{c, T.StrBody{SCon{Chr{y}, acc}}})
          == R(T.Esc.ctl(y, rest), P.SVStr{c, T.StrBody{acc}}) : P.Out},
        b0 => b1 => b2 => b3 => b4 => ctl_caseP(b0, b1, b2, b3, b4, c, acc, rest), x)(e)

def char_lP(ch: Char, -c: P.Ctx, -acc: String, -rest: String) ->
  {R(rest, P.SVStr{c, T.StrBody{SCon{ch, acc}}}) == R(T.Esc.char(ch, rest), P.SVStr{c, T.StrBody{acc}}) : P.Out}:
  match ch:
    case Chr{+x}:
      char_kP(x, T.Esc.kind(x), {==}, c, acc, rest)

def esc_goP(s: String, -c: P.Ctx, -acc: String, -rest: String) ->
  {R(rest, P.SVStr{c, T.StrBody{String.reverse.go(s, acc)}})
    == R(T.Esc.go(s, rest), P.SVStr{c, T.StrBody{acc}}) : P.Out}:
  match s:
    case SNil{}:
      {==}
    case SCon{+ch, t}:
      %char_lP(ch, c, acc, T.Esc.go(t, rest)) :
        {R(rest, P.SVStr{c, T.StrBody{String.reverse.go(SCon{ch, t}, acc)}}) == _ : P.Out}
      esc_goP(t, c, SCon{ch, acc}, rest)

# SKStr: the parser's own loop over an escaped string
def ctl_caseP_k(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, -c: P.Ctx, -acc: String, -rest: String) ->
  {R(rest, P.SKStr{c, T.StrBody{SCon{Chr{Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n))}, acc}}})
    == R(T.Esc.ctl(Lo5(b0, b1, b2, b3, b4, False{}, Word.zero(26n)), rest), P.SKStr{c, T.StrBody{acc}}) : P.Out}:
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

def char_kP_k(+x: U32, k: T.CKind, e: {T.Esc.kind(x) == k : T.CKind}, -c: P.Ctx, -acc: String,
  -rest: String) ->
  {R(rest, P.SKStr{c, T.StrBody{SCon{Chr{x}, acc}}})
    == R(T.Esc.char.k(x, k, rest), P.SKStr{c, T.StrBody{acc}}) : P.Out}:
  match k:
    case T.KPlain{}:
      %Equal.sym(T.CKind, T.Esc.kind(x), T.KPlain{}, e) :
        {R(rest, P.SKStr{c, T.StrBody{SCon{Chr{x}, acc}}}) == P.P.run(rest, P.P.kstr(c, T.Str.raw(acc, x, _))) : P.Out}
      {==}
    case T.KQuote{}:
      %Equal.sym(U32, x, 34, kind_quote(x, e)) :
        {R(rest, P.SKStr{c, T.StrBody{SCon{Chr{_}, acc}}})
          == R(T.Esc.char.k(x, T.KQuote{}, rest), P.SKStr{c, T.StrBody{acc}}) : P.Out}
      {==}
    case T.KBack{}:
      %Equal.sym(U32, x, 92, kind_back(x, e)) :
        {R(rest, P.SKStr{c, T.StrBody{SCon{Chr{_}, acc}}})
          == R(T.Esc.char.k(x, T.KBack{}, rest), P.SKStr{c, T.StrBody{acc}}) : P.Out}
      {==}
    case T.KCtl{}:
      ctl_split(y => {R(rest, P.SKStr{c, T.StrBody{SCon{Chr{y}, acc}}})
          == R(T.Esc.ctl(y, rest), P.SKStr{c, T.StrBody{acc}}) : P.Out},
        b0 => b1 => b2 => b3 => b4 => ctl_caseP_k(b0, b1, b2, b3, b4, c, acc, rest), x)(e)

def char_lP_k(ch: Char, -c: P.Ctx, -acc: String, -rest: String) ->
  {R(rest, P.SKStr{c, T.StrBody{SCon{ch, acc}}}) == R(T.Esc.char(ch, rest), P.SKStr{c, T.StrBody{acc}}) : P.Out}:
  match ch:
    case Chr{+x}:
      char_kP_k(x, T.Esc.kind(x), {==}, c, acc, rest)

def esc_goP_k(s: String, -c: P.Ctx, -acc: String, -rest: String) ->
  {R(rest, P.SKStr{c, T.StrBody{String.reverse.go(s, acc)}})
    == R(T.Esc.go(s, rest), P.SKStr{c, T.StrBody{acc}}) : P.Out}:
  match s:
    case SNil{}:
      {==}
    case SCon{+ch, t}:
      %char_lP_k(ch, c, acc, T.Esc.go(t, rest)) :
        {R(rest, P.SKStr{c, T.StrBody{String.reverse.go(SCon{ch, t}, acc)}}) == _ : P.Out}
      esc_goP_k(t, c, SCon{ch, acc}, rest)

# a string value: quote, escaped body, quote
def str_val(+s: String, -close: Bool, -c: P.Ctx, -rest: String) ->
  {R(rest, P.SDone{c, V.JStr{s}}) == R(T.quote(s, rest), P.SVal{close, c}) : P.Out}:
  %esc_goP(s, c, SNil{}, SCon{'"', rest}) : {R(rest, P.SDone{c, V.JStr{s}}) == _ : P.Out}
  %rev_rev(s, SNil{}) : {R(rest, P.SDone{c, V.JStr{s}}) == R(rest, P.SDone{c, V.JStr{_}}) : P.Out}
  {==}

# a key: the same, ending at the colon
def key_str(+s: String, -close: Bool, -c: P.Ctx, -rest: String) ->
  {R(rest, P.SColon{c, s}) == R(T.quote(s, rest), P.SKey{close, c}) : P.Out}:
  %esc_goP_k(s, c, SNil{}, SCon{'"', rest}) : {R(rest, P.SColon{c, s}) == _ : P.Out}
  %rev_rev(s, SNil{}) : {R(rest, P.SColon{c, s}) == R(rest, P.SColon{c, _}) : P.Out}
  {==}

# the char after a value in printed text, and that text's rest
type Dl is Data:
  DComma{}
  DBrack{}
  DBrace{}
  DNl{}

def Dl.ch(d: Dl) -> Char:
  match d:
    case DComma{}:
      ','
    case DBrack{}:
      ']'
    case DBrace{}:
      '}'
    case DNl{}:
      '\n'

type Rest is Data:
  REnd{}
  RDl{d: Dl, r: String}

def Rest.str(rr: Rest) -> String:
  match rr:
    case REnd{}:
      SNil{}
    case RDl{d, r}:
      SCon{Dl.ch(d), r}

# where a value leaves the parser: a number is still open
def Pend(v: V.Json, c: P.Ctx) -> P.St:
  match v:
    case V.JNum{n}:
      SN(c, NS(n))
    case o:
      P.SDone{c, o}

def end_int(-neg: Bool, -acc: List<&2, D.Digit>, d: Dl) ->
  {P.NEnd{MK(P.NInt{neg, acc})} == P.N.step(P.NInt{neg, acc}, Dl.ch(d)) : P.NRes}:
  match d:
    case DComma{}:
      {==}
    case DBrack{}:
      {==}
    case DBrace{}:
      {==}
    case DNl{}:
      {==}

def end_frac(-neg: Bool, -acc: List<&2, D.Digit>, -f: Nat, d: Dl) ->
  {P.NEnd{MK(P.NFrac{neg, acc, 1n+f})} == P.N.step(P.NFrac{neg, acc, 1n+f}, Dl.ch(d)) : P.NRes}:
  match d:
    case DComma{}:
      {==}
    case DBrack{}:
      {==}
    case DBrace{}:
      {==}
    case DNl{}:
      {==}

def end_exp(-neg: Bool, -acc: List<&2, D.Digit>, -fl: Nat, -eneg: Bool, -x: D.Digit,
  -t: List<&2, D.Digit>, d: Dl) ->
  {P.NEnd{MK(P.NExpD{neg, acc, fl, eneg, x <> t})}
    == P.N.step(P.NExpD{neg, acc, fl, eneg, x <> t}, Dl.ch(d)) : P.NRes}:
  match d:
    case DComma{}:
      {==}
    case DBrack{}:
      {==}
    case DBrace{}:
      {==}
    case DNl{}:
      {==}

def end_ready(ns: P.NumSt, d: Dl, r: Ready(ns)) -> {P.NEnd{MK(ns)} == P.N.step(ns, Dl.ch(d)) : P.NRes}:
  match ns:
    case P.NSign{neg}:
      Empty.absurd({P.NEnd{MK(P.NSign{neg})} == P.N.step(P.NSign{neg}, Dl.ch(d)) : P.NRes}, r)
    case P.NInt{neg, acc}:
      end_int(neg, acc, d)
    case P.NFrac{neg, acc, 0n}:
      Empty.absurd({P.NEnd{MK(P.NFrac{neg, acc, 0n})} == P.N.step(P.NFrac{neg, acc, 0n}, Dl.ch(d)) : P.NRes}, r)
    case P.NFrac{neg, acc, 1n+f}:
      end_frac(neg, acc, f, d)
    case P.NExp{neg, acc, fl}:
      Empty.absurd({P.NEnd{MK(P.NExp{neg, acc, fl})} == P.N.step(P.NExp{neg, acc, fl}, Dl.ch(d)) : P.NRes}, r)
    case P.NExpD{neg, acc, fl, eneg, Nil{}}:
      Empty.absurd({P.NEnd{MK(P.NExpD{neg, acc, fl, eneg, Nil{}})} == P.N.step(P.NExpD{neg, acc, fl, eneg, Nil{}}, Dl.ch(d)) : P.NRes}, r)
    case P.NExpD{neg, acc, fl, eneg, Con{x, t}}:
      end_exp(neg, acc, fl, eneg, x, t, d)

def end_g(+ns: P.NumSt, -n: D.Num, d: Dl, g: Good(ns, n)) -> {P.NEnd{n} == P.N.step(ns, Dl.ch(d)) : P.NRes}:
  (r, eq) = g
  %Equal.sym(D.Num, n, MK(ns), eq) : {P.NEnd{_} == P.N.step(ns, Dl.ch(d)) : P.NRes}
  end_ready(ns, d, r)

# a delimiter after a value acts as after any complete value
def pend_dl(v: V.Json, -c: P.Ctx, +d: Dl, -rest: String, h: {V.Json.is_norm(v) == True{} : Bool}) ->
  {P.P.run(rest, P.P.after(c, v, Dl.ch(d))) == R(SCon{Dl.ch(d), rest}, Pend(v, c)) : P.Out}:
  match v:
    case V.JNull{}:
      {==}
    case V.JBool{b}:
      {==}
    case V.JNum{+n}:
      %end_g(NS(n), n, d, good_num(n, h)) :
        {P.P.run(rest, P.P.after(c, V.JNum{n}, Dl.ch(d))) == P.P.run(rest, P.P.num(c, Dl.ch(d), _)) : P.Out}
      {==}
    case V.JStr{x}:
      {==}
    case V.JArr{xs}:
      {==}
    case V.JObj{ms}:
      {==}

# the end of input after a value
def eof_pend(v: V.Json, -r: Nat, h: {V.Json.is_norm(v) == True{} : Bool}, +len: Nat) ->
  {Done{v} == P.P.eof(Pend(v, P.Ctx{Nil{}, r}), len) : Result<&2, &2, P.Err, V.Json>}:
  match v:
    case V.JNull{}:
      {==}
    case V.JBool{b}:
      {==}
    case V.JNum{+n}:
      %fin_g(NS(n), n, good_num(n, h)) :
        {Done{V.JNum{n}} == P.P.eof.num(_, len) : Result<&2, &2, P.Err, V.Json>}
      {==}
    case V.JStr{x}:
      {==}
    case V.JArr{xs}:
      {==}
    case V.JObj{ms}:
      {==}

def le_zero(c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_max(a: Nat, b: Nat, c: Nat, h: {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool} & {Nat.is_le(b, c) == True{} : Bool}:
  match a b c:
    case 0n b0 0n:
      ({==}, h)
    case 0n b0 1n+q:
      ({==}, h)
    case 1n+p 0n c0:
      (h, le_zero(c0))
    case 1n+p 1n+q 0n:
      %h : BM(_, {Nat.is_le(1n+p, 0n) == True{} : Bool} & {Nat.is_le(1n+q, 0n) == True{} : Bool}, Unit)
      Unit{}
    case 1n+p 1n+q 1n+r:
      le_max(p, q, r, h)

def lrev(-A: Data, xs: List<&2, A>, -acc: List<&2, A>) ->
  {List.reverse.go(&2, A, acc, xs) == List.reverse(&2, A, List.reverse.go(&2, A, xs, acc)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      lrev(A, t, h <> acc)

# The claim, by the printer's mode
# --------------------------------
# mode 1n: a value read from SVal ends in Pend(v). mode 0n: the items of a
# nonempty array (object), read after its '[' ('{') up to its ']' ('}'),
# close the frame on top of the stack.

def ICA(x: V.Json, t: List<&2, V.Json>, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match stk:
    case Con{P.FArr{acc}, s2}:
      {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json, List.reverse.go(&2, V.Json, x <> t, acc))}})
        == R(Pr.Pr.go(V.JArr{x <> t}, 0n, SCon{']', Rest.str(rr)}), P.SVal{close, P.Ctx{P.FArr{acc} <> s2, room}}) : P.Out}
    case _:
      Unit

def ICO(m: V.Member, t: List<&2, V.Member>, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match stk:
    case Con{P.FObj{items, k0}, s2}:
      {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member, List.reverse.go(&2, V.Member, m <> t, items))}})
        == R(Pr.Pr.go(V.JObj{m <> t}, 0n, SCon{'}', Rest.str(rr)}), P.SKey{close, P.Ctx{P.FObj{items, k0} <> s2, room}}) : P.Out}
    case _:
      Unit

def IC(v: V.Json, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match v:
    case V.JArr{Con{x, t}}:
      ICA(x, t, close, stk, room, rr)
    case V.JObj{Con{m, t}}:
      ICO(m, t, close, stk, room, rr)
    case _:
      Unit

def Room(mode: Nat, room: Nat) -> Nat:
  match mode:
    case 0n:
      1n+room
    case _:
      room

def VC(v: V.Json, mode: Nat, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match mode:
    case 0n:
      IC(v, close, stk, room, rr)
    case 1n:
      {R(Rest.str(rr), Pend(v, P.Ctx{stk, room})) == R(Pr.Pr.go(v, 1n, Rest.str(rr)), P.SVal{close, P.Ctx{stk, room}}) : P.Out}
    case 2n+k:
      Unit

def NormH(v: V.Json) -> Data:
  {V.Json.is_norm(v) == True{} : Bool}

def DepH(v: V.Json, n: Nat) -> Data:
  {Nat.is_le(V.Json.depth(v), n) == True{} : Bool}

def dep_arr(+x: V.Json, +t: List<&2, V.Json>, +n: Nat, h: DepH(V.JArr{x <> t}, n)) ->
  {Nat.is_le(1n+V.Json.depth(x), n) == True{} : Bool} & DepH(V.JArr{t}, n):
  le_max(1n+V.Json.depth(x), V.Json.depth(V.JArr{t}), n, h)

def dep_obj(-k: String, +x: V.Json, +t: List<&2, V.Member>, +n: Nat, h: DepH(V.JObj{V.Mem{k, x} <> t}, n)) ->
  {Nat.is_le(1n+V.Json.depth(x), n) == True{} : Bool} & DepH(V.JObj{t}, n):
  le_max(1n+V.Json.depth(x), V.Json.depth(V.JObj{t}), n, h)

# the helpers take the induction hypotheses as arguments

def arr_empty(-close: Bool, -stk: List<&2, P.Frame>, room: Nat, -rr: Rest, h: DepH(V.JArr{Nil{}}, room)) ->
  VC(V.JArr{Nil{}}, 1n, close, stk, room, rr):
  match room:
    case 0n:
      %h : BM(_, VC(V.JArr{Nil{}}, 1n, close, stk, 0n, rr), Unit)
      Unit{}
    case 1n+r:
      {==}

def obj_empty(-close: Bool, -stk: List<&2, P.Frame>, room: Nat, -rr: Rest, h: DepH(V.JObj{Nil{}}, room)) ->
  VC(V.JObj{Nil{}}, 1n, close, stk, room, rr):
  match room:
    case 0n:
      %h : BM(_, VC(V.JObj{Nil{}}, 1n, close, stk, 0n, rr), Unit)
      Unit{}
    case 1n+r:
      {==}

def arr_open(+x: V.Json, t: List<&2, V.Json>, -close: Bool, +stk: List<&2, P.Frame>, +r: Nat, +rr: Rest) ->
  IC(V.JArr{x <> t}, True{}, P.FArr{Nil{}} <> stk, r, rr) -> VC(V.JArr{x <> t}, 1n, close, stk, 1n+r, rr):
  match t:
    case Nil{}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> Nil{}}}) == _ : P.Out}
        %lrev(V.Json, x <> Nil{}, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> Nil{}}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{_}}) : P.Out}
        {==})
    case Con{+y, +w}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> y <> w}}) == _ : P.Out}
        %lrev(V.Json, x <> y <> w, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> y <> w}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{_}}) : P.Out}
        {==})

def obj_open(+k: String, +x: V.Json, t: List<&2, V.Member>, -close: Bool, +stk: List<&2, P.Frame>, +r: Nat, +rr: Rest) ->
  IC(V.JObj{V.Mem{k, x} <> t}, True{}, P.FObj{Nil{}, SNil{}} <> stk, r, rr) -> VC(V.JObj{V.Mem{k, x} <> t}, 1n, close, stk, 1n+r, rr):
  match t:
    case Nil{}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> Nil{}}}) == _ : P.Out}
        %lrev(V.Member, V.Mem{k, x} <> Nil{}, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> Nil{}}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{_}}) : P.Out}
        {==})
    case Con{+y, +w}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> y <> w}}) == _ : P.Out}
        %lrev(V.Member, V.Mem{k, x} <> y <> w, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> y <> w}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{_}}) : P.Out}
        {==})

def arr_last(+x: V.Json, +acc: List<&2, V.Json>, +s2: List<&2, P.Frame>, +close: Bool, +room: Nat, +rr: Rest, +hx: NormH(x),
  ih: VC(x, 1n, close, P.FArr{acc} <> s2, room, RDl{DBrack{}, Rest.str(rr)})) ->
  ICA(x, Nil{}, close, P.FArr{acc} <> s2, room, rr):
  %ih : {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json, x <> acc)}}) == _ : P.Out}
  pend_dl(x, P.Ctx{P.FArr{acc} <> s2, room}, DBrack{}, Rest.str(rr), hx)

def arr_next(+x: V.Json, +y: V.Json, +t: List<&2, V.Json>, +acc: List<&2, V.Json>, +s2: List<&2, P.Frame>, +close: Bool, +room: Nat,
  +rr: Rest, +hx: NormH(x),
  ihx: VC(x, 1n, close, P.FArr{acc} <> s2, room,
    RDl{DComma{}, Pr.Pr.go(V.JArr{y <> t}, 0n, SCon{']', Rest.str(rr)})}),
  iht: ICA(y, t, False{}, P.FArr{x <> acc} <> s2, room, rr)) ->
  ICA(x, y <> t, close, P.FArr{acc} <> s2, room, rr):
  %ihx : {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json,
    List.reverse.go(&2, V.Json, x <> y <> t, acc))}}) == _ : P.Out}
  %pend_dl(x, P.Ctx{P.FArr{acc} <> s2, room}, DComma{},
    Pr.Pr.go(V.JArr{y <> t}, 0n, SCon{']', Rest.str(rr)}), hx) :
    {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json,
      List.reverse.go(&2, V.Json, x <> y <> t, acc))}}) == _ : P.Out}
  iht

def obj_last(+k: String, +x: V.Json, +items: List<&2, V.Member>, -k0: String, +s2: List<&2, P.Frame>,
  +close: Bool, +room: Nat, +rr: Rest, +hx: NormH(x),
  ih: VC(x, 1n, False{}, P.FObj{items, k} <> s2, room, RDl{DBrace{}, Rest.str(rr)})) ->
  ICO(V.Mem{k, x}, Nil{}, close, P.FObj{items, k0} <> s2, room, rr):
  %key_str(k, close, P.Ctx{P.FObj{items, k0} <> s2, room}, SCon{':', Pr.Pr.go(x, 1n, SCon{'}', Rest.str(rr)})}) :
    {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member, V.Mem{k, x} <> items)}}) == _ : P.Out}
  %ih : {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member, V.Mem{k, x} <> items)}}) == _ : P.Out}
  pend_dl(x, P.Ctx{P.FObj{items, k} <> s2, room}, DBrace{}, Rest.str(rr), hx)

def obj_next(+k: String, +x: V.Json, +m2: V.Member, +t: List<&2, V.Member>, +items: List<&2, V.Member>,
  -k0: String, +s2: List<&2, P.Frame>, +close: Bool, +room: Nat, +rr: Rest, +hx: NormH(x),
  ihx: VC(x, 1n, False{}, P.FObj{items, k} <> s2, room,
    RDl{DComma{}, Pr.Pr.go(V.JObj{m2 <> t}, 0n, SCon{'}', Rest.str(rr)})}),
  iht: ICO(m2, t, False{}, P.FObj{V.Mem{k, x} <> items, SNil{}} <> s2, room, rr)) ->
  ICO(V.Mem{k, x}, m2 <> t, close, P.FObj{items, k0} <> s2, room, rr):
  %key_str(k, close, P.Ctx{P.FObj{items, k0} <> s2, room}, SCon{':', Pr.Pr.go(x, 1n,
    SCon{',', Pr.Pr.go(V.JObj{m2 <> t}, 0n, SCon{'}', Rest.str(rr)})})}) :
    {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member,
      List.reverse.go(&2, V.Member, V.Mem{k, x} <> m2 <> t, items))}}) == _ : P.Out}
  %ihx : {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member,
      List.reverse.go(&2, V.Member, V.Mem{k, x} <> m2 <> t, items))}}) == _ : P.Out}
  %pend_dl(x, P.Ctx{P.FObj{items, k} <> s2, room}, DComma{},
    Pr.Pr.go(V.JObj{m2 <> t}, 0n, SCon{'}', Rest.str(rr)}), hx) :
    {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member,
      List.reverse.go(&2, V.Member, V.Mem{k, x} <> m2 <> t, items))}}) == _ : P.Out}
  iht

def fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

def deg(+x: V.Json, +n: Nat, h: {Nat.is_le(1n+V.Json.depth(x), 1n+n) == True{} : Bool}) -> DepH(x, n):
  h

# the value lemma: every printed value, item list and member list parses
def VL(v: V.Json, mode: Nat, +close: Bool, +stk: List<&2, P.Frame>, +room: Nat, +rr: Rest,
  +hn: NormH(v), +hd: DepH(v, Room(mode, room))) -> VC(v, mode, close, stk, room, rr):
  match v mode:
    case v0 2n+k:
      Unit{}
    case V.JNull{} 1n:
      {==}
    case V.JNull{} 0n:
      Unit{}
    case V.JBool{True{}} 1n:
      {==}
    case V.JBool{False{}} 1n:
      {==}
    case V.JBool{b} 0n:
      Unit{}
    case V.JNum{+n} 1n:
      run_num(n, close, hn, P.Ctx{stk, room}, Rest.str(rr))
    case V.JNum{n} 0n:
      Unit{}
    case V.JStr{+s} 1n:
      str_val(s, close, P.Ctx{stk, room}, Rest.str(rr))
    case V.JStr{s} 0n:
      Unit{}
    case V.JArr{Nil{}} 1n:
      arr_empty(close, stk, room, rr, hd)
    case V.JArr{Nil{}} 0n:
      Unit{}
    case V.JArr{+x <> +t} 1n:
      match room:
        case 0n:
          %fst({Nat.is_le(1n+V.Json.depth(x), 0n) == True{} : Bool}, DepH(V.JArr{t}, 0n),
            dep_arr(x, t, 0n, hd)) : BM(_, VC(V.JArr{x <> t}, 1n, close, stk, 0n, rr), Unit)
          Unit{}
        case 1n++r:
          arr_open(x, t, close, stk, r, rr)(VL(V.JArr{x <> t}, 0n, True{}, P.FArr{Nil{}} <> stk, r, rr, hn, hd))
    case V.JArr{+x <> Nil{}} 0n:
      match stk:
        case Con{P.FArr{+acc}, +s2}:
          +hx = fst(NormH(x), NormH(V.JArr{Nil{}}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JArr{Nil{}}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JArr{Nil{}}, 1n+room),
            dep_arr(x, Nil{}, 1n+room, hd)))
          arr_last(x, acc, s2, close, room, rr, hx,
            VL(x, 1n, close, P.FArr{acc} <> s2, room, RDl{DBrack{}, Rest.str(rr)}, hx, hdx))
        case Nil{}:
          Unit{}
        case Con{P.FObj{a, b}, s2}:
          Unit{}
    case V.JArr{+x <> (+y <> +t)} 0n:
      match stk:
        case Con{P.FArr{+acc}, +s2}:
          +hx = fst(NormH(x), NormH(V.JArr{y <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JArr{y <> t}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JArr{y <> t}, 1n+room), dep_arr(x, y <> t, 1n+room, hd)))
          arr_next(x, y, t, acc, s2, close, room, rr, hx,
            VL(x, 1n, close, P.FArr{acc} <> s2, room,
              RDl{DComma{}, Pr.Pr.go(V.JArr{y <> t}, 0n, SCon{']', Rest.str(rr)})}, hx, hdx),
            VL(V.JArr{y <> t}, 0n, False{}, P.FArr{x <> acc} <> s2, room, rr,
              snd(NormH(x), NormH(V.JArr{y <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JArr{y <> t}), hn)),
              snd({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JArr{y <> t}, 1n+room), dep_arr(x, y <> t, 1n+room, hd))))
        case Nil{}:
          Unit{}
        case Con{P.FObj{a, b}, s2}:
          Unit{}
    case V.JObj{Nil{}} 1n:
      obj_empty(close, stk, room, rr, hd)
    case V.JObj{Nil{}} 0n:
      Unit{}
    case V.JObj{V.Mem{+k, +x} <> +t} 1n:
      match room:
        case 0n:
          %fst({Nat.is_le(1n+V.Json.depth(x), 0n) == True{} : Bool}, DepH(V.JObj{t}, 0n),
            dep_obj(k, x, t, 0n, hd)) : BM(_, VC(V.JObj{V.Mem{k, x} <> t}, 1n, close, stk, 0n, rr), Unit)
          Unit{}
        case 1n++r:
          obj_open(k, x, t, close, stk, r, rr)(VL(V.JObj{V.Mem{k, x} <> t}, 0n, True{},
            P.FObj{Nil{}, SNil{}} <> stk, r, rr, hn, hd))
    case V.JObj{V.Mem{+k, +x} <> Nil{}} 0n:
      match stk:
        case Con{P.FObj{+items, +k0}, +s2}:
          +hx = fst(NormH(x), NormH(V.JObj{Nil{}}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JObj{Nil{}}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JObj{Nil{}}, 1n+room),
            dep_obj(k, x, Nil{}, 1n+room, hd)))
          obj_last(k, x, items, k0, s2, close, room, rr, hx,
            VL(x, 1n, False{}, P.FObj{items, k} <> s2, room, RDl{DBrace{}, Rest.str(rr)}, hx, hdx))
        case Nil{}:
          Unit{}
        case Con{P.FArr{a}, s2}:
          Unit{}
    case V.JObj{V.Mem{+k, +x} <> (+m2 <> +t)} 0n:
      match stk:
        case Con{P.FObj{+items, +k0}, +s2}:
          +hx = fst(NormH(x), NormH(V.JObj{m2 <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JObj{m2 <> t}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JObj{m2 <> t}, 1n+room), dep_obj(k, x, m2 <> t, 1n+room, hd)))
          obj_next(k, x, m2, t, items, k0, s2, close, room, rr, hx,
            VL(x, 1n, False{}, P.FObj{items, k} <> s2, room,
              RDl{DComma{}, Pr.Pr.go(V.JObj{m2 <> t}, 0n, SCon{'}', Rest.str(rr)})}, hx, hdx),
            VL(V.JObj{m2 <> t}, 0n, False{}, P.FObj{V.Mem{k, x} <> items, SNil{}} <> s2, room, rr,
              snd(NormH(x), NormH(V.JObj{m2 <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JObj{m2 <> t}), hn)),
              snd({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JObj{m2 <> t}, 1n+room), dep_obj(k, x, m2 <> t, 1n+room, hd))))
        case Nil{}:
          Unit{}
        case Con{P.FArr{a}, s2}:
          Unit{}

def Laws.roundtrip_compact(v, h1, h2):
  %VL(v, 1n, False{}, Nil{}, 512n, REnd{}, h1, h2) :
    {P.P.out(_, String.length(Pr.print(v))) == Done{v} : Result<&2, &2, P.Err, V.Json>}
  %eof_pend(v, 512n, h1, String.length(Pr.print(v))) : {_ == Done{v} : Result<&2, &2, P.Err, V.Json>}
  {==}

# Law 3b: pretty text
# -------------------

def ws_val(n: Nat, -close: Bool, -c: P.Ctx, -r: String) ->
  {R(r, P.SVal{close, c}) == R(Pr.Pr.spaces(n, r), P.SVal{close, c}) : P.Out}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ws_val(p, close, c, r)

def ws_key(n: Nat, -close: Bool, -c: P.Ctx, -r: String) ->
  {R(r, P.SKey{close, c}) == R(Pr.Pr.spaces(n, r), P.SKey{close, c}) : P.Out}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ws_key(p, close, c, r)

def ws_done(n: Nat, -c: P.Ctx, -v: V.Json, -r: String) ->
  {R(r, P.SDone{c, v}) == R(Pr.Pr.spaces(n, r), P.SDone{c, v}) : P.Out}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ws_done(p, c, v, r)

# the claims: items sit at level 1n+lvl, their closer at lvl
def ICAp(x: V.Json, t: List<&2, V.Json>, ind: Nat, lvl: Nat, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match stk:
    case Con{P.FArr{acc}, s2}:
      {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json, List.reverse.go(&2, V.Json, x <> t, acc))}})
        == R(Pr.Pr.pp(V.JArr{x <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{']', Rest.str(rr)})),
          P.SVal{close, P.Ctx{P.FArr{acc} <> s2, room}}) : P.Out}
    case _:
      Unit

def ICOp(m: V.Member, t: List<&2, V.Member>, ind: Nat, lvl: Nat, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match stk:
    case Con{P.FObj{items, k0}, s2}:
      {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member, List.reverse.go(&2, V.Member, m <> t, items))}})
        == R(Pr.Pr.pp(V.JObj{m <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{'}', Rest.str(rr)})),
          P.SKey{close, P.Ctx{P.FObj{items, k0} <> s2, room}}) : P.Out}
    case _:
      Unit

def ICp(v: V.Json, ind: Nat, lvl: Nat, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match v:
    case V.JArr{Con{x, t}}:
      ICAp(x, t, ind, lvl, close, stk, room, rr)
    case V.JObj{Con{m, t}}:
      ICOp(m, t, ind, lvl, close, stk, room, rr)
    case _:
      Unit

def VCp(v: V.Json, mode: Nat, ind: Nat, lvl: Nat, close: Bool, stk: List<&2, P.Frame>, room: Nat, rr: Rest) -> Type:
  match mode:
    case 0n:
      ICp(v, ind, lvl, close, stk, room, rr)
    case 1n:
      {R(Rest.str(rr), Pend(v, P.Ctx{stk, room})) == R(Pr.Pr.pp(v, 1n, ind, lvl, Rest.str(rr)), P.SVal{close, P.Ctx{stk, room}}) : P.Out}
    case 2n+k:
      Unit

def arr_empty_p(-ind: Nat, -lvl: Nat, -close: Bool, -stk: List<&2, P.Frame>, room: Nat, -rr: Rest, h: DepH(V.JArr{Nil{}}, room)) ->
  VCp(V.JArr{Nil{}}, 1n, ind, lvl, close, stk, room, rr):
  match room:
    case 0n:
      %h : BM(_, VCp(V.JArr{Nil{}}, 1n, ind, lvl, close, stk, 0n, rr), Unit)
      Unit{}
    case 1n+r:
      {==}

def obj_empty_p(-ind: Nat, -lvl: Nat, -close: Bool, -stk: List<&2, P.Frame>, room: Nat, -rr: Rest, h: DepH(V.JObj{Nil{}}, room)) ->
  VCp(V.JObj{Nil{}}, 1n, ind, lvl, close, stk, room, rr):
  match room:
    case 0n:
      %h : BM(_, VCp(V.JObj{Nil{}}, 1n, ind, lvl, close, stk, 0n, rr), Unit)
      Unit{}
    case 1n+r:
      {==}

def arr_open_p(+x: V.Json, t: List<&2, V.Json>, +ind: Nat, +lvl: Nat, -close: Bool, +stk: List<&2, P.Frame>, +r: Nat, +rr: Rest) ->
  ICp(V.JArr{x <> t}, ind, lvl, True{}, P.FArr{Nil{}} <> stk, r, rr) -> VCp(V.JArr{x <> t}, 1n, ind, lvl, close, stk, 1n+r, rr):
  match t:
    case Nil{}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> Nil{}}}) == _ : P.Out}
        %lrev(V.Json, x <> Nil{}, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> Nil{}}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{_}}) : P.Out}
        {==})
    case Con{+y, +w}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> y <> w}}) == _ : P.Out}
        %lrev(V.Json, x <> y <> w, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{x <> y <> w}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JArr{_}}) : P.Out}
        {==})

def obj_open_p(+k: String, +x: V.Json, t: List<&2, V.Member>, +ind: Nat, +lvl: Nat, -close: Bool, +stk: List<&2, P.Frame>, +r: Nat, +rr: Rest) ->
  ICp(V.JObj{V.Mem{k, x} <> t}, ind, lvl, True{}, P.FObj{Nil{}, SNil{}} <> stk, r, rr) -> VCp(V.JObj{V.Mem{k, x} <> t}, 1n, ind, lvl, close, stk, 1n+r, rr):
  match t:
    case Nil{}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> Nil{}}}) == _ : P.Out}
        %lrev(V.Member, V.Mem{k, x} <> Nil{}, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> Nil{}}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{_}}) : P.Out}
        {==})
    case Con{+y, +w}:
      ih => (%ih : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> y <> w}}) == _ : P.Out}
        %lrev(V.Member, V.Mem{k, x} <> y <> w, Nil{}) : {R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{V.Mem{k, x} <> y <> w}})
          == R(Rest.str(rr), P.SDone{P.Ctx{stk, 1n+r}, V.JObj{_}}) : P.Out}
        {==})

def arr_last_p(+x: V.Json, +acc: List<&2, V.Json>, +s2: List<&2, P.Frame>, +ind: Nat, +lvl: Nat, +close: Bool, +room: Nat, +rr: Rest,
  +hx: NormH(x),
  ih: VCp(x, 1n, ind, 1n+lvl, close, P.FArr{acc} <> s2, room, RDl{DNl{}, Pr.Pr.spaces(Nat.mul(lvl, ind), SCon{']', Rest.str(rr)})})) ->
  ICAp(x, Nil{}, ind, lvl, close, P.FArr{acc} <> s2, room, rr):
  +c = {P.Ctx{P.FArr{acc} <> s2, room} : P.Ctx}
  +L = {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json, x <> acc)}}) : P.Out}
  %ws_val(Nat.mul(1n+lvl, ind), close, c, Pr.Pr.pp(x, 1n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{']', Rest.str(rr)}))) : {L == _ : P.Out}
  %ih : {L == _ : P.Out}
  %pend_dl(x, c, DNl{}, Pr.Pr.spaces(Nat.mul(lvl, ind), SCon{']', Rest.str(rr)}), hx) : {L == _ : P.Out}
  %ws_done(Nat.mul(lvl, ind), c, x, SCon{']', Rest.str(rr)}) : {L == _ : P.Out}
  {==}

def arr_next_p(+x: V.Json, +y: V.Json, +t: List<&2, V.Json>, +acc: List<&2, V.Json>, +s2: List<&2, P.Frame>, +ind: Nat, +lvl: Nat, +close: Bool,
  +room: Nat, +rr: Rest, +hx: NormH(x),
  ihx: VCp(x, 1n, ind, 1n+lvl, close, P.FArr{acc} <> s2, room,
    RDl{DComma{}, Pr.Pr.pp(V.JArr{y <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{']', Rest.str(rr)}))}),
  iht: ICAp(y, t, ind, lvl, False{}, P.FArr{x <> acc} <> s2, room, rr)) ->
  ICAp(x, y <> t, ind, lvl, close, P.FArr{acc} <> s2, room, rr):
  +c = {P.Ctx{P.FArr{acc} <> s2, room} : P.Ctx}
  +g = {Pr.Pr.pp(V.JArr{y <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{']', Rest.str(rr)})) : String}
  +L = {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JArr{List.reverse(&2, V.Json,
    List.reverse.go(&2, V.Json, x <> y <> t, acc))}}) : P.Out}
  %ws_val(Nat.mul(1n+lvl, ind), close, c, Pr.Pr.pp(x, 1n, ind, 1n+lvl, SCon{',', g})) : {L == _ : P.Out}
  %ihx : {L == _ : P.Out}
  %pend_dl(x, c, DComma{}, g, hx) : {L == _ : P.Out}
  iht

def obj_last_p(+k: String, +x: V.Json, +items: List<&2, V.Member>, +k0: String, +s2: List<&2, P.Frame>, +ind: Nat, +lvl: Nat,
  +close: Bool, +room: Nat, +rr: Rest, +hx: NormH(x),
  ih: VCp(x, 1n, ind, 1n+lvl, False{}, P.FObj{items, k} <> s2, room, RDl{DNl{}, Pr.Pr.spaces(Nat.mul(lvl, ind), SCon{'}', Rest.str(rr)})})) ->
  ICOp(V.Mem{k, x}, Nil{}, ind, lvl, close, P.FObj{items, k0} <> s2, room, rr):
  +c0 = {P.Ctx{P.FObj{items, k0} <> s2, room} : P.Ctx}
  +c = {P.Ctx{P.FObj{items, k} <> s2, room} : P.Ctx}
  +X = {Pr.Pr.pp(x, 1n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{'}', Rest.str(rr)})) : String}
  +L = {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member, V.Mem{k, x} <> items)}}) : P.Out}
  %ws_key(Nat.mul(1n+lvl, ind), close, c0, T.quote(k, SCon{':', SCon{' ', X}})) : {L == _ : P.Out}
  %key_str(k, close, c0, SCon{':', SCon{' ', X}}) : {L == _ : P.Out}
  %ih : {L == _ : P.Out}
  %pend_dl(x, c, DNl{}, Pr.Pr.spaces(Nat.mul(lvl, ind), SCon{'}', Rest.str(rr)}), hx) : {L == _ : P.Out}
  %ws_done(Nat.mul(lvl, ind), c, x, SCon{'}', Rest.str(rr)}) : {L == _ : P.Out}
  {==}

def obj_next_p(+k: String, +x: V.Json, +m2: V.Member, +t: List<&2, V.Member>, +items: List<&2, V.Member>, +k0: String, +s2: List<&2, P.Frame>,
  +ind: Nat, +lvl: Nat, +close: Bool, +room: Nat, +rr: Rest, +hx: NormH(x),
  ihx: VCp(x, 1n, ind, 1n+lvl, False{}, P.FObj{items, k} <> s2, room,
    RDl{DComma{}, Pr.Pr.pp(V.JObj{m2 <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{'}', Rest.str(rr)}))}),
  iht: ICOp(m2, t, ind, lvl, False{}, P.FObj{V.Mem{k, x} <> items, SNil{}} <> s2, room, rr)) ->
  ICOp(V.Mem{k, x}, m2 <> t, ind, lvl, close, P.FObj{items, k0} <> s2, room, rr):
  +c0 = {P.Ctx{P.FObj{items, k0} <> s2, room} : P.Ctx}
  +c = {P.Ctx{P.FObj{items, k} <> s2, room} : P.Ctx}
  +g = {Pr.Pr.pp(V.JObj{m2 <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{'}', Rest.str(rr)})) : String}
  +X = {Pr.Pr.pp(x, 1n, ind, 1n+lvl, SCon{',', g}) : String}
  +L = {R(Rest.str(rr), P.SDone{P.Ctx{s2, 1n+room}, V.JObj{List.reverse(&2, V.Member,
    List.reverse.go(&2, V.Member, V.Mem{k, x} <> m2 <> t, items))}}) : P.Out}
  %ws_key(Nat.mul(1n+lvl, ind), close, c0, T.quote(k, SCon{':', SCon{' ', X}})) : {L == _ : P.Out}
  %key_str(k, close, c0, SCon{':', SCon{' ', X}}) : {L == _ : P.Out}
  %ihx : {L == _ : P.Out}
  %pend_dl(x, c, DComma{}, g, hx) : {L == _ : P.Out}
  iht

def VLp(v: V.Json, mode: Nat, +ind: Nat, +lvl: Nat, +close: Bool, +stk: List<&2, P.Frame>, +room: Nat,
  +rr: Rest, +hn: NormH(v), +hd: DepH(v, Room(mode, room))) -> VCp(v, mode, ind, lvl, close, stk, room, rr):
  match v mode:
    case v0 2n+k:
      Unit{}
    case V.JNull{} 1n:
      {==}
    case V.JNull{} 0n:
      Unit{}
    case V.JBool{True{}} 1n:
      {==}
    case V.JBool{False{}} 1n:
      {==}
    case V.JBool{b} 0n:
      Unit{}
    case V.JNum{+n} 1n:
      run_num(n, close, hn, P.Ctx{stk, room}, Rest.str(rr))
    case V.JNum{n} 0n:
      Unit{}
    case V.JStr{+s} 1n:
      str_val(s, close, P.Ctx{stk, room}, Rest.str(rr))
    case V.JStr{s} 0n:
      Unit{}
    case V.JArr{Nil{}} 1n:
      arr_empty_p(ind, lvl, close, stk, room, rr, hd)
    case V.JArr{Nil{}} 0n:
      Unit{}
    case V.JArr{+x <> +t} 1n:
      match room:
        case 0n:
          %fst({Nat.is_le(1n+V.Json.depth(x), 0n) == True{} : Bool}, DepH(V.JArr{t}, 0n),
            dep_arr(x, t, 0n, hd)) : BM(_, VCp(V.JArr{x <> t}, 1n, ind, lvl, close, stk, 0n, rr), Unit)
          Unit{}
        case 1n++r:
          arr_open_p(x, t, ind, lvl, close, stk, r, rr)(VLp(V.JArr{x <> t}, 0n, ind, lvl, True{},
            P.FArr{Nil{}} <> stk, r, rr, hn, hd))
    case V.JArr{+x <> Nil{}} 0n:
      match stk:
        case Con{P.FArr{+acc}, +s2}:
          +hx = fst(NormH(x), NormH(V.JArr{Nil{}}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JArr{Nil{}}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JArr{Nil{}}, 1n+room), dep_arr(x, Nil{}, 1n+room, hd)))
          arr_last_p(x, acc, s2, ind, lvl, close, room, rr, hx,
            VLp(x, 1n, ind, 1n+lvl, close, P.FArr{acc} <> s2, room, RDl{DNl{}, Pr.Pr.spaces(Nat.mul(lvl, ind), SCon{']', Rest.str(rr)})}, hx, hdx))
        case Nil{}:
          Unit{}
        case Con{P.FObj{a, b}, s2}:
          Unit{}
    case V.JArr{+x <> (+y <> +t)} 0n:
      match stk:
        case Con{P.FArr{+acc}, +s2}:
          +hx = fst(NormH(x), NormH(V.JArr{y <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JArr{y <> t}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JArr{y <> t}, 1n+room), dep_arr(x, y <> t, 1n+room, hd)))
          arr_next_p(x, y, t, acc, s2, ind, lvl, close, room, rr, hx,
            VLp(x, 1n, ind, 1n+lvl, close, P.FArr{acc} <> s2, room,
              RDl{DComma{}, Pr.Pr.pp(V.JArr{y <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{']', Rest.str(rr)}))}, hx, hdx),
            VLp(V.JArr{y <> t}, 0n, ind, lvl, False{}, P.FArr{x <> acc} <> s2, room, rr,
              snd(NormH(x), NormH(V.JArr{y <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JArr{y <> t}), hn)),
              snd({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JArr{y <> t}, 1n+room), dep_arr(x, y <> t, 1n+room, hd))))
        case Nil{}:
          Unit{}
        case Con{P.FObj{a, b}, s2}:
          Unit{}
    case V.JObj{Nil{}} 1n:
      obj_empty_p(ind, lvl, close, stk, room, rr, hd)
    case V.JObj{Nil{}} 0n:
      Unit{}
    case V.JObj{V.Mem{+k, +x} <> +t} 1n:
      match room:
        case 0n:
          %fst({Nat.is_le(1n+V.Json.depth(x), 0n) == True{} : Bool}, DepH(V.JObj{t}, 0n),
            dep_obj(k, x, t, 0n, hd)) : BM(_, VCp(V.JObj{V.Mem{k, x} <> t}, 1n, ind, lvl, close, stk, 0n, rr), Unit)
          Unit{}
        case 1n++r:
          obj_open_p(k, x, t, ind, lvl, close, stk, r, rr)(VLp(V.JObj{V.Mem{k, x} <> t}, 0n, ind, lvl,
            True{}, P.FObj{Nil{}, SNil{}} <> stk, r, rr, hn, hd))
    case V.JObj{V.Mem{+k, +x} <> Nil{}} 0n:
      match stk:
        case Con{P.FObj{+items, +k0}, +s2}:
          +hx = fst(NormH(x), NormH(V.JObj{Nil{}}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JObj{Nil{}}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JObj{Nil{}}, 1n+room), dep_obj(k, x, Nil{}, 1n+room, hd)))
          obj_last_p(k, x, items, k0, s2, ind, lvl, close, room, rr, hx,
            VLp(x, 1n, ind, 1n+lvl, False{}, P.FObj{items, k} <> s2, room, RDl{DNl{}, Pr.Pr.spaces(Nat.mul(lvl, ind), SCon{'}', Rest.str(rr)})}, hx, hdx))
        case Nil{}:
          Unit{}
        case Con{P.FArr{a}, s2}:
          Unit{}
    case V.JObj{V.Mem{+k, +x} <> (+m2 <> +t)} 0n:
      match stk:
        case Con{P.FObj{+items, +k0}, +s2}:
          +hx = fst(NormH(x), NormH(V.JObj{m2 <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JObj{m2 <> t}), hn))
          +hdx = deg(x, room, fst({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JObj{m2 <> t}, 1n+room), dep_obj(k, x, m2 <> t, 1n+room, hd)))
          obj_next_p(k, x, m2, t, items, k0, s2, ind, lvl, close, room, rr, hx,
            VLp(x, 1n, ind, 1n+lvl, False{}, P.FObj{items, k} <> s2, room,
              RDl{DComma{}, Pr.Pr.pp(V.JObj{m2 <> t}, 0n, ind, 1n+lvl, Pr.Pr.nl(ind, lvl, SCon{'}', Rest.str(rr)}))}, hx, hdx),
            VLp(V.JObj{m2 <> t}, 0n, ind, lvl, False{}, P.FObj{V.Mem{k, x} <> items, SNil{}} <> s2, room, rr,
              snd(NormH(x), NormH(V.JObj{m2 <> t}), and_true(V.Json.is_norm(x), V.Json.is_norm(V.JObj{m2 <> t}), hn)),
              snd({Nat.is_le(1n+V.Json.depth(x), 1n+room) == True{} : Bool}, DepH(V.JObj{m2 <> t}, 1n+room), dep_obj(k, x, m2 <> t, 1n+room, hd))))
        case Nil{}:
          Unit{}
        case Con{P.FArr{a}, s2}:
          Unit{}

def Laws.roundtrip_pretty(ind, v, h1, h2):
  %VLp(v, 1n, ind, 0n, False{}, Nil{}, 512n, REnd{}, h1, h2) :
    {P.P.out(_, String.length(Pr.pretty(ind, v))) == Done{v} : Result<&2, &2, P.Err, V.Json>}
  %eof_pend(v, 512n, h1, String.length(Pr.pretty(ind, v))) : {_ == Done{v} : Result<&2, &2, P.Err, V.Json>}
  {==}
