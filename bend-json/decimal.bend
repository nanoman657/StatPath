# decimal.bend: exact JSON numbers.
#
# A Num is sign * coef * 10^(esign exp), every part exact:
# - coef: a decimal natural as a List of Digits, least significant first
# - exp:  the exponent's magnitude, also least significant first
# A normalized Num has no zero digit at either end of coef (trailing zeros
# move into the exponent), no high zero in exp, and zero is the single value
# Num{False, [], False, []}. Equal numbers are then equal values.

import Base
import ./bignat.bend as B

type Digit is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

type Num is Data:
  Num{neg: Bool, coef: List<&2, Digit>, eneg: Bool, exp: List<&2, Digit>}

# A signed exponent, used while normalizing
type SExp is Data:
  SExp{neg: Bool, mag: List<&2, Digit>}

# Digit
# -----

def Digit.to_char(d: Digit) -> Char:
  match d:
    case D0{}:
      '0'
    case D1{}:
      '1'
    case D2{}:
      '2'
    case D3{}:
      '3'
    case D4{}:
      '4'
    case D5{}:
      '5'
    case D6{}:
      '6'
    case D7{}:
      '7'
    case D8{}:
      '8'
    case D9{}:
      '9'

def Digit.to_nat(d: Digit) -> Nat:
  match d:
    case D0{}:
      0n
    case D1{}:
      1n
    case D2{}:
      2n
    case D3{}:
      3n
    case D4{}:
      4n
    case D5{}:
      5n
    case D6{}:
      6n
    case D7{}:
      7n
    case D8{}:
      8n
    case D9{}:
      9n

def Digit.of_char(c: Char) -> Maybe<&2, Digit>:
  match c:
    case '0':
      Some{D0{}}
    case '1':
      Some{D1{}}
    case '2':
      Some{D2{}}
    case '3':
      Some{D3{}}
    case '4':
      Some{D4{}}
    case '5':
      Some{D5{}}
    case '6':
      Some{D6{}}
    case '7':
      Some{D7{}}
    case '8':
      Some{D8{}}
    case '9':
      Some{D9{}}
    case _:
      None{}

# a non-digit reads as 0: for text known to be digits
def Digit.of_char_total(c: Char) -> Digit:
  match c:
    case '1':
      D1{}
    case '2':
      D2{}
    case '3':
      D3{}
    case '4':
      D4{}
    case '5':
      D5{}
    case '6':
      D6{}
    case '7':
      D7{}
    case '8':
      D8{}
    case '9':
      D9{}
    case _:
      D0{}

def Digit.to_u32(d: Digit) -> U32:
  U32.from_nat(Digit.to_nat(d))

def Digit.is_eq(a: Digit, b: Digit) -> Bool:
  Nat.is_eq(Digit.to_nat(a), Digit.to_nat(b))

# Dec: a decimal natural, least significant digit first
# ---

def Dec.inc(xs: List<&2, Digit>) -> List<&2, Digit>:
  match xs:
    case Nil{}:
      [D1{}]
    case D0{} <> t:
      D1{} <> t
    case D1{} <> t:
      D2{} <> t
    case D2{} <> t:
      D3{} <> t
    case D3{} <> t:
      D4{} <> t
    case D4{} <> t:
      D5{} <> t
    case D5{} <> t:
      D6{} <> t
    case D6{} <> t:
      D7{} <> t
    case D7{} <> t:
      D8{} <> t
    case D8{} <> t:
      D9{} <> t
    case D9{} <> t:
      D0{} <> Dec.inc(t)

# the predecessor of a normalized Dec, normalized; 0 stays 0
def Dec.dec(xs: List<&2, Digit>) -> List<&2, Digit>:
  match xs:
    case Nil{}:
      Nil{}
    case D0{} <> t:
      D9{} <> Dec.dec(t)
    case D1{} <> Nil{}:
      Nil{}
    case D1{} <> (h <> t):
      D0{} <> h <> t
    case D2{} <> t:
      D1{} <> t
    case D3{} <> t:
      D2{} <> t
    case D4{} <> t:
      D3{} <> t
    case D5{} <> t:
      D4{} <> t
    case D6{} <> t:
      D5{} <> t
    case D7{} <> t:
      D6{} <> t
    case D8{} <> t:
      D7{} <> t
    case D9{} <> t:
      D8{} <> t

# applies Dec.inc n times
def Dec.iter(n: Nat, xs: List<&2, Digit>) -> List<&2, Digit>:
  match n:
    case 0n:
      xs
    case 1n+p:
      Dec.iter(p, Dec.inc(xs))

def Dec.norm.one(d: Digit) -> List<&2, Digit>:
  match d:
    case D0{}:
      Nil{}
    case o:
      [o]

def Dec.norm.fin(d: Digit, t: List<&2, Digit>) -> List<&2, Digit>:
  match t:
    case Nil{}:
      Dec.norm.one(d)
    case h <> r:
      d <> h <> r

# drops the high zeros
def Dec.norm(xs: List<&2, Digit>) -> List<&2, Digit>:
  match xs:
    case Nil{}:
      Nil{}
    case d <> t:
      Dec.norm.fin(d, Dec.norm(t))

def Dec.strip_low.fin(r: SExp) -> SExp:
  match r:
    case SExp{b, m}:
      SExp{b, m}

def Dec.strip_low.inc(r: List<&2, Digit> & Nat) -> List<&2, Digit> & Nat:
  (xs, n) = r
  (xs, 1n+n)

# drops the low zeros and counts them
def Dec.strip_low(xs: List<&2, Digit>) -> List<&2, Digit> & Nat:
  match xs:
    case D0{} <> t:
      Dec.strip_low.inc(Dec.strip_low(t))
    case o:
      (o, 0n)

def Dec.to_nat(xs: List<&2, Digit>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case d <> t:
      Nat.add(Digit.to_nat(d), Nat.mul(Dec.to_nat(t), 10n))

def Dec.is_eq(xs: List<&2, Digit>, ys: List<&2, Digit>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      Bool.and(Digit.is_eq(a, b), Dec.is_eq(at, bt))
    case _ _:
      False{}

# the digits, most significant first, in front of acc
def Dec.show(xs: List<&2, Digit>, acc: String) -> String:
  match xs:
    case Nil{}:
      acc
    case d <> t:
      Dec.show(t, SCon{Digit.to_char(d), acc})

# reads decimal text, most significant first, onto acc
def Dec.of_chars(s: String, acc: List<&2, Digit>) -> List<&2, Digit>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      Dec.of_chars(t, Digit.of_char_total(c) <> acc)

def Dec.of_nat(n: Nat) -> List<&2, Digit>:
  Dec.norm(Dec.of_chars(Nat.show(n), Nil{}))

# whether no digit is zero at either end (the empty Dec counts too)
def Dec.is_norm(xs: List<&2, Digit>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case d <> Nil{}:
      Bool.not(Digit.is_eq(d, D0{}))
    case d <> (h <> r):
      Dec.is_norm(h <> r)

def Str.zeros(n: Nat, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      SCon{'0', Str.zeros(p, acc)}

# SExp
# ----

def SExp.mk(neg: Bool, m: List<&2, Digit>) -> SExp:
  match m:
    case Nil{}:
      SExp{False{}, Nil{}}
    case h <> t:
      SExp{neg, h <> t}

def SExp.inc(e: SExp) -> SExp:
  match e:
    case SExp{False{}, m}:
      SExp{False{}, Dec.inc(m)}
    case SExp{True{}, m}:
      SExp.mk(True{}, Dec.dec(m))

def SExp.dec(e: SExp) -> SExp:
  match e:
    case SExp{False{}, Nil{}}:
      SExp{True{}, [D1{}]}
    case SExp{False{}, h <> t}:
      SExp{False{}, Dec.dec(h <> t)}
    case SExp{True{}, m}:
      SExp{True{}, Dec.inc(m)}

def SExp.add_n(k: Nat, e: SExp) -> SExp:
  match k:
    case 0n:
      e
    case 1n+p:
      SExp.add_n(p, SExp.inc(e))

def SExp.sub_n(k: Nat, e: SExp) -> SExp:
  match k:
    case 0n:
      e
    case 1n+p:
      SExp.sub_n(p, SExp.dec(e))

# Num
# ---

def Num.zero() -> Num:
  Num{False{}, Nil{}, False{}, Nil{}}

def Num.make.at(neg: Bool, h: Digit, t: List<&2, Digit>, e: SExp) -> Num:
  match e:
    case SExp{s, m}:
      Num{neg, h <> t, s, m}

def Num.make.fin(neg: Bool, ct: List<&2, Digit> & Nat, eneg: Bool,
  e: List<&2, Digit>, fl: Nat) -> Num:
  (c, tz) = ct
  match c:
    case Nil{}:
      Num.zero()
    case h <> t:
      Num.make.at(neg, h, t,
        SExp.sub_n(fl, SExp.add_n(tz, SExp.mk(eneg, Dec.norm(e)))))

# the normalized number acc * 10^(eneg e - fl): acc and e are read digits,
# least significant first, with any zeros, and fl counts fraction digits
def Num.make(neg: Bool, acc: List<&2, Digit>, eneg: Bool, e: List<&2, Digit>,
  fl: Nat) -> Num:
  Num.make.fin(neg, Dec.strip_low(Dec.norm(acc)), eneg, e, fl)

def Num.normalize(n: Num) -> Num:
  match n:
    case Num{neg, c, eneg, e}:
      Num.make(neg, c, eneg, e, 0n)

def Num.is_norm.exp(eneg: Bool, e: List<&2, Digit>) -> Bool:
  match e:
    case Nil{}:
      Bool.not(eneg)
    case h <> t:
      Dec.is_norm(h <> t)

def Num.is_norm(n: Num) -> Bool:
  match n:
    case Num{neg, Nil{}, eneg, e}:
      Bool.not(neg || eneg || Bool.not(List.is_empty(&2, Digit, e)))
    case Num{neg, D0{} <> t, eneg, e}:
      False{}
    case Num{neg, h <> t, eneg, e}:
      Dec.is_norm(h <> t) && Num.is_norm.exp(eneg, e)

def Bool.is_eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

# structural equality: numeric equality on normalized numbers
def Num.is_eq(a: Num, b: Num) -> Bool:
  match a b:
    case Num{n1, c1, s1, e1} Num{n2, c2, s2, e2}:
      Bool.is_eq(n1, n2) && Dec.is_eq(c1, c2) && Bool.is_eq(s1, s2)
        && Dec.is_eq(e1, e2)

# Printing
# --------
# A normalized number c * 10^e prints as JSON in one of four forms:
# - plain digits, with e zeros when 0 <= e and len(c) + e <= 21: 1500
# - a point inside the digits when -len(c) < e < 0: 19.99
# - "0." and up to 5 zeros when -len(c) - 5 <= e <= -len(c): 0.0025
# - else the digits with an exponent: 15e+399, 1e-400

def Num.show.sign(neg: Bool, s: String) -> String:
  match neg:
    case True{}:
      SCon{'-', s}
    case False{}:
      s

def Num.show.esign(neg: Bool, s: String) -> String:
  match neg:
    case True{}:
      SCon{'-', s}
    case False{}:
      SCon{'+', s}

def Num.show.exp(c: List<&2, Digit>, eneg: Bool, e: List<&2, Digit>,
  acc: String) -> String:
  Dec.show(c, SCon{'e', Num.show.esign(eneg, Dec.show(e, acc))})

def Num.show.pos.fit(+c: List<&2, Digit>, +e: List<&2, Digit>, acc: String,
  fit: Bool) -> String:
  match fit:
    case True{}:
      Dec.show(c, Str.zeros(Dec.to_nat(e), acc))
    case False{}:
      Num.show.exp(c, False{}, e, acc)

def Num.show.pos(+c: List<&2, Digit>, +e: List<&2, Digit>, acc: String,
  small: Bool) -> String:
  match small:
    case True{}:
      Num.show.pos.fit(c, e, acc, Nat.is_le(Nat.add(List.length(&2, Digit, c),
        Dec.to_nat(e)), 21n))
    case False{}:
      Num.show.exp(c, False{}, e, acc)

def Num.show.neg.zeros(+c: List<&2, Digit>, +e: List<&2, Digit>, +k: Nat,
  +l: Nat, acc: String, fit: Bool) -> String:
  match fit:
    case True{}:
      SCon{'0', SCon{'.', Str.zeros(Nat.sub(k, l), Dec.show(c, acc))}}
    case False{}:
      Num.show.exp(c, True{}, e, acc)

def Num.show.neg.point(+c: List<&2, Digit>, +e: List<&2, Digit>, +k: Nat,
  +l: Nat, acc: String, inside: Bool) -> String:
  match inside:
    case True{}:
      Dec.show(List.drop(&2, Digit, c, k),
        SCon{'.', Dec.show(List.take(&2, Digit, c, k), acc)})
    case False{}:
      Num.show.neg.zeros(c, e, k, l, acc, Nat.is_le(Nat.sub(k, l), 5n))

def Num.show.neg.at(+c: List<&2, Digit>, +e: List<&2, Digit>, +k: Nat,
  acc: String) -> String:
  +l = List.length(&2, Digit, c)
  Num.show.neg.point(c, e, k, l, acc, Nat.is_lt(k, l))

def Num.show.neg(+c: List<&2, Digit>, +e: List<&2, Digit>, acc: String,
  small: Bool) -> String:
  match small:
    case True{}:
      Num.show.neg.at(c, e, Dec.to_nat(e), acc)
    case False{}:
      Num.show.exp(c, True{}, e, acc)

def Num.show.body(+c: List<&2, Digit>, eneg: Bool, +e: List<&2, Digit>,
  acc: String) -> String:
  match eneg e:
    case False{} Nil{}:
      Dec.show(c, acc)
    case False{} h <> t:
      Num.show.pos(c, h <> t, acc, Nat.is_le(List.length(&2, Digit, h <> t), 2n))
    case True{} m:
      Num.show.neg(c, m, acc, Nat.is_le(List.length(&2, Digit, m), 6n))

# the JSON text of n in front of acc
def Num.show(n: Num, acc: String) -> String:
  match n:
    case Num{neg, Nil{}, eneg, e}:
      SCon{'0', acc}
    case Num{neg, h <> t, eneg, e}:
      Num.show.sign(neg, Num.show.body(h <> t, eneg, e, acc))

def Num.to_string(n: Num) -> String:
  Num.show(n, SNil{})

# Conversions
# -----------

def Num.to_nat.read(+c: List<&2, Digit>, +e: Nat, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Nat.read(Dec.show(c, Str.zeros(e, SNil{})))

def Num.to_nat.fits(+c: List<&2, Digit>, +e: Nat) -> Maybe<&2, Nat>:
  Num.to_nat.read(c, e,
    Nat.is_le(Nat.add(List.length(&2, Digit, c), e), 15n))

def Num.to_nat.gate(+c: List<&2, Digit>, +e: List<&2, Digit>, small: Bool) ->
  Maybe<&2, Nat>:
  match small:
    case False{}:
      None{}
    case True{}:
      Num.to_nat.fits(c, Dec.to_nat(e))

# the Nat n is, if n is a natural below 2^48 (Base's largest Nat); n is
# taken normalized
def Num.to_nat(n: Num) -> Maybe<&2, Nat>:
  match n:
    case Num{neg, Nil{}, eneg, e}:
      Some{0n}
    case Num{True{}, h <> t, eneg, e}:
      None{}
    case Num{False{}, h <> t, True{}, e}:
      None{}
    case Num{False{}, h <> t, False{}, +e}:
      Num.to_nat.gate(h <> t, e, Nat.is_le(List.length(&2, Digit, e), 2n))

def Num.to_u32.at(+x: Nat, ok: Bool) -> Maybe<&2, U32>:
  match ok:
    case True{}:
      Some{U32.from_nat(x)}
    case False{}:
      None{}

def Num.to_u32.fin(m: Maybe<&2, Nat>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{+x}:
      Num.to_u32.at(x, Nat.is_le(x, 4294967295n))

# the U32 n is, if n is a natural below 2^32
def Num.to_u32(n: Num) -> Maybe<&2, U32>:
  Num.to_u32.fin(Num.to_nat(n))

def Num.from_nat(n: Nat) -> Num:
  Num.make(False{}, Dec.of_chars(Nat.show(n), Nil{}), False{}, Nil{}, 0n)

def Num.from_u32(x: U32) -> Num:
  Num.from_nat(U32.to_nat(x))

# F32
# ---
# to_f32 rounds to the nearest F32, ties to even, with subnormals and
# infinities, as IEEE 754 decimal conversion does. It is lossy: an F32 has
# 24 bits of precision. The work is exact on Bigs: past 120 significant
# digits the rest only count as a nonzero tail, as no F32 tie needs more.

def Num.f32.big(c: List<&2, Digit>) -> List<&2, U32>:
  match c:
    case Nil{}:
      Nil{}
    case d <> t:
      B.Big.mul_add(Num.f32.big(t), 10, Digit.to_u32(d))

def F32.inf() -> F32:
  F32.div(1.0, 0.0)

# f * 2^x, or f / 2^x: each step is exact until the result is reached
def F32.scale(x: Nat, +up: Bool, f: F32) -> F32:
  match x:
    case 0n:
      f
    case 1n+p:
      F32.scale(p, up, F32.mul(f, Bool.pick(F32, up, 2.0, 0.5)))

def Num.f32.build(+m: U32, +shift: Nat, +s: Nat) -> F32:
  F32.scale(Nat.sub(Nat.max(shift, s), Nat.min(shift, s)), Nat.is_ge(shift, s),
    U32.to_f32(m))

def Num.f32.round.at(r: List<&2, U32> & Bool, +shift: Nat, +s: Nat) -> F32:
  (q1, st) = r
  +q = B.Big.low(q1)
  +m0 = (q >> 1n : U32)
  +up = Bool.and(U32.is_eq((q .&. 1 : U32), 1),
    Bool.or(st, U32.is_eq((m0 .&. 1 : U32), 1)))
  Num.f32.build((m0 + Bool.to_u32(up) : U32), shift, s)

# rounds m away the low shift bits; the value is m * 2^-s
def Num.f32.round(+m: List<&2, U32>, shift: Nat, +s: Nat, st: Bool) -> F32:
  match shift:
    case 0n:
      Num.f32.build(B.Big.low(m), 0n, s)
    case 1n++sh:
      Num.f32.round.at(B.Big.shr(m, sh, st), 1n+sh, s)

# keeps 24 bits, or fewer below the normal range, whose last is 2^-149
def Num.f32.finish(+m: List<&2, U32>, +s: Nat, st: Bool) -> F32:
  +bl = B.Big.bits(m)
  +shift = Bool.pick(Nat, Nat.is_le(s, Nat.add(bl, 125n)), Nat.sub(bl, 24n),
    Nat.sub(s, 149n))
  Num.f32.round(m, shift, s, st)

def Num.f32.neg.at(r: List<&2, U32> & Bool, +s: Nat) -> F32:
  (m, st) = r
  Num.f32.finish(m, s, st)

# n / 10^q: scaled by 2^s first, so the quotient keeps 26 bits or more
def Num.f32.neg(+n: List<&2, U32>, +q: Nat, st: Bool) -> F32:
  +s = Nat.sub(Nat.add(Nat.mul(4n, q), 26n), B.Big.bits(n))
  Num.f32.neg.at(B.Big.div_pow10(B.Big.shl(n, s), q, st), s)

def Num.f32.core.neg(+n: List<&2, U32>, +k: Nat, +j: Nat, st: Bool, up: Bool) ->
  F32:
  match up:
    case True{}:
      Num.f32.finish(B.Big.mul_pow10(n, Nat.sub(j, k)), 0n, st)
    case False{}:
      Num.f32.neg(n, Nat.sub(k, j), st)

def Num.f32.core(+n: List<&2, U32>, eneg: Bool, +k: Nat, +j: Nat, st: Bool) ->
  F32:
  match eneg:
    case False{}:
      Num.f32.finish(B.Big.mul_pow10(n, Nat.add(k, j)), 0n, st)
    case True{}:
      Num.f32.core.neg(n, k, j, st, Nat.is_ge(j, k))

def Num.f32.trunc(+c: List<&2, Digit>, eneg: Bool, +k: Nat, +l: Nat, long: Bool) ->
  F32:
  match long:
    case False{}:
      Num.f32.core(Num.f32.big(c), eneg, k, 0n, False{})
    case True{}:
      +j = Nat.sub(l, 120n)
      Num.f32.core(Num.f32.big(List.drop(&2, Digit, c, j)), eneg, k, j, True{})

def Num.f32.range(+c: List<&2, Digit>, eneg: Bool, +k: Nat, +l: Nat, out: Bool) ->
  F32:
  match eneg out:
    case False{} True{}:
      F32.inf()
    case True{} True{}:
      0.0
    case e False{}:
      Num.f32.trunc(c, e, k, l, Nat.is_gt(l, 120n))

def Num.f32.mag.at(+c: List<&2, Digit>, eneg: Bool, +k: Nat, +l: Nat) -> F32:
  match eneg:
    case False{}:
      Num.f32.range(c, False{}, k, l, Nat.is_gt(Nat.add(l, k), 39n))
    case True{}:
      Num.f32.range(c, True{}, k, l, Nat.is_ge(k, Nat.add(l, 46n)))

def Num.f32.mag(+c: List<&2, Digit>, eneg: Bool, +k: Nat) -> F32:
  Num.f32.mag.at(c, eneg, k, List.length(&2, Digit, c))

def Num.f32.gate(+c: List<&2, Digit>, eneg: Bool, +e: List<&2, Digit>,
  small: Bool) -> F32:
  match eneg small:
    case s True{}:
      Num.f32.mag(c, s, Dec.to_nat(e))
    case False{} False{}:
      F32.inf()
    case True{} False{}:
      0.0

def Num.f32.sign(neg: Bool, f: F32) -> F32:
  match neg:
    case True{}:
      F32.neg(f)
    case False{}:
      f

# the nearest F32 to n (lossy)
def Num.to_f32(n: Num) -> F32:
  match n:
    case Num{neg, Nil{}, eneg, e}:
      0.0
    case Num{neg, h <> t, eneg, +e}:
      Num.f32.sign(neg, Num.f32.gate(h <> t, eneg, e,
        Nat.is_le(List.length(&2, Digit, e), 9n)))
