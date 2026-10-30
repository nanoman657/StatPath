# bignat.bend: arbitrary naturals as 16-bit limbs held in U32s.
#
# A Big is a List of limbs, least significant first, each below 2^16 and
# with no zero limb on top, so 0 is the empty list. Every step multiplies a
# limb by a small factor (below 2^16) and adds a carry below 2^16, so each
# product and carry fits in 32 bits.

import Base

def Big.norm.one(+h: U32, z: Bool) -> List<&2, U32>:
  match z:
    case True{}:
      Nil{}
    case False{}:
      [h]

def Big.norm.fin(+h: U32, t: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Nil{}:
      Big.norm.one(h, U32.is_zero(h))
    case x <> r:
      h <> x <> r

# drops the zero limbs on top
def Big.norm(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Big.norm.fin(h, Big.norm(t))

def Big.is_zero(xs: List<&2, U32>) -> Bool:
  List.is_empty(&2, U32, xs)

def Big.small(+c: U32, z: Bool) -> List<&2, U32>:
  match z:
    case True{}:
      Nil{}
    case False{}:
      [c]

# xs * m + c, for m and c below 2^16
def Big.mul_add(xs: List<&2, U32>, +m: U32, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Big.small(c, U32.is_zero(c))
    case h <> t:
      +v = (h * m + c : U32)
      (v .&. 65535 : U32) <> Big.mul_add(t, m, (v >> 16n : U32))

def Big.divmod.go(xs: List<&2, U32>, +d: U32, +r: U32, acc: List<&2, U32>) ->
  List<&2, U32> & U32:
  match xs:
    case Nil{}:
      (Big.norm(acc), r)
    case h <> t:
      +v = ((r << 16n) .|. h : U32)
      Big.divmod.go(t, d, (v % d : U32), (v / d : U32) <> acc)

# the quotient and remainder of xs by d, for 0 < d < 2^16
def Big.divmod(xs: List<&2, U32>, +d: U32) -> List<&2, U32> & U32:
  Big.divmod.go(List.reverse(&2, U32, xs), d, 0, Nil{})

def Big.bits.go(xs: List<&2, U32>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> Nil{}:
      Nat.add(Nat.mul(n, 16n), 1n+U32.log2(h))
    case h <> (x <> t):
      Big.bits.go(x <> t, 1n+n)

# the number of bits: 0 for 0
def Big.bits(xs: List<&2, U32>) -> Nat:
  Big.bits.go(xs, 0n)

def Big.of_digits(ds: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> t:
      Big.mul_add(Big.of_digits(t), 10, d)

def Big.mul_pow10.go(p: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match p:
    case 0n:
      xs
    case 1n+q:
      Big.mul_pow10.go(q, Big.mul_add(xs, 10, 0))

def Big.mul_pow10(xs: List<&2, U32>, p: Nat) -> List<&2, U32>:
  Big.mul_pow10.go(p, xs)

def Big.zeros(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      0 <> Big.zeros(p, xs)

def Big.shl.at(+xs: List<&2, U32>, qr: Nat & Nat) -> List<&2, U32>:
  (q, r) = qr
  Big.mul_add(Big.zeros(q, xs), U32.shln(1, r), 0)

# xs * 2^n
def Big.shl(+xs: List<&2, U32>, n: Nat) -> List<&2, U32>:
  Big.shl.at(xs, Nat.divmod(n, 16n))

def Big.sticky(r: List<&2, U32> & U32, s: Bool) -> List<&2, U32> & Bool:
  (q, +m) = r
  (q, Bool.or(s, U32.is_ne(m, 0)))

# floor(xs / 10^p), and whether anything was lost (or s already was)
def Big.div_pow10.go(p: Nat, r: List<&2, U32> & Bool) -> List<&2, U32> & Bool:
  match p:
    case 0n:
      r
    case 1n+k:
      (xs, s) = r
      Big.div_pow10.go(k, Big.sticky(Big.divmod(xs, 10), s))

def Big.div_pow10(xs: List<&2, U32>, p: Nat, s: Bool) -> List<&2, U32> & Bool:
  Big.div_pow10.go(p, (xs, s))

def Big.drop(xs: List<&2, U32>, n: Nat, s: Bool) -> List<&2, U32> & Bool:
  match xs n:
    case ys 0n:
      (ys, s)
    case Nil{} 1n+p:
      (Nil{}, s)
    case (+h <> t) 1n+p:
      Big.drop(t, p, Bool.or(s, U32.is_ne(h, 0)))

def Big.shr.bits(r: Nat, ds: List<&2, U32> & Bool) -> List<&2, U32> & Bool:
  (ys, s) = ds
  Big.sticky(Big.divmod(ys, U32.shln(1, r)), s)

def Big.shr.at(qr: Nat & Nat, xs: List<&2, U32>, s: Bool) -> List<&2, U32> & Bool:
  (q, r) = qr
  Big.shr.bits(r, Big.drop(xs, q, s))

# floor(xs / 2^n), and whether a 1 bit was lost (or s already was)
def Big.shr(xs: List<&2, U32>, n: Nat, s: Bool) -> List<&2, U32> & Bool:
  Big.shr.at(Nat.divmod(n, 16n), xs, s)

# the low 32 bits
def Big.low(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case a <> Nil{}:
      a
    case a <> (b <> t):
      (a .|. (b << 16n) : U32)

def Big.is_eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{a, at} Con{b, bt}:
      Bool.and(U32.is_eq(a, b), Big.is_eq(at, bt))
    case _ _:
      False{}

# the decimal text of xs, for tests
def Big.show.go(f: Nat, qr: List<&2, U32> & U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+g:
      (q, r) = qr
      match q:
        case Nil{}:
          SCon{Chr{(48 + r : U32)}, acc}
        case h <> t:
          Big.show.go(g, Big.divmod(h <> t, 10), SCon{Chr{(48 + r : U32)}, acc})

def Big.show(+xs: List<&2, U32>) -> String:
  Big.show.go(Nat.mul(5n, 1n+List.length(&2, U32, xs)), Big.divmod(xs, 10), SNil{})
