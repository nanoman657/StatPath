# bigint.bend: unsigned big integers as little-endian lists of 16-bit limbs
# (List<&2, Nat>, each limb below 2^16), and Montgomery multiplication modulo
# an odd modulus. A modulus of n limbs is held in lists of n + 2 limbs, so no
# carry runs off the end.

import Base

# the list of n zero limbs
def bi.zeros(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0n <> bi.zeros(p)

# t + k * x + c, limb by limb (t and x have the same length); the final carry
# is dropped, so t must be long enough to hold the result
def bi.addk(t: List<&2, Nat>, x: List<&2, Nat>, +k: Nat, +c: Nat) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Nil{}
    case a <> at:
      match x:
        case Nil{}:
          Nil{}
        case b <> bt:
          +v = Nat.add(Nat.add(a, Nat.mul(k, b)), c)
          Nat.mod(v, 65536n) <> bi.addk(at, bt, k, Nat.div(v, 65536n))

# the limb of a difference with its borrow folded in, and the rest's result
def bi.subb.cons(+v: Nat, r: List<&2, Nat> & Nat) -> List<&2, Nat> & Nat:
  (rest, bo) = r
  (Nat.mod(v, 65536n) <> rest, bo)

# a - b - borrow, limb by limb (same length): the difference and the final
# borrow, 1 when a < b
def bi.subb(a: List<&2, Nat>, b: List<&2, Nat>, +borrow: Nat) -> List<&2, Nat> & Nat:
  match a:
    case Nil{}:
      (Nil{}, borrow)
    case +x <> xt:
      match b:
        case Nil{}:
          (Nil{}, borrow)
        case +y <> yt:
          bi.subb.cons(Nat.sub(Nat.add(x, 65536n), Nat.add(y, borrow)),
            bi.subb(xt, yt, Nat.sub(1n, Nat.div(Nat.sub(Nat.add(x, 65536n), Nat.add(y, borrow)), 65536n))))

def bi.csub.choose(a: List<&2, Nat>, d: List<&2, Nat>, bo: Nat) -> List<&2, Nat>:
  match bo:
    case 0n:
      d
    case 1n+_:
      a

def bi.csub.pick(a: List<&2, Nat>, r: List<&2, Nat> & Nat) -> List<&2, Nat>:
  (d, bo) = r
  bi.csub.choose(a, d, bo)

# a - m when a >= m, else a (both of the same length)
def bi.csub(+a: List<&2, Nat>, +m: List<&2, Nat>) -> List<&2, Nat>:
  bi.csub.pick(a, bi.subb(a, m, 0n))

# drop the lowest limb and add a zero on top, keeping the length
def bi.shift1(t: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Nil{}
    case x <> xt:
      List.append(&2, Nat, xt, 0n <> Nil{})

# the lowest limb of t
def bi.low(t: List<&2, Nat>) -> Nat:
  match t:
    case Nil{}:
      0n
    case x <> xt:
      x

# Montgomery reduction of t: add u * m with u making the low limb zero, then
# divide by 2^16
def bi.mont.reduce(+t: List<&2, Nat>, +m: List<&2, Nat>, +n0: Nat) -> List<&2, Nat>:
  bi.shift1(bi.addk(t, m, Nat.mod(Nat.mul(bi.low(t), n0), 65536n), 0n))

# one Montgomery step: t + a_i * b, then reduced
def bi.mont.step(t: List<&2, Nat>, +ai: Nat, +b: List<&2, Nat>, +m: List<&2, Nat>, +n0: Nat) ->
  List<&2, Nat>:
  bi.mont.reduce(bi.addk(t, b, ai, 0n), m, n0)

# the Montgomery steps over the limbs of a, least significant first
def bi.mont.loop(a: List<&2, Nat>, t: List<&2, Nat>, +b: List<&2, Nat>, +m: List<&2, Nat>,
  +n0: Nat) -> List<&2, Nat>:
  match a:
    case Nil{}:
      t
    case x <> xt:
      bi.mont.loop(xt, bi.mont.step(t, x, b, m, n0), b, m, n0)

# a * b / 2^(16 n) mod m, with a and b below m, all lists of length n + 2
def bi.mont(+a: List<&2, Nat>, +b: List<&2, Nat>, +m: List<&2, Nat>, +n0: Nat, +n: Nat) ->
  List<&2, Nat>:
  bi.csub(bi.mont.loop(List.take(&2, Nat, a, n), bi.zeros(Nat.add(n, 2n)), b, m, n0), m)

# one Newton step for the inverse of m0 modulo 2^16, kept in range
def bi.newton(+m0: Nat, +x: Nat) -> Nat:
  Nat.mod(Nat.mul(x, Nat.sub(Nat.add(2n, 65536n), Nat.mod(Nat.mul(m0, x), 65536n))), 65536n)

# -m^-1 mod 2^16 for an odd lowest limb m0: m0 is its own inverse mod 8, and
# each Newton step doubles the correct bits, so three steps reach 24 bits
def bi.n0(+m0: Nat) -> Nat:
  Nat.mod(Nat.sub(65536n, bi.newton(m0, bi.newton(m0, bi.newton(m0, m0)))), 65536n)
