# p256.bend: NIST P-256 (secp256r1) for ECDSA verification with SHA-256. Values
# are 18-limb lists of 16-bit limbs (bigint.bend), least significant first. Field
# values are in Montgomery form (x * 2^256 mod p). Points are projective (X : Y : Z),
# affine (x, y) = (X / Z, Y / Z), with (0 : 1 : 0) the point at infinity.
# The constants come from gen_p256.py, which checks them against cryptography.
# p256.bend is generated: python3 -I gen_p256.py

import Base
import ./bigint.bend as B

#@@CONST@@

# Field arithmetic mod p
# ----------------------

def p256.mul(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(a, b, p256.P(), p256.P0(), 16n)

def p256.sqr(+a: List<&2, Nat>) -> List<&2, Nat>:
  p256.mul(a, a)

def p256.add(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.csub(B.bi.addk(a, b, 1n, 0n), p256.P())

def p256.sub(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  p256.sub.pick(B.bi.subb(a, b, 0n), p256.P())

def p256.sub.pick(r: List<&2, Nat> & Nat, +m: List<&2, Nat>) -> List<&2, Nat>:
  (d, bo) = r
  p256.sub.fix(bo, d, m)

# a - b, plus m when the subtraction borrowed
def p256.sub.fix(bo: Nat, +d: List<&2, Nat>, +m: List<&2, Nat>) -> List<&2, Nat>:
  match bo:
    case 0n:
      d
    case 1n+_:
      B.bi.addk(d, m, 1n, 0n)

def p256.f2(+a: List<&2, Nat>) -> List<&2, Nat>:
  p256.add(a, a)

def p256.f3(+a: List<&2, Nat>) -> List<&2, Nat>:
  p256.add(p256.f2(a), a)

def p256.f4(+a: List<&2, Nat>) -> List<&2, Nat>:
  p256.f2(p256.f2(a))

def p256.f8(+a: List<&2, Nat>) -> List<&2, Nat>:
  p256.f2(p256.f4(a))

def p256.is0(+xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(Nat.is_eq(x, 0n), p256.is0(t))

def p256.eqn(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case x <> t:
      match b:
        case Nil{}:
          False{}
        case y <> u:
          Bool.and(Nat.is_eq(x, y), p256.eqn(t, u))

# a < b, from the borrow of a - b
def p256.lt(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  p256.lt.at(B.bi.subb(a, b, 0n))

def p256.lt.at(r: List<&2, Nat> & Nat) -> Bool:
  (d, bo) = r
  match bo:
    case 0n:
      False{}
    case 1n+_:
      True{}

# Montgomery form and back
def p256.tom(+x: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(x, p256.R2P(), p256.P(), p256.P0(), 16n)

def p256.fromm(+x: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(x, 1n <> B.bi.zeros(17n), p256.P(), p256.P0(), 16n)

# Points (projective)
# --------------------

# A point is (X : Y : Z), with affine (x, y) = (X / Z, Y / Z); the point at infinity is (0 : 1 : 0).
# The complete addition formulas of Renes, Costello and Batina (2016, algorithm 1, for a = -3) add
# any two points, doubling and infinity included, with no case split on the data.
type JP is Data:
  JP{x: List<&2, Nat>, y: List<&2, Nat>, z: List<&2, Nat>}

def p256.inf() -> JP:
  JP{B.bi.zeros(18n), p256.ONE_P(), B.bi.zeros(18n)}

# 3b, the curve constant b times three, in Montgomery form
def p256.b3() -> List<&2, Nat>:
  p256.add(p256.BM(), p256.add(p256.BM(), p256.BM()))

# -3x mod p
def p256.neg3(+x: List<&2, Nat>) -> List<&2, Nat>:
  p256.sub(B.bi.zeros(18n), p256.add(p256.f2(x), x))

# P + Q for any two points (algorithm 1 of the paper, with its names: t0 .. t5 and the sums)
def p256.cadd(+p: JP, +q: JP) -> JP:
  match p:
    case JP{+x1, +y1, +z1}:
      match q:
        case JP{+x2, +y2, +z2}:
          p256.cadd.go(x1, y1, z1, x2, y2, z2)

def p256.cadd.go(+x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>, +x2: List<&2, Nat>,
  +y2: List<&2, Nat>, +z2: List<&2, Nat>) -> JP:
  +t0 : List<&2, Nat> = p256.mul(x1, x2)
  +t1 : List<&2, Nat> = p256.mul(y1, y2)
  +t2 : List<&2, Nat> = p256.mul(z1, z2)
  +t3 : List<&2, Nat> = p256.sub(p256.mul(p256.add(x1, y1), p256.add(x2, y2)), p256.add(t0, t1))
  +t4 : List<&2, Nat> = p256.sub(p256.mul(p256.add(x1, z1), p256.add(x2, z2)), p256.add(t0, t2))
  +t5 : List<&2, Nat> = p256.sub(p256.mul(p256.add(y1, z1), p256.add(y2, z2)), p256.add(t1, t2))
  +x3a : List<&2, Nat> = p256.mul(p256.b3(), t2)
  +z3a : List<&2, Nat> = p256.add(p256.neg3(t4), x3a)
  +x3b : List<&2, Nat> = p256.sub(t1, z3a)
  +z3b : List<&2, Nat> = p256.add(t1, z3a)
  +y3a : List<&2, Nat> = p256.mul(x3b, z3b)
  +t1a : List<&2, Nat> = p256.add(p256.f2(t0), t0)
  +t2a : List<&2, Nat> = p256.neg3(t2)
  +t4a : List<&2, Nat> = p256.mul(p256.b3(), t4)
  +t1b : List<&2, Nat> = p256.add(t1a, t2a)
  +t2b : List<&2, Nat> = p256.neg3(p256.sub(t0, t2a))
  +t4b : List<&2, Nat> = p256.add(t4a, t2b)
  +t0a : List<&2, Nat> = p256.mul(t1b, t4b)
  +y3b : List<&2, Nat> = p256.add(y3a, t0a)
  +t0b : List<&2, Nat> = p256.mul(t5, t4b)
  +x3c : List<&2, Nat> = p256.sub(p256.mul(t3, x3b), t0b)
  +t0c : List<&2, Nat> = p256.mul(t3, t1b)
  +z3c : List<&2, Nat> = p256.add(p256.mul(t5, z3b), t0c)
  JP{x3c, y3b, z3c}

# P + P
def p256.pdbl(+p: JP) -> JP:
  p256.cadd(p, p)

# P + Q for an affine Q = (qx, qy) in Montgomery form
def p256.madd(+p: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  p256.cadd(p, JP{qx, qy, p256.ONE_P()})

# a when s is 1, b when s is 0, with no branch on s
def p256.sel(+s: Nat, +a: JP, +b: JP) -> JP:
  match a:
    case JP{+x1, +y1, +z1}:
      match b:
        case JP{+x2, +y2, +z2}:
          JP{B.bi.sel(s, x1, x2), B.bi.sel(s, y1, y2), B.bi.sel(s, z1, z2)}

# Scalar multiplication
# ---------------------

# the bits of the low 256 bits of a limb list, most significant first
def p256.bits(+k: List<&2, Nat>) -> List<&2, Nat>:
  p256.bits.limbs(List.reverse(&2, Nat, List.take(&2, Nat, k, 16n)))

def p256.bits.limbs(+ls: List<&2, Nat>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case x <> t:
      List.append(&2, Nat, p256.bits16(x), p256.bits.limbs(t))

def p256.bits16(+v: Nat) -> List<&2, Nat>:
  p256.bits.go(16n, v, 32768n)

# the bits of v from the one worth pw (2^(fuel - 1)) down
def p256.bits.go(fuel: Nat, +v: Nat, +pw: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+q:
      Nat.mod(Nat.div(v, pw), 2n) <> p256.bits.go(q, v, Nat.div(pw, 2n))

# k * (qx, qy), by double-and-add over the bits of k (most significant first): each bit doubles,
# adds Q, and keeps the sum when the bit is 1. The choice is a select, not a branch on the bit.
def p256.smul(bits: List<&2, Nat>, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  p256.smul.go(bits, p256.inf(), qx, qy)

def p256.smul.go(bits: List<&2, Nat>, +acc: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p256.smul.go(t, p256.step(acc, qx, qy, b), qx, qy)

def p256.step(+acc: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>, b: Nat) -> JP:
  p256.sel(b, p256.madd(p256.pdbl(acc), qx, qy), p256.pdbl(acc))

# Arithmetic mod n (the group order), in Montgomery form
# -------------------------------------------------------

def p256.nmul(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(a, b, p256.N(), p256.N0(), 16n)

# base^e in Montgomery form, e given by its bits (most significant first)
def p256.npow(bits: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  p256.npow.go(bits, p256.ONE_N(), base)

def p256.npow.go(bits: List<&2, Nat>, +acc: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p256.npow.go(t, p256.npow.step(acc, base, b), base)

def p256.npow.step(+acc: List<&2, Nat>, +base: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  match b:
    case 0n:
      p256.nmul(acc, acc)
    case _:
      p256.nmul(p256.nmul(acc, acc), base)

# base^e mod p in Montgomery form, e given by its bits (most significant first)
def p256.pow(bits: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  p256.pow.go(bits, p256.ONE_P(), base)

def p256.pow.go(bits: List<&2, Nat>, +acc: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p256.pow.go(t, p256.pow.step(acc, base, b), base)

def p256.pow.step(+acc: List<&2, Nat>, +base: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  match b:
    case 0n:
      p256.mul(acc, acc)
    case _:
      p256.mul(p256.mul(acc, acc), base)

# the affine coordinates (x, y) = (X / Z, Y / Z) as 64 big-endian bytes, x then y
def p256.affine(+pt: JP) -> List<&2, U32>:
  match pt:
    case JP{+x, +y, +z}:
      p256.affine.go(x, y, p256.pow(p256.bits(p256.PM2()), z))

def p256.affine.go(+x: List<&2, Nat>, +y: List<&2, Nat>, +zi: List<&2, Nat>) -> List<&2, U32>:
  List.append(&2, U32, p256.bytes_be(p256.fromm(p256.mul(x, zi))),
    p256.bytes_be(p256.fromm(p256.mul(y, zi))))

# k G as 64 bytes (x then y), for a 32-byte big-endian k below n
def p256.base_mul(+k: List<&2, U32>) -> List<&2, U32>:
  p256.affine(p256.smul(p256.bits(p256.limbs(k)), p256.GXM(), p256.GYM()))

# ECDH (SEC 1 3.3.1): the x coordinate of d * Q, 32 bytes. A private scalar is 32
# bytes below 2^255 (less than n, so a fresh random one needs no reduction).
# p256.scalar clears the top bit of random bytes.
def p256.scalar(+bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case x <> t:
      U32.and(x, 127) <> t

# the shared x coordinate; Nil when the peer key is malformed (not 32 + 32 bytes, or
# not on the curve) or the private scalar is out of range
def p256.ecdh(+d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  p256.ecdh.len(Bool.and(Bool.and(Nat.is_eq(List.length(&2, U32, d), 32n), Nat.is_eq(List.length(&2, U32, qx), 32n)),
    Nat.is_eq(List.length(&2, U32, qy), 32n)), d, qx, qy)

def p256.ecdh.len(ok: Bool, +d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      p256.ecdh.check(p256.nonzero_lt_n(p256.limbs(d)),
        p256.oncurve(p256.tom(p256.limbs(qx)), p256.tom(p256.limbs(qy))), d, qx, qy)
    case False{}:
      Nil{}

def p256.ecdh.check(scalar_ok: Bool, point_ok: Bool, +d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  match scalar_ok:
    case True{}:
      p256.ecdh.point(point_ok, d, qx, qy)
    case False{}:
      Nil{}

def p256.ecdh.point(point_ok: Bool, +d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  match point_ok:
    case True{}:
      List.take(&2, U32, p256.affine(p256.smul(p256.bits(p256.limbs(d)), p256.tom(p256.limbs(qx)), p256.tom(p256.limbs(qy)))), 32n)
    case False{}:
      Nil{}

# ECDSA verification (FIPS 186-4 6.4)
# -----------------------------------

# big-endian bytes (32 of them) as 18 limbs
def p256.limbs(+bs: List<&2, U32>) -> List<&2, Nat>:
  List.append(&2, Nat, p256.limbs.pairs(List.reverse(&2, U32, bs)), 0n <> 0n <> Nil{})

def p256.limbs.pairs(+le: List<&2, U32>) -> List<&2, Nat>:
  match le:
    case Nil{}:
      Nil{}
    case x <> t:
      match t:
        case Nil{}:
          U32.to_nat(x) <> Nil{}
        case y <> u:
          Nat.add(U32.to_nat(x), Nat.mul(256n, U32.to_nat(y))) <> p256.limbs.pairs(u)

# 18 limbs as 32 big-endian bytes (the top two limbs must be zero)
def p256.bytes_be(+x: List<&2, Nat>) -> List<&2, U32>:
  List.reverse(&2, U32, List.take(&2, U32, p256.bytes.le(x), 32n))

def p256.bytes.le(+x: List<&2, Nat>) -> List<&2, U32>:
  match x:
    case Nil{}:
      Nil{}
    case l <> t:
      U32.from_nat(Nat.mod(l, 256n)) <> U32.from_nat(Nat.mod(Nat.div(l, 256n), 256n)) <> p256.bytes.le(t)

# the digest as an integer mod n (a 256-bit value is below 2n)
def p256.reduce_n(+e: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.csub(e, p256.N())

# 0 < x < n
def p256.nonzero_lt_n(+x: List<&2, Nat>) -> Bool:
  p256.nonzero.at(p256.is0(x), x)

def p256.nonzero.at(z: Bool, +x: List<&2, Nat>) -> Bool:
  match z:
    case True{}:
      False{}
    case False{}:
      p256.lt(x, p256.N())

# y^2 = x^3 - 3x + b for affine (x, y) in Montgomery form
def p256.oncurve(+xm: List<&2, Nat>, +ym: List<&2, Nat>) -> Bool:
  p256.eqn(p256.sqr(ym), p256.add(p256.sub(p256.mul(p256.sqr(xm), xm), p256.f3(xm)), p256.BM()))

# the signature (r, s) on the digest e under the public key (qx, qy); all big-endian
# bytes: qx and qy 32 each, e the 32-byte digest, r and s 32 each
def p256.verify(+qx: List<&2, U32>, +qy: List<&2, U32>, +e: List<&2, U32>,
  +r: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  p256.verify.len(Bool.and(Bool.and(Nat.is_eq(List.length(&2, U32, qx), 32n), Nat.is_eq(List.length(&2, U32, qy), 32n)),
    Bool.and(Bool.and(Nat.is_eq(List.length(&2, U32, e), 32n), Nat.is_eq(List.length(&2, U32, r), 32n)),
      Nat.is_eq(List.length(&2, U32, s), 32n))), qx, qy, e, r, s)

# the inputs are 32 bytes each; anything else is not a signature
def p256.verify.len(ok: Bool, +qx: List<&2, U32>, +qy: List<&2, U32>, +e: List<&2, U32>,
  +r: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  match ok:
    case True{}:
      p256.verify.go(p256.limbs(r), p256.limbs(s), p256.reduce_n(p256.limbs(e)),
        p256.tom(p256.limbs(qx)), p256.tom(p256.limbs(qy)))
    case False{}:
      False{}

def p256.verify.go(+rl: List<&2, Nat>, +sl: List<&2, Nat>, +el: List<&2, Nat>,
  +xm: List<&2, Nat>, +ym: List<&2, Nat>) -> Bool:
  p256.verify.check(Bool.and(Bool.and(p256.nonzero_lt_n(rl), p256.nonzero_lt_n(sl)),
    p256.oncurve(xm, ym)), p256.verify.point(rl, sl, el, xm, ym), rl)

# u1 G + u2 Q with u1 = e / s and u2 = r / s mod n. The inverse of s is s^(n-2);
# nmul(e, w) with w = s^(n-2) in Montgomery form is e * w mod n in plain form.
def p256.verify.point(+rl: List<&2, Nat>, +sl: List<&2, Nat>, +el: List<&2, Nat>,
  +xm: List<&2, Nat>, +ym: List<&2, Nat>) -> JP:
  p256.verify.point.at(p256.npow(p256.bits(p256.NM2()), p256.nmul(sl, p256.R2N())), rl, el, xm, ym)

def p256.verify.point.at(+wm: List<&2, Nat>, +rl: List<&2, Nat>, +el: List<&2, Nat>,
  +xm: List<&2, Nat>, +ym: List<&2, Nat>) -> JP:
  p256.cadd(p256.smul(p256.bits(p256.nmul(el, wm)), p256.GXM(), p256.GYM()),
    p256.smul(p256.bits(p256.nmul(rl, wm)), xm, ym))

# the signature holds when the point is not infinity and its x coordinate, mod n,
# is r: x = r or (when r + n < p) x = r + n, checked as X == r Z in projective form
def p256.verify.check(ok: Bool, +pt: JP, +rl: List<&2, Nat>) -> Bool:
  match ok:
    case True{}:
      p256.verify.hit(pt, rl)
    case False{}:
      False{}

def p256.verify.hit(+pt: JP, +rl: List<&2, Nat>) -> Bool:
  match pt:
    case JP{+x, +y, +z}:
      p256.verify.cmp(p256.is0(z), x, z, rl)

def p256.verify.cmp(zinf: Bool, +x: List<&2, Nat>, +z: List<&2, Nat>, +rl: List<&2, Nat>) -> Bool:
  match zinf:
    case True{}:
      False{}
    case False{}:
      p256.verify.cmp2(p256.eqn(x, p256.mul(z, p256.tom(rl))), x, z, rl)

def p256.verify.cmp2(c1: Bool, +x: List<&2, Nat>, +z: List<&2, Nat>, +rl: List<&2, Nat>) -> Bool:
  match c1:
    case True{}:
      True{}
    case False{}:
      p256.verify.cmp3(x, z, B.bi.addk(rl, p256.N(), 1n, 0n))

def p256.verify.cmp3(+x: List<&2, Nat>, +z: List<&2, Nat>, +rn: List<&2, Nat>) -> Bool:
  p256.verify.cmp4(p256.lt(rn, p256.P()), p256.eqn(x, p256.mul(z, p256.tom(rn))))

def p256.verify.cmp4(small: Bool, c2: Bool) -> Bool:
  match small:
    case True{}:
      c2
    case False{}:
      False{}
