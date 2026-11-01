# p384.bend: NIST P-384 (secp384r1) for ECDSA verification and ECDH. Generated from p256_body.bend by gen_p384.py. Values
# are 18-limb lists of 16-bit limbs (bigint.bend), least significant first. Field
# values are in Montgomery form (x * 2^256 mod p). Points are projective (X : Y : Z),
# affine (x, y) = (X / Z, Y / Z), with (0 : 1 : 0) the point at infinity.
# The constants come from gen_p384.py, which checks them against cryptography.
# p384.bend is generated: python3 -I gen_p384.py

import Base
import ./bigint.bend as B

def p384.P() -> List<&2, Nat>:
  [65535n, 65535n, 0n, 0n, 0n, 0n, 65535n, 65535n, 65534n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 0n, 0n]

def p384.N() -> List<&2, Nat>:
  [10611n, 52421n, 6506n, 60652n, 42874n, 18608n, 3506n, 22554n, 11743n, 62519n, 19841n, 51043n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 0n, 0n]

def p384.NM2() -> List<&2, Nat>:
  [10609n, 52421n, 6506n, 60652n, 42874n, 18608n, 3506n, 22554n, 11743n, 62519n, 19841n, 51043n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 0n, 0n]

def p384.PM2() -> List<&2, Nat>:
  [65533n, 65535n, 0n, 0n, 0n, 0n, 65535n, 65535n, 65534n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 65535n, 0n, 0n]

def p384.BM() -> List<&2, Nat>:
  [11724n, 40257n, 34929n, 2065n, 13036n, 31308n, 44504n, 63273n, 558n, 6432n, 8347n, 30706n, 35554n, 38035n, 19438n, 58167n, 8340n, 7938n, 8692n, 46635n, 49145n, 24655n, 4427n, 52488n, 0n, 0n]

def p384.GXM() -> List<&2, Nat>:
  [46376n, 18880n, 30054n, 15824n, 52792n, 41174n, 30946n, 8419n, 19822n, 21531n, 15100n, 34716n, 3839n, 22947n, 34436n, 25684n, 56875n, 24910n, 63267n, 33071n, 5395n, 10654n, 44482n, 19770n, 0n, 0n]

def p384.GYM() -> List<&2, Nat>:
  [42238n, 19203n, 15789n, 8964n, 43436n, 31668n, 43199n, 41407n, 45136n, 11907n, 59222n, 35757n, 65497n, 26868n, 21017n, 50883n, 43072n, 14697n, 550n, 56704n, 50665n, 23061n, 43970n, 11128n, 0n, 0n]

def p384.R2P() -> List<&2, Nat>:
  [1n, 0n, 65534n, 65535n, 0n, 0n, 2n, 0n, 0n, 0n, 65534n, 65535n, 0n, 0n, 2n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

def p384.R2N() -> List<&2, Nat>:
  [2473n, 6580n, 39716n, 11569n, 42009n, 57114n, 33253n, 65341n, 10567n, 64696n, 18490n, 48190n, 7365n, 19115n, 18711n, 54285n, 26773n, 10278n, 23418n, 16304n, 48929n, 11065n, 60929n, 3204n, 0n, 0n]

def p384.ONE_P() -> List<&2, Nat>:
  [1n, 0n, 65535n, 65535n, 65535n, 65535n, 0n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

def p384.ONE_N() -> List<&2, Nat>:
  [54925n, 13114n, 59029n, 4883n, 22661n, 46927n, 62029n, 42981n, 53792n, 3016n, 45694n, 14492n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

def p384.P0() -> Nat:
  1n

def p384.N0() -> Nat:
  56389n


# Field arithmetic mod p
# ----------------------

def p384.mul(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(a, b, p384.P(), p384.P0(), 24n)

def p384.sqr(+a: List<&2, Nat>) -> List<&2, Nat>:
  p384.mul(a, a)

def p384.add(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.csub(B.bi.addk(a, b, 1n, 0n), p384.P())

def p384.sub.fix(bo: Nat, +d: List<&2, Nat>, +m: List<&2, Nat>) -> List<&2, Nat>:
  match bo:
    case 0n:
      d
    case 1n+_:
      B.bi.addk(d, m, 1n, 0n)

def p384.sub.pick(r: List<&2, Nat> & Nat, +m: List<&2, Nat>) -> List<&2, Nat>:
  (d, bo) = r
  p384.sub.fix(bo, d, m)

# a - b, plus m when the subtraction borrowed
def p384.sub(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  p384.sub.pick(B.bi.subb(a, b, 0n), p384.P())

def p384.f2(+a: List<&2, Nat>) -> List<&2, Nat>:
  p384.add(a, a)

def p384.f3(+a: List<&2, Nat>) -> List<&2, Nat>:
  p384.add(p384.f2(a), a)

def p384.f4(+a: List<&2, Nat>) -> List<&2, Nat>:
  p384.f2(p384.f2(a))

def p384.f8(+a: List<&2, Nat>) -> List<&2, Nat>:
  p384.f2(p384.f4(a))

def p384.is0(+xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(Nat.is_eq(x, 0n), p384.is0(t))

def p384.eqn(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case x <> t:
      match b:
        case Nil{}:
          False{}
        case y <> u:
          Bool.and(Nat.is_eq(x, y), p384.eqn(t, u))

# a < b, from the borrow of a - b
def p384.lt.at(r: List<&2, Nat> & Nat) -> Bool:
  (d, bo) = r
  match bo:
    case 0n:
      False{}
    case 1n+_:
      True{}

# Montgomery form and back
def p384.lt(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Bool:
  p384.lt.at(B.bi.subb(a, b, 0n))

def p384.tom(+x: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(x, p384.R2P(), p384.P(), p384.P0(), 24n)

def p384.fromm(+x: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(x, 1n <> B.bi.zeros(25n), p384.P(), p384.P0(), 24n)

# Points (projective)
# --------------------

# A point is (X : Y : Z), with affine (x, y) = (X / Z, Y / Z); the point at infinity is (0 : 1 : 0).
# The complete addition formulas of Renes, Costello and Batina (2016, algorithm 1, for a = -3) add
# any two points, doubling and infinity included, with no case split on the data.
type JP is Data:
  JP{x: List<&2, Nat>, y: List<&2, Nat>, z: List<&2, Nat>}

def p384.inf() -> JP:
  JP{B.bi.zeros(26n), p384.ONE_P(), B.bi.zeros(26n)}

# 3b, the curve constant b times three, in Montgomery form
def p384.b3() -> List<&2, Nat>:
  p384.add(p384.BM(), p384.add(p384.BM(), p384.BM()))

# -3x mod p
def p384.neg3(+x: List<&2, Nat>) -> List<&2, Nat>:
  p384.sub(B.bi.zeros(26n), p384.add(p384.f2(x), x))

# P + Q for any two points (algorithm 1 of the paper, with its names: t0 .. t5 and the sums)
def p384.cadd.go(+x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>, +x2: List<&2, Nat>,
  +y2: List<&2, Nat>, +z2: List<&2, Nat>) -> JP:
  +t0 : List<&2, Nat> = p384.mul(x1, x2)
  +t1 : List<&2, Nat> = p384.mul(y1, y2)
  +t2 : List<&2, Nat> = p384.mul(z1, z2)
  +t3 : List<&2, Nat> = p384.sub(p384.mul(p384.add(x1, y1), p384.add(x2, y2)), p384.add(t0, t1))
  +t4 : List<&2, Nat> = p384.sub(p384.mul(p384.add(x1, z1), p384.add(x2, z2)), p384.add(t0, t2))
  +t5 : List<&2, Nat> = p384.sub(p384.mul(p384.add(y1, z1), p384.add(y2, z2)), p384.add(t1, t2))
  +x3a : List<&2, Nat> = p384.mul(p384.b3(), t2)
  +z3a : List<&2, Nat> = p384.add(p384.neg3(t4), x3a)
  +x3b : List<&2, Nat> = p384.sub(t1, z3a)
  +z3b : List<&2, Nat> = p384.add(t1, z3a)
  +y3a : List<&2, Nat> = p384.mul(x3b, z3b)
  +t1a : List<&2, Nat> = p384.add(p384.f2(t0), t0)
  +t2a : List<&2, Nat> = p384.neg3(t2)
  +t4a : List<&2, Nat> = p384.mul(p384.b3(), t4)
  +t1b : List<&2, Nat> = p384.add(t1a, t2a)
  +t2b : List<&2, Nat> = p384.neg3(p384.sub(t0, t2a))
  +t4b : List<&2, Nat> = p384.add(t4a, t2b)
  +t0a : List<&2, Nat> = p384.mul(t1b, t4b)
  +y3b : List<&2, Nat> = p384.add(y3a, t0a)
  +t0b : List<&2, Nat> = p384.mul(t5, t4b)
  +x3c : List<&2, Nat> = p384.sub(p384.mul(t3, x3b), t0b)
  +t0c : List<&2, Nat> = p384.mul(t3, t1b)
  +z3c : List<&2, Nat> = p384.add(p384.mul(t5, z3b), t0c)
  JP{x3c, y3b, z3c}

# P + P
def p384.cadd(+p: JP, +q: JP) -> JP:
  match p:
    case JP{+x1, +y1, +z1}:
      match q:
        case JP{+x2, +y2, +z2}:
          p384.cadd.go(x1, y1, z1, x2, y2, z2)

def p384.pdbl(+p: JP) -> JP:
  p384.cadd(p, p)

# P + Q for an affine Q = (qx, qy) in Montgomery form
def p384.madd(+p: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  p384.cadd(p, JP{qx, qy, p384.ONE_P()})

# a when s is 1, b when s is 0, with no branch on s
def p384.sel(+s: Nat, +a: JP, +b: JP) -> JP:
  match a:
    case JP{+x1, +y1, +z1}:
      match b:
        case JP{+x2, +y2, +z2}:
          JP{B.bi.sel(s, x1, x2), B.bi.sel(s, y1, y2), B.bi.sel(s, z1, z2)}

# Scalar multiplication
# ---------------------

# the bits of the low 256 bits of a limb list, most significant first
def p384.bits.go(fuel: Nat, +v: Nat, +pw: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+q:
      Nat.mod(Nat.div(v, pw), 2n) <> p384.bits.go(q, v, Nat.div(pw, 2n))

# k * (qx, qy), by double-and-add over the bits of k (most significant first): each bit doubles,
# adds Q, and keeps the sum when the bit is 1. The choice is a select, not a branch on the bit.
def p384.bits16(+v: Nat) -> List<&2, Nat>:
  p384.bits.go(16n, v, 32768n)

# the bits of v from the one worth pw (2^(fuel - 1)) down
def p384.bits.limbs(+ls: List<&2, Nat>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case x <> t:
      List.append(&2, Nat, p384.bits16(x), p384.bits.limbs(t))

def p384.bits(+k: List<&2, Nat>) -> List<&2, Nat>:
  p384.bits.limbs(List.reverse(&2, Nat, List.take(&2, Nat, k, 24n)))

def p384.step(+acc: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>, b: Nat) -> JP:
  p384.sel(b, p384.madd(p384.pdbl(acc), qx, qy), p384.pdbl(acc))

# Arithmetic mod n (the group order), in Montgomery form
# -------------------------------------------------------

def p384.smul.go(bits: List<&2, Nat>, +acc: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p384.smul.go(t, p384.step(acc, qx, qy, b), qx, qy)

def p384.smul(bits: List<&2, Nat>, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  p384.smul.go(bits, p384.inf(), qx, qy)

def p384.nmul(+a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.mont(a, b, p384.N(), p384.N0(), 24n)

# base^e in Montgomery form, e given by its bits (most significant first)
def p384.npow.step(+acc: List<&2, Nat>, +base: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  match b:
    case 0n:
      p384.nmul(acc, acc)
    case _:
      p384.nmul(p384.nmul(acc, acc), base)

# base^e mod p in Montgomery form, e given by its bits (most significant first)
def p384.npow.go(bits: List<&2, Nat>, +acc: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p384.npow.go(t, p384.npow.step(acc, base, b), base)

def p384.npow(bits: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  p384.npow.go(bits, p384.ONE_N(), base)

def p384.pow.step(+acc: List<&2, Nat>, +base: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  match b:
    case 0n:
      p384.mul(acc, acc)
    case _:
      p384.mul(p384.mul(acc, acc), base)

# the affine coordinates (x, y) = (X / Z, Y / Z) as 64 big-endian bytes, x then y
def p384.pow.go(bits: List<&2, Nat>, +acc: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p384.pow.go(t, p384.pow.step(acc, base, b), base)

def p384.pow(bits: List<&2, Nat>, +base: List<&2, Nat>) -> List<&2, Nat>:
  p384.pow.go(bits, p384.ONE_P(), base)

def p384.bytes.le(+x: List<&2, Nat>) -> List<&2, U32>:
  match x:
    case Nil{}:
      Nil{}
    case l <> t:
      U32.from_nat(Nat.mod(l, 256n)) <> U32.from_nat(Nat.mod(Nat.div(l, 256n), 256n)) <> p384.bytes.le(t)

# the digest as an integer mod n (a 256-bit value is below 2n)
def p384.bytes_be(+x: List<&2, Nat>) -> List<&2, U32>:
  List.reverse(&2, U32, List.take(&2, U32, p384.bytes.le(x), 48n))

def p384.affine.go(+x: List<&2, Nat>, +y: List<&2, Nat>, +zi: List<&2, Nat>) -> List<&2, U32>:
  List.append(&2, U32, p384.bytes_be(p384.fromm(p384.mul(x, zi))),
    p384.bytes_be(p384.fromm(p384.mul(y, zi))))

# k G as 64 bytes (x then y), for a 32-byte big-endian k below n
def p384.affine(+pt: JP) -> List<&2, U32>:
  match pt:
    case JP{+x, +y, +z}:
      p384.affine.go(x, y, p384.pow(p384.bits(p384.PM2()), z))

def p384.limbs.pairs(+le: List<&2, U32>) -> List<&2, Nat>:
  match le:
    case Nil{}:
      Nil{}
    case x <> t:
      match t:
        case Nil{}:
          U32.to_nat(x) <> Nil{}
        case y <> u:
          Nat.add(U32.to_nat(x), Nat.mul(256n, U32.to_nat(y))) <> p384.limbs.pairs(u)

# 18 limbs as 32 big-endian bytes (the top two limbs must be zero)
def p384.limbs(+bs: List<&2, U32>) -> List<&2, Nat>:
  List.append(&2, Nat, p384.limbs.pairs(List.reverse(&2, U32, bs)), 0n <> 0n <> Nil{})

def p384.base_mul(+k: List<&2, U32>) -> List<&2, U32>:
  p384.affine(p384.smul(p384.bits(p384.limbs(k)), p384.GXM(), p384.GYM()))

# ECDH (SEC 1 3.3.1): the x coordinate of d * Q, 48 bytes. A private scalar is 48
# bytes below 2^383 (less than n, so a fresh random one needs no reduction).
# p384.scalar clears the top bit of random bytes.
def p384.scalar(+bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case x <> t:
      U32.and(x, 127) <> t

# the shared x coordinate; Nil when the peer key is malformed (not 48 + 48 bytes, or
# not on the curve) or the private scalar is out of range
def p384.ecdh.point(point_ok: Bool, +d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  match point_ok:
    case True{}:
      List.take(&2, U32, p384.affine(p384.smul(p384.bits(p384.limbs(d)), p384.tom(p384.limbs(qx)), p384.tom(p384.limbs(qy)))), 48n)
    case False{}:
      Nil{}

# ECDSA verification (FIPS 186-4 6.4)
# -----------------------------------

# big-endian bytes (32 of them) as 18 limbs
def p384.ecdh.check(scalar_ok: Bool, point_ok: Bool, +d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  match scalar_ok:
    case True{}:
      p384.ecdh.point(point_ok, d, qx, qy)
    case False{}:
      Nil{}

def p384.nonzero.at(z: Bool, +x: List<&2, Nat>) -> Bool:
  match z:
    case True{}:
      False{}
    case False{}:
      p384.lt(x, p384.N())

# y^2 = x^3 - 3x + b for affine (x, y) in Montgomery form
def p384.nonzero_lt_n(+x: List<&2, Nat>) -> Bool:
  p384.nonzero.at(p384.is0(x), x)

def p384.oncurve(+xm: List<&2, Nat>, +ym: List<&2, Nat>) -> Bool:
  p384.eqn(p384.sqr(ym), p384.add(p384.sub(p384.mul(p384.sqr(xm), xm), p384.f3(xm)), p384.BM()))

# the digest e is at most 48 bytes (SHA-384, or SHA-256 on a P-384 key): it is left-padded to 48
# bytes, which keeps its integer value
def p384.ecdh.len(ok: Bool, +d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      p384.ecdh.check(p384.nonzero_lt_n(p384.limbs(d)),
        p384.oncurve(p384.tom(p384.limbs(qx)), p384.tom(p384.limbs(qy))), d, qx, qy)
    case False{}:
      Nil{}

def p384.ecdh(+d: List<&2, U32>, +qx: List<&2, U32>, +qy: List<&2, U32>) -> List<&2, U32>:
  p384.ecdh.len(Bool.and(Bool.and(Nat.is_eq(List.length(&2, U32, d), 48n), Nat.is_eq(List.length(&2, U32, qx), 48n)),
    Nat.is_eq(List.length(&2, U32, qy), 48n)), d, qx, qy)

def p384.reduce_n(+e: List<&2, Nat>) -> List<&2, Nat>:
  B.bi.csub(e, p384.N())

# 0 < x < n
def p384.zero32(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> p384.zero32(p)

# the signature (r, s) on the digest e under the public key (qx, qy); all big-endian
# bytes: qx and qy 32 each, e the 32-byte digest, r and s 32 each
def p384.lpad(+e: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, p384.zero32(Nat.sub(48n, List.length(&2, U32, e))), e)

def p384.verify.cmp4(small: Bool, c2: Bool) -> Bool:
  match small:
    case True{}:
      c2
    case False{}:
      False{}

def p384.verify.cmp3(+x: List<&2, Nat>, +z: List<&2, Nat>, +rn: List<&2, Nat>) -> Bool:
  p384.verify.cmp4(p384.lt(rn, p384.P()), p384.eqn(x, p384.mul(z, p384.tom(rn))))

def p384.verify.cmp2(c1: Bool, +x: List<&2, Nat>, +z: List<&2, Nat>, +rl: List<&2, Nat>) -> Bool:
  match c1:
    case True{}:
      True{}
    case False{}:
      p384.verify.cmp3(x, z, B.bi.addk(rl, p384.N(), 1n, 0n))

def p384.verify.cmp(zinf: Bool, +x: List<&2, Nat>, +z: List<&2, Nat>, +rl: List<&2, Nat>) -> Bool:
  match zinf:
    case True{}:
      False{}
    case False{}:
      p384.verify.cmp2(p384.eqn(x, p384.mul(z, p384.tom(rl))), x, z, rl)

def p384.verify.hit(+pt: JP, +rl: List<&2, Nat>) -> Bool:
  match pt:
    case JP{+x, +y, +z}:
      p384.verify.cmp(p384.is0(z), x, z, rl)

def p384.verify.check(ok: Bool, +pt: JP, +rl: List<&2, Nat>) -> Bool:
  match ok:
    case True{}:
      p384.verify.hit(pt, rl)
    case False{}:
      False{}

def p384.verify.point.at(+wm: List<&2, Nat>, +rl: List<&2, Nat>, +el: List<&2, Nat>,
  +xm: List<&2, Nat>, +ym: List<&2, Nat>) -> JP:
  p384.cadd(p384.smul(p384.bits(p384.nmul(el, wm)), p384.GXM(), p384.GYM()),
    p384.smul(p384.bits(p384.nmul(rl, wm)), xm, ym))

# the signature holds when the point is not infinity and its x coordinate, mod n,
# is r: x = r or (when r + n < p) x = r + n, checked as X == r Z in projective form
def p384.verify.point(+rl: List<&2, Nat>, +sl: List<&2, Nat>, +el: List<&2, Nat>,
  +xm: List<&2, Nat>, +ym: List<&2, Nat>) -> JP:
  p384.verify.point.at(p384.npow(p384.bits(p384.NM2()), p384.nmul(sl, p384.R2N())), rl, el, xm, ym)

def p384.verify.go(+rl: List<&2, Nat>, +sl: List<&2, Nat>, +el: List<&2, Nat>,
  +xm: List<&2, Nat>, +ym: List<&2, Nat>) -> Bool:
  p384.verify.check(Bool.and(Bool.and(p384.nonzero_lt_n(rl), p384.nonzero_lt_n(sl)),
    p384.oncurve(xm, ym)), p384.verify.point(rl, sl, el, xm, ym), rl)

# u1 G + u2 Q with u1 = e / s and u2 = r / s mod n. The inverse of s is s^(n-2);
# nmul(e, w) with w = s^(n-2) in Montgomery form is e * w mod n in plain form.
def p384.verify.len(ok: Bool, +qx: List<&2, U32>, +qy: List<&2, U32>, +e: List<&2, U32>,
  +r: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  match ok:
    case True{}:
      p384.verify.go(p384.limbs(r), p384.limbs(s), p384.reduce_n(p384.limbs(p384.lpad(e))),
        p384.tom(p384.limbs(qx)), p384.tom(p384.limbs(qy)))
    case False{}:
      False{}

def p384.verify(+qx: List<&2, U32>, +qy: List<&2, U32>, +e: List<&2, U32>,
  +r: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  p384.verify.len(Bool.and(Bool.and(Nat.is_eq(List.length(&2, U32, qx), 48n), Nat.is_eq(List.length(&2, U32, qy), 48n)),
    Bool.and(Bool.and(Nat.is_le(List.length(&2, U32, e), 48n), Nat.is_eq(List.length(&2, U32, r), 48n)),
      Nat.is_eq(List.length(&2, U32, s), 48n))), qx, qy, e, r, s)

# the inputs are 32 bytes each; anything else is not a signature