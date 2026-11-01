# p256.bend: NIST P-256 (secp256r1) for ECDSA verification with SHA-256. Values
# are 18-limb lists of 16-bit limbs (bigint.bend), least significant first. Field
# values are in Montgomery form (x * 2^256 mod p). Points are Jacobian (X, Y, Z),
# affine (x, y) = (X / Z^2, Y / Z^3), with Z = 0 for the point at infinity.
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

# Points (Jacobian)
# -----------------

type JP is Data:
  JP{x: List<&2, Nat>, y: List<&2, Nat>, z: List<&2, Nat>}

def p256.inf() -> JP:
  JP{p256.ONE_P(), p256.ONE_P(), B.bi.zeros(18n)}

# doubling (dbl-2001-b, a = -3)
def p256.pdbl(+p: JP) -> JP:
  match p:
    case JP{+x, +y, +z}:
      p256.pdbl.go(x, y, z)

def p256.pdbl.go(+x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>) -> JP:
  +delta : List<&2, Nat> = p256.sqr(z)
  +gamma : List<&2, Nat> = p256.sqr(y)
  +beta : List<&2, Nat> = p256.mul(x, gamma)
  +alpha : List<&2, Nat> = p256.f3(p256.mul(p256.sub(x, delta), p256.add(x, delta)))
  +x3 : List<&2, Nat> = p256.sub(p256.sqr(alpha), p256.f8(beta))
  +z3 : List<&2, Nat> = p256.sub(p256.sub(p256.sqr(p256.add(y, z)), gamma), delta)
  +y3 : List<&2, Nat> = p256.sub(p256.mul(alpha, p256.sub(p256.f4(beta), x3)), p256.f8(p256.sqr(gamma)))
  JP{x3, y3, z3}

# P + Q for an affine Q = (qx, qy) (madd-2007-bl)
def p256.madd(+p: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  match p:
    case JP{+x, +y, +z}:
      p256.madd.go(p256.is0(z), x, y, z, qx, qy)

def p256.madd.go(zinf: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>,
  +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  match zinf:
    case True{}:
      JP{qx, qy, p256.ONE_P()}
    case False{}:
      p256.madd.gen(x, y, z, qx, qy)

def p256.madd.gen(+x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>,
  +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  +z1z1 : List<&2, Nat> = p256.sqr(z)
  +u2 : List<&2, Nat> = p256.mul(qx, z1z1)
  +s2 : List<&2, Nat> = p256.mul(qy, p256.mul(z, z1z1))
  +h : List<&2, Nat> = p256.sub(u2, x)
  +r : List<&2, Nat> = p256.f2(p256.sub(s2, y))
  p256.madd.case(p256.is0(h), p256.is0(r), x, y, z, h, r, z1z1)

def p256.madd.case(h0: Bool, r0: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>,
  +h: List<&2, Nat>, +r: List<&2, Nat>, +z1z1: List<&2, Nat>) -> JP:
  match h0:
    case True{}:
      p256.same(r0, x, y, z)
    case False{}:
      p256.madd.fin(x, y, z, h, r, z1z1)

# the same x: the same point doubles, the opposite one is infinity
def p256.same(r0: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>) -> JP:
  match r0:
    case True{}:
      p256.pdbl(JP{x, y, z})
    case False{}:
      p256.inf()

def p256.madd.fin(+x: List<&2, Nat>, +y: List<&2, Nat>, +z: List<&2, Nat>, +h: List<&2, Nat>,
  +r: List<&2, Nat>, +z1z1: List<&2, Nat>) -> JP:
  +hh : List<&2, Nat> = p256.sqr(h)
  +i : List<&2, Nat> = p256.f4(hh)
  +j : List<&2, Nat> = p256.mul(h, i)
  +v : List<&2, Nat> = p256.mul(x, i)
  +x3 : List<&2, Nat> = p256.sub(p256.sub(p256.sqr(r), j), p256.f2(v))
  +y3 : List<&2, Nat> = p256.sub(p256.mul(r, p256.sub(v, x3)), p256.f2(p256.mul(y, j)))
  +z3 : List<&2, Nat> = p256.sub(p256.sub(p256.sqr(p256.add(z, h)), z1z1), hh)
  JP{x3, y3, z3}

# P + Q for Jacobian P and Q (add-2007-bl)
def p256.padd(+p1: JP, +p2: JP) -> JP:
  match p1:
    case JP{+x1, +y1, +z1}:
      match p2:
        case JP{+x2, +y2, +z2}:
          p256.padd.go(p256.is0(z1), p256.is0(z2), x1, y1, z1, x2, y2, z2)

def p256.padd.go(z1inf: Bool, z2inf: Bool, +x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>,
  +x2: List<&2, Nat>, +y2: List<&2, Nat>, +z2: List<&2, Nat>) -> JP:
  match z1inf:
    case True{}:
      JP{x2, y2, z2}
    case False{}:
      p256.padd.two(z2inf, x1, y1, z1, x2, y2, z2)

def p256.padd.two(z2inf: Bool, +x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>,
  +x2: List<&2, Nat>, +y2: List<&2, Nat>, +z2: List<&2, Nat>) -> JP:
  match z2inf:
    case True{}:
      JP{x1, y1, z1}
    case False{}:
      p256.padd.gen(x1, y1, z1, x2, y2, z2)

def p256.padd.gen(+x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>,
  +x2: List<&2, Nat>, +y2: List<&2, Nat>, +z2: List<&2, Nat>) -> JP:
  +z1z1 : List<&2, Nat> = p256.sqr(z1)
  +z2z2 : List<&2, Nat> = p256.sqr(z2)
  +u1 : List<&2, Nat> = p256.mul(x1, z2z2)
  +u2 : List<&2, Nat> = p256.mul(x2, z1z1)
  +s1 : List<&2, Nat> = p256.mul(y1, p256.mul(z2, z2z2))
  +s2 : List<&2, Nat> = p256.mul(y2, p256.mul(z1, z1z1))
  +h : List<&2, Nat> = p256.sub(u2, u1)
  +r : List<&2, Nat> = p256.f2(p256.sub(s2, s1))
  p256.padd.case(p256.is0(h), p256.is0(r), x1, y1, z1, z2, h, r, z1z1, z2z2, u1, s1)

def p256.padd.case(h0: Bool, r0: Bool, +x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>,
  +z2: List<&2, Nat>, +h: List<&2, Nat>, +r: List<&2, Nat>, +z1z1: List<&2, Nat>,
  +z2z2: List<&2, Nat>, +u1: List<&2, Nat>, +s1: List<&2, Nat>) -> JP:
  match h0:
    case True{}:
      p256.same(r0, x1, y1, z1)
    case False{}:
      p256.padd.fin(x1, y1, z1, z2, h, r, z1z1, z2z2, u1, s1)

def p256.padd.fin(+x1: List<&2, Nat>, +y1: List<&2, Nat>, +z1: List<&2, Nat>, +z2: List<&2, Nat>,
  +h: List<&2, Nat>, +r: List<&2, Nat>, +z1z1: List<&2, Nat>, +z2z2: List<&2, Nat>,
  +u1: List<&2, Nat>, +s1: List<&2, Nat>) -> JP:
  +i : List<&2, Nat> = p256.f4(p256.sqr(h))
  +j : List<&2, Nat> = p256.mul(h, i)
  +v : List<&2, Nat> = p256.mul(u1, i)
  +x3 : List<&2, Nat> = p256.sub(p256.sub(p256.sqr(r), j), p256.f2(v))
  +y3 : List<&2, Nat> = p256.sub(p256.mul(r, p256.sub(v, x3)), p256.f2(p256.mul(s1, j)))
  +z3 : List<&2, Nat> = p256.mul(p256.sub(p256.sub(p256.sqr(p256.add(z1, z2)), z1z1), z2z2), h)
  JP{x3, y3, z3}

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

# k * (qx, qy), by double-and-add over the bits of k (most significant first)
def p256.smul(bits: List<&2, Nat>, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  p256.smul.go(bits, p256.inf(), qx, qy)

def p256.smul.go(bits: List<&2, Nat>, +acc: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>) -> JP:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      p256.smul.go(t, p256.step(acc, qx, qy, b), qx, qy)

def p256.step(+acc: JP, +qx: List<&2, Nat>, +qy: List<&2, Nat>, b: Nat) -> JP:
  match b:
    case 0n:
      p256.pdbl(acc)
    case _:
      p256.madd(p256.pdbl(acc), qx, qy)

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

# the affine coordinates (x, y) = (X / Z^2, Y / Z^3) as 64 big-endian bytes, x then y
def p256.affine(+pt: JP) -> List<&2, U32>:
  match pt:
    case JP{+x, +y, +z}:
      p256.affine.go(x, y, p256.pow(p256.bits(p256.PM2()), z))

def p256.affine.go(+x: List<&2, Nat>, +y: List<&2, Nat>, +zi: List<&2, Nat>) -> List<&2, U32>:
  +zi2 : List<&2, Nat> = p256.sqr(zi)
  List.append(&2, U32, p256.bytes_be(p256.fromm(p256.mul(x, zi2))),
    p256.bytes_be(p256.fromm(p256.mul(y, p256.mul(zi2, zi)))))

# k G as 64 bytes (x then y), for a 32-byte big-endian k below n
def p256.base_mul(+k: List<&2, U32>) -> List<&2, U32>:
  p256.affine(p256.smul(p256.bits(p256.limbs(k)), p256.GXM(), p256.GYM()))

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
  p256.padd(p256.smul(p256.bits(p256.nmul(el, wm)), p256.GXM(), p256.GYM()),
    p256.smul(p256.bits(p256.nmul(rl, wm)), xm, ym))

# the signature holds when the point is not infinity and its x coordinate, mod n,
# is r: x = r or (when r + n < p) x = r + n, checked as X == r Z^2 in Jacobian form
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
      p256.verify.cmp2(p256.eqn(x, p256.mul(p256.sqr(z), p256.tom(rl))), x, z, rl)

def p256.verify.cmp2(c1: Bool, +x: List<&2, Nat>, +z: List<&2, Nat>, +rl: List<&2, Nat>) -> Bool:
  match c1:
    case True{}:
      True{}
    case False{}:
      p256.verify.cmp3(x, z, B.bi.addk(rl, p256.N(), 1n, 0n))

def p256.verify.cmp3(+x: List<&2, Nat>, +z: List<&2, Nat>, +rn: List<&2, Nat>) -> Bool:
  p256.verify.cmp4(p256.lt(rn, p256.P()), p256.eqn(x, p256.mul(p256.sqr(z), p256.tom(rn))))

def p256.verify.cmp4(small: Bool, c2: Bool) -> Bool:
  match small:
    case True{}:
      c2
    case False{}:
      False{}
