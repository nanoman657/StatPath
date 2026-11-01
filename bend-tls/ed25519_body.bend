# ed25519.bend: Ed25519 signature verification (RFC 8032 5.1.7), over the field of
# x25519.bend (p = 2^255 - 19) and the big integers of bigint.bend (mod L, the group
# order). Points are extended Edwards coordinates (X, Y, Z, T) with T = XY/Z, on
# -x^2 + y^2 = 1 + d x^2 y^2. Public keys, signatures and messages are byte lists
# (U32 values 0..255). The constants come from gen_ed25519.py, which checks them.
# ed25519.bend is generated: python3 -I gen_ed25519.py

import Base
import ./x25519.bend as X
import ./sha512.bend as SH
import ./p256.bend as P
import ./bigint.bend as B

#@@CONST@@

# Constants as field elements
# ---------------------------

def ed.d() -> X.FE:
  X.fe.of_bytes(ed.dbytes())

def ed.d2() -> X.FE:
  X.fe.of_bytes(ed.d2bytes())

def ed.sqrt_m1() -> X.FE:
  X.fe.of_bytes(ed.ibytes())

# the base point (x, y) and the point itself in extended coordinates
def ed.base() -> EP:
  ed.base.at(X.fe.of_bytes(ed.bxbytes()), X.fe.of_bytes(ed.bybytes()))

def ed.base.at(+bx: X.FE, +by: X.FE) -> EP:
  EP{bx, by, X.fe.one(), X.fe.mul(bx, by)}

# Points
# ------

type EP is Data:
  EP{x: X.FE, y: X.FE, z: X.FE, t: X.FE}

def ed.ident() -> EP:
  EP{X.fe.zero(), X.fe.one(), X.fe.one(), X.fe.zero()}

def ed.neg(+p: EP) -> EP:
  match p:
    case EP{+x, +y, +z, +t}:
      EP{X.fe.sub(X.fe.zero(), x), y, z, X.fe.sub(X.fe.zero(), t)}

# P + Q in extended coordinates (add-2008-hwcd-3, a = -1). The formula is complete
# for this curve, so it also doubles.
def ed.add(+p: EP, +q: EP) -> EP:
  match p:
    case EP{+x1, +y1, +z1, +t1}:
      match q:
        case EP{+x2, +y2, +z2, +t2}:
          ed.add.go(x1, y1, z1, t1, x2, y2, z2, t2)

def ed.add.go(+x1: X.FE, +y1: X.FE, +z1: X.FE, +t1: X.FE,
  +x2: X.FE, +y2: X.FE, +z2: X.FE, +t2: X.FE) -> EP:
  +a : X.FE = X.fe.mul(X.fe.sub(y1, x1), X.fe.sub(y2, x2))
  +b : X.FE = X.fe.mul(X.fe.add(y1, x1), X.fe.add(y2, x2))
  +c : X.FE = X.fe.mul(X.fe.mul(t1, ed.d2()), t2)
  +dd : X.FE = X.fe.mul(X.fe.add(z1, z1), z2)
  +e : X.FE = X.fe.sub(b, a)
  +f : X.FE = X.fe.sub(dd, c)
  +g : X.FE = X.fe.add(dd, c)
  +h : X.FE = X.fe.add(b, a)
  EP{X.fe.mul(e, f), X.fe.mul(g, h), X.fe.mul(f, g), X.fe.mul(e, h)}

# k P for the bits of k (most significant first), by double-and-add
def ed.smul(bits: List<&2, Nat>, +p: EP) -> EP:
  ed.smul.go(bits, ed.ident(), p)

def ed.smul.go(bits: List<&2, Nat>, +acc: EP, +p: EP) -> EP:
  match bits:
    case Nil{}:
      acc
    case b <> t:
      ed.smul.go(t, ed.step(acc, p, b), p)

def ed.step(+acc: EP, +p: EP, b: Nat) -> EP:
  match b:
    case 0n:
      ed.add(acc, acc)
    case _:
      ed.add(ed.add(acc, acc), p)

# Bytes and integers
# ------------------

def ed.nat_bytes(+bs: List<&2, U32>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case x <> t:
      U32.to_nat(x) <> ed.nat_bytes(t)

# the first byte's value, or 0 for an empty list
def ed.head_n(+xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      x

# the top bit of a 32-byte little-endian encoding is the x sign (the last byte's bit 7)
def ed.clear_top(+xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> Nil{}:
      Nat.mod(x, 128n) <> Nil{}
    case x <> t:
      x <> ed.clear_top(t)

def ed.last(+xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> Nil{}:
      x
    case x <> t:
      ed.last(t)

# the encoding with the x parity in bit 7 of the last byte
def ed.set_top(+ys: List<&2, Nat>, parity: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> Nil{}:
      Nat.add(y, Nat.mul(128n, parity)) <> Nil{}
    case y <> t:
      y <> ed.set_top(t, parity)

# little-endian bytes as 18 limbs of 16 bits (the top two zero)
def ed.le_limbs(+bs: List<&2, U32>) -> List<&2, Nat>:
  List.append(&2, Nat, P.p256.limbs.pairs(bs), 0n <> 0n <> Nil{})

# Decoding and encoding
# ---------------------

# the point of a 32-byte encoding (RFC 8032 5.1.3): y below p, x the root of
# (y^2 - 1) / (d y^2 + 1) with the sign bit, and no sign for x = 0
def ed.decode(+bs: List<&2, U32>) -> Maybe<&2, EP>:
  ed.decode.at(ed.nat_bytes(bs))

def ed.decode.at(+ns: List<&2, Nat>) -> Maybe<&2, EP>:
  ed.decode.canon(ed.clear_top(ns), Nat.div(ed.last(ns), 128n))

def ed.decode.canon(+yb: List<&2, Nat>, sign: Nat) -> Maybe<&2, EP>:
  ed.decode.canon.at(X.fe.bytes(X.fe.canon(X.fe.of_bytes(yb))), yb, sign)

def ed.decode.canon.at(+back: List<&2, Nat>, +yb: List<&2, Nat>, sign: Nat) -> Maybe<&2, EP>:
  ed.decode.canon.pick(P.p256.eqn(back, yb), X.fe.of_bytes(yb), sign)

def ed.decode.canon.pick(c: Bool, +y: X.FE, sign: Nat) -> Maybe<&2, EP>:
  match c:
    case True{}:
      ed.decode.root(y, sign)
    case False{}:
      None{}

def ed.decode.root(+y: X.FE, sign: Nat) -> Maybe<&2, EP>:
  +y2 : X.FE = X.fe.sq(y)
  +u : X.FE = X.fe.norm(X.fe.sub(y2, X.fe.one()))
  +v : X.FE = X.fe.add(X.fe.mul(ed.d(), y2), X.fe.one())
  +v3 : X.FE = X.fe.mul(X.fe.sq(v), v)
  +v7 : X.FE = X.fe.mul(X.fe.sq(v3), v)
  +cand : X.FE = X.fe.mul(X.fe.mul(u, v3), X.fe.pow(ed.sqrt_bits(), X.fe.mul(u, v7), X.fe.one()))
  +vx2 : X.FE = X.fe.mul(v, X.fe.sq(cand))
  ed.decode.root.pick(P.p256.eqn(X.fe.bytes(X.fe.canon(vx2)), X.fe.bytes(X.fe.canon(u))),
    P.p256.eqn(X.fe.bytes(X.fe.canon(vx2)), X.fe.bytes(X.fe.canon(X.fe.sub(X.fe.zero(), u)))),
    y, cand, sign)

def ed.decode.root.pick(c1: Bool, c2: Bool, +y: X.FE, +cand: X.FE, sign: Nat) -> Maybe<&2, EP>:
  match c1:
    case True{}:
      ed.decode.sign(cand, y, sign)
    case False{}:
      match c2:
        case True{}:
          ed.decode.sign(X.fe.mul(cand, ed.sqrt_m1()), y, sign)
        case False{}:
          None{}

# the root with the sign: x = 0 cannot carry the sign bit 1; otherwise x takes the sign's parity
def ed.decode.sign(+x: X.FE, +y: X.FE, sign: Nat) -> Maybe<&2, EP>:
  ed.decode.sign.at(P.p256.is0(X.fe.bytes(X.fe.canon(x))), x, y, sign,
    Nat.mod(ed.head_n(X.fe.bytes(X.fe.canon(x))), 2n))

def ed.decode.sign.at(zero: Bool, +x: X.FE, +y: X.FE, +sign: Nat, +parity: Nat) -> Maybe<&2, EP>:
  match zero:
    case True{}:
      ed.decode.sign.fin(Nat.is_eq(sign, 1n), x, y, sign, parity)
    case False{}:
      ed.decode.sign.fin(False{}, x, y, sign, parity)

def ed.decode.sign.fin(bad: Bool, +x: X.FE, +y: X.FE, sign: Nat, parity: Nat) -> Maybe<&2, EP>:
  match bad:
    case True{}:
      None{}
    case False{}:
      Some{ed.point(ed.decode.flip(Nat.is_eq(parity, sign), x), y)}

def ed.decode.flip(same: Bool, +x: X.FE) -> X.FE:
  match same:
    case True{}:
      x
    case False{}:
      X.fe.sub(X.fe.zero(), x)

def ed.point(+x: X.FE, +y: X.FE) -> EP:
  EP{x, y, X.fe.one(), X.fe.mul(x, y)}

# the 32-byte encoding of P: y, and the parity of x in the top bit
def ed.encode(+p: EP) -> List<&2, Nat>:
  match p:
    case EP{+x, +y, +z, +t}:
      ed.encode.at(X.fe.inv(z), x, y)

def ed.encode.at(+zi: X.FE, +x: X.FE, +y: X.FE) -> List<&2, Nat>:
  ed.encode.fin(X.fe.bytes(X.fe.canon(X.fe.mul(x, zi))), X.fe.bytes(X.fe.canon(X.fe.mul(y, zi))))

def ed.encode.fin(+xb: List<&2, Nat>, +yb: List<&2, Nat>) -> List<&2, Nat>:
  ed.set_top(yb, Nat.mod(ed.head_n(xb), 2n))

# Reduction mod L
# ---------------

# the bits of v, most significant first, in 8 bits
def ed.bits8(+v: Nat) -> List<&2, Nat>:
  P.p256.bits.go(8n, v, 128n)

# the bits of the bytes (most significant byte first) folded into r mod L: r = 2r + bit,
# minus L when that reaches L (r < L always, so 2r + bit < 2L)
def ed.modl.bytes(bs: List<&2, Nat>, +r: List<&2, Nat>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      r
    case b <> t:
      ed.modl.bytes(t, ed.modl.bits(ed.bits8(b), r))

def ed.modl.bits(bits: List<&2, Nat>, +r: List<&2, Nat>) -> List<&2, Nat>:
  match bits:
    case Nil{}:
      r
    case b <> t:
      ed.modl.bits(t, ed.modl.step(r, b))

def ed.modl.step(+r: List<&2, Nat>, b: Nat) -> List<&2, Nat>:
  B.bi.csub(B.bi.addk(r, r, 1n, b), ed.lmb())

# a little-endian 64-byte integer mod L, as 18 limbs
def ed.modl(+hle: List<&2, U32>) -> List<&2, Nat>:
  ed.modl.bytes(List.reverse(&2, Nat, ed.nat_bytes(hle)), B.bi.zeros(18n))

# SHA-512(R || A || M) mod L
def ed.hash_k(+r: List<&2, U32>, +pk: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, Nat>:
  ed.modl(SH.sha512.hash(List.append(&2, U32, r, List.append(&2, U32, pk, msg))))

# Verification
# ------------

# RFC 8032 5.1.7: S < L, A decodes, and encode([S]B - [k]A) = R (the cofactorless
# check, which the RFC's equality [S]B = R + [k]A is)
def ed.verify(+pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  ed.verify.len(Bool.and(Nat.is_eq(List.length(&2, U32, pk), 32n), Nat.is_eq(List.length(&2, U32, sig), 64n)),
    pk, msg, sig)

def ed.verify.len(ok: Bool, +pk: List<&2, U32>, +msg: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  match ok:
    case True{}:
      ed.verify.go(pk, msg, List.take(&2, U32, sig, 32n), List.drop(&2, U32, sig, 32n))
    case False{}:
      False{}

def ed.verify.go(+pk: List<&2, U32>, +msg: List<&2, U32>, +r: List<&2, U32>, +s: List<&2, U32>) -> Bool:
  ed.verify.check(P.p256.lt(ed.le_limbs(s), ed.lmb()), ed.decode(pk), r, ed.le_limbs(s),
    ed.hash_k(r, pk, msg))

def ed.verify.check(s_ok: Bool, +a: Maybe<&2, EP>, +r: List<&2, U32>, +s: List<&2, Nat>,
  +k: List<&2, Nat>) -> Bool:
  match s_ok:
    case True{}:
      ed.verify.point(a, r, s, k)
    case False{}:
      False{}

def ed.verify.point(+a: Maybe<&2, EP>, +r: List<&2, U32>, +s: List<&2, Nat>, +k: List<&2, Nat>) -> Bool:
  match a:
    case Some{+ap}:
      P.p256.eqn(ed.encode(ed.add(ed.smul(P.p256.bits(s), ed.base()), ed.smul(P.p256.bits(k), ed.neg(ap)))),
        ed.nat_bytes(r))
    case None{}:
      False{}
