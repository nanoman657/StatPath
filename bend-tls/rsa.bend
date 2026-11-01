# rsa.bend: RSA public-key operations for TLS certificate and handshake
# signatures: s^65537 mod n, PKCS#1 v1.5 and PSS (RFC 8017) signature checks
# with SHA-256. Big-endian byte lists (List<&2, U32>, values 0..255) are the
# interface; limbs (bigint.bend) are the arithmetic.

import Base
import ./sha256.bend as S
import ./bigint.bend as B

# Counting and conversions
# ------------------------

def rsa.count(+xs: List<&2, Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      rsa.count(t, 1n+acc)

# the little-endian bytes of a little-endian limb list (each limb two bytes)
def rsa.limb_bytes(+xs: List<&2, Nat>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      U32.from_nat(Nat.mod(x, 256n)) <> U32.from_nat(Nat.div(x, 256n)) <> rsa.limb_bytes(t)

# the little-endian limbs of little-endian bytes
def rsa.byte_limbs(+bs: List<&2, U32>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case a <> rest:
      match rest:
        case Nil{}:
          U32.to_nat(a) <> Nil{}
        case b <> t:
          Nat.add(U32.to_nat(a), Nat.mul(256n, U32.to_nat(b))) <> rsa.byte_limbs(t)

# a big-endian number of k bytes as a list of L limbs (L >= k / 2 rounded up)
def rsa.limbs.pad(+xs: List<&2, Nat>, L: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, xs, B.bi.zeros(Nat.sub(L, rsa.count(xs, 0n))))

def rsa.limbs_of_be(+bs: List<&2, U32>, L: Nat) -> List<&2, Nat>:
  rsa.limbs.pad(rsa.byte_limbs(List.reverse(&2, U32, bs)), L)

def rsa.countu(+xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      rsa.countu(t, 1n+acc)

# the last k of the big-endian reading of the little-endian bytes le
def rsa.be.last(+k: Nat, +le: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, List.reverse(&2, U32, le), Nat.sub(rsa.countu(le, 0n), k))

# the k big-endian bytes of a limb list (the value must fit in k bytes)
def rsa.be_of_limbs(+xs: List<&2, Nat>, k: Nat) -> List<&2, U32>:
  rsa.be.last(k, rsa.limb_bytes(xs))

# Exponentiation
# --------------

# R^2 mod m for R = 2^(16 n): 2^(32 n) mod m by doubling from 1
def rsa.r2.loop(fuel: Nat, +x: List<&2, Nat>, +m: List<&2, Nat>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      x
    case 1n+p:
      rsa.r2.loop(p, B.bi.csub(B.bi.addk(x, x, 1n, 0n), m), m)

def rsa.one(L: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, 1n <> Nil{}, B.bi.zeros(Nat.sub(L, 1n)))

# y^(2^k) in the Montgomery domain
def rsa.square.loop(k: Nat, +y: List<&2, Nat>, +m: List<&2, Nat>, +n0: Nat, +n: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      y
    case 1n+p:
      rsa.square.loop(p, B.bi.mont(y, y, m, n0, n), m, n0, n)

# s^65537 mod m, in limbs; s < m, lists of length n + 2
def rsa.pow65537(+s: List<&2, Nat>, +m: List<&2, Nat>, +n0: Nat, +n: Nat) -> List<&2, Nat>:
  +r2 = rsa.r2.loop(Nat.mul(32n, n), rsa.one(Nat.add(n, 2n)), m)
  +sm = B.bi.mont(s, r2, m, n0, n)
  +y = rsa.square.loop(16n, sm, m, n0, n)
  B.bi.mont(B.bi.mont(y, sm, m, n0, n), rsa.one(Nat.add(n, 2n)), m, n0, n)

# the limb count of a modulus of k bytes
def rsa.nlimbs(k: Nat) -> Nat:
  Nat.div(Nat.add(k, 1n), 2n)

# sig^65537 mod m as the k big-endian bytes; m is the modulus in limbs (length
# n + 2), sig is below m
def rsa.public.mod(+sig: List<&2, U32>, +m: List<&2, Nat>, k: Nat) -> List<&2, U32>:
  rsa.be_of_limbs(rsa.pow65537(rsa.limbs_of_be(sig, rsa.count(m, 0n)), m,
    B.bi.n0(B.bi.low(m)), Nat.sub(rsa.count(m, 0n), 2n)), k)

# RSAVP1 with e = 65537: sig^65537 mod n, n given as k big-endian bytes
def rsa.public(+sig: List<&2, U32>, +nbe: List<&2, U32>) -> List<&2, U32>:
  rsa.public.mod(sig, rsa.limbs_of_be(nbe, Nat.add(rsa.nlimbs(rsa.countu(nbe, 0n)), 2n)),
    rsa.countu(nbe, 0n))

# Signature encodings
# -------------------

def rsa.eqb(+a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case _:
          False{}
    case x <> xt:
      match b:
        case y <> yt:
          Bool.and(U32.is_eq(x, y), rsa.eqb(xt, yt))
        case _:
          False{}

def rsa.xorb(+a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      Nil{}
    case x <> xt:
      match b:
        case y <> yt:
          U32.xor(x, y) <> rsa.xorb(xt, yt)
        case _:
          Nil{}

def rsa.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (0 : U32) <> rsa.zeros(p)

def rsa.allzero(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(U32.is_eq(x, 0), rsa.allzero(t))

# the MGF1 mask of seed, length len: SHA-256(seed || counter) blocks in order
def rsa.be4(+c: Nat) -> List<&2, U32>:
  U32.from_nat(Nat.div(c, 16777216n)) <> U32.from_nat(Nat.mod(Nat.div(c, 65536n), 256n))
    <> U32.from_nat(Nat.mod(Nat.div(c, 256n), 256n)) <> U32.from_nat(Nat.mod(c, 256n)) <> Nil{}

def rsa.mgf1.blocks(k: Nat, +c: Nat, +seed: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, S.sha256_bytes(List.append(&2, U32, seed, rsa.be4(c))),
        rsa.mgf1.blocks(p, 1n+c, seed))

# the 4-byte big-endian encoding of c
def rsa.mgf1(+seed: List<&2, U32>, +len: Nat) -> List<&2, U32>:
  List.take(&2, U32, rsa.mgf1.blocks(Nat.div(Nat.add(len, 31n), 32n), 0n, seed), len)

# DigestInfo of SHA-256 (RFC 8017 section 9.2 note 1)
def rsa.digestinfo() -> List<&2, U32>:
  48 <> 49 <> 48 <> 13 <> 6 <> 9 <> 96 <> 134 <> 72 <> 1 <> 101 <> 3 <> 4 <> 2 <> 1 <> 5 <> 0 <> 4 <> 32 <> Nil{}

# RSASSA-PKCS1-v1_5 with SHA-256: the signature sig of msg under n
def rsa.ffs(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (255 : U32) <> rsa.ffs(p)

# the first and last bytes of a list
def rsa.pkcs1.encode(k: Nat, h: List<&2, U32>) -> List<&2, U32>:
  (0 : U32) <> (1 : U32) <> List.append(&2, U32, rsa.ffs(Nat.sub(k, 54n)),
    (0 : U32) <> List.append(&2, U32, rsa.digestinfo(), h))

def rsa.pkcs1.check(+em: List<&2, U32>, +nbe: List<&2, U32>, +msg: List<&2, U32>) -> Bool:
  rsa.eqb(em, rsa.pkcs1.encode(rsa.countu(nbe, 0n), S.sha256_bytes(msg)))

# 0x00 0x01 FF..FF 0x00 DigestInfo H, k bytes
def rsa.verify_pkcs1(+nbe: List<&2, U32>, +sig: List<&2, U32>, +msg: List<&2, U32>) -> Bool:
  rsa.pkcs1.check(rsa.public(sig, nbe), nbe, msg)

def rsa.firstbyte(+xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> t:
      x

def rsa.lastbyte(+xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> t:
      match t:
        case Nil{}:
          x
        case y <> u:
          rsa.lastbyte(t)

# the DB with its top bit cleared (emBits = 8k - 1, so one bit of DB[0] is unused)
def rsa.clear_top(+db: List<&2, U32>) -> List<&2, U32>:
  match db:
    case Nil{}:
      Nil{}
    case x <> t:
      U32.and(x, 127) <> t

# H' = SHA-256(0^8 || mHash || salt) must be H
def rsa.pss.hash(+mh: List<&2, U32>, +h: List<&2, U32>, +salt: List<&2, U32>) -> Bool:
  rsa.eqb(S.sha256_bytes(List.append(&2, U32, rsa.zeros(8n), List.append(&2, U32, mh, salt))), h)

# DB = 0^(k-66) || 0x01 || salt: the separator byte and the zero run, then the hash
def rsa.pss.sep.ok(+mh: List<&2, U32>, +h: List<&2, U32>, salt: List<&2, U32>, ok: Bool) -> Bool:
  match ok:
    case True{}:
      rsa.pss.hash(mh, h, salt)
    case False{}:
      False{}

# the mask of H removes maskedDB's random bytes; then the separator is checked
def rsa.pss.sep(+k: Nat, +mh: List<&2, U32>, +h: List<&2, U32>, +db: List<&2, U32>) -> Bool:
  rsa.pss.sep.ok(mh, h, List.drop(&2, U32, db, Nat.add(Nat.sub(k, 66n), 1n)),
    Bool.and(rsa.allzero(List.take(&2, U32, db, Nat.sub(k, 66n))),
      U32.is_eq(rsa.firstbyte(List.drop(&2, U32, db, Nat.sub(k, 66n))), 1)))

def rsa.pss.db(+k: Nat, +mh: List<&2, U32>, +h: List<&2, U32>, +masked: List<&2, U32>) -> Bool:
  rsa.pss.sep(k, mh, h, rsa.clear_top(rsa.xorb(masked, rsa.mgf1(h, Nat.sub(k, 33n)))))

# the top bit of EM must be clear, then the DB checks run
def rsa.pss.top.at(+k: Nat, +mh: List<&2, U32>, +h: List<&2, U32>, +masked: List<&2, U32>, ok: Bool) -> Bool:
  match ok:
    case True{}:
      rsa.pss.db(k, mh, h, masked)
    case False{}:
      False{}

# EM must end in 0xbc
def rsa.pss.top(+k: Nat, +em: List<&2, U32>, +mh: List<&2, U32>) -> Bool:
  rsa.pss.top.at(k, mh, List.take(&2, U32, List.drop(&2, U32, em, Nat.sub(k, 33n)), 32n),
    List.take(&2, U32, em, Nat.sub(k, 33n)), U32.is_eq(U32.and(rsa.firstbyte(em), 128), 0))

def rsa.pss.check.at(+k: Nat, +em: List<&2, U32>, +mh: List<&2, U32>, ok: Bool) -> Bool:
  match ok:
    case True{}:
      rsa.pss.top(k, em, mh)
    case False{}:
      False{}

# RSASSA-PSS verify with SHA-256, MGF1 with SHA-256, salt length 32 (k = 256 for
# a 2048-bit modulus; the EM length is k)
def rsa.pss.check(+k: Nat, +em: List<&2, U32>, +mh: List<&2, U32>) -> Bool:
  rsa.pss.check.at(k, em, mh, U32.is_eq(rsa.lastbyte(em), 188))

def rsa.verify_pss(+nbe: List<&2, U32>, +sig: List<&2, U32>, +msg: List<&2, U32>) -> Bool:
  rsa.pss.check(rsa.countu(nbe, 0n), rsa.public(sig, nbe), S.sha256_bytes(msg))
