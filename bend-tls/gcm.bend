# GCM (NIST SP 800-38D) over AES-128: the AEAD of TLS_AES_128_GCM_SHA256.
# gcm.seal and gcm.open take a 16-byte key, a 12-byte nonce, and the associated
# data and the plaintext (or ciphertext) as byte lists (U32 values 0..255). The
# sealed output is the ciphertext followed by the 16-byte tag. Field elements
# are 16-byte lists, most significant byte first, as GCM orders its bits.

import Base
import ./aes.bend as AES
import ./rsa.bend as R

# n bytes of 0
def gcm.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> gcm.zeros(p)

# the 4 bytes of w, big-endian
def gcm.be32(+w: U32) -> List<&2, U32>:
  U32.and(U32.shrn(w, 24n), 255) <> U32.and(U32.shrn(w, 16n), 255)
    <> U32.and(U32.shrn(w, 8n), 255) <> U32.and(w, 255) <> Nil{}

# the big-endian 32-bit value of the first 4 bytes of xs
def gcm.word(+xs: List<&2, U32>) -> U32:
  U32.or(U32.or(U32.shln(AES.aes.at(xs, 0n), 24n), U32.shln(AES.aes.at(xs, 1n), 16n)),
    U32.or(U32.shln(AES.aes.at(xs, 2n), 8n), AES.aes.at(xs, 3n)))

# the counter block after ctr: the nonce part, then the last 4 bytes plus 1 mod 2^32
def gcm.inc(+ctr: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, List.take(&2, U32, ctr, 12n),
    gcm.be32(U32.add(gcm.word(List.drop(&2, U32, ctr, 12n)), 1)))

# the first counter block: the nonce and 0x00000001
def gcm.j0(+nonce: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, nonce, 0 <> 0 <> 0 <> 1 <> Nil{})

# the bytes of xs, zero-padded to a multiple of 16
def gcm.pad(+xs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs,
    gcm.zeros(Nat.mod(Nat.sub(16n, Nat.mod(List.length(&2, U32, xs), 16n)), 16n)))

# the length block part for n bytes: 64 bits, big-endian, of the length in bits
def gcm.len64(n: Nat) -> List<&2, U32>:
  List.append(&2, U32, gcm.zeros(4n), gcm.be32(U32.from_nat(Nat.mul(8n, n))))

# shift right by one bit a big-endian byte list: carry is the bit from the byte
# before (the first byte gets 0)
def gcm.shr(+v: List<&2, U32>, carry: U32) -> List<&2, U32>:
  match v:
    case Nil{}:
      Nil{}
    case +x <> t:
      U32.or(U32.shrn(x, 1n), U32.shln(carry, 7n)) <> gcm.shr(t, U32.and(x, 1))

# the reduction (GCM 6.3): the bit shifted out of a field element, from the least significant
# end (bit, 0 or 1), xors 0xe1 into the first byte: a multiplication by the bit, with no branch
def gcm.reduce(+bit: U32, +v: List<&2, U32>) -> List<&2, U32>:
  match v:
    case +x <> t:
      U32.xor(x, U32.mul(bit, 225)) <> t
    case Nil{}:
      Nil{}

# v times x in the field: one bit shifted right, reduced if the bit is set
def gcm.shr1(+v: List<&2, U32>) -> List<&2, U32>:
  gcm.reduce(U32.and(AES.aes.at(v, 15n), 1), gcm.shr(v, 0))

# a where bit is 1, b where it is 0, byte by byte, with no branch: a * bit + b * (1 - bit)
def gcm.cond(+bit: U32, +a: List<&2, U32>, +b: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Nil{}:
      Nil{}
    case +x <> t:
      match b:
        case Nil{}:
          Nil{}
        case +y <> u:
          U32.add(U32.mul(x, bit), U32.mul(y, U32.xor(bit, 1))) <> gcm.cond(bit, t, u)

# the field product x * y (GCM Algorithm 1): for each bit of x from the most
# significant (bit k of the 128, byte k / 8, bit 7 - k mod 8), z gets v when the
# bit is set, and v is then multiplied by x
def gcm.mul.go(fuel: Nat, +k: Nat, +x: List<&2, U32>, +z: List<&2, U32>, +v: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      z
    case 1n+p:
      gcm.mul.go(p, Nat.add(k, 1n), x,
        gcm.cond(U32.and(U32.shrn(AES.aes.at(x, Nat.div(k, 8n)), Nat.sub(7n, Nat.mod(k, 8n))), 1),
          AES.aes.xor(z, v), z),
        gcm.shr1(v))

# GHASH over whole blocks: each block is xored into y, then multiplied by h
def gcm.mul(+x: List<&2, U32>, +y: List<&2, U32>) -> List<&2, U32>:
  gcm.mul.go(128n, 0n, x, gcm.zeros(16n), y)

def gcm.gh(fuel: Nat, +h: List<&2, U32>, +xs: List<&2, U32>, +y: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      y
    case 1n+p:
      gcm.gh(p, h, List.drop(&2, U32, xs, 16n),
        gcm.mul(AES.aes.xor(y, List.take(&2, U32, xs, 16n)), h))

# GHASH of the associated data and the ciphertext, each zero-padded, then their
# lengths in bits
def gcm.ghash(+h: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  +xs : List<&2, U32> = List.append(&2, U32, gcm.pad(aad), List.append(&2, U32, gcm.pad(ct),
    List.append(&2, U32, gcm.len64(List.length(&2, U32, aad)), gcm.len64(List.length(&2, U32, ct)))))
  gcm.gh(Nat.div(List.length(&2, U32, xs), 16n), h, xs, gcm.zeros(16n))

# CTR mode: one block at a time, the keystream block being the cipher of the counter
def gcm.ctr(fuel: Nat, +ctr: List<&2, U32>, +rk: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, AES.aes.xor(List.take(&2, U32, xs, 16n), AES.aes.enc(rk, ctr)),
        gcm.ctr(p, gcm.inc(ctr), rk, List.drop(&2, U32, xs, 16n)))

def gcm.trunc(+xs: List<&2, U32>, n: Nat) -> List<&2, U32>:
  List.take(&2, U32, xs, n)

# the GCM encryption (or decryption) of xs: the same operation both ways
def gcm.crypt(+key: List<&2, U32>, +nonce: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  +rk : List<&2, U32> = AES.aes.expand(key)
  +padded : List<&2, U32> = gcm.pad(xs)
  gcm.trunc(gcm.ctr(Nat.div(List.length(&2, U32, padded), 16n), gcm.inc(gcm.j0(nonce)), rk, padded),
    List.length(&2, U32, xs))

# the 16-byte tag over the associated data and the ciphertext
def gcm.tag(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  +rk : List<&2, U32> = AES.aes.expand(key)
  +h : List<&2, U32> = AES.aes.enc(rk, gcm.zeros(16n))
  AES.aes.xor(AES.aes.enc(rk, gcm.j0(nonce)), gcm.ghash(h, aad, ct))

def gcm.seal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>, +pt: List<&2, U32>) -> List<&2, U32>:
  +ct : List<&2, U32> = gcm.crypt(key, nonce, pt)
  List.append(&2, U32, ct, gcm.tag(key, nonce, aad, ct))

# the plaintext, or None if the tag does not match
def gcm.open.at(ok: Bool, +key: List<&2, U32>, +nonce: List<&2, U32>, +ct: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{gcm.crypt(key, nonce, ct)}
    case False{}:
      None{}

# whether sealed opens under the key, nonce and associated data
def gcm.open(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>,
  +sealed: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  +n : Nat = Nat.sub(List.length(&2, U32, sealed), 16n)
  +ct : List<&2, U32> = List.take(&2, U32, sealed, n)
  gcm.open.at(R.rsa.eqb(gcm.tag(key, nonce, aad, ct), List.drop(&2, U32, sealed, n)), key, nonce, ct)

def gcm.valid.at(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case Some{+p}:
      True{}
    case None{}:
      False{}

def gcm.valid(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>,
  +sealed: List<&2, U32>) -> Bool:
  gcm.valid.at(gcm.open(key, nonce, aad, sealed))
