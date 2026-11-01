# aead.bend: ChaCha20-Poly1305 AEAD (RFC 8439 sections 2.5, 2.6 and 2.8).
# Bytes are List<&2, U32> with values 0..255. This is the cipher suite
# TLS_CHACHA20_POLY1305_SHA256 uses for records.

import Base
import ./chacha20.bend as C
import ./poly1305.bend as P

# the Poly1305 key: r with its clamping bits cleared (RFC 8439 section 2.5.1)
def ae.clamp(r: List<&2, U32>) -> List<&2, U32>:
  match r:
    case r0 <> r1 <> r2 <> r3 <> r4 <> r5 <> r6 <> r7 <> r8 <> r9 <> r10 <> r11 <> r12 <> r13 <> r14 <> r15 <> Nil{}:
      r0 <> r1 <> r2 <> U32.and(r3, 15) <> U32.and(r4, 252) <> r5 <> r6 <> U32.and(r7, 15)
        <> U32.and(r8, 252) <> r9 <> r10 <> U32.and(r11, 15) <> U32.and(r12, 252) <> r13
        <> r14 <> U32.and(r15, 15) <> Nil{}
    case _:
      Nil{}

# the first n bytes of xs, and xs with them dropped
def ae.take(n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, xs, n)

def ae.drop(n: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, xs, n)

# the list of n zero bytes
def ae.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (0 : U32) <> ae.zeros(p)

# the 8-byte little-endian encoding of x
def ae.le64(k: Nat, +x: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      U32.from_nat(Nat.mod(x, 256n)) <> ae.le64(p, Nat.div(x, 256n))

def ae.len(+xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      ae.len(t, 1n+acc)

# xs padded with zero bytes to a multiple of 16
def ae.pad16(+xs: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ae.zeros(Nat.mod(Nat.sub(16n, Nat.mod(ae.len(xs, 0n), 16n)), 16n)))

# the MAC input: aad, padded; ciphertext, padded; the two lengths
def ae.mac_data(+aad: List<&2, U32>, +ct: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, ae.pad16(aad), List.append(&2, U32, ae.pad16(ct),
    List.append(&2, U32, ae.le64(8n, ae.len(aad, 0n)), ae.le64(8n, ae.len(ct, 0n)))))

# the 16 blocks of msg, each with a 0x01 byte appended, and the Poly1305 sum
def ae.blocks(nb: Nat, +msg: List<&2, U32>, +r: P.F, +h: P.F) -> P.F:
  match nb:
    case 0n:
      h
    case 1n+p:
      ae.blocks(p, ae.drop(16n, msg), r,
        P.pl.mul(P.pl.add(h, P.pl.of_bytes(List.append(&2, U32, ae.take(16n, msg), (1 : U32) <> Nil{}))), r))

def ae.fin(r: P.F & Nat) -> List<&2, U32>:
  (y, c) = r
  P.pl.pack(P.pl.bits_of(y))

# the Poly1305 tag of msg under the key (r, s), 16 bytes
def poly1305_tag(+r16: List<&2, U32>, +s16: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  ae.fin(P.pl.carrynw(P.pl.add(P.pl.canon(ae.blocks(Nat.div(Nat.add(ae.len(msg, 0n), 15n), 16n),
    msg, P.pl.of_bytes(ae.clamp(r16)), P.pl.zero())), P.pl.of_bytes(s16))))

# the one-time key: the first 32 bytes of the block with counter 0
def ae.otk(+key: List<&2, U32>, +nonce: List<&2, U32>) -> List<&2, U32>:
  ae.take(32n, C.chacha20_block(key, 0, nonce))

# seal: the ciphertext of pt followed by its 16-byte tag
def aead_seal(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>,
  +pt: List<&2, U32>) -> List<&2, U32>:
  +ct = C.chacha20_xor(key, 1, nonce, pt)
  List.append(&2, U32, ct, poly1305_tag(ae.take(16n, ae.otk(key, nonce)),
    ae.drop(16n, ae.otk(key, nonce)), ae.mac_data(aad, ct)))

# equal byte lists
def ae.eq(+a: List<&2, U32>, +b: List<&2, U32>) -> Bool:
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
          Bool.and(U32.is_eq(x, y), ae.eq(xt, yt))
        case _:
          False{}

# the check of a tag, then the decryption when it holds
def aead.open.check(ok: Bool, +key: List<&2, U32>, +nonce: List<&2, U32>, +ct: List<&2, U32>) ->
  Maybe<&2, List<&2, U32>>:
  match ok:
    case True{}:
      Some{C.chacha20_xor(key, 1, nonce, ct)}
    case False{}:
      None{}

def aead.open.at(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>,
  +ct: List<&2, U32>, +tag: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  aead.open.check(ae.eq(tag, poly1305_tag(ae.take(16n, ae.otk(key, nonce)),
    ae.drop(16n, ae.otk(key, nonce)), ae.mac_data(aad, ct))), key, nonce, ct)

# open: the plaintext if the tag checks, else None
def aead_open(+key: List<&2, U32>, +nonce: List<&2, U32>, +aad: List<&2, U32>,
  +sealed: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  aead.open.at(key, nonce, aad, ae.take(Nat.sub(ae.len(sealed, 0n), 16n), sealed),
    ae.drop(Nat.sub(ae.len(sealed, 0n), 16n), sealed))
