# hkdf.bend: HKDF (RFC 5869) with SHA-256, and the TLS 1.3 key schedule
# (RFC 8446 section 7.1): HKDF-Expand-Label, Derive-Secret, and the early,
# handshake and master secrets with their traffic keys.
#
# Byte strings are List<&2, U32> (values 0..255), as in sha256.bend.

import Base
import ./sha256.bend as S
import ./hmac.bend as H

# Extract and Expand
# ------------------

def hk.zeros(k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      (0 : U32) <> hk.zeros(p)

# the bytes of xs followed by ys
def hk.cat(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

# PRK = HMAC-Hash(salt, IKM). An empty salt is the 32 zero bytes, which
# HMAC already uses as its key padding, so no special case is needed.
def hkdf_extract(+salt: List<&2, U32>, +ikm: List<&2, U32>) -> List<&2, U32>:
  H.hmac(salt, ikm)

# T(1) .. T(k) with T(i) = HMAC(prk, T(i-1) || info || i), in order
def hk.blocks(k: Nat, +t: U32, +prev: List<&2, U32>, +prk: List<&2, U32>,
  +info: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      +ti = H.hmac(prk, hk.cat(prev, hk.cat(info, t <> Nil{})))
      hk.cat(ti, hk.blocks(p, U32.add(t, 1), ti, prk, info))

# the first len bytes of the output keying material
def hkdf_expand(+prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> List<&2, U32>:
  List.take(&2, U32, hk.blocks(Nat.div(Nat.add(len, 31n), 32n), 1, Nil{}, prk, info), len)

# TLS 1.3 labels and derivations
# ------------------------------

# HkdfLabel: uint16 length, opaque label<..255> ("tls13 " + label),
# opaque context<..255>
def hk.label(+len: Nat, +label: List<&2, U32>, +context: List<&2, U32>) -> List<&2, U32>:
  +full = hk.cat(S.bytes_of("tls13 "), label)
  U32.from_nat(Nat.div(len, 256n)) <> U32.from_nat(Nat.mod(len, 256n))
    <> U32.from_nat(List.length(&2, U32, full)) <> hk.cat(full,
    U32.from_nat(List.length(&2, U32, context)) <> hk.cat(context, Nil{}))

# HKDF-Expand-Label(secret, label, context, length)
def expand_label(+secret: List<&2, U32>, label: String, +context: List<&2, U32>, +len: Nat) ->
  List<&2, U32>:
  hkdf_expand(secret, hk.label(len, S.bytes_of(label), context), len)

# Derive-Secret(secret, label, Transcript-Hash(messages)): the caller passes the
# transcript hash, so this is HKDF-Expand-Label with a 32-byte output
def derive_secret(+secret: List<&2, U32>, label: String, +transcript: List<&2, U32>) ->
  List<&2, U32>:
  expand_label(secret, label, transcript, 32n)

# the hash of the empty message, the transcript for "derived"
def empty_hash() -> List<&2, U32>:
  S.sha256_bytes(Nil{})

# early secret: Extract with no PSK (32 zero bytes) and salt 0
def early_secret() -> List<&2, U32>:
  hkdf_extract(hk.zeros(32n), hk.zeros(32n))

# handshake secret, from the early secret and the (EC)DHE shared secret
def handshake_secret(+early: List<&2, U32>, +dhe: List<&2, U32>) -> List<&2, U32>:
  hkdf_extract(derive_secret(early, "derived", empty_hash()), dhe)

# master secret, from the handshake secret
def master_secret(+hs: List<&2, U32>) -> List<&2, U32>:
  hkdf_extract(derive_secret(hs, "derived", empty_hash()), hk.zeros(32n))

# the record key and IV of a traffic secret: 16-byte key, 12-byte IV
def traffic_key(+secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(secret, "key", Nil{}, 16n)

def traffic_iv(+secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(secret, "iv", Nil{}, 12n)

# the Finished MAC key of a base traffic secret
def finished_key(+secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(secret, "finished", Nil{}, 32n)

# the verify_data of a Finished message over the transcript hash
def finished_mac(+secret: List<&2, U32>, +transcript: List<&2, U32>) -> List<&2, U32>:
  H.hmac(finished_key(secret), transcript)
