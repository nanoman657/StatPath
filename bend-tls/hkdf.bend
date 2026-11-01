# hkdf.bend: HKDF (RFC 5869) and the TLS 1.3 key schedule (RFC 8446 section 7.1) for the
# two hashes of our suites: SHA-256 (hl = 32, TLS_AES_128_GCM_SHA256 and
# TLS_CHACHA20_POLY1305_SHA256) and SHA-384 (hl = 48, TLS_AES_256_GCM_SHA384). Every
# function takes hl, the hash length, first; it selects the hash and its HMAC.
#
# Byte strings are List<&2, U32> (values 0..255), as in sha256.bend.

import Base
import ./sha256.bend as S
import ./hmac.bend as H
import ./hmac384.bend as H3
import ./sha512.bend as SH

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

# the hash of xs: SHA-256 when hl is 32, SHA-384 when it is 48
def hash_of.at(is384: Bool, +xs: List<&2, U32>) -> List<&2, U32>:
  match is384:
    case True{}:
      SH.sha384.hash(xs)
    case False{}:
      S.sha256_bytes(xs)

# HMAC with the hash of length hl
def hash_of(hl: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  hash_of.at(Nat.is_eq(hl, 48n), xs)

def hmac_of.at(is384: Bool, +key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  match is384:
    case True{}:
      H3.hmac384(key, msg)
    case False{}:
      H.hmac(key, msg)

# PRK = HMAC-Hash(salt, IKM). An empty salt is the zero bytes that HMAC already uses as
# its key padding, so no special case is needed.
def hmac_of(hl: Nat, +key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  hmac_of.at(Nat.is_eq(hl, 48n), key, msg)

def hkdf_extract(hl: Nat, +salt: List<&2, U32>, +ikm: List<&2, U32>) -> List<&2, U32>:
  hmac_of(hl, salt, ikm)

# T(1) .. T(k) with T(i) = HMAC(prk, T(i-1) || info || i), in order
def hk.blocks(+hl: Nat, k: Nat, +t: U32, +prev: List<&2, U32>, +prk: List<&2, U32>,
  +info: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      +ti = hmac_of(hl, prk, hk.cat(prev, hk.cat(info, t <> Nil{})))
      hk.cat(ti, hk.blocks(hl, p, U32.add(t, 1), ti, prk, info))

# the first len bytes of the output keying material
def hkdf_expand(+hl: Nat, +prk: List<&2, U32>, +info: List<&2, U32>, +len: Nat) -> List<&2, U32>:
  List.take(&2, U32, hk.blocks(hl, Nat.div(Nat.add(len, Nat.sub(hl, 1n)), hl), 1, Nil{}, prk, info), len)

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
def expand_label(hl: Nat, +secret: List<&2, U32>, label: String, +context: List<&2, U32>, +len: Nat) ->
  List<&2, U32>:
  hkdf_expand(hl, secret, hk.label(len, S.bytes_of(label), context), len)

# Derive-Secret(secret, label, Transcript-Hash(messages)): the caller passes the
# transcript hash, so this is HKDF-Expand-Label with an hl-byte output
def derive_secret(+hl: Nat, +secret: List<&2, U32>, label: String, +transcript: List<&2, U32>) ->
  List<&2, U32>:
  expand_label(hl, secret, label, transcript, hl)

# the hash of the empty message, the transcript for "derived"
def empty_hash(hl: Nat) -> List<&2, U32>:
  hash_of(hl, Nil{})

# early secret: Extract with no PSK (hl zero bytes) and salt 0
def early_secret(+hl: Nat) -> List<&2, U32>:
  hkdf_extract(hl, hk.zeros(hl), hk.zeros(hl))

# handshake secret, from the early secret and the (EC)DHE shared secret
def handshake_secret(+hl: Nat, +early: List<&2, U32>, +dhe: List<&2, U32>) -> List<&2, U32>:
  hkdf_extract(hl, derive_secret(hl, early, "derived", empty_hash(hl)), dhe)

# master secret, from the handshake secret
def master_secret(+hl: Nat, +hs: List<&2, U32>) -> List<&2, U32>:
  hkdf_extract(hl, derive_secret(hl, hs, "derived", empty_hash(hl)), hk.zeros(hl))

# the record key and IV of a traffic secret: 16-byte key, 12-byte IV
def traffic_key(+hl: Nat, +secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(hl, secret, "key", Nil{}, 16n)

def traffic_iv(+hl: Nat, +secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(hl, secret, "iv", Nil{}, 12n)

# the Finished MAC key of a base traffic secret (hl bytes)
def finished_key(+hl: Nat, +secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(hl, secret, "finished", Nil{}, hl)

# the verify_data of a Finished message over the transcript hash
def finished_mac(+hl: Nat, +secret: List<&2, U32>, +transcript: List<&2, U32>) -> List<&2, U32>:
  hmac_of(hl, finished_key(hl, secret), transcript)

# the 32-byte record key of a traffic secret, for TLS_CHACHA20_POLY1305_SHA256
def traffic_key32(+hl: Nat, +secret: List<&2, U32>) -> List<&2, U32>:
  expand_label(hl, secret, "key", Nil{}, 32n)

# the record key of a traffic secret of len bytes (16 for AES-128-GCM, 32 for AES-256-GCM and ChaCha20)
def traffic_keyn(+hl: Nat, +secret: List<&2, U32>, +len: Nat) -> List<&2, U32>:
  expand_label(hl, secret, "key", Nil{}, len)
