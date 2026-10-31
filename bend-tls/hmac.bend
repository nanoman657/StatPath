# hmac.bend: HMAC-SHA256 (RFC 2104) over byte lists.
#
#   HMAC(K, m) = H((K0 xor opad) || H((K0 xor ipad) || m)), with K0 the key
#   padded with zeros to 64 bytes, or H(key) padded when the key is longer.

import Base
import ./sha256.bend as S

# the length of xs, counted without deep recursion
def hm.len(+xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      hm.len(t, 1n+acc)

# xs with every byte xored with c
def hm.xor(+xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case b <> t:
      U32.xor(b, c) <> hm.xor(t, c)

def hm.zeros(k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      (0 : U32) <> hm.zeros(p)

# the key as a 64-byte block: the hash of a long key, zero-padded
def hm.k0.at(long: Bool, +k: List<&2, U32>) -> List<&2, U32>:
  match long:
    case True{}:
      List.append(&2, U32, S.sha256_bytes(k), hm.zeros(32n))
    case False{}:
      List.append(&2, U32, k, hm.zeros(Nat.sub(64n, hm.len(k, 0n))))

def hm.k0(+k: List<&2, U32>) -> List<&2, U32>:
  hm.k0.at(Nat.is_gt(hm.len(k, 0n), 64n), k)

# HMAC-SHA256 of msg under key: 32 bytes
def hmac(+key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +k0 = hm.k0(key)
  +inner = S.sha256_bytes(List.append(&2, U32, hm.xor(k0, 54), msg))
  S.sha256_bytes(List.append(&2, U32, hm.xor(k0, 92), inner))

# the HMAC of msg as 64 hex digits
def hmac_hex(+key: List<&2, U32>, +msg: List<&2, U32>) -> String:
  S.hex_of(hmac(key, msg))
