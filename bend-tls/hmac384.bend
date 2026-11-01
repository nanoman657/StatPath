# hmac384.bend: HMAC-SHA-384 (RFC 2104) over byte lists, for TLS_AES_256_GCM_SHA384.
#
#   HMAC(K, m) = H((K0 xor opad) || H((K0 xor ipad) || m)), with K0 the key padded
#   with zeros to the 128-byte block of SHA-384, or H(key) padded when the key is
#   longer. The tag is 48 bytes.

import Base
import ./sha512.bend as SH

# the length of xs, counted without deep recursion
def h3.len(+xs: List<&2, U32>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case h <> t:
      h3.len(t, 1n+acc)

# xs with every byte xored with c
def h3.xor(+xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case b <> t:
      U32.xor(b, c) <> h3.xor(t, c)

def h3.zeros(k: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      (0 : U32) <> h3.zeros(p)

# the key as a 128-byte block: the hash of a long key, zero-padded
def h3.k0.at(long: Bool, +k: List<&2, U32>) -> List<&2, U32>:
  match long:
    case True{}:
      List.append(&2, U32, SH.sha384.hash(k), h3.zeros(80n))
    case False{}:
      List.append(&2, U32, k, h3.zeros(Nat.sub(128n, h3.len(k, 0n))))

def h3.k0(+k: List<&2, U32>) -> List<&2, U32>:
  h3.k0.at(Nat.is_gt(h3.len(k, 0n), 128n), k)

# HMAC-SHA-384 of msg under key: 48 bytes
def hmac384(+key: List<&2, U32>, +msg: List<&2, U32>) -> List<&2, U32>:
  +k0 = h3.k0(key)
  +inner = SH.sha384.hash(List.append(&2, U32, h3.xor(k0, 54), msg))
  SH.sha384.hash(List.append(&2, U32, h3.xor(k0, 92), inner))
