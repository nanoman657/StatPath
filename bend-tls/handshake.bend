# handshake.bend: the client side of a TLS 1.3 handshake with
# TLS_CHACHA20_POLY1305_SHA256 and x25519 (RFC 8446), as pure functions over
# byte lists: the key schedule, the protected records, and the checks of the
# server's Certificate, CertificateVerify and Finished.

import Base
import ./sha256.bend as S
import ./hmac.bend as H
import ./hkdf.bend as K
import ./aead.bend as A
import ./x25519.bend as X
import ./tls.bend as T
import ./x509.bend as C
import ./rsa.bend as R

# the server's protected records: the AEAD open of a record body under the key
# and nonce, with the record header as the associated data (RFC 8446 5.2)
type Inner is Data:
  Inner{ctype: U32, body: List<&2, U32>}

def hs.open(+key: List<&2, U32>, +iv: List<&2, U32>, seq: Nat, +rec: List<&2, U32>) ->
  Maybe<&2, List<&2, U32>>:
  A.aead_open(key, T.tls.nonce(iv, seq), List.take(&2, U32, rec, 5n), List.drop(&2, U32, rec, 5n))

# the content type is the last nonzero byte of the decrypted record
def hs.zero(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      U32.is_eq(x, 0)

def hs.strip(+rev: List<&2, U32>, z: Bool) -> Inner:
  match rev:
    case Nil{}:
      Inner{0, Nil{}}
    case x <> t:
      match z:
        case True{}:
          hs.strip(t, hs.zero(List.take(&2, U32, t, 1n)))
        case False{}:
          Inner{x, List.reverse(&2, U32, t)}

def hs.unpad(+inner: List<&2, U32>) -> Inner:
  hs.strip(List.reverse(&2, U32, inner), hs.zero(List.take(&2, U32, List.reverse(&2, U32, inner), 1n)))

# the handshake secret of the x25519 exchange with the server's key share
def hs.hs_secret(+priv: List<&2, U32>, +spub: List<&2, U32>) -> List<&2, U32>:
  K.handshake_secret(K.early_secret(), X.x25519(priv, spub))

def hs.master(+priv: List<&2, U32>, +spub: List<&2, U32>) -> List<&2, U32>:
  K.master_secret(hs.hs_secret(priv, spub))

# the bytes of a message: its header and body (the raw encoding)
def hs.raw.at(+m: T.HM) -> List<&2, U32>:
  match m:
    case T.HM{t, body, rest}:
      T.tls.hs(t, body)

# the CertificateVerify content the server signed (RFC 8446 4.4.3)
def hs.raw(+m: T.HM) -> List<&2, U32>:
  hs.raw.at(m)

def hs.label() -> List<&2, U32>:
  S.bytes_of("TLS 1.3, server CertificateVerify")

# the server's CertificateVerify: rsa_pss_rsae_sha256 over the content, with the
# leaf key
def hs.spaces(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      (32 : U32) <> hs.spaces(p)

def hs.cv_content(+th: List<&2, U32>) -> List<&2, U32>:
  T.tls.cat(hs.spaces(64n), T.tls.cat(hs.label(), T.tls.cat(0 <> Nil{}, th)))

def hs.cv_ok.at(alg: Nat, +leaf: List<&2, U32>, +th: List<&2, U32>, +sig: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(alg, 2052n), R.rsa.verify_pss(C.x509.nkey(C.x509.spki(leaf)), sig, hs.cv_content(th)))

# the server's Finished: the MAC of the transcript under its traffic key
def hs.cv_ok(+leaf: List<&2, U32>, +th: List<&2, U32>, +body: List<&2, U32>) -> Bool:
  hs.cv_ok.at(T.tls.num(2n, body), leaf, th, List.drop(&2, U32, body, 4n))

def hs.fin_ok(+s_hs: List<&2, U32>, +th: List<&2, U32>, +body: List<&2, U32>) -> Bool:
  R.rsa.eqb(K.finished_mac(s_hs, th), body)
