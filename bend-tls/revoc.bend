# revoc.bend: the revocation sources of a certificate, and the OCSP check (RFC 5280 4.2.2.1, RFC 6960).
#
#   rev.cdp_uris(c)           the URIs of c's CRL distribution points (extension 2.5.29.31)
#   rev.ocsp_uri(c)           the URI of c's OCSP responder (authority information access, method ocsp)
#   rev.ocsp_request(c, n)    the DER of an OCSPRequest for c, issued by n, with a SHA-256 CertID
#   rev.ocsp_ok(reply, c, n, now)  the reply is a successful answer that says c is good, now
#
# A reply is signed by n, or by a delegated responder certificate in the reply that n issued and
# that has the OCSP-signing purpose. A reply for another certificate, or one that says revoked or
# unknown, is not good.

import Base
import ./asn1.bend as A
import ./x509.bend as X
import ./crl.bend as CR
import ./sha256.bend as S
import ./rsa.bend as R

# OIDs (their contents): CRL distribution points, authority information access, the OCSP
# method, the basic response type, SHA-256, extended key usage and the OCSP-signing purpose
def rev.oid_cdp() -> List<&2, U32>:
  85 <> 29 <> 31 <> Nil{}

def rev.oid_ocsp() -> List<&2, U32>:
  43 <> 6 <> 1 <> 5 <> 5 <> 7 <> 48 <> 1 <> Nil{}

def rev.oid_aia() -> List<&2, U32>:
  43 <> 6 <> 1 <> 5 <> 5 <> 7 <> 1 <> 1 <> Nil{}

def rev.oid_basic() -> List<&2, U32>:
  43 <> 6 <> 1 <> 5 <> 5 <> 7 <> 48 <> 1 <> 1 <> Nil{}

def rev.oid_sha256() -> List<&2, U32>:
  96 <> 134 <> 72 <> 1 <> 101 <> 3 <> 4 <> 2 <> 1 <> Nil{}

def rev.oid_eku() -> List<&2, U32>:
  85 <> 29 <> 37 <> Nil{}

def rev.oid_ocspsign() -> List<&2, U32>:
  43 <> 6 <> 1 <> 5 <> 5 <> 7 <> 3 <> 9 <> Nil{}

# ---- DER encoding ----

# n as k big-endian bytes
def rev.be(+k: Nat, +n: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, U32, rev.be(p, Nat.div(n, 256n)), U32.from_nat(Nat.mod(n, 256n)) <> Nil{})

# the number of bytes of n (at least one), counted by dividing by 256 (fuel bounds the steps)
def rev.nbytes(+fuel: Nat, +n: Nat, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      Bool.pick(Nat, Nat.is_lt(n, 256n), Nat.add(acc, 1n), rev.nbytes(p, Nat.div(n, 256n), Nat.add(acc, 1n)))

# the DER length of n bytes
def rev.der_len.long(+k: Nat, +n: Nat) -> List<&2, U32>:
  U32.from_nat(Nat.add(128n, k)) <> rev.be(k, n)

# a DER element: the tag, the length, the content
def rev.der_len.at(+short: Bool, +n: Nat) -> List<&2, U32>:
  match short:
    case True{}:
      U32.from_nat(n) <> Nil{}
    case False{}:
      rev.der_len.long(rev.nbytes(8n, n, 0n), n)

def rev.der_len(+n: Nat) -> List<&2, U32>:
  rev.der_len.at(Nat.is_lt(n, 128n), n)

def rev.tlv(+tag: U32, +content: List<&2, U32>) -> List<&2, U32>:
  tag <> List.append(&2, U32, rev.der_len(List.length(&2, U32, content)), content)

# ---- reading DER ----

# the content of the first element of xs
def rev.content(+xs: List<&2, U32>) -> List<&2, U32>:
  X.x509.valof(A.asn1.read(xs))

# the element at the front of xs, with its header
def rev.first(+xs: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, xs, A.asn1.total(xs))

# the elements after the first
def rev.rest(+xs: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, xs, A.asn1.total(xs))

# the contents of the elements of xs with the tag want (one level down only)
def rev.kids.one(+hit: Bool, +xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match hit:
    case True{}:
      rev.content(xs) <> Nil{}
    case False{}:
      Nil{}

# the same, over each of several lists
def rev.kids(+fuel: Nat, +xs: List<&2, U32>, +want: U32) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case _:
          List.append(&2, List<&2, U32>, rev.kids.one(U32.is_eq(A.asn1.tag(xs), want), xs),
            rev.kids(p, rev.rest(xs), want))

def rev.kids_all(+xss: List<&2, List<&2, U32>>, +want: U32) -> List<&2, List<&2, U32>>:
  match xss:
    case Nil{}:
      Nil{}
    case +xs <> t:
      List.append(&2, List<&2, U32>, rev.kids(1000000n, xs, want), rev.kids_all(t, want))

# ---- the revocation sources ----

# the value of the extension with oid in c (the DER inside the OCTET STRING), or Nil
def rev.ext(+c: List<&2, U32>, +oid: List<&2, U32>) -> List<&2, U32>:
  X.x509.ext.value(X.x509.exts(c), oid)

# the URIs of the CRL distribution points: distributionPoint [0] (160), fullName [0] (160),
# and the GeneralName URIs [6] (134) of the full name
def rev.cdp.at(+v: List<&2, U32>) -> List<&2, List<&2, U32>>:
  rev.kids_all(rev.kids_all(rev.kids_all(rev.kids(1000000n, rev.content(v), 48), 160), 160), 134)

# the URI of the first OCSP access description (method id-ad-ocsp), or Nil when there is none
def rev.cdp_uris(+c: List<&2, U32>) -> List<&2, List<&2, U32>>:
  rev.cdp.at(rev.ext(c, rev.oid_cdp()))

def rev.access_method(+d: List<&2, U32>) -> List<&2, U32>:
  rev.content(d)

def rev.first_of(+xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> t:
      x

# ---- the OCSP request ----

# the CertID of c (issued by n): SHA-256 of n's subject name and of its key, and c's serial number
def rev.ocsp.first(+xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case +d <> t:
      Bool.pick(List<&2, U32>, R.rsa.eqb(rev.access_method(d), rev.oid_ocsp()),
        rev.first_of(rev.kids(1000000n, d, 134)), rev.ocsp.first(t))

# the OID of an access description (its first element)
def rev.ocsp_uri(+c: List<&2, U32>) -> List<&2, U32>:
  rev.ocsp.first(rev.kids(1000000n, rev.content(rev.ext(c, rev.oid_aia())), 48))

def rev.alg_sha256() -> List<&2, U32>:
  rev.tlv(48, List.append(&2, U32, rev.tlv(6, rev.oid_sha256()), rev.tlv(5, Nil{})))

# the DER of an OCSPRequest for c, issued by n: one request, no signature, no extensions
def rev.certid(+c: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  rev.tlv(48, List.append(&2, U32, rev.alg_sha256(),
    List.append(&2, U32, rev.tlv(4, S.sha256_bytes(CR.crl.subject_raw(n))),
    List.append(&2, U32, rev.tlv(4, S.sha256_bytes(List.drop(&2, U32, X.x509.valof(A.asn1.nth(1n, X.x509.spki(n))), 1n))),
    X.x509.rawof(X.x509.field(X.x509.tbs(c), 0n))))))

def rev.ocsp_request(+c: List<&2, U32>, +n: List<&2, U32>) -> List<&2, U32>:
  rev.tlv(48, rev.tlv(48, rev.tlv(48, rev.tlv(48, rev.certid(c, n)))))

# ---- the OCSP reply ----

# the OCSPResponse's status is successful (0): the ENUMERATED first in its body
def rev.status_ok.at(+st: List<&2, U32>) -> Bool:
  Bool.and(U32.is_eq(A.asn1.tag(st), 10), R.rsa.eqb(rev.content(st), 0 <> Nil{}))

# the DER of the BasicOCSPResponse inside the reply: the responseBytes [0] (160) holds a SEQUENCE
# of the response type (id-pkix-ocsp-basic) and an OCTET STRING, which holds the response
def rev.status_ok(+reply: List<&2, U32>) -> Bool:
  rev.status_ok.at(rev.first(rev.content(reply)))

def rev.basic_of.octet(+seq: List<&2, U32>) -> List<&2, U32>:
  rev.content(rev.rest(seq))
# ---- checking the OCSP reply ----

# the content of the tbsResponseData (the first element of the BasicOCSPResponse)
def rev.basic_of.tagged(+hit: Bool, +rb: List<&2, U32>) -> List<&2, U32>:
  match hit:
    case True{}:
      rev.basic_of.octet(rev.content(rev.content(rb)))
    case False{}:
      Nil{}

def rev.basic_of.at(+rb: List<&2, U32>) -> List<&2, U32>:
  rev.basic_of.tagged(U32.is_eq(A.asn1.tag(rb), 160), rb)

def rev.basic_of(+reply: List<&2, U32>) -> List<&2, U32>:
  rev.basic_of.at(rev.rest(rev.content(reply)))

def rev.tbs_content(+basic: List<&2, U32>) -> List<&2, U32>:
  rev.content(rev.first(rev.content(basic)))

# the contents of the SingleResponse elements of the reply (the responses SEQUENCE OF them)
def rev.singles(+basic: List<&2, U32>) -> List<&2, List<&2, U32>>:
  rev.kids(1000000n, rev.first_of(rev.kids(1000000n, rev.tbs_content(basic), 48)), 48)

# the first certificate of the responses' certs [0] (160), or Nil when there is none
def rev.responder.tagged(+hit: Bool, +e3: List<&2, U32>) -> List<&2, U32>:
  match hit:
    case True{}:
      rev.first(rev.content(rev.content(e3)))
    case False{}:
      Nil{}

# the OCSP-signing purpose is among the extended key usages of d
def rev.responder.at(+e3: List<&2, U32>) -> List<&2, U32>:
  rev.responder.tagged(U32.is_eq(A.asn1.tag(e3), 160), e3)

def rev.responder(+basic: List<&2, U32>) -> List<&2, U32>:
  rev.responder.at(X.x509.skip(3n, rev.content(basic)))

def rev.any_eq(+xs: List<&2, List<&2, U32>>, +oid: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +x <> t:
      Bool.or(R.rsa.eqb(x, oid), rev.any_eq(t, oid))

# a delegated responder d: n issued it, it has the OCSP-signing purpose, and it signed the reply
def rev.ocsp_signing(+d: List<&2, U32>) -> Bool:
  rev.any_eq(rev.kids(1000000n, rev.content(rev.ext(d, rev.oid_eku())), 6), rev.oid_ocspsign())

def rev.delegated.at(+present: Bool, +d: List<&2, U32>, +basic: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  match present:
    case True{}:
      Bool.and(X.x509.sigok(d, n), Bool.and(rev.ocsp_signing(d), X.x509.sigok(basic, d)))
    case False{}:
      False{}

# the reply is signed by n, or by a delegated responder
def rev.delegated(+d: List<&2, U32>, +basic: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  rev.delegated.at(X.x509.nonempty(d), d, basic, n)

def rev.signed_ok(+basic: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  Bool.or(X.x509.sigok(basic, n), rev.delegated(rev.responder(basic), basic, n))

# the single response for c: its status is good, and now is within thisUpdate .. nextUpdate
def rev.next_time.at(+hit: Bool, +e4: List<&2, U32>) -> Nat:
  match hit:
    case True{}:
      X.x509.time(A.asn1.tag(rev.content(e4)), rev.content(rev.content(e4)))
    case False{}:
      4294967295n

# the reply for c (issued by n) is a successful answer that says c is good, now
def rev.next_time(+e4: List<&2, U32>) -> Nat:
  rev.next_time.at(U32.is_eq(A.asn1.tag(e4), 160), e4)

def rev.single.window(+good: Bool, +thisT: Nat, +e4: List<&2, U32>, +now: Nat) -> Bool:
  Bool.and(good, Bool.and(Nat.is_le(thisT, now), Nat.is_le(now, rev.next_time(e4))))

# nextUpdate ([0] (160) EXPLICIT GeneralizedTime) when present; a reply without one is current
def rev.this_time(+this: List<&2, U32>) -> Nat:
  X.x509.time(A.asn1.tag(this), rev.content(this))

def rev.single.at(+s: List<&2, U32>, +now: Nat) -> Bool:
  rev.single.window(U32.is_eq(A.asn1.tag(rev.rest(s)), 128),
    rev.this_time(rev.first(rev.rest(rev.rest(s)))), rev.rest(rev.rest(rev.rest(s))), now)

def rev.single_ok(+singles: List<&2, List<&2, U32>>, +certid: List<&2, U32>, +now: Nat) -> Bool:
  match singles:
    case Nil{}:
      False{}
    case +s <> t:
      Bool.pick(Bool, R.rsa.eqb(rev.first(s), certid), rev.single.at(s, now), rev.single_ok(t, certid, now))

def rev.ocsp.basic(+present: Bool, +basic: List<&2, U32>, +c: List<&2, U32>, +n: List<&2, U32>, +now: Nat) -> Bool:
  match present:
    case True{}:
      Bool.and(rev.signed_ok(basic, n), rev.single_ok(rev.singles(basic), rev.certid(c, n), now))
    case False{}:
      False{}

def rev.ocsp.go(+status: Bool, +basic: List<&2, U32>, +c: List<&2, U32>, +n: List<&2, U32>, +now: Nat) -> Bool:
  match status:
    case True{}:
      rev.ocsp.basic(X.x509.nonempty(basic), basic, c, n, now)
    case False{}:
      False{}

def rev.ocsp_ok(+reply: List<&2, U32>, +c: List<&2, U32>, +n: List<&2, U32>, +now: Nat) -> Bool:
  rev.ocsp.go(rev.status_ok(reply), rev.basic_of(reply), c, n, now)
