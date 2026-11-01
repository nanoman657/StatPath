# crl.bend: certificate revocation lists (RFC 5280 section 5), checked along a chain.
#
# A CRL is a certificate-shaped structure: an outer SEQUENCE of the TBSCertList, the signature
# algorithm and the signature. crl.chain.ok checks, for each certificate of a chain, the CRL of
# its issuer (the next certificate, or the anchor for the last one): the CRL must be signed by
# that issuer and be current (thisUpdate <= now, and now <= nextUpdate when present), and the
# certificate's serial number must not be on it. A CRL issued for another name is not about the
# certificate and says nothing about it; so does an anchor that is the certificate itself.

import Base
import ./asn1.bend as A
import ./rsa.bend as R
import ./x509.bend as X

# TBSCertList fields are counted from the first one, after an optional version (an INTEGER)
def crl.off.at(ok: Bool) -> Nat:
  match ok:
    case True{}:
      1n
    case False{}:
      0n

def crl.off(+tbs: List<&2, U32>) -> Nat:
  crl.off.at(U32.is_eq(A.asn1.tag(tbs), 2))

# the elements of the TBSCertList from field i on: 0 signature, 1 issuer, 2 thisUpdate,
# 3 nextUpdate (when present) or the revoked list, then the revoked list and crlExtensions
def crl.from(+tbs: List<&2, U32>, i: Nat) -> List<&2, U32>:
  X.x509.skip(Nat.add(crl.off(tbs), i), tbs)

# a Time element (UTCTime 23 or GeneralizedTime 24)
def crl.is_time(+tag: U32) -> Bool:
  Bool.or(U32.is_eq(tag, 23), U32.is_eq(tag, 24))

# the issuer Name of the CRL, as encoded (the raw element)
def crl.issuer_raw(+tbs: List<&2, U32>) -> List<&2, U32>:
  X.x509.rawof(A.asn1.nth(0n, crl.from(tbs, 1n)))

# the subject Name of a certificate, as encoded
def crl.subject_raw(+der: List<&2, U32>) -> List<&2, U32>:
  X.x509.rawof(X.x509.field(X.x509.tbs(der), 4n))

# thisUpdate, as a number of seconds
def crl.this_time(+tbs: List<&2, U32>) -> Nat:
  X.x509.time(A.asn1.tag(crl.from(tbs, 2n)), X.x509.valof(A.asn1.read(crl.from(tbs, 2n))))

# nextUpdate, as a number of seconds: a CRL without one is current until the end of time
def crl.next_time.at(has: Bool, +tbs: List<&2, U32>) -> Nat:
  match has:
    case True{}:
      X.x509.time(A.asn1.tag(crl.from(tbs, 3n)), X.x509.valof(A.asn1.read(crl.from(tbs, 3n))))
    case False{}:
      4294967295n

def crl.next_time(+tbs: List<&2, U32>) -> Nat:
  crl.next_time.at(crl.is_time(A.asn1.tag(crl.from(tbs, 3n))), tbs)

# the revokedCertificates list (the content of its SEQUENCE), or Nil when there is none
def crl.revoked.seq.at(is_seq: Bool, +e: List<&2, U32>) -> List<&2, U32>:
  match is_seq:
    case True{}:
      X.x509.valof(A.asn1.read(e))
    case False{}:
      Nil{}

def crl.revoked.seq(+e: List<&2, U32>) -> List<&2, U32>:
  crl.revoked.seq.at(U32.is_eq(A.asn1.tag(e), 48), e)

def crl.revoked.at(has_next: Bool, +tbs: List<&2, U32>) -> List<&2, U32>:
  match has_next:
    case True{}:
      crl.revoked.seq(crl.from(tbs, 4n))
    case False{}:
      crl.revoked.seq(crl.from(tbs, 3n))

def crl.revoked(+tbs: List<&2, U32>) -> List<&2, U32>:
  crl.revoked.at(crl.is_time(A.asn1.tag(crl.from(tbs, 3n))), tbs)

# the serial number (the INTEGER's content) of a revoked-certificate entry
def crl.entry.serial(+e: List<&2, U32>) -> List<&2, U32>:
  X.x509.valof(A.asn1.nth(0n, X.x509.valof(A.asn1.read(e))))

# is serial the number of one of the entries xs (fuel bounds the walk by the list length)
def crl.has(fuel: Nat, +xs: List<&2, U32>, +serial: List<&2, U32>) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+p:
      match xs:
        case Nil{}:
          False{}
        case _:
          Bool.or(R.rsa.eqb(crl.entry.serial(xs), serial),
            crl.has(p, List.drop(&2, U32, xs, A.asn1.total(xs)), serial))

# the CRL is current at now: thisUpdate <= now <= nextUpdate
def crl.current(+tbs: List<&2, U32>, +now: Nat) -> Bool:
  Bool.and(Nat.is_le(crl.this_time(tbs), now), Nat.is_le(now, crl.next_time(tbs)))

# the CRL is for the issuer n: its issuer name is n's subject
def crl.for_issuer(+crl: List<&2, U32>, +n: List<&2, U32>) -> Bool:
  R.rsa.eqb(crl.issuer_raw(X.x509.tbs(crl)), crl.subject_raw(n))

# the verdict of a CRL for a certificate c issued by n, when the CRL is for n: signed by n,
# current, and c's serial number is not on it
def crl.verdict(+crl: List<&2, U32>, +n: List<&2, U32>, +c: List<&2, U32>, +now: Nat) -> Bool:
  Bool.and(X.x509.sigok(crl, n), Bool.and(crl.current(X.x509.tbs(crl), now),
    Bool.pick(Bool, crl.has(1000000n, crl.revoked(X.x509.tbs(crl)), X.x509.valof(X.x509.field(X.x509.tbs(c), 0n))),
      False{}, True{})))

# a certificate c issued by n is not revoked by a CRL that is for n (a CRL for another name says nothing)
def crl.ok.at(for_n: Bool, +crl: List<&2, U32>, +n: List<&2, U32>, +c: List<&2, U32>, +now: Nat) -> Bool:
  match for_n:
    case True{}:
      crl.verdict(crl, n, c, now)
    case False{}:
      True{}

# every certificate of the chain (leaf first) is not revoked by the CRL of its issuer: the next
# certificate, or the anchor for the last one (which is not checked when it is the anchor itself)
def crl.ok(+crl: List<&2, U32>, +n: List<&2, U32>, +c: List<&2, U32>, +now: Nat) -> Bool:
  crl.ok.at(crl.for_issuer(crl, n), crl, n, c, now)

def crl.chain.go(chain: List<&2, List<&2, U32>>, +anchor: List<&2, U32>, +crl: List<&2, U32>, +now: Nat) -> Bool:
  match chain:
    case Nil{}:
      True{}
    case +c <> rest:
      match rest:
        case Nil{}:
          Bool.pick(Bool, R.rsa.eqb(c, anchor), True{}, crl.ok(crl, anchor, c, now))
        case +n <> more:
          Bool.and(crl.ok(crl, n, c, now), crl.chain.go(rest, anchor, crl, now))

# the revocation check of a chain against crl (DER); an empty crl checks nothing
def crl.chain.at(present: Bool, chain: List<&2, List<&2, U32>>, +anchor: List<&2, U32>, +crl: List<&2, U32>, +now: Nat) -> Bool:
  match present:
    case True{}:
      crl.chain.go(chain, anchor, crl, now)
    case False{}:
      True{}

def crl.chain.ok(chain: List<&2, List<&2, U32>>, +anchor: List<&2, U32>, +crl: List<&2, U32>, +now: Nat) -> Bool:
  crl.chain.at(X.x509.nonempty(crl), chain, anchor, crl, now)
