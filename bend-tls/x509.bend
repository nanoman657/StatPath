# x509.bend: X.509 certificates (RFC 5280) as far as TLS server authentication
# needs: the fields, the RSA public key, the validity period, the subject
# alternative DNS names, and the signature chain up to a trust anchor. Only RSA
# keys with e = 65537 and RSASSA-PKCS1-v1_5 / RSASSA-PSS signatures are handled.
# basicConstraints and key usage are not checked: a chain's intermediates are
# trusted to be CAs. See README.md.

import Base
import ./asn1.bend as A
import ./rsa.bend as R
import ./sha256.bend as S
import ./p256.bend as P
import ./ed25519.bend as ED

# Accessors
# ---------

def x509.valof(+t: A.TLV) -> List<&2, U32>:
  match t:
    case A.TLV{tag, val, raw, rest}:
      val

def x509.rawof(+t: A.TLV) -> List<&2, U32>:
  match t:
    case A.TLV{tag, val, raw, rest}:
      raw

# the content of the outer SEQUENCE of a certificate
def x509.body(+der: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.read(der))

# the signed bytes, exactly as encoded: the TBSCertificate element
def x509.tbs_raw(+der: List<&2, U32>) -> List<&2, U32>:
  x509.rawof(A.asn1.nth(0n, x509.body(der)))

# the signature bytes (the BIT STRING without its unused-bits byte)
def x509.signature(+der: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, x509.valof(A.asn1.nth(2n, x509.body(der))), 1n)

# the signature algorithm OID content
def x509.sigalg_oid(+der: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.nth(1n, x509.body(der)))))

# the TBS content: the elements of TBSCertificate
def x509.tbs(+der: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.nth(0n, x509.body(der)))

# the number of elements to skip before the fields: the optional version [0]
def x509.off.at(ok: Bool) -> Nat:
  match ok:
    case True{}:
      1n
    case False{}:
      0n

# field i of the TBS content, counted from the serial number (0)
def x509.off(+tbs: List<&2, U32>) -> Nat:
  x509.off.at(U32.is_eq(A.asn1.tag(tbs), 160))

def x509.field(+tbs: List<&2, U32>, i: Nat) -> A.TLV:
  A.asn1.nth(Nat.add(x509.off(tbs), i), tbs)

# the subjectPublicKeyInfo content
def x509.spki(+der: List<&2, U32>) -> List<&2, U32>:
  x509.valof(x509.field(x509.tbs(der), 5n))

# the RSA modulus (without a leading zero byte) and exponent, from the SPKI
def x509.strip0.at(+xs: List<&2, U32>, z: Bool) -> List<&2, U32>:
  match z:
    case True{}:
      List.drop(&2, U32, xs, 1n)
    case False{}:
      xs

# Validity
# --------

# the decimal digits of bs from position i for n digits, as a Nat
def x509.strip0(+xs: List<&2, U32>) -> List<&2, U32>:
  x509.strip0.at(xs, U32.is_eq(A.asn1.tag(xs), 0))

def x509.rsa_key.pair.fin(+rk: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  (x509.strip0(x509.valof(A.asn1.nth(0n, rk))), x509.valof(A.asn1.nth(1n, rk)))

# a leading zero byte (the sign byte of an INTEGER) removed
def x509.rsa_key.pair(+seq: A.TLV) -> List<&2, U32> & List<&2, U32>:
  x509.rsa_key.pair.fin(x509.valof(seq))

def x509.rsa_key.at(+bitstr: A.TLV) -> List<&2, U32> & List<&2, U32>:
  x509.rsa_key.pair(A.asn1.nth(0n, x509.valof(A.asn1.read(List.drop(&2, U32, x509.valof(bitstr), 1n)))))

def x509.rsa_key(+spki: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  x509.rsa_key.at(A.asn1.nth(1n, spki))

def x509.digits.fold(+bs: List<&2, U32>, acc: Nat) -> Nat:
  match bs:
    case Nil{}:
      acc
    case d <> t:
      x509.digits.fold(t, Nat.add(Nat.mul(acc, 10n), Nat.sub(U32.to_nat(d), 48n)))

# 1 when m is January or February (the year then counts from the March before)
def x509.digits(+bs: List<&2, U32>, i: Nat, n: Nat) -> Nat:
  x509.digits.fold(List.take(&2, U32, List.drop(&2, U32, bs, i), n), 0n)

def x509.le2.at(ok: Bool) -> Nat:
  match ok:
    case True{}:
      1n
    case False{}:
      0n

# days from the proleptic Gregorian epoch of year 0 to y-m-d (Howard Hinnant's
# days_from_civil, with the constant 719468 left out so the value stays a Nat)
def x509.le2(+m: Nat) -> Nat:
  x509.le2.at(Nat.is_le(m, 2n))

def x509.days.doe(+era: Nat, +yoe: Nat, doy: Nat) -> Nat:
  Nat.add(Nat.mul(era, 146097n), Nat.sub(Nat.add(Nat.add(Nat.mul(yoe, 365n), Nat.div(yoe, 4n)), doy),
    Nat.div(yoe, 100n)))

# seconds since the same epoch for y-m-d h:mi:s
def x509.days.at(+m: Nat, +d: Nat, +yy: Nat) -> Nat:
  x509.days.doe(Nat.div(yy, 400n), Nat.mod(yy, 400n), Nat.add(Nat.div(Nat.add(Nat.mul(153n,
    Nat.mod(Nat.add(m, 9n), 12n)), 2n), 5n), Nat.sub(d, 1n)))

def x509.days(+y: Nat, +m: Nat, +d: Nat) -> Nat:
  x509.days.at(m, d, Nat.sub(y, x509.le2(m)))

def x509.secs(+y: Nat, +m: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> Nat:
  Nat.add(Nat.mul(x509.days(y, m, d), 86400n), Nat.add(Nat.mul(h, 3600n), Nat.add(Nat.mul(mi, 60n), s)))

# the offset of the Unix epoch in those seconds (719468 days)
def x509.unix_offset() -> Nat:
  Nat.mul(719468n, 86400n)

# the Unix time (seconds) of a UTCTime or GeneralizedTime value
def x509.time.fields.at(+y: Nat, +m: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> Nat:
  Nat.sub(x509.secs(y, m, d, h, mi, s), x509.unix_offset())

# valid at time now (Unix seconds): notBefore <= now <= notAfter
def x509.time.fields(+utc: Bool, +bs: List<&2, U32>, +y: Nat) -> Nat:
  x509.time.fields.at(y, x509.digits(bs, Bool.pick(Nat, utc, 2n, 4n), 2n),
    x509.digits(bs, Bool.pick(Nat, utc, 4n, 6n), 2n), x509.digits(bs, Bool.pick(Nat, utc, 6n, 8n), 2n),
    x509.digits(bs, Bool.pick(Nat, utc, 8n, 10n), 2n), x509.digits(bs, Bool.pick(Nat, utc, 10n, 12n), 2n))

def x509.time.year2.at(utc: Bool, +y2: Nat, +y4: Nat) -> Nat:
  match utc:
    case True{}:
      Bool.pick(Nat, Nat.is_ge(y2, 50n), Nat.add(1900n, y2), Nat.add(2000n, y2))
    case False{}:
      y4

def x509.time.year2(+utc: Bool, +bs: List<&2, U32>) -> Nat:
  x509.time.year2.at(utc, x509.digits(bs, 0n, 2n), x509.digits(bs, 0n, 4n))

def x509.time.year(+utc: Bool, +bs: List<&2, U32>) -> Nat:
  x509.time.fields(utc, bs, x509.time.year2(utc, bs))

def x509.time.at(+utc: Bool, +bs: List<&2, U32>) -> Nat:
  x509.time.year(utc, bs)

# the year: UTCTime has two digits (50..99 are 19xx, 00..49 are 20xx)
def x509.time(tag: U32, +bs: List<&2, U32>) -> Nat:
  x509.time.at(U32.is_eq(tag, 23), bs)

def x509.valid_at(+now: Nat, +nb: Nat, +na: Nat) -> Bool:
  Bool.and(Nat.is_le(nb, now), Nat.is_le(now, na))


# Subject alternative names
# -------------------------

# the first n elements of bs are skipped
def x509.skip(k: Nat, +bs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      bs
    case 1n+p:
      x509.skip(p, List.drop(&2, U32, bs, A.asn1.total(bs)))

# the content of the first [3] (extensions) element of the TBS content; ok says
# whether bs starts with it
def x509.ext.find(fuel: Nat, +bs: List<&2, U32>, ok: Bool) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match ok:
        case True{}:
          x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.read(bs))))
        case False{}:
          x509.ext.find(p, List.drop(&2, U32, bs, A.asn1.total(bs)),
            U32.is_eq(A.asn1.tag(List.drop(&2, U32, bs, A.asn1.total(bs))), 163))

# the extension list of a certificate (the SEQUENCE OF Extension content)
def x509.exts(+der: List<&2, U32>) -> List<&2, U32>:
  x509.ext.find(1000000n, x509.tbs(der), False{})

# the OCTET STRING content of an extension element (its last element)
def x509.octet.find(fuel: Nat, +bs: List<&2, U32>, ok: Bool) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match ok:
        case True{}:
          x509.valof(A.asn1.read(bs))
        case False{}:
          x509.octet.find(p, List.drop(&2, U32, bs, A.asn1.total(bs)),
            U32.is_eq(A.asn1.tag(List.drop(&2, U32, bs, A.asn1.total(bs))), 4))

# the extension with OID oid among exts (the extension list content): is it the first one
def x509.ext.is(+exts: List<&2, U32>, +oid: List<&2, U32>) -> Bool:
  match exts:
    case Nil{}:
      False{}
    case _:
      R.rsa.eqb(x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.read(exts)))), oid)

# the content of the extnValue OCTET STRING of the extension with OID oid, or Nil
def x509.nonempty(+xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case _:
      True{}

# the bytes before the first '.' (46), and the bytes after it (the '.' itself dropped)
def x509.ext.by(fuel: Nat, +exts: List<&2, U32>, +oid: List<&2, U32>, ok: Bool, more: Bool) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match ok:
        case True{}:
          x509.octet.find(1000000n, x509.valof(A.asn1.read(exts)), False{})
        case False{}:
          match more:
            case True{}:
              x509.ext.by(p, List.drop(&2, U32, exts, A.asn1.total(exts)), oid,
                x509.ext.is(List.drop(&2, U32, exts, A.asn1.total(exts)), oid),
                x509.nonempty(List.drop(&2, U32, exts, A.asn1.total(exts))))
            case False{}:
              Nil{}

# basicConstraints (2.5.29.19) and keyUsage (2.5.29.15)
def x509.ext.value(+exts: List<&2, U32>, +oid: List<&2, U32>) -> List<&2, U32>:
  x509.ext.by(1000000n, exts, oid, x509.ext.is(exts, oid), x509.nonempty(exts))

# more says whether exts has an element (the caller checks, so exts is not matched here)
def x509.oid_bc() -> List<&2, U32>:
  85 <> 29 <> 19 <> Nil{}

def x509.oid_ku() -> List<&2, U32>:
  85 <> 29 <> 15 <> Nil{}

# cA is TRUE: basicConstraints is a SEQUENCE whose first element is a BOOLEAN TRUE
# (a missing extension, or a missing cA, means not a CA)
def x509.true_at(boolean: Bool, +seq: List<&2, U32>) -> Bool:
  match boolean:
    case True{}:
      R.rsa.eqb(x509.valof(A.asn1.read(seq)), 255 <> Nil{})
    case False{}:
      False{}

# keyUsage, when present, must include keyCertSign (the bit 0x04 of the first flag byte)
def x509.is_ca.seq(+seq: List<&2, U32>) -> Bool:
  match seq:
    case Nil{}:
      False{}
    case _:
      x509.true_at(U32.is_eq(A.asn1.tag(seq), 1), seq)

def x509.is_ca.at(+bc: List<&2, U32>) -> Bool:
  match bc:
    case Nil{}:
      False{}
    case _:
      x509.is_ca.seq(x509.valof(A.asn1.read(bc)))

def x509.is_ca(+der: List<&2, U32>) -> Bool:
  x509.is_ca.at(x509.ext.value(x509.exts(der), x509.oid_bc()))

def x509.head(+xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> t:
      x

# a CA may issue certificates: basicConstraints cA, and keyCertSign if keyUsage is present
def x509.ku_ok.bits(+bits: List<&2, U32>) -> Bool:
  U32.is_eq(U32.and(x509.head(List.drop(&2, U32, bits, 1n)), 4), 4)

def x509.ku_ok.at(+ku: List<&2, U32>) -> Bool:
  match ku:
    case Nil{}:
      True{}
    case _:
      x509.ku_ok.bits(x509.valof(A.asn1.read(ku)))

def x509.ku_ok(+der: List<&2, U32>) -> Bool:
  x509.ku_ok.at(x509.ext.value(x509.exts(der), x509.oid_ku()))

def x509.issuer_ok(+der: List<&2, U32>) -> Bool:
  Bool.and(x509.is_ca(der), x509.ku_ok(der))

# the SAN extension's OID content: 2.5.29.17
def x509.san_oid() -> List<&2, U32>:
  85 <> 29 <> 17 <> Nil{}

# the value of the SAN extension among the extensions exts (or Nil); ok says
# whether the first extension is the SAN one
def x509.san.find(fuel: Nat, +exts: List<&2, U32>, ok: Bool) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match ok:
        case True{}:
          x509.octet.find(1000000n, x509.valof(A.asn1.read(exts)), False{})
        case False{}:
          x509.san.find(p, List.drop(&2, U32, exts, A.asn1.total(exts)),
            R.rsa.eqb(x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.read(List.drop(&2, U32, exts, A.asn1.total(exts)))))),
              x509.san_oid()))

# the dNSName entries (tag 0x82) of a GeneralNames sequence's content
def x509.dns.find(fuel: Nat, +bs: List<&2, U32>, ok: Bool) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match ok:
        case True{}:
          x509.valof(A.asn1.read(bs)) <> x509.dns.find(p, List.drop(&2, U32, bs, A.asn1.total(bs)),
            U32.is_eq(A.asn1.tag(List.drop(&2, U32, bs, A.asn1.total(bs))), 130))
        case False{}:
          x509.dns.find(p, List.drop(&2, U32, bs, A.asn1.total(bs)),
            U32.is_eq(A.asn1.tag(List.drop(&2, U32, bs, A.asn1.total(bs))), 130))

# the DNS names of a certificate (empty when it has no SAN extension): the SAN
# value's content is a GeneralNames SEQUENCE, whose elements are the names
def x509.dns.start(+names: List<&2, U32>) -> List<&2, List<&2, U32>>:
  x509.dns.find(1000000n, names, U32.is_eq(A.asn1.tag(names), 130))

# the ASCII lowercase of a byte: 32 is added to A..Z
def x509.dns_names.at(+san: List<&2, U32>) -> List<&2, List<&2, U32>>:
  x509.dns.start(x509.valof(A.asn1.read(san)))

def x509.dns_names(+der: List<&2, U32>) -> List<&2, List<&2, U32>>:
  x509.dns_names.at(x509.san.find(1000000n, x509.exts(der), R.rsa.eqb(
    x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.read(x509.exts(der))))), x509.san_oid())))

def x509.lowerc(+x: U32) -> U32:
  U32.add(x, U32.mul(Bool.to_u32(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90))), 32))

# ASCII lowercase of a byte list
def x509.lower(+xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      x509.lowerc(x) <> x509.lower(t)

# the certificate names the host (exact match on a DNS name, ASCII case-insensitive)
def x509.split_dot.cons(x: U32, r: List<&2, U32> & List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  (l, rr) = r
  (x <> l, rr)

def x509.split_dot(+bs: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match bs:
    case Nil{}:
      (Nil{}, Nil{})
    case 46 <> t:
      (Nil{}, t)
    case x <> t:
      x509.split_dot.cons(x, x509.split_dot(t))

def x509.wild.check(+label: List<&2, U32>, +hrest: List<&2, U32>, +name: List<&2, U32>) -> Bool:
  Bool.and(x509.nonempty(label), Bool.and(x509.nonempty(hrest), R.rsa.eqb(hrest, List.drop(&2, U32, name, 2n))))

def x509.wild.split(lr: List<&2, U32> & List<&2, U32>, +name: List<&2, U32>) -> Bool:
  (label, hrest) = lr
  x509.wild.check(label, hrest, name)

def x509.wild.at(star: Bool, +name: List<&2, U32>, +host: List<&2, U32>) -> Bool:
  match star:
    case True{}:
      x509.wild.split(x509.split_dot(host), name)
    case False{}:
      False{}

def x509.wild.match(+name: List<&2, U32>, +host: List<&2, U32>) -> Bool:
  x509.wild.at(R.rsa.eqb(List.take(&2, U32, name, 2n), 42 <> 46 <> Nil{}), name, host)

def x509.names_host(+host: List<&2, U32>, +names: List<&2, List<&2, U32>>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case n <> rest:
      Bool.or(R.rsa.eqb(x509.lower(n), x509.lower(host)),
        Bool.or(x509.wild.match(x509.lower(n), x509.lower(host)), x509.names_host(host, rest)))

# a wildcard name *.rest (in the leftmost label only) names a host whose first label is
# not empty and whose remaining labels are rest
def x509.host_ok(+der: List<&2, U32>, +host: List<&2, U32>) -> Bool:
  x509.names_host(host, x509.dns_names(der))

# RSA keys
# --------

# the algorithm OID and the curve OID of a subjectPublicKeyInfo content
def x509.spki_alg_oid(+spki: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.nth(0n, spki))))

def x509.spki_curve(+spki: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.nth(1n, x509.valof(A.asn1.nth(0n, spki))))

def x509.oid_rsa_enc() -> List<&2, U32>:
  42 <> 134 <> 72 <> 134 <> 247 <> 13 <> 1 <> 1 <> 1 <> Nil{}

# the signature algorithm OIDs of sha256WithRSAEncryption and RSASSA-PSS
def x509.is_rsa(+spki: List<&2, U32>) -> Bool:
  R.rsa.eqb(x509.spki_alg_oid(spki), x509.oid_rsa_enc())

# a P-256 key: id-ecPublicKey on prime256v1
def x509.oid_ec_pub() -> List<&2, U32>:
  42 <> 134 <> 72 <> 206 <> 61 <> 2 <> 1 <> Nil{}

def x509.oid_p256() -> List<&2, U32>:
  42 <> 134 <> 72 <> 206 <> 61 <> 3 <> 1 <> 7 <> Nil{}

def x509.is_ec(+spki: List<&2, U32>) -> Bool:
  Bool.and(R.rsa.eqb(x509.spki_alg_oid(spki), x509.oid_ec_pub()),
    R.rsa.eqb(x509.spki_curve(spki), x509.oid_p256()))

# the uncompressed point (04 || X || Y) is the BIT STRING after its unused-bits byte;
# ec_xy is X || Y, 64 bytes
def x509.ec_xy(+spki: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, x509.valof(A.asn1.nth(1n, spki)), 2n)

def x509.ec_qx(+spki: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, x509.ec_xy(spki), 32n)

def x509.ec_qy(+spki: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, x509.ec_xy(spki), 32n)

# Ed25519 (id-Ed25519 1.3.101.112): the key is 32 bytes after the BIT STRING's unused-bits byte
def x509.oid_ed25519() -> List<&2, U32>:
  43 <> 101 <> 112 <> Nil{}

def x509.is_ed(+spki: List<&2, U32>) -> Bool:
  R.rsa.eqb(x509.spki_alg_oid(spki), x509.oid_ed25519())

def x509.ed_pub(+spki: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, x509.valof(A.asn1.nth(1n, spki)), 1n)

# the r and s INTEGERs of an ECDSA signature (a DER SEQUENCE), as 32 bytes each
def x509.zeros(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      0 <> x509.zeros(p)

# the RSAPublicKey content of a subjectPublicKeyInfo content
def x509.pad32.at(ok: Bool, +xs: List<&2, U32>) -> List<&2, U32>:
  match ok:
    case True{}:
      List.append(&2, U32, x509.zeros(Nat.sub(32n, List.length(&2, U32, xs))), xs)
    case False{}:
      x509.zeros(32n)

def x509.pad32(+xs: List<&2, U32>) -> List<&2, U32>:
  x509.pad32.at(Nat.is_le(List.length(&2, U32, xs), 32n), xs)

# an integer longer than 32 bytes is not a P-256 scalar: it becomes 0, which fails
def x509.ecdsa.r(+sig: List<&2, U32>) -> List<&2, U32>:
  x509.pad32(x509.strip0(x509.valof(A.asn1.nth(0n, x509.valof(A.asn1.read(sig))))))

def x509.ecdsa.s(+sig: List<&2, U32>) -> List<&2, U32>:
  x509.pad32(x509.strip0(x509.valof(A.asn1.nth(1n, x509.valof(A.asn1.read(sig))))))

# big-endian bytes left-padded with zeros to 32
def x509.rk(+spki: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.read(List.drop(&2, U32, x509.valof(A.asn1.nth(1n, spki)), 1n)))

# the modulus, as k big-endian bytes (a leading sign byte removed)
def x509.nkey(+spki: List<&2, U32>) -> List<&2, U32>:
  x509.strip0(x509.valof(A.asn1.nth(0n, x509.rk(spki))))

# the exponent bytes; the verifier only accepts 65537
def x509.ekey(+spki: List<&2, U32>) -> List<&2, U32>:
  x509.valof(A.asn1.nth(1n, x509.rk(spki)))

def x509.e65537() -> List<&2, U32>:
  1 <> 0 <> 1 <> Nil{}

# Chains
# ------

# the algorithm OIDs of ECDSA with SHA-256, id-ecPublicKey, prime256v1 and rsaEncryption
def x509.oid_ecdsa() -> List<&2, U32>:
  42 <> 134 <> 72 <> 206 <> 61 <> 4 <> 3 <> 2 <> Nil{}

def x509.oid_pkcs1() -> List<&2, U32>:
  42 <> 134 <> 72 <> 134 <> 247 <> 13 <> 1 <> 1 <> 11 <> Nil{}

def x509.oid_pss() -> List<&2, U32>:
  42 <> 134 <> 72 <> 134 <> 247 <> 13 <> 1 <> 1 <> 10 <> Nil{}

# the signature of cert, checked with the key of issuer (a DER certificate)
def x509.sigok.pick(pkcs1: Bool, pss: Bool, v1: Bool, v2: Bool) -> Bool:
  match pkcs1:
    case True{}:
      v1
    case False{}:
      match pss:
        case True{}:
          v2
        case False{}:
          False{}

# the time element (UTCTime or GeneralizedTime) at position i of the validity
def x509.time_tlv(+der: List<&2, U32>, i: Nat) -> A.TLV:
  A.asn1.nth(i, x509.valof(x509.field(x509.tbs(der), 3n)))

# the Unix time (seconds) of a time element, by its tag
def x509.time_of.at(+t: A.TLV) -> Nat:
  match t:
    case A.TLV{tag, val, raw, rest}:
      x509.time(tag, val)

# notBefore and notAfter, as Unix seconds
def x509.time_of(+t: A.TLV) -> Nat:
  x509.time_of.at(t)

def x509.nb_time(+der: List<&2, U32>) -> Nat:
  x509.time_of(x509.time_tlv(der, 0n))

def x509.na_time(+der: List<&2, U32>) -> Nat:
  x509.time_of(x509.time_tlv(der, 1n))

# the certificate der is valid at now (Unix seconds)
def x509.valid(+der: List<&2, U32>, +now: Nat) -> Bool:
  x509.valid_at(now, x509.nb_time(der), x509.na_time(der))

# the last certificate of a chain is trusted when it is an anchor itself, or when
# an anchor's key signed it (and it is valid at now)
def x509.sigok.run(pkcs1: Bool, pss: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  x509.sigok.pick(pkcs1, pss,
    R.rsa.verify_pkcs1(x509.nkey(x509.spki(issuer)), x509.signature(cert), x509.tbs_raw(cert)),
    R.rsa.verify_pss(x509.nkey(x509.spki(issuer)), x509.signature(cert), x509.tbs_raw(cert)))

def x509.sigok.key(pkcs1: Bool, pss: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>, e: Bool) -> Bool:
  match e:
    case True{}:
      x509.sigok.run(pkcs1, pss, cert, issuer)
    case False{}:
      False{}

def x509.sigok.alg(pkcs1: Bool, pss: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  x509.sigok.key(pkcs1, pss, cert, issuer,
    Bool.and(x509.is_rsa(x509.spki(issuer)), R.rsa.eqb(x509.ekey(x509.spki(issuer)), x509.e65537())))

def x509.sigok.ec.at(ok: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  match ok:
    case True{}:
      P.p256.verify(x509.ec_qx(x509.spki(issuer)), x509.ec_qy(x509.spki(issuer)),
        S.sha256_bytes(x509.tbs_raw(cert)), x509.ecdsa.r(x509.signature(cert)), x509.ecdsa.s(x509.signature(cert)))
    case False{}:
      False{}

def x509.sigok.ec(+cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  x509.sigok.ec.at(x509.is_ec(x509.spki(issuer)), cert, issuer)

def x509.sigok.ed.at(ok: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  match ok:
    case True{}:
      ED.ed.verify(x509.ed_pub(x509.spki(issuer)), x509.tbs_raw(cert), x509.signature(cert))
    case False{}:
      False{}

def x509.sigok.ed(+cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  x509.sigok.ed.at(x509.is_ed(x509.spki(issuer)), cert, issuer)

def x509.sigok.ed.by(ed: Bool, pkcs1: Bool, pss: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  match ed:
    case True{}:
      x509.sigok.ed(cert, issuer)
    case False{}:
      x509.sigok.alg(pkcs1, pss, cert, issuer)

# an Ed25519 certificate: the signature (64 bytes) over the TBS bytes, with the issuer's key
def x509.sigok.by(ecdsa: Bool, pkcs1: Bool, pss: Bool, ed: Bool, +cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  match ecdsa:
    case True{}:
      x509.sigok.ec(cert, issuer)
    case False{}:
      x509.sigok.ed.by(ed, pkcs1, pss, cert, issuer)

def x509.sigok(+cert: List<&2, U32>, +issuer: List<&2, U32>) -> Bool:
  x509.sigok.by(R.rsa.eqb(x509.sigalg_oid(cert), x509.oid_ecdsa()),
    R.rsa.eqb(x509.sigalg_oid(cert), x509.oid_pkcs1()),
    R.rsa.eqb(x509.sigalg_oid(cert), x509.oid_pss()),
    R.rsa.eqb(x509.sigalg_oid(cert), x509.oid_ed25519()), cert, issuer)

# ECDSA certificates are checked by the P-256 verifier, RSA ones by the RSA path
def x509.anchor.match(+c: List<&2, U32>, +a: List<&2, U32>, now: Nat) -> Bool:
  Bool.or(R.rsa.eqb(c, a), Bool.and(x509.valid(c, now), Bool.and(x509.issuer_ok(a), x509.sigok(c, a))))

def x509.anchor.any(+c: List<&2, U32>, anchors: List<&2, List<&2, U32>>, +now: Nat) -> Bool:
  match anchors:
    case Nil{}:
      False{}
    case a <> more:
      Bool.or(x509.anchor.match(c, a, now), x509.anchor.any(c, more, now))

# each certificate is valid at now and signed by the next one; the last is
# trusted through an anchor
def x509.chain.ok(chain: List<&2, List<&2, U32>>, anchors: List<&2, List<&2, U32>>, +now: Nat) -> Bool:
  match chain:
    case Nil{}:
      False{}
    case +c <> rest:
      match rest:
        case Nil{}:
          x509.anchor.any(c, anchors, now)
        case +n <> more:
          Bool.and(x509.valid(c, now), Bool.and(x509.sigok(c, n), Bool.and(x509.issuer_ok(n), x509.chain.ok(rest, anchors, now))))

# the server authentication check: the leaf (first in chain) names host, and the
# chain verifies against the anchors at time now (Unix seconds)
def x509.verify_server.at(chain: List<&2, List<&2, U32>>, anchors: List<&2, List<&2, U32>>,
  +host: List<&2, U32>, now: Nat) -> Bool:
  match chain:
    case Nil{}:
      False{}
    case +leaf <> more:
      Bool.and(x509.host_ok(leaf, host), x509.chain.ok(chain, anchors, now))

def x509.verify_server(chain: List<&2, List<&2, U32>>, anchors: List<&2, List<&2, U32>>,
  +host: List<&2, U32>, now: Nat) -> Bool:
  x509.verify_server.at(chain, anchors, host, now)

# the signature of cert, checked with the key of issuer (a DER certificate);
# only e = 65537 is accepted