# Writes x509_ext_tests.bend: basicConstraints and keyUsage in chains, and wildcard
# DNS names. Each negative chain is wrong in one way only: an intermediate that is
# not a CA, one with no basicConstraints, one whose keyUsage lacks keyCertSign, and
# an anchor that is not a CA. Expected values come from the cryptography package's
# certificates, fixed by how each was built.
#   python3 -I gen_x509_ext_tests.py
import datetime as dt
import time
from cryptography import x509 as cx
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def name(cn):
    return cx.Name([cx.NameAttribute(NameOID.COMMON_NAME, cn)])

def ku(cert_sign):
    return cx.KeyUsage(digital_signature=True, content_commitment=False, key_encipherment=False,
                       data_encipherment=False, key_agreement=False, key_cert_sign=cert_sign,
                       crl_sign=cert_sign, encipher_only=False, decipher_only=False)

def make(subject, key, issuer_name, issuer_key, nb, na, bc=None, usage=None, san=None, eku=None, pathlen=None, nc=None, extra=()):
    """bc: None (no basicConstraints), True (CA) or False (not a CA); usage: None or a
    KeyUsage extension value; san: a list of DNS names or None."""
    b = (cx.CertificateBuilder().subject_name(name(subject)).issuer_name(issuer_name)
         .public_key(key.public_key()).serial_number(cx.random_serial_number())
         .not_valid_before(nb).not_valid_after(na))
    if bc is not None:
        b = b.add_extension(cx.BasicConstraints(ca=bc, path_length=pathlen), critical=True)
    if usage is not None:
        b = b.add_extension(usage, critical=True)
    if san:
        b = b.add_extension(cx.SubjectAlternativeName([cx.DNSName(s) for s in san]), critical=False)
    if eku is not None:
        b = b.add_extension(cx.ExtendedKeyUsage(eku), critical=False)
    if nc is not None:
        permitted, excluded = nc
        b = b.add_extension(cx.NameConstraints(
            permitted_subtrees=[cx.DNSName(s) for s in permitted] if permitted else None,
            excluded_subtrees=[cx.DNSName(s) for s in excluded] if excluded else None), critical=True)
    for e in extra:
        b = b.add_extension(e, critical=True)
    return b.sign(issuer_key, hashes.SHA256())

def der(c):
    return list(c.public_bytes(serialization.Encoding.DER))

now = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
NOW = int(now.timestamp())
day = dt.timedelta(days=1)
ecp = lambda: ec.generate_private_key(ec.SECP256R1())
host = lambda s: lst(list(s.encode()))

out = []
def boolcase(name_, expr, want):
    out.append(f'  kcase("{name_}", Bool.show({expr}), "{want}") <>')

def chain_expr(leaf, inter, root, h="example.test"):
    return f"X.x509.verify_server([{lst(leaf)}, {lst(inter)}], [{lst(root)}], {host(h)}, {NOW}n)"

def build(inter_bc, inter_usage, root_bc=True, leaf_san=("example.test",), leaf_eku=None):
    root_k, inter_k, leaf_k = ecp(), ecp(), ecp()
    root = make("Ext Root", root_k, name("Ext Root"), root_k, now - 30 * day, now + 3650 * day,
                bc=root_bc, usage=ku(True))
    inter = make("Ext Intermediate", inter_k, root.subject, root_k, now - 30 * day, now + 1000 * day,
                 bc=inter_bc, usage=inter_usage)
    leaf = make("example.test", leaf_k, inter.subject, inter_k, now - day, now + 365 * day,
                bc=False, san=list(leaf_san), eku=leaf_eku)
    return der(root), der(inter), der(leaf)

# a certificate entry is exactly one DER element: a byte after it is refused
r, i, l = build(True, ku(True))
boolcase("trailing-byte-refused", chain_expr(l + [0], i, r), "False")

# baseline: CA with keyCertSign
r, i, l = build(True, ku(True))
boolcase("ca-with-keycertsign", chain_expr(l, i, r), "True")
# intermediate: basicConstraints cA = FALSE
r, i, l = build(False, ku(True))
boolcase("intermediate-not-ca", chain_expr(l, i, r), "False")
# intermediate: no basicConstraints
r, i, l = build(None, ku(True))
boolcase("intermediate-no-basic-constraints", chain_expr(l, i, r), "False")
# intermediate: keyUsage without keyCertSign
r, i, l = build(True, ku(False))
boolcase("intermediate-keyusage-no-certsign", chain_expr(l, i, r), "False")
# intermediate: no keyUsage at all (allowed)
r, i, l = build(True, None)
boolcase("intermediate-no-keyusage", chain_expr(l, i, r), "True")
# anchor: not a CA
r, i, l = build(True, ku(True), root_bc=False)
boolcase("anchor-not-ca", chain_expr(l, i, r), "False")

# extended key usage on the leaf: serverAuth, anyExtendedKeyUsage, several purposes,
# and clientAuth alone (which does not authenticate a server)
from cryptography.x509.oid import ExtendedKeyUsageOID as EKU
for label, eku, want in [
    ("eku-server-auth", [EKU.SERVER_AUTH], "True"),
    ("eku-any", [EKU.ANY_EXTENDED_KEY_USAGE], "True"),
    ("eku-several", [EKU.CLIENT_AUTH, EKU.SERVER_AUTH], "True"),
    ("eku-client-auth-only", [EKU.CLIENT_AUTH], "False"),
]:
    r, i, l = build(True, ku(True), leaf_eku=eku)
    boolcase(label, chain_expr(l, i, r), want)

# path length: a CA with pathLenConstraint 0 may not have a CA below it (in the chain
# root -> i1 -> i2 -> leaf, i1 has i2 below it); 1 allows it; 0 with the leaf directly below is fine
def path_chain(i1_len, with_i2):
    root_k, i1_k, i2_k, leaf_k = ecp(), ecp(), ecp(), ecp()
    root = make("Path Root", root_k, name("Path Root"), root_k, now - 30 * day, now + 3650 * day,
                bc=True, usage=ku(True))
    i1 = make("Path I1", i1_k, root.subject, root_k, now - 30 * day, now + 1000 * day,
              bc=True, usage=ku(True), pathlen=i1_len)
    issuer, issuer_k = i1, i1_k
    below = []
    if with_i2:
        i2 = make("Path I2", i2_k, i1.subject, i1_k, now - 30 * day, now + 1000 * day,
                  bc=True, usage=ku(True))
        issuer, issuer_k = i2, i2_k
        below = [der(i2)]
    leaf = make("example.test", leaf_k, issuer.subject, issuer_k, now - day, now + 365 * day,
                bc=False, san=["example.test"])
    # the chain runs from the leaf up: leaf, the intermediates below i1 (nearest first), i1
    leaf_chain = [der(leaf)] + below + [der(i1)]
    return leaf_chain, [der(root)]

for label, i1_len, with_i2, want in [
    ("pathlen-0-with-ca-below", 0, True, "False"),
    ("pathlen-1-with-ca-below", 1, True, "True"),
    ("pathlen-0-leaf-below", 0, False, "True"),
]:
    leaf_chain, anchors = path_chain(i1_len, with_i2)
    chain_text = ", ".join(lst(c) for c in leaf_chain)
    boolcase(label, f"X.x509.verify_server([{chain_text}], [{lst(anchors[0])}], {host('example.test')}, {NOW}n)", want)

# wildcard names: *.example.test matches one label only
r, i, l = build(True, ku(True), leaf_san=("*.example.test",))
boolcase("wild-one-label", chain_expr(l, i, r, "www.example.test"), "True")
boolcase("wild-case-insensitive", chain_expr(l, i, r, "WWW.Example.TEST"), "True")
boolcase("wild-two-labels", chain_expr(l, i, r, "a.b.example.test"), "False")
boolcase("wild-bare-suffix", chain_expr(l, i, r, "example.test"), "False")
boolcase("wild-other-suffix", chain_expr(l, i, r, "www.example.org"), "False")
boolcase("wild-empty-label", chain_expr(l, i, r, ".example.test"), "False")
boolcase("wild-names-host-direct",
         f"X.x509.names_host({host('mail.example.test')}, [{host('*.example.test')}])", "True")
boolcase("wild-names-host-not-leftmost",
         f"X.x509.names_host({host('www.a.example.test')}, [{host('a.*.example.test')}])", "False")
boolcase("exact-still-matches", f"X.x509.names_host({host('example.test')}, [{host('example.test')}])", "True")


# anchor path length and name constraints. The chain is root (the anchor) -> i1 -> leaf, or
# root -> leaf; a chain may also end with the anchor itself.
def nc_chain(root_pathlen=None, root_nc=None, i1_nc=None, i1_san=None, leaf_san=("example.test",), leaf_under_i1=True):
    root_k, i1_k, leaf_k = ecp(), ecp(), ecp()
    root = make("NC Root", root_k, name("NC Root"), root_k, now - 30 * day, now + 3650 * day,
                bc=True, usage=ku(True), pathlen=root_pathlen, nc=root_nc)
    i1 = make("NC I1", i1_k, root.subject, root_k, now - 30 * day, now + 1000 * day,
              bc=True, usage=ku(True), san=i1_san, nc=i1_nc)
    issuer, issuer_k = (i1, i1_k) if leaf_under_i1 else (root, root_k)
    leaf = make("example.test", leaf_k, issuer.subject, issuer_k, now - day, now + 365 * day,
                bc=False, san=list(leaf_san))
    return der(leaf), der(i1), der(root)

def vs(chain, anchors, h="example.test"):
    return f"X.x509.verify_server([{', '.join(lst(c) for c in chain)}], [{', '.join(lst(a) for a in anchors)}], {host(h)}, {NOW}n)"

# the anchor's pathLenConstraint counts the CA certificates between the leaf and the anchor
l, i, r = nc_chain(root_pathlen=0)
boolcase("anchor-pathlen-0-ca-below", vs([l, i], [r]), "False")
l, i, r = nc_chain(root_pathlen=1)
boolcase("anchor-pathlen-1-ca-below", vs([l, i], [r]), "True")
l, i, r = nc_chain(root_pathlen=0, leaf_under_i1=False)
boolcase("anchor-pathlen-0-leaf-below", vs([l], [r]), "True")
l, i, r = nc_chain(root_pathlen=0)
boolcase("anchor-in-chain-pathlen-0", vs([l, i, r], [r]), "False")
l, i, r = nc_chain(root_pathlen=1)
boolcase("anchor-in-chain-pathlen-1", vs([l, i, r], [r]), "True")
l, i, r = nc_chain(root_pathlen=0, leaf_under_i1=False)
boolcase("anchor-in-chain-leaf-pathlen-0", vs([l, r], [r]), "True")

# name constraints (DNS): permitted subtrees, excluded subtrees, leading dots, and the anchor's
l, i, r = nc_chain(i1_nc=(["example.test"], None), leaf_san=("www.example.test",))
boolcase("nc-permitted-subdomain", vs([l, i], [r], "www.example.test"), "True")
l, i, r = nc_chain(i1_nc=(["example.test"], None))
boolcase("nc-permitted-exact", vs([l, i], [r]), "True")
l, i, r = nc_chain(i1_nc=(["example.test"], None), leaf_san=("example.org",))
boolcase("nc-permitted-other-domain", vs([l, i], [r], "example.org"), "False")
l, i, r = nc_chain(i1_nc=(["example.test"], None), leaf_san=("notexample.test",))
boolcase("nc-permitted-not-a-label-suffix", vs([l, i], [r], "notexample.test"), "False")
l, i, r = nc_chain(i1_nc=(None, ["example.test"]))
boolcase("nc-excluded-match", vs([l, i], [r]), "False")
l, i, r = nc_chain(i1_nc=(None, ["evil.test"]))
boolcase("nc-excluded-other", vs([l, i], [r]), "True")
l, i, r = nc_chain(i1_nc=([".example.test"], None))
boolcase("nc-leading-dot-excludes-exact", vs([l, i], [r]), "False")
l, i, r = nc_chain(i1_nc=([".example.test"], None), leaf_san=("www.example.test",))
boolcase("nc-leading-dot-subdomain", vs([l, i], [r], "www.example.test"), "True")
l, i, r = nc_chain(root_nc=(["example.test"], None), leaf_san=("example.org",))
boolcase("nc-anchor-permitted-other", vs([l, i], [r], "example.org"), "False")
l, i, r = nc_chain(root_nc=(["example.test"], None))
boolcase("nc-anchor-identity-names-below", vs([l, i, r], [r]), "True")
l, i, r = nc_chain(root_nc=(["example.test"], None), i1_san=("other.example.org",))
boolcase("nc-anchor-checks-intermediate-san", vs([l, i], [r]), "False")
l, i, r = nc_chain(root_nc=(["example.test"], None), i1_san=("sub.example.test",))
boolcase("nc-anchor-intermediate-san-permitted", vs([l, i], [r]), "True")


# name constraints in DER, with the subtree fields the profile forbids (RFC 5280 4.2.1.10: the
# minimum must be zero and omitted, and no maximum): each is refused, the plain subtree accepted
def der_len(n):
    if n < 128:
        return bytes([n])
    body = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([0x80 | len(body)]) + body

def tlv(tag, content):
    return bytes([tag]) + der_len(len(content)) + content

def nc_der(min_=None, max_=None, explicit_zero_min=False):
    extra = b""
    if min_ is not None:
        extra += tlv(0x80, min_.to_bytes(1, "big"))
    elif explicit_zero_min:
        extra += tlv(0x80, b"\x00")
    if max_ is not None:
        extra += tlv(0x81, max_.to_bytes(1, "big"))
    subtree = tlv(0x30, tlv(0x82, b"example.test") + extra)
    return tlv(0x30, tlv(0xa0, subtree))

def nc_ext(value):
    return cx.UnrecognizedExtension(cx.ObjectIdentifier("2.5.29.30"), value)

def nc_chain(value):
    root_k, i_k, l_k = ecp(), ecp(), ecp()
    root = make("NC Root", root_k, name("NC Root"), root_k, now - 30 * day, now + 3650 * day,
                bc=True, usage=ku(True))
    inter = make("NC Inter", i_k, root.subject, root_k, now - 30 * day, now + 1000 * day,
                 bc=True, usage=ku(True), extra=(nc_ext(value),))
    leaf = make("example.test", l_k, inter.subject, i_k, now - day, now + 365 * day,
                bc=False, san=["example.test"])
    return der(leaf), der(inter), der(root)

for label, value, want in [
    ("nc-raw-plain-accepted", nc_der(), "True"),
    ("nc-minimum-1-refused", nc_der(min_=1), "False"),
    ("nc-maximum-5-refused", nc_der(max_=5), "False"),
    ("nc-explicit-zero-minimum-refused", nc_der(explicit_zero_min=True), "False"),
]:
    l, i, r = nc_chain(value)
    boolcase(label, chain_expr(l, i, r), want)

src = r'''# x509_ext_tests.bend: basicConstraints, keyUsage and wildcard DNS names (generated by
# gen_x509_ext_tests.py; expected values from the cryptography package).
#   bend x509_ext_tests.bend

import Base
import ./x509.bend as X

type Case is Data:
  Case{name: String, got: String, want: String}

def kcase(name: String, +got: String, want: String) -> Case:
  Case{name, got, want}

def cases() -> List<&2, Case>:
''' + "\n".join(out) + r'''
  Nil{}

def fails.at(+c: Case, +rest: List<&2, String>) -> List<&2, String>:
  match c:
    case Case{n, +g, +w}:
      Bool.pick(List<&2, String>, String.eq(g, w), rest,
        ("FAIL " ++ n ++ "\n  got:  " ++ g ++ "\n  want: " ++ w) <> rest)

def fails(cs: List<&2, Case>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      fails.at(c, fails(t))

def main() -> IO(Unit):
  +cs = cases()
  +n = List.length(&2, Case, cs)
  +fs = fails(cs)
  +f = List.length(&2, String, fs)
  do IO<Unit>:
    List.for_each(~&2, ~String, ~IO.print, fs)
    IO.print("x509-ext: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("x509_ext_tests.bend", "w").write(src)
print(len(out), "cases")
