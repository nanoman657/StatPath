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

def make(subject, key, issuer_name, issuer_key, nb, na, bc=None, usage=None, san=None, eku=None, pathlen=None):
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
