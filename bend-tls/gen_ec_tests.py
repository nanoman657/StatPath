# Writes ec_tests.bend: P-256 certificates and the ECDSA CertificateVerify.
# Chains are made with the cryptography package: an all-ECDSA chain, a mixed chain
# (RSA root, ECDSA intermediate, RSA leaf), and tampered, wrong-anchor and
# misused variants that must fail. The CertificateVerify cases sign the TLS 1.3
# server content with an ECDSA key and check hs.cv_ok (alg 0x0403).
#   python3 -I gen_ec_tests.py
import datetime as dt
import time
from cryptography import x509 as cx
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, rsa

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def name(cn):
    return cx.Name([cx.NameAttribute(NameOID.COMMON_NAME, cn)])

def make(subject, key, issuer_name, issuer_key, nb, na, ca=False, san=None):
    b = (cx.CertificateBuilder().subject_name(name(subject)).issuer_name(issuer_name)
         .public_key(key.public_key()).serial_number(cx.random_serial_number())
         .not_valid_before(nb).not_valid_after(na))
    if ca:
        b = b.add_extension(cx.BasicConstraints(ca=True, path_length=None), critical=True)
    if san:
        b = b.add_extension(cx.SubjectAlternativeName([cx.DNSName(s) for s in san]), critical=False)
    return b.sign(issuer_key, hashes.SHA256())

def der(c):
    return list(c.public_bytes(serialization.Encoding.DER))

now = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
NOW = int(now.timestamp())
day = dt.timedelta(days=1)
ecp = lambda: ec.generate_private_key(ec.SECP256R1())
rsa_k = lambda: rsa.generate_private_key(65537, 2048)

out = []
def kc(name_, expr, want):
    out.append(f'  kcase("{name_}", {expr}, "{want}") <>')

def boolcase(name_, expr, want):
    out.append(f'  kcase("{name_}", Bool.show({expr}), "{want}") <>')

host = lambda s: lst(list(s.encode()))

# all-ECDSA chain
ec_root_k, ec_inter_k, ec_leaf_k = ecp(), ecp(), ecp()
ec_root = make("EC Root", ec_root_k, name("EC Root"), ec_root_k, now - 30 * day, now + 3650 * day, ca=True)
ec_inter = make("EC Intermediate", ec_inter_k, ec_root.subject, ec_root_k, now - 30 * day, now + 1000 * day, ca=True)
ec_leaf = make("example.test", ec_leaf_k, ec_inter.subject, ec_inter_k, now - day, now + 365 * day,
               san=["example.test"])
E_ROOT, E_INTER, E_LEAF = der(ec_root), der(ec_inter), der(ec_leaf)
boolcase("ec-chain-valid",
         f"X.x509.verify_server([{lst(E_LEAF)}, {lst(E_INTER)}], [{lst(E_ROOT)}], {host('example.test')}, {NOW}n)",
         "True")
boolcase("ec-chain-wrong-host",
         f"X.x509.verify_server([{lst(E_LEAF)}, {lst(E_INTER)}], [{lst(E_ROOT)}], {host('other.test')}, {NOW}n)",
         "False")
other_root_k = ecp()
other_root = make("Other Root", other_root_k, name("Other Root"), other_root_k, now - 30 * day, now + 3650 * day, ca=True)
boolcase("ec-chain-wrong-anchor",
         f"X.x509.verify_server([{lst(E_LEAF)}, {lst(E_INTER)}], [{lst(der(other_root))}], {host('example.test')}, {NOW}n)",
         "False")
# an intermediate given as the anchor is trusted, as RFC 5280 allows
boolcase("ec-chain-intermediate-anchor",
         f"X.x509.verify_server([{lst(E_LEAF)}, {lst(E_INTER)}], [{lst(E_INTER)}], {host('example.test')}, {NOW}n)",
         "True")
tampered = bytearray(E_LEAF)
tbs_start = 8
tampered[tbs_start + 40] ^= 1
boolcase("ec-chain-tampered-leaf",
         f"X.x509.verify_server([{lst(list(tampered))}, {lst(E_INTER)}], [{lst(E_ROOT)}], {host('example.test')}, {NOW}n)",
         "False")
boolcase("ec-is-ec", f"X.x509.is_ec(X.x509.spki({lst(E_LEAF)}))", "True")
boolcase("ec-is-not-rsa", f"X.x509.is_rsa(X.x509.spki({lst(E_LEAF)}))", "False")
ecpub = ec_leaf_k.public_key().public_numbers()
kc("ec-qx", f"S.hex_of(X.x509.ec_qx(X.x509.spki({lst(E_LEAF)})))", ecpub.x.to_bytes(32, "big").hex())
kc("ec-qy", f"S.hex_of(X.x509.ec_qy(X.x509.spki({lst(E_LEAF)})))", ecpub.y.to_bytes(32, "big").hex())

# mixed: RSA root, ECDSA intermediate, RSA leaf
m_root_k, m_leaf_k = rsa_k(), rsa_k()
m_root = make("Mixed Root", m_root_k, name("Mixed Root"), m_root_k, now - 30 * day, now + 3650 * day, ca=True)
m_inter = make("Mixed Intermediate", ec_inter_k, m_root.subject, m_root_k, now - 30 * day, now + 1000 * day, ca=True)
m_leaf = make("example.test", m_leaf_k, m_inter.subject, ec_inter_k, now - day, now + 365 * day,
              san=["example.test"])
M_ROOT, M_INTER, M_LEAF = der(m_root), der(m_inter), der(m_leaf)
boolcase("mixed-chain-valid",
         f"X.x509.verify_server([{lst(M_LEAF)}, {lst(M_INTER)}], [{lst(M_ROOT)}], {host('example.test')}, {NOW}n)",
         "True")
boolcase("mixed-leaf-is-rsa", f"X.x509.is_rsa(X.x509.spki({lst(M_LEAF)}))", "True")
boolcase("mixed-inter-is-ec", f"X.x509.is_ec(X.x509.spki({lst(M_INTER)}))", "True")

# CertificateVerify with ecdsa_secp256r1_sha256: the content is the TLS 1.3 server
# content over the transcript hash th, signed with SHA-256
def cv_content(th):
    return b"\x20" * 64 + b"TLS 1.3, server CertificateVerify" + b"\x00" + th

def cv_body(alg, sig):
    return alg.to_bytes(2, "big") + len(sig).to_bytes(2, "big") + sig

th = bytes(range(32))
sig_ec = ec_leaf_k.sign(cv_content(th), ec.ECDSA(hashes.SHA256()))
boolcase("cv-ecdsa-valid", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th))}, {lst(list(cv_body(1027, sig_ec)))})", "True")
th2 = bytes([th[0] ^ 1]) + th[1:]
boolcase("cv-ecdsa-other-transcript", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th2))}, {lst(list(cv_body(1027, sig_ec)))})", "False")
boolcase("cv-ecdsa-wrong-alg", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th))}, {lst(list(cv_body(2052, sig_ec)))})", "False")
# an RSA leaf under the ECDSA algorithm code is refused
r_leaf_k = rsa_k()
r_leaf = make("example.test", r_leaf_k, m_inter.subject, ec_inter_k, now - day, now + 365 * day, san=["example.test"])
R_LEAF = der(r_leaf)
sig_rsa_ec = ec_inter_k.sign(cv_content(th), ec.ECDSA(hashes.SHA256()))
boolcase("cv-ecdsa-on-rsa-leaf", f"H.hs.cv_ok({lst(R_LEAF)}, {lst(list(th))}, {lst(list(cv_body(1027, sig_rsa_ec)))})", "False")
# RSA-PSS on the ECDSA leaf is refused
pss = ec_leaf_k.sign(cv_content(th), ec.ECDSA(hashes.SHA256()))
boolcase("cv-pss-on-ec-leaf", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th))}, {lst(list(cv_body(2052, pss)))})", "False")

# P-384: a chain signed with ECDSA-with-SHA384, and CertificateVerify with
# ecdsa_secp384r1_sha384 (1283); a P-256 leaf and the P-384 code are refused each way
def make384(subject, key, issuer_name, issuer_key, nb, na, ca=False, san=None):
    b = (cx.CertificateBuilder().subject_name(name(subject)).issuer_name(issuer_name)
         .public_key(key.public_key()).serial_number(cx.random_serial_number())
         .not_valid_before(nb).not_valid_after(na))
    if ca:
        b = b.add_extension(cx.BasicConstraints(ca=True, path_length=None), critical=True)
    if san:
        b = b.add_extension(cx.SubjectAlternativeName([cx.DNSName(s) for s in san]), critical=False)
    return b.sign(issuer_key, hashes.SHA384())

p384 = lambda: ec.generate_private_key(ec.SECP384R1())
r384_k, i384_k, l384_k = p384(), p384(), p384()
r384 = make384("P384 Root", r384_k, name("P384 Root"), r384_k, now - 30 * day, now + 3650 * day, ca=True)
i384 = make384("P384 Intermediate", i384_k, r384.subject, r384_k, now - 30 * day, now + 1000 * day, ca=True)
l384 = make384("example.test", l384_k, i384.subject, i384_k, now - day, now + 365 * day, san=["example.test"])
E384_ROOT, E384_INTER, E384_LEAF = der(r384), der(i384), der(l384)
boolcase("p384-chain-valid",
         f"X.x509.verify_server([{lst(E384_LEAF)}, {lst(E384_INTER)}], [{lst(E384_ROOT)}], {host('example.test')}, {NOW}n)",
         "True")
tampered384 = bytearray(E384_LEAF)
tampered384[48] ^= 1
boolcase("p384-chain-tampered-leaf",
         f"X.x509.verify_server([{lst(list(tampered384))}, {lst(E384_INTER)}], [{lst(E384_ROOT)}], {host('example.test')}, {NOW}n)",
         "False")
boolcase("p384-is-p384", f"X.x509.is_p384(X.x509.spki({lst(E384_LEAF)}))", "True")
boolcase("p384-is-not-p256", f"X.x509.is_ec(X.x509.spki({lst(E384_LEAF)}))", "False")
sig384 = l384_k.sign(cv_content(th), ec.ECDSA(hashes.SHA384()))
boolcase("cv-ecdsa384-valid", f"H.hs.cv_ok({lst(E384_LEAF)}, {lst(list(th))}, {lst(list(cv_body(1283, sig384)))})", "True")
boolcase("cv-ecdsa384-other-transcript", f"H.hs.cv_ok({lst(E384_LEAF)}, {lst(list(th2))}, {lst(list(cv_body(1283, sig384)))})", "False")
boolcase("cv-ecdsa384-on-p256-leaf", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th))}, {lst(list(cv_body(1283, sig384)))})", "False")
boolcase("cv-ecdsa256-on-p384-leaf", f"H.hs.cv_ok({lst(E384_LEAF)}, {lst(list(th))}, {lst(list(cv_body(1027, sig384)))})", "False")

src = r'''# ec_tests.bend: P-256 certificate chains and the ECDSA CertificateVerify
# (generated by gen_ec_tests.py; expected values from the cryptography package).
#   bend ec_tests.bend

import Base
import ./sha256.bend as S
import ./x509.bend as X
import ./handshake.bend as H

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
    IO.print("ec: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("ec_tests.bend", "w").write(src)
print(len(out), "cases")
