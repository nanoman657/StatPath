# Writes ed25519_tests.bend: Ed25519 verification. The RFC 8032 section 7.1 test 1 key
# and signature are checked against cryptography first; random signatures come from
# cryptography too. Rejected inputs: a changed message, R or S, a non-canonical S
# (S + L), another key, a non-canonical key encoding, and a key of the wrong length.
#   python3 -I gen_ed25519_tests.py
import datetime as dt
import hashlib
import random
import time
from cryptography import x509 as cx
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import ed25519

p = 2 ** 255 - 19
L = 2 ** 252 + 27742317777372353535851937790883648493

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def raw_pub(priv):
    return priv.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)

def sign(priv, msg):
    return priv.sign(msg)

rng = random.Random(8032)
out = []
def boolcase(name, expr, want):
    out.append(f'  kcase("{name}", Bool.show({expr}), "{want}") <>')

def kc(name, expr, want):
    out.append(f'  kcase("{name}", {expr}, "{want}") <>')

def verify_expr(pk, msg, sig):
    return f"ED.ed.verify({lst(pk)}, {lst(msg)}, {lst(sig)})"

# RFC 8032 7.1 test 1 (the empty message)
rfc_seed = bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
rfc_pub = bytes.fromhex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
rfc_sig = bytes.fromhex("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
priv1 = ed25519.Ed25519PrivateKey.from_private_bytes(rfc_seed)
assert raw_pub(priv1) == rfc_pub, "the RFC public key differs from cryptography"
assert sign(priv1, b"") == rfc_sig, "the RFC signature differs from cryptography"
boolcase("rfc8032-test1", verify_expr(rfc_pub, b"", rfc_sig), "True")

# a second RFC-style case: one byte message
rfc2_seed = bytes.fromhex("4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb")
priv2 = ed25519.Ed25519PrivateKey.from_private_bytes(rfc2_seed)
pub2 = raw_pub(priv2)
sig2 = sign(priv2, b"\x72")
boolcase("rfc8032-test2-shape", verify_expr(pub2, b"\x72", sig2), "True")

keys = [ed25519.Ed25519PrivateKey.from_private_bytes(bytes(rng.randrange(256) for _ in range(32))) for _ in range(4)]
msgs = [b"", b"abc", bytes(rng.randrange(256) for _ in range(129)), b"x" * 300]
for i, (k, m) in enumerate(zip(keys, msgs)):
    boolcase(f"valid-{i}", verify_expr(raw_pub(k), m, sign(k, m)), "True")

k, m = keys[2], msgs[2]
pk, sg = raw_pub(k), sign(k, m)
boolcase("other-message", verify_expr(pk, m + b"!", sg), "False")
boolcase("r-changed", verify_expr(pk, m, bytes([sg[0] ^ 1]) + sg[1:]), "False")
boolcase("s-changed", verify_expr(pk, m, sg[:40] + bytes([sg[40] ^ 1]) + sg[41:]), "False")
s_int = int.from_bytes(sg[32:], "little")
s_plus_l = (s_int + L).to_bytes(32, "little")
boolcase("s-not-reduced", verify_expr(pk, m, sg[:32] + s_plus_l), "False")
boolcase("other-key", verify_expr(raw_pub(keys[0]), m, sg), "False")
boolcase("key-wrong-length", verify_expr(pk[:31], m, sg), "False")
boolcase("sig-wrong-length", verify_expr(pk, m, sg[:63]), "False")
# a key encoding with y = p (not reduced): no point, so no signature
nonreduced = (p).to_bytes(32, "little")
boolcase("key-y-not-reduced", verify_expr(nonreduced, m, sg), "False")

# [a]B encodes the public key: a is the clamped low half of SHA-512(seed)
seed = bytes(rng.randrange(256) for _ in range(32))
h = bytearray(hashlib.sha512(seed).digest()[:32])
h[0] &= 248
h[31] &= 127
h[31] |= 64
pub_seed = raw_pub(ed25519.Ed25519PrivateKey.from_private_bytes(seed))
boolcase("base-mul-public-key",
         f"P.p256.eqn(ED.ed.encode(ED.ed.smul(P.p256.bits(ED.ed.le_limbs({lst(list(bytes(h)))})), ED.ed.base())), ED.ed.nat_bytes({lst(list(pub_seed))}))",
         "True")

# the challenge reduction: a 64-byte little-endian integer mod L
for i, n in enumerate([0, 1, L - 1, L, L + 5, 2 ** 511 + 12345]):
    limbs = [(n % L >> (16 * j)) & 0xffff for j in range(18)]
    hle = (n).to_bytes(64, "little")
    nat_lst = "[" + ", ".join(f"{v}n" for v in limbs) + "]"
    boolcase(f"modl-{i}", f"P.p256.eqn(ED.ed.modl({lst(list(hle))}), {nat_lst})", "True")

# certificates: an all-Ed25519 chain (Ed25519 signs without a hash function), with
# the tampered and wrong-anchor variants
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
    return b.sign(issuer_key, None)

now = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
NOW = int(now.timestamp())
day = dt.timedelta(days=1)
r_k, i_k, l_k = (ed25519.Ed25519PrivateKey.generate() for _ in range(3))
root = make("Ed Root", r_k, name("Ed Root"), r_k, now - 30 * day, now + 3650 * day, ca=True)
inter = make("Ed Intermediate", i_k, root.subject, r_k, now - 30 * day, now + 1000 * day, ca=True)
leaf = make("example.test", l_k, inter.subject, i_k, now - day, now + 365 * day, san=["example.test"])
E_ROOT, E_INTER, E_LEAF = list(root.public_bytes(serialization.Encoding.DER)), \
    list(inter.public_bytes(serialization.Encoding.DER)), list(leaf.public_bytes(serialization.Encoding.DER))
host = lambda s: lst(list(s.encode()))
boolcase("ed-chain-valid",
         f"X.x509.verify_server([{lst(E_LEAF)}, {lst(E_INTER)}], [{lst(E_ROOT)}], {host('example.test')}, {NOW}n)",
         "True")
boolcase("ed-chain-wrong-host",
         f"X.x509.verify_server([{lst(E_LEAF)}, {lst(E_INTER)}], [{lst(E_ROOT)}], {host('other.test')}, {NOW}n)",
         "False")
tampered = bytearray(E_LEAF)
tampered[48] ^= 1
boolcase("ed-chain-tampered-leaf",
         f"X.x509.verify_server([{lst(list(tampered))}, {lst(E_INTER)}], [{lst(E_ROOT)}], {host('example.test')}, {NOW}n)",
         "False")
boolcase("ed-is-ed", f"X.x509.is_ed(X.x509.spki({lst(E_LEAF)}))", "True")
boolcase("ed-is-not-ec", f"X.x509.is_ec(X.x509.spki({lst(E_LEAF)}))", "False")
pub_leaf = l_k.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
kc("ed-pub", f"S.hex_of(X.x509.ed_pub(X.x509.spki({lst(E_LEAF)})))", pub_leaf.hex())

# CertificateVerify with ed25519 (0x0807): the content itself is signed
def cv_content(th):
    return b"\x20" * 64 + b"TLS 1.3, server CertificateVerify" + b"\x00" + th
def cv_body(alg, sig):
    return alg.to_bytes(2, "big") + len(sig).to_bytes(2, "big") + sig
th = bytes(range(32))
sig_cv = l_k.sign(cv_content(th))
boolcase("cv-ed25519-valid", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th))}, {lst(list(cv_body(2055, sig_cv)))})", "True")
th2 = bytes([th[0] ^ 1]) + th[1:]
boolcase("cv-ed25519-other-transcript", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th2))}, {lst(list(cv_body(2055, sig_cv)))})", "False")
boolcase("cv-ed25519-wrong-alg", f"H.hs.cv_ok({lst(E_LEAF)}, {lst(list(th))}, {lst(list(cv_body(1027, sig_cv)))})", "False")

src = r'''# ed25519_tests.bend: Ed25519 verification and its parts (generated by gen_ed25519_tests.py;
# expected values from the cryptography package and RFC 8032).
#   bend ed25519_tests.bend

import Base
import ./ed25519.bend as ED
import ./p256.bend as P
import ./x509.bend as X
import ./handshake.bend as H
import ./sha256.bend as S

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
    IO.print("ed25519: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("ed25519_tests.bend", "w").write(src)
print(len(out), "cases")
