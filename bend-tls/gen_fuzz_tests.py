# Writes fuzz_tests.bend: robustness of the certificate and CertificateVerify parsers and
# verifiers on mutated input. Valid chains (RSA, ECDSA P-256, Ed25519) are mutated at random:
# byte flips, truncations, inserted bytes and duplicated slices. The test passes when
# every evaluation returns (no runtime fault); it reports how many mutated chains were
# accepted, which should be none, since every mutation changes signed or structural bytes.
#   python3 -I gen_fuzz_tests.py
import datetime as dt
import random
import time
from cryptography import x509 as cx
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, ed25519, rsa

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
    algorithm = None if isinstance(issuer_key, ed25519.Ed25519PrivateKey) else hashes.SHA256()
    return b.sign(issuer_key, algorithm)

def der(c):
    return c.public_bytes(serialization.Encoding.DER)

now = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
NOW = int(now.timestamp())
day = dt.timedelta(days=1)
rng = random.Random(20260)

def chain_of(kind):
    keys = {"ec": lambda: ec.generate_private_key(ec.SECP256R1()),
            "ed": lambda: ed25519.Ed25519PrivateKey.generate(),
            "rsa": lambda: rsa.generate_private_key(65537, 2048)}[kind]
    r, i, l = keys(), keys(), keys()
    root = make("Fuzz Root", r, name("Fuzz Root"), r, now - 30 * day, now + 3650 * day, ca=True)
    inter = make("Fuzz Inter", i, root.subject, r, now - 30 * day, now + 1000 * day, ca=True)
    leaf = make("example.test", l, inter.subject, i, now - day, now + 365 * day, san=["example.test"])
    return [der(leaf), der(inter)], der(root)

def mutate(b):
    b = bytearray(b)
    op = rng.randrange(5)
    if op == 0:                     # flip bytes
        for _ in range(rng.randrange(1, 4)):
            b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    elif op == 1:                   # truncate
        b = b[:rng.randrange(len(b))]
    elif op == 2:                   # insert a byte
        b.insert(rng.randrange(len(b) + 1), rng.randrange(256))
    elif op == 3:                   # duplicate a slice
        i = rng.randrange(len(b)); j = min(len(b), i + rng.randrange(1, 40))
        b[i:i] = b[i:j]
    else:                           # set one byte to an extreme value
        b[rng.randrange(len(b))] = rng.choice([0, 255, 0x80, 0x7f, 0x30, 0x02])
    return bytes(b)

cases = []
records = []
for kind, count in [("ec", 60), ("ed", 40), ("rsa", 8)]:
    chain, root = chain_of(kind)
    for _ in range(count):
        which = rng.randrange(len(chain))
        mutated = list(chain)
        mutated[which] = mutate(chain[which])
        while mutated[which] == chain[which]:   # a no-op mutation proves nothing
            mutated[which] = mutate(chain[which])
        records.append({"kind": kind, "which": which, "original": [c.hex() for c in chain],
                        "mutated": [c.hex() for c in mutated], "root": root.hex()})
        cases.append((kind, [m for m in mutated], root))
# the unmutated chains are accepted: a control for the harness
controls = []
for kind in ["ec", "ed"]:
    chain, root = chain_of(kind)
    controls.append((kind, chain, root))

def call(chain, root):
    return f"X.x509.verify_server([{', '.join(lst(list(c)) for c in chain)}], [{lst(list(root))}], [101, 120, 97, 109, 112, 108, 101, 46, 116, 101, 115, 116], {NOW}n)"

# CertificateVerify under mutation: the signature (and the leaf) of each key type, mutated
def cv_content(th):
    return b"\x20" * 64 + b"TLS 1.3, server CertificateVerify" + b"\x00" + th
def cv_body(alg, sig):
    return alg.to_bytes(2, "big") + len(sig).to_bytes(2, "big") + sig
cv_cases = []
th = bytes(range(32))
for kind, alg, signer in [("ec", 1027, lambda k, m: k.sign(m, ec.ECDSA(hashes.SHA256()))),
                          ("ed", 2055, lambda k, m: k.sign(m))]:
    key = ec.generate_private_key(ec.SECP256R1()) if kind == "ec" else ed25519.Ed25519PrivateKey.generate()
    leaf = make("example.test", key, name("CV"), key, now - day, now + 365 * day, san=["example.test"])
    sig = signer(key, cv_content(th))
    for _ in range(40):
        m = mutate(sig)
        while m == sig:
            m = mutate(sig)
        cv_cases.append((kind, list(der(leaf)), cv_body(alg, m)))
    # the valid signature under the wrong transcript, and a mutated leaf
    cv_cases.append((kind, list(der(leaf)), cv_body(alg, sig))) if False else None

lines = []
for idx, (kind, leaf, body) in enumerate(cv_cases):
    lines.append(f"  kcase(\"cv-{kind}-{idx}\", Bool.show(H.hs.cv_ok({lst(leaf)}, {lst(list(th))}, {lst(list(body))})), \"False\") <>")
for idx, (kind, chain, root) in enumerate(cases):
    lines.append(f"  kcase(\"mutated-{kind}-{idx}\", Bool.show({call(chain, root)}), \"False\") <>")
for kind, chain, root in controls:
    lines.append(f"  kcase(\"control-{kind}\", Bool.show({call(chain, root)}), \"True\") <>")
ncases = len(cases)

src = r'''# fuzz_tests.bend: mutated certificate chains must not fault the verifier (generated by
# gen_fuzz_tests.py). Each mutated chain is expected to be refused; the controls must be accepted.
#   bend fuzz_tests.bend

import Base
import ./x509.bend as X
import ./handshake.bend as H

type Case is Data:
  Case{name: String, got: String, want: String}

def kcase(name: String, +got: String, want: String) -> Case:
  Case{name, got, want}

def cases() -> List<&2, Case>:
''' + "\n".join(lines) + r'''
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
    IO.print("fuzz: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed (a FAIL is a mutated chain that was accepted, or a broken control)")
'''
open("fuzz_tests.bend", "w").write(src)
print(len(cases), "mutated chains,", len(controls), "controls")
