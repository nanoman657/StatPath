# Writes a test PKI into a directory for e2e/run.sh:
#   root.der   the trust anchor, DER
#   inter.pem  the intermediate CA, PEM
#   leaf.pem   the server's certificate for example.test (SAN), PEM
#   leaf.key   its private key, PEM
# The kind picks the key types: rsa (all RSA), ec (all P-256, so every signature
# is ECDSA), mixed (RSA root, P-256 intermediate, RSA leaf), ed (all Ed25519), or ec384
# (all P-384, signed with SHA-384). The leaf is valid
# from a day ago for a year; the root and intermediate for longer.
#   python3 -I e2e/mkpki.py <dir> [rsa|ec|mixed|ed|ec384]
import datetime as dt
import os
import sys
import time
from cryptography import x509 as cx
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec, ed25519, rsa

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
    # Ed25519 signs without a hash function; the others sign with SHA-256
    if isinstance(issuer_key, ed25519.Ed25519PrivateKey):
        algorithm = None
    elif isinstance(issuer_key, ec.EllipticCurvePrivateKey) and issuer_key.curve.name == "secp384r1":
        algorithm = hashes.SHA384()
    else:
        algorithm = hashes.SHA256()
    return b.sign(issuer_key, algorithm)

KINDS = {
    "rsa": ("rsa", "rsa", "rsa"),
    "ec": ("ec", "ec", "ec"),
    "mixed": ("rsa", "ec", "rsa"),
    "ed": ("ed", "ed", "ed"),
    "ec384": ("ec384", "ec384", "ec384"),
}
out = sys.argv[1] if len(sys.argv) > 1 else "."
kind = sys.argv[2] if len(sys.argv) > 2 else "rsa"
root_t, inter_t, leaf_t = KINDS[kind]
new_key = {"rsa": lambda: rsa.generate_private_key(65537, 2048),
           "ec": lambda: ec.generate_private_key(ec.SECP256R1()),
           "ed": lambda: ed25519.Ed25519PrivateKey.generate(),
           "ec384": lambda: ec.generate_private_key(ec.SECP384R1())}
now = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
day = dt.timedelta(days=1)
root_key, inter_key, leaf_key = (new_key[root_t](), new_key[inter_t](), new_key[leaf_t]())
root = make("E2E Root", root_key, name("E2E Root"), root_key, now - 30 * day, now + 3650 * day, ca=True)
inter = make("E2E Intermediate", inter_key, root.subject, root_key, now - 30 * day, now + 1000 * day, ca=True)
leaf = make("example.test", leaf_key, inter.subject, inter_key, now - day, now + 365 * day,
            san=["example.test"])
pem = lambda c: c.public_bytes(serialization.Encoding.PEM)
files = {
    "root.der": root.public_bytes(serialization.Encoding.DER),
    "inter.pem": pem(inter),
    "leaf.pem": pem(leaf),
    "leaf.key": leaf_key.private_bytes(serialization.Encoding.PEM,
        serialization.PrivateFormat.PKCS8, serialization.NoEncryption()),
}
for fname, data in files.items():
    with open(os.path.join(out, fname), "wb") as f:
        f.write(data)
print("wrote", kind, "PKI:", ", ".join(files), "to", out)
