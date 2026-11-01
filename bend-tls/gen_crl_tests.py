# Writes crl_tests.bend: certificate revocation lists checked along a chain (crl.bend). Each
# CRL and chain is built with the cryptography package, and the expected verdict follows from
# how it was built: a listed serial is revoked, a CRL outside its window or signed by another
# key is no use, a CRL for another name says nothing, and an anchor in the chain is not checked.
#   python3 -I gen_crl_tests.py
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

now = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
NOW = int(now.timestamp())
day = dt.timedelta(days=1)
ecp = lambda: ec.generate_private_key(ec.SECP256R1())

def ku_sign():
    return cx.KeyUsage(digital_signature=True, content_commitment=False, key_encipherment=False,
                       data_encipherment=False, key_agreement=False, key_cert_sign=True,
                       crl_sign=True, encipher_only=False, decipher_only=False)

def make(subject, key, issuer_name, issuer_key, nb, na, ca=False, san=None, issuer_cn=None):
    b = (cx.CertificateBuilder().subject_name(name(subject)).issuer_name(issuer_name)
         .public_key(key.public_key()).serial_number(cx.random_serial_number())
         .not_valid_before(nb).not_valid_after(na))
    if ca:
        b = b.add_extension(cx.BasicConstraints(ca=True, path_length=None), critical=True)
        b = b.add_extension(ku_sign(), critical=True)
    if san:
        b = b.add_extension(cx.SubjectAlternativeName([cx.DNSName(s) for s in san]), critical=False)
    return b.sign(issuer_key, hashes.SHA256())

def der(c):
    return list(c.public_bytes(serialization.Encoding.DER))

def crl(issuer_name_obj, issuer_key, revoked_serials, this_u, next_u=None):
    b = cx.CertificateRevocationListBuilder().issuer_name(issuer_name_obj).last_update(this_u)
    if next_u is not None:
        b = b.next_update(next_u)
    for s in revoked_serials:
        b = b.add_revoked_certificate(cx.RevokedCertificateBuilder().serial_number(s)
                                      .revocation_date(this_u).build())
    return b.sign(issuer_key, hashes.SHA256())

def pki():
    rk, ik, lk = ecp(), ecp(), ecp()
    root = make("CRL Root", rk, name("CRL Root"), rk, now - 30 * day, now + 3650 * day, ca=True)
    inter = make("CRL Inter", ik, root.subject, rk, now - 30 * day, now + 1000 * day, ca=True)
    leaf = make("example.test", lk, inter.subject, ik, now - day, now + 365 * day, san=["example.test"])
    return dict(rk=rk, ik=ik, lk=lk, root=root, inter=inter, leaf=leaf)

out = []
def boolcase(name_, expr, want):
    out.append(f'  kcase("{name_}", Bool.show({expr}), "{want}") <>')

def chk(chain, anchor, crl_der, t=None):
    t = NOW if t is None else t
    return (f"CR.crl.chain.ok([{', '.join(lst(c) for c in chain)}], {lst(anchor)}, "
            f"{lst(crl_der)}, {t}n)")

# no CRL: nothing is checked; a current CRL that does not list the leaf: the chain is accepted
p = pki()
chain = [der(p["leaf"]), der(p["inter"])]
anchor = der(p["root"])
boolcase("no-crl", chk(chain, anchor, []), "True")
c_ok = crl(p["root"].subject, p["rk"], [], now - day, now + 30 * day)
boolcase("current-crl-not-listed", chk(chain, anchor, list(c_ok.public_bytes(serialization.Encoding.DER))), "True")

# the leaf is listed by the intermediate's CRL (the leaf's issuer): revoked
c_leaf = crl(p["inter"].subject, p["ik"], [p["leaf"].serial_number], now - day, now + 30 * day)
boolcase("leaf-revoked", chk(chain, anchor, list(c_leaf.public_bytes(serialization.Encoding.DER))), "False")

# the intermediate is listed by the root's CRL: the chain is refused
c_inter = crl(p["root"].subject, p["rk"], [p["inter"].serial_number], now - day, now + 30 * day)
boolcase("intermediate-revoked", chk(chain, anchor, list(c_inter.public_bytes(serialization.Encoding.DER))), "False")

# a CRL for the leaf's issuer that lists another serial: the leaf is not revoked
c_other = crl(p["inter"].subject, p["ik"], [12345], now - day, now + 30 * day)
boolcase("other-serial-listed", chk(chain, anchor, list(c_other.public_bytes(serialization.Encoding.DER))), "True")

# time: a CRL past its nextUpdate, or not yet current, is no use
c_old = crl(p["inter"].subject, p["ik"], [], now - 60 * day, now - day)
boolcase("crl-expired", chk(chain, anchor, list(c_old.public_bytes(serialization.Encoding.DER))), "False")
c_future = crl(p["inter"].subject, p["ik"], [p["leaf"].serial_number], now + 5 * day, now + 30 * day)
boolcase("crl-not-yet-current", chk(chain, anchor, list(c_future.public_bytes(serialization.Encoding.DER))), "False")
c_far = crl(p["inter"].subject, p["ik"], [], now - day, now + 3000 * day)
boolcase("crl-far-nextupdate", chk(chain, anchor, list(c_far.public_bytes(serialization.Encoding.DER))), "True")

# the CRL must be signed by the issuer: signed by another key under the issuer's name is refused
forged = crl(p["inter"].subject, ecp(), [p["leaf"].serial_number], now - day, now + 30 * day)
boolcase("crl-forged", chk(chain, anchor, list(forged.public_bytes(serialization.Encoding.DER))), "False")

# a CRL for another name says nothing about the leaf (here: the root's CRL, listing the leaf's serial)
other_name = crl(name("Some Other CA"), p["rk"], [p["leaf"].serial_number], now - day, now + 30 * day)
boolcase("crl-other-issuer", chk(chain, anchor, list(other_name.public_bytes(serialization.Encoding.DER))), "True")

# a tampered CRL (a byte of its signature flipped) is refused
raw = bytearray(c_leaf.public_bytes(serialization.Encoding.DER))
raw[-1] ^= 1
boolcase("crl-tampered-signature", chk(chain, anchor, list(raw)), "False")

# the anchor itself in the chain is not checked against the CRL
chain_with_anchor = [der(p["leaf"]), der(p["inter"]), anchor]
boolcase("anchor-in-chain-not-checked",
         chk(chain_with_anchor, anchor, list(c_inter.public_bytes(serialization.Encoding.DER))), "False")
boolcase("anchor-in-chain-no-listing",
         chk(chain_with_anchor, anchor, list(c_ok.public_bytes(serialization.Encoding.DER))), "True")

src = r'''# crl_tests.bend: certificate revocation lists along a chain (generated by gen_crl_tests.py).
#   bend crl_tests.bend

import Base
import ./crl.bend as CR

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
    IO.print("crl: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("crl_tests.bend", "w").write(src)
print(len(out), "cases")
