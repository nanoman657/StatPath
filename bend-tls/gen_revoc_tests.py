# Writes revoc_tests.bend: the revocation sources of a certificate (rev.cdp_uris, rev.ocsp_uri),
# the OCSP request for it (byte for byte the request cryptography builds), and the check of an OCSP
# reply (rev.ocsp_ok), against replies cryptography signs: good, revoked, for another certificate,
# with a bad signature, past nextUpdate, by a delegated responder with and without the OCSP-signing
# purpose, and an error status. The expected values are the ones the RFC rules give.
#   python3 -I gen_revoc_tests.py
import datetime as dt
import time
from cryptography import x509 as cx
from cryptography.x509 import ocsp
from cryptography.x509.oid import NameOID, ExtendedKeyUsageOID, AuthorityInformationAccessOID
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
CDP_URL = "http://127.0.0.1:4480/crl.der"
OCSP_URL = "http://127.0.0.1:4480/"

def cert(subject, key, issuer_name, issuer_key, ca=False, eku=None, aia=True, cdp=True, nb=None, na=None, serial=None):
    b = (cx.CertificateBuilder().subject_name(name(subject)).issuer_name(issuer_name)
         .public_key(key.public_key())
         .serial_number(serial if serial is not None else cx.random_serial_number())
         .not_valid_before(nb or now - day).not_valid_after(na or now + 365 * day))
    if ca:
        b = b.add_extension(cx.BasicConstraints(ca=True, path_length=None), critical=True)
    if eku is not None:
        b = b.add_extension(cx.ExtendedKeyUsage(eku), critical=False)
    if cdp:
        b = b.add_extension(cx.CRLDistributionPoints([cx.DistributionPoint(
            full_name=[cx.UniformResourceIdentifier(CDP_URL)], relative_name=None,
            reasons=None, crl_issuer=None)]), critical=False)
    if aia:
        b = b.add_extension(cx.AuthorityInformationAccess([cx.AccessDescription(
            AuthorityInformationAccessOID.OCSP, cx.UniformResourceIdentifier(OCSP_URL))]), critical=False)
    return b.sign(issuer_key, hashes.SHA256())

def der(c):
    return list(c.public_bytes(serialization.Encoding.DER))

rk, ik, lk, dk = ecp(), ecp(), ecp(), ecp()
root = cx.CertificateBuilder().subject_name(name("OCSP Root")).issuer_name(name("OCSP Root")) \
    .public_key(rk.public_key()).serial_number(cx.random_serial_number()) \
    .not_valid_before(now - day).not_valid_after(now + 3650 * day) \
    .add_extension(cx.BasicConstraints(ca=True, path_length=None), critical=True).sign(rk, hashes.SHA256())
inter = cert("OCSP Inter", ik, root.subject, rk, ca=True, cdp=False, aia=False)
leaf = cert("example.test", lk, inter.subject, ik)
noaia = cert("plain.test", lk, inter.subject, ik, aia=False, cdp=False)
delegated = cert("OCSP Responder", dk, inter.subject, ik, eku=[ExtendedKeyUsageOID.OCSP_SIGNING], cdp=False, aia=False)
notdelegated = cert("Not A Responder", dk, inter.subject, ik, eku=[ExtendedKeyUsageOID.SERVER_AUTH], cdp=False, aia=False)

out = []
def kc(name_, expr, want):
    out.append(f'  kcase("{name_}", {expr}, "{want}") <>')
def boolcase(name_, expr, want):
    out.append(f'  kcase("{name_}", Bool.show({expr}), "{want}") <>')

kc("cdp-uri", f"H.http.ip_str(rev.first_of(rev.cdp_uris({lst(der(leaf))})))", CDP_URL)
kc("ocsp-uri", f"H.http.ip_str(rev.ocsp_uri({lst(der(leaf))}))", OCSP_URL)
kc("no-ocsp-uri", f"Nat.show(List.length(&2, U32, rev.ocsp_uri({lst(der(noaia))})))", "0")
kc("no-cdp-uri", f"Nat.show(List.length(&2, List<&2, U32>, rev.cdp_uris({lst(der(noaia))})))", "0")

req = ocsp.OCSPRequestBuilder().add_certificate(leaf, inter, hashes.SHA256()).build()
kc("ocsp-request-bytes", f"S.hex_of(rev.ocsp_request({lst(der(leaf))}, {lst(der(inter))}))",
   req.public_bytes(serialization.Encoding.DER).hex())

def respond(cert_status, responder_cert=None, responder_key=None, signer=None, this=now - day, nxt=now + 7 * day,
            for_cert=leaf, status=None, tamper=False):
    if status is not None:
        return ocsp.OCSPResponseBuilder.build_unsuccessful(status).public_bytes(serialization.Encoding.DER)
    b = ocsp.OCSPResponseBuilder().add_response(cert=for_cert, issuer=inter, algorithm=hashes.SHA256(),
        cert_status=cert_status, this_update=this, next_update=nxt,
        revocation_time=(now - day) if cert_status == ocsp.OCSPCertStatus.REVOKED else None,
        revocation_reason=None)
    if responder_cert is not None:
        b = b.responder_id(ocsp.OCSPResponderEncoding.HASH, responder_cert).certificates([responder_cert])
        key = responder_key
    else:
        b = b.responder_id(ocsp.OCSPResponderEncoding.HASH, inter)
        key = ik
    raw = bytearray(b.sign(key, hashes.SHA256()).public_bytes(serialization.Encoding.DER))
    if tamper:
        raw[-3] ^= 1
    return bytes(raw)

G = ocsp.OCSPCertStatus.GOOD
R = ocsp.OCSPCertStatus.REVOKED
def ok(reply, c=leaf, n=inter):
    return f"rev.ocsp_ok({lst(list(reply))}, {lst(der(c))}, {lst(der(n))}, {NOW}n)"

boolcase("ocsp-good", ok(respond(G)), "True")
boolcase("ocsp-revoked", ok(respond(R)), "False")
boolcase("ocsp-unknown-refused", ok(respond(ocsp.OCSPCertStatus.UNKNOWN)), "False")
boolcase("ocsp-other-certificate", ok(respond(G, for_cert=noaia)), "False")
boolcase("ocsp-tampered", ok(respond(G, tamper=True)), "False")
boolcase("ocsp-past-nextupdate", ok(respond(G, this=now - 10 * day, nxt=now - day)), "False")
boolcase("ocsp-not-yet-current", ok(respond(G, this=now + day, nxt=now + 8 * day)), "False")
boolcase("ocsp-delegated-good", ok(respond(G, responder_cert=delegated, responder_key=dk)), "True")
boolcase("ocsp-delegated-without-purpose", ok(respond(G, responder_cert=notdelegated, responder_key=dk)), "False")
boolcase("ocsp-try-later-refused", ok(respond(G, status=ocsp.OCSPResponseStatus.TRY_LATER)), "False")

src = r'''# revoc_tests.bend: revocation sources and the OCSP check (generated by gen_revoc_tests.py).
#   bend revoc_tests.bend

import Base
import ./revoc.bend as V
import ./http.bend as H
import ./sha256.bend as S

type Case is Data:
  Case{name: String, got: String, want: String}

def kcase(name: String, +got: String, want: String) -> Case:
  Case{name, got, want}

def cases() -> List<&2, Case>:
''' + "\n".join(out).replace("rev.", "V.rev.").replace("H.http.", "H.http.") + r'''
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
    IO.print("revoc: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("revoc_tests.bend", "w").write(src)
print(len(out), "cases")
