#!/usr/bin/env python3
# End-to-end test of revocation fetching: client.bend with the fetch argument takes the status of
# the server's certificate over HTTP. The OCSP responder is openssl ocsp, serving a status index;
# the CRL distribution point is a Python HTTP server. The handshake is refused when the certificate
# is revoked, its status is unknown, or its revocation URL cannot be fetched or does not confirm it.
# A certificate with no revocation URI is accepted, and without the fetch argument nothing is fetched.
#   python3 -I e2e/fetch.py           # JS (bend client.bend ...)
#   python3 -I e2e/fetch.py native    # native binary
# Needs openssl and Python's cryptography package.
import datetime as dt
import os
import shutil
import socket
import subprocess
import sys
import tempfile
import time
from cryptography import x509 as cx
from cryptography.x509 import ocsp as _ocsp  # noqa: F401  (the responder is openssl's)
from cryptography.x509.oid import NameOID, AuthorityInformationAccessOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
MODE = sys.argv[1] if len(sys.argv) > 1 else "js"
DAY = dt.timedelta(days=1)


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def wait_listening(port, seconds=10):
    end = time.time() + seconds
    while time.time() < end:
        try:
            with socket.create_connection(("127.0.0.1", port), timeout=0.5):
                return True
        except OSError:
            time.sleep(0.1)
    return False


def name(cn):
    return cx.Name([cx.NameAttribute(NameOID.COMMON_NAME, cn)])


def ca(subject, key, issuer_name, issuer_key, now):
    return (cx.CertificateBuilder().subject_name(name(subject)).issuer_name(issuer_name)
            .public_key(key.public_key()).serial_number(cx.random_serial_number())
            .not_valid_before(now - DAY).not_valid_after(now + 3650 * DAY)
            .add_extension(cx.BasicConstraints(ca=True, path_length=None), critical=True)
            .sign(issuer_key, hashes.SHA256()))


def leaf(cn, key, issuer, issuer_key, now, ocsp_url=None, cdp_url=None):
    b = (cx.CertificateBuilder().subject_name(name(cn)).issuer_name(issuer.subject)
         .public_key(key.public_key()).serial_number(cx.random_serial_number())
         .not_valid_before(now - DAY).not_valid_after(now + 365 * DAY)
         .add_extension(cx.SubjectAlternativeName([cx.DNSName("example.test")]), critical=False))
    if ocsp_url:
        b = b.add_extension(cx.AuthorityInformationAccess([cx.AccessDescription(
            AuthorityInformationAccessOID.OCSP, cx.UniformResourceIdentifier(ocsp_url))]), critical=False)
    if cdp_url:
        b = b.add_extension(cx.CRLDistributionPoints([cx.DistributionPoint(
            full_name=[cx.UniformResourceIdentifier(cdp_url)], relative_name=None,
            reasons=None, crl_issuer=None)]), critical=False)
    return b.sign(issuer_key, hashes.SHA256())


def pem_key(key, path):
    with open(path, "wb") as f:
        f.write(key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                  serialization.NoEncryption()))


def pem_cert(c, path):
    with open(path, "wb") as f:
        f.write(c.public_bytes(serialization.Encoding.PEM))


def der_cert(c, path):
    with open(path, "wb") as f:
        f.write(c.public_bytes(serialization.Encoding.DER))


def crl_for(issuer, issuer_key, revoked_serials, now):
    b = (cx.CertificateRevocationListBuilder().issuer_name(issuer.subject)
         .last_update(now - DAY).next_update(now + 7 * DAY))
    for s in revoked_serials:
        b = b.add_revoked_certificate(cx.RevokedCertificateBuilder()
                                      .serial_number(s).revocation_date(now - DAY).build())
    return b.sign(issuer_key, hashes.SHA256()).public_bytes(serialization.Encoding.DER)


def index_line(status, serial, now, cn):
    ts = lambda t: t.strftime("%y%m%d%H%M%SZ")
    exp = ts(now + 3650 * DAY)
    if status == "R":
        return f"R\t{exp}\t{ts(now - DAY)}\t{serial:X}\tunknown\t/CN={cn}\n"
    return f"V\t{exp}\t\t{serial:X}\tunknown\t/CN={cn}\n"


def main():
    work = tempfile.mkdtemp(prefix="fetch-e2e-")
    procs = []
    results = {"pass": 0, "fail": 0}
    try:
        now_dt = dt.datetime.fromtimestamp(time.time(), dt.timezone.utc)
        now = int(now_dt.timestamp())
        sport = free_port()
        oport = free_port()
        cport = free_port()
        dead = free_port()          # nothing listens here: a revocation URL that cannot be fetched
        ocsp_url = f"http://127.0.0.1:{oport}/"
        crl_base = f"http://127.0.0.1:{cport}"
        dead_ocsp = f"http://127.0.0.1:{dead}/"
        dead_crl = f"http://127.0.0.1:{dead}/crl.der"

        rk, ik = ec.generate_private_key(ec.SECP256R1()), ec.generate_private_key(ec.SECP256R1())
        root = ca("Fetch Root", rk, name("Fetch Root"), rk, now_dt)
        inter = ca("Fetch Inter", ik, root.subject, rk, now_dt)
        der_cert(root, f"{work}/root.der")
        pem_cert(inter, f"{work}/inter.pem")
        pem_key(ik, f"{work}/inter.key")

        # (name, the leaf's OCSP URI, its CRL URI, the OCSP index status ("V", "R" or None for
        # absent), whether its CRL lists it, want with fetch ("ok" or "fail"))
        scenarios = [
            ("ocsp-good",        ocsp_url, None,       "V",  False, "ok"),
            ("ocsp-revoked",     ocsp_url, None,       "R",  False, "fail"),
            ("ocsp-unknown",     ocsp_url, None,       None, False, "fail"),
            ("ocsp-unreachable", dead_ocsp, None,      "V",  False, "fail"),
            ("crl-clean",        None, f"{crl_base}/clean.der", None, False, "ok"),
            ("crl-revoked",      None, f"{crl_base}/revoked.der", None, True, "fail"),
            ("crl-unreachable",  None, dead_crl,       None, False, "fail"),
            ("no-urls",          None, None,           None, False, "ok"),
        ]
        index = ""
        leaves = {}
        serials = {}
        for sname, ou, cu, status, revoked, _ in scenarios:
            lk = ec.generate_private_key(ec.SECP256R1())
            c = leaf(f"{sname}.example.test", lk, inter, ik, now_dt, ou, cu)
            leaves[sname] = (c, lk)
            serials[sname] = c.serial_number
            if status:
                index += index_line(status, c.serial_number, now_dt, f"{sname}.example.test")
            pem_cert(c, f"{work}/{sname}.pem")
            pem_key(lk, f"{work}/{sname}.key")
        # the CRLs the HTTP server serves: clean lists nothing; revoked lists the revoked leaf
        with open(f"{work}/index.txt", "w") as f:
            f.write(index)
        os.makedirs(f"{work}/crl")
        with open(f"{work}/crl/clean.der", "wb") as f:
            f.write(crl_for(inter, ik, [], now_dt))
        with open(f"{work}/crl/revoked.der", "wb") as f:
            f.write(crl_for(inter, ik, [serials["crl-revoked"]], now_dt))

        ocsp_proc = subprocess.Popen(
            ["openssl", "ocsp", "-index", f"{work}/index.txt", "-port", str(oport),
             "-CA", f"{work}/inter.pem", "-rsigner", f"{work}/inter.pem", "-rkey", f"{work}/inter.key",
             "-ndays", "1"], stdout=subprocess.DEVNULL, stderr=open(f"{work}/ocsp.log", "w"))
        crl_proc = subprocess.Popen(
            [sys.executable, "-m", "http.server", str(cport), "--bind", "127.0.0.1", "--directory", f"{work}/crl"],
            stdout=subprocess.DEVNULL, stderr=open(f"{work}/crl.log", "w"))
        procs += [ocsp_proc, crl_proc]
        # openssl ocsp spins after a bare TCP connect and close, so it gets a fixed wait
        # instead of a probe; the CRL server is probed
        time.sleep(1.0)
        if ocsp_proc.poll() is not None or not wait_listening(cport):
            print("FAIL: the OCSP responder or the CRL server did not start")
            for name_, p_, log in [("ocsp", ocsp_proc, "ocsp.log"), ("crl", crl_proc, "crl.log")]:
                print(f"  {name_}: poll={p_.poll()}", open(f"{work}/{log}").read()[-300:])
            return 1

        if MODE == "native":
            built = subprocess.run(["timeout", "580", "bend", "client.bend", "-o", f"{work}/client"],
                                   cwd=ROOT, capture_output=True)
            if built.returncode != 0:
                print("build failed")
                return 1
            run_prefix = [f"{work}/client"]
        else:
            run_prefix = ["bend", "client.bend"]

        # each case verifies at a time after its responses were made: the native build takes minutes,
        # and an OCSP reply made later than the verification time is not current (thisUpdate > now)
        def run_case(label, sname, want, fetch):
            shutil.copy(f"{work}/{sname}.pem", f"{work}/leaf.pem")
            shutil.copy(f"{work}/{sname}.key", f"{work}/leaf.key")
            server = subprocess.Popen(
                ["openssl", "s_server", "-accept", str(sport), "-cert", f"{work}/leaf.pem",
                 "-cert_chain", f"{work}/inter.pem", "-key", f"{work}/leaf.key", "-tls1_3",
                 "-ciphersuites", "TLS_AES_128_GCM_SHA256", "-groups", "X25519", "-www"],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            procs.append(server)
            try:
                if not wait_listening(sport):
                    results["fail"] += 1
                    print(f"FAIL {label}: the TLS server did not start")
                    return
                args = run_prefix + ["example.test", "127.0.0.1", str(sport), f"{work}/root.der", str(int(time.time()) + 60), ""]
                if fetch:
                    args.append("fetch")
                try:
                    p = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=600)
                    out = p.stdout + p.stderr
                    code = p.returncode
                except subprocess.TimeoutExpired:
                    out, code = "timed out", -1
                fetched_page = code == 0 and "HTTP/1.0 200" in out
                refused = code != 0 and ("revoc" in out or "did not check" in out)
                ok = fetched_page if want == "ok" else refused
                if ok:
                    results["pass"] += 1
                    print(f"PASS {label}")
                else:
                    results["fail"] += 1
                    print(f"FAIL {label}: exit {code}")
                    print("\n".join(l for l in out.splitlines() if l.strip())[-600:])
            finally:
                server.terminate()
                server.wait()
                procs.remove(server)
                time.sleep(0.3)

        for sname, ou, cu, status, revoked, want in scenarios:
            run_case(f"{sname} with fetch", sname, want, True)
        # without the fetch argument nothing is fetched: a revoked certificate is not refused here
        run_case("ocsp-revoked without fetch", "ocsp-revoked", "ok", False)

        total = results["pass"] + results["fail"]
        print(f"e2e fetch ({MODE}): {results['pass']} passed, {results['fail']} failed of {total}")
        return 0 if results["fail"] == 0 else 1
    finally:
        for p in procs:
            p.terminate()
        for p in procs:
            p.wait()
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
