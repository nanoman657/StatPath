# Rejection paths of the client's HelloRetryRequest and ServerHello checks. A fake server
# (a thread here) sends one scripted reply to the ClientHello, and the client must refuse it:
# exit status 1, with the message for a ServerHello it does not take. Modes:
#   hrr-group-29     a HelloRetryRequest selecting x25519, which the first ClientHello shared
#   hrr-group-23     one selecting secp256r1, which it shared too
#   hrr-group-25     one selecting a group we do not offer
#   hrr-suite-1305   one with a cipher suite we do not offer
#   hrr-twice        a HelloRetryRequest for secp384r1, then another one after the second hello
#   sh-group-24      a ServerHello selecting secp384r1 without a HelloRetryRequest
#   hrr-cookie       a HelloRetryRequest with a cookie: the second ClientHello must echo it
#   (no mode)        runs them all:  python3 -I e2e/rejects.py [js|native]
import os
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import hashlib
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
HRR_RANDOM = hashlib.sha256(b"HelloRetryRequest").digest()
COOKIE = bytes(range(1, 9))

def vec(n, b):
    return len(b).to_bytes(n, "big") + b

def hs(t, body):
    return bytes([t]) + len(body).to_bytes(3, "big") + body

def rec(ctype, body):
    return bytes([ctype, 3, 3]) + len(body).to_bytes(2, "big") + body

def hrr(group, suite=0x1301, cookie=None):
    exts = b"\x00\x2b" + vec(2, bytes([3, 4])) + b"\x00\x33" + vec(2, group.to_bytes(2, "big"))
    if cookie is not None:
        exts += b"\x00\x2c" + vec(2, vec(2, cookie))
    body = b"\x03\x03" + HRR_RANDOM + b"\x00" + suite.to_bytes(2, "big") + b"\x00" + vec(2, exts)
    return rec(22, hs(2, body))

def server_hello(group):
    key = b"\x04" + bytes(range(96))
    exts = b"\x00\x2b" + vec(2, bytes([3, 4])) + b"\x00\x33" + vec(2, group.to_bytes(2, "big") + vec(2, key))
    body = b"\x03\x03" + bytes(32) + b"\x00" + b"\x13\x01" + b"\x00" + vec(2, exts)
    return rec(22, hs(2, body))

def read_exact(sock, n):
    buf = b""
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise EOFError
        buf += chunk
    return buf

def read_client_hello(sock):
    """The body of the next ClientHello record: its extensions as (type, data) pairs."""
    header = read_exact(sock, 5)
    body = read_exact(sock, struct.unpack(">H", header[3:5])[0])
    assert body[0] == 1, "not a ClientHello"
    msg = body[4:]
    pos = 2 + 32
    sid = msg[pos]; pos += 1 + sid
    cs = struct.unpack(">H", msg[pos:pos + 2])[0]; pos += 2 + cs
    comp = msg[pos]; pos += 1 + comp
    ext_len = struct.unpack(">H", msg[pos:pos + 2])[0]; pos += 2
    exts, end = [], pos + ext_len
    while pos < end:
        t, l = struct.unpack(">HH", msg[pos:pos + 4]); pos += 4
        exts.append((t, msg[pos:pos + l])); pos += l
    return exts

def shares(exts):
    data = dict(exts)[51]
    n = struct.unpack(">H", data[:2])[0]
    out, pos = [], 2
    while pos < 2 + n:
        g, l = struct.unpack(">HH", data[pos:pos + 4]); pos += 4 + l
        out.append(g)
    return out

def cookie_of(exts):
    data = dict(exts).get(44)
    return None if data is None else data[2:]

# the scripted replies: each returns (what the server checked, or None)
def run_mode(mode, sock):
    exts = read_client_hello(sock)
    if mode == "hrr-group-29":
        sock.sendall(hrr(29))
    elif mode == "hrr-group-23":
        sock.sendall(hrr(23))
    elif mode == "hrr-group-25":
        sock.sendall(hrr(25))
    elif mode == "hrr-suite-1305":
        sock.sendall(hrr(24, suite=0x1305))
    elif mode == "hrr-twice":
        sock.sendall(hrr(24))
        exts2 = read_client_hello(sock)
        sock.sendall(hrr(24))
        return "second hello offers %s" % shares(exts2)
    elif mode == "sh-group-24":
        sock.sendall(server_hello(24))
    elif mode == "hrr-cookie":
        sock.sendall(hrr(24, cookie=COOKIE))
        exts2 = read_client_hello(sock)
        ok = cookie_of(exts2) == COOKIE and shares(exts2) == [24]
        return "cookie echoed: %s" % ok
    else:
        raise ValueError(mode)
    return None

def serve(mode, port, result):
    srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    srv.bind(("127.0.0.1", port))
    srv.listen(1)
    srv.settimeout(120)
    try:
        conn, _ = srv.accept()
        conn.settimeout(60)
        with conn:
            result["seen"] = run_mode(mode, conn)
    except Exception as e:  # reported with the result, the client's exit is what counts
        result["error"] = repr(e)
    finally:
        srv.close()

MODES = {
    "hrr-group-29": ("not a ServerHello", None),
    "hrr-group-23": ("not a ServerHello", None),
    "hrr-group-25": ("not a ServerHello", None),
    "hrr-suite-1305": ("not a ServerHello", None),
    "hrr-twice": ("not a ServerHello", None),
    "sh-group-24": ("not a ServerHello", None),
    "hrr-cookie": (None, "cookie echoed: True"),
}

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "js"
    tmp = tempfile.mkdtemp()
    anchor = os.path.join(tmp, "root.der")
    subprocess.run([sys.executable, "-I", os.path.join(HERE, "mkpki.py"), tmp, "rsa"],
                   check=True, stdout=subprocess.DEVNULL)
    if which == "native":
        exe = os.path.join(tmp, "client")
        subprocess.run(["bend", "client.bend", "-o", exe], cwd=ROOT, check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=580)
        run = [exe]
    else:
        run = ["bend", "client.bend"]
    passed = failed = 0
    base = 4460
    for i, (mode, (want_msg, want_seen)) in enumerate(MODES.items()):
        port = base + i
        result = {}
        t = threading.Thread(target=serve, args=(mode, port, result))
        t.start()
        time.sleep(0.5)
        cmd = run + ["example.test", "127.0.0.1", str(port), anchor, str(int(time.time()))]
        try:
            p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=300)
            code, text = p.returncode, p.stdout + p.stderr
        except subprocess.TimeoutExpired:
            code, text = None, "timeout"
        t.join(timeout=130)
        ok = code == 1 and (want_msg is None or want_msg in text)
        if want_seen is not None:
            ok = ok and result.get("seen") == want_seen
        if ok:
            passed += 1
            print("PASS %s: refused (exit 1)%s" % (mode, "; " + result["seen"] if want_seen else ""))
        else:
            failed += 1
            print("FAIL %s: exit %s, server saw %r, error %r" % (mode, code, result.get("seen"), result.get("error")))
            print("  " + text.strip().replace("\n", "\n  ")[:400])
    shutil.rmtree(tmp, ignore_errors=True)
    print("rejects (%s): %d passed, %d failed" % (which, passed, failed))
    return 0 if failed == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
