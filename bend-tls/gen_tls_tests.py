# Writes tls_tests.bend: the TLS 1.3 client encodings against independent Python
# encodings of RFC 8446 (ClientHello) and the record layer against the
# cryptography package's ChaCha20-Poly1305 (nonce and header construction).
#   python3 -I gen_tls_tests.py
import random, struct
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def vec(n, b):
    return len(b).to_bytes(n, "big") + b

def share(group, key):
    return bytes([0, group]) + vec(2, key)

def client_hello(rnd, entries, host, cookie=b""):
    host = host.encode()
    exts = b""
    exts += b"\x00\x2b" + vec(2, bytes([2, 3, 4]))                                    # supported_versions
    exts += b"\x00\x0a" + vec(2, vec(2, b"\x00\x1d\x00\x17\x00\x18"))               # supported_groups: x25519, secp256r1, secp384r1
    exts += b"\x00\x0d" + vec(2, vec(2, b"\x08\x04\x04\x01\x04\x03\x08\x07\x05\x03"))  # signature_algorithms
    exts += b"\x00\x33" + vec(2, vec(2, entries))                                     # key_share
    exts += b"\x00\x00" + vec(2, vec(2, b"\x00" + vec(2, host)))                      # server_name
    if cookie:
        exts += b"\x00\x2c" + vec(2, vec(2, cookie))                                  # cookie
    body = (b"\x03\x03" + rnd + b"\x00" + vec(2, b"\x13\x01\x13\x03") + b"\x01\x00" + vec(2, exts))
    return b"\x01" + len(body).to_bytes(3, "big") + body

def nonce(iv, seq):
    x = b"\x00" * 4 + seq.to_bytes(8, "big")
    return bytes(a ^ b for a, b in zip(iv, x))

def seal(key, iv, seq, ctype, pt):
    inner = pt + bytes([ctype])
    hdr = b"\x17\x03\x03" + (len(inner) + 16).to_bytes(2, "big")
    return hdr + ChaCha20Poly1305(key).encrypt(nonce(iv, seq), inner, hdr)

rng = random.Random(8446)
def rb(n):
    return bytes(rng.randrange(256) for _ in range(n))

out = []
for i, host in enumerate(["example.test", "a.b", "www.example.test"]):
    rnd, pub, pubp, pubq = rb(32), rb(32), b"\x04" + rb(64), b"\x04" + rb(96)
    # the first ClientHello: x25519 and secp256r1 key shares, no cookie
    out.append(f'  kcase("clienthello-{i}", S.hex_of(T.tls.client_hello({lst(rnd)}, T.tls.cat(T.tls.share(29, {lst(pub)}), T.tls.share(23, {lst(pubp)})), {lst(host.encode())}, Nil{{}})), "{client_hello(rnd, share(29, pub) + share(23, pubp), host, b'').hex()}") <>')
    # the second ClientHello after a HelloRetryRequest: the secp384r1 share and a cookie
    cookie = rb(8)
    out.append(f'  kcase("clienthello-retry-{i}", S.hex_of(T.tls.client_hello({lst(rnd)}, T.tls.share(24, {lst(pubq)}), {lst(host.encode())}, {lst(cookie)})), "{client_hello(rnd, share(24, pubq), host, cookie).hex()}") <>')
for i, (pt_len, seq, ctype) in enumerate([(0, 0, 22), (5, 0, 23), (40, 7, 22), (300, 65536, 23)]):
    key, iv, pt = rb(32), rb(12), rb(pt_len)
    out.append(f'  kcase("seal-{i}", S.hex_of(T.tls.seal({lst(key)}, {lst(iv)}, {seq}n, {ctype}, {lst(pt)})), "{seal(key, iv, seq, ctype, pt).hex()}") <>')
for i, seq in enumerate([0, 1, 255, 256, 2**31 + 5]):
    iv = rb(12)
    out.append(f'  kcase("nonce-{i}", S.hex_of(T.tls.nonce({lst(iv)}, {seq}n)), "{nonce(iv, seq).hex()}") <>')


# server messages (RFC 8446 section 4.1.3 and 4.4.2), built here and parsed by Bend
def hs(t, body):
    return bytes([t]) + len(body).to_bytes(3, "big") + body

def server_hello(rnd, pub, sid=b"", group=0x1d):
    exts = b"\x00\x2b" + vec(2, bytes([3, 4])) + b"\x00\x33" + vec(2, group.to_bytes(2, "big") + vec(2, pub))
    body = b"\x03\x03" + rnd + bytes([len(sid)]) + sid + b"\x13\x03" + b"\x00" + vec(2, exts)
    return hs(2, body)

def certificate(certs):
    entries = b"".join(vec(3, c) + b"\x00\x00" for c in certs)
    return hs(11, b"\x00" + vec(3, entries))

sh_rnd, sh_pub = rb(32), rb(32)
sh = server_hello(sh_rnd, sh_pub)
sh256_pub = b"\x04" + rb(64)
sh256 = server_hello(sh_rnd, sh256_pub, group=0x17)
sh384_pub = b"\x04" + rb(96)
sh384 = server_hello(sh_rnd, sh384_pub, group=0x18)
cert_a, cert_b = rb(300), rb(120)
cert_msg = certificate([cert_a, cert_b])
fin_msg = hs(20, rb(32))
# HelloRetryRequest (RFC 8446 4.1.4): its random is the SHA-256 of "HelloRetryRequest"; it
# selects a group in key_share (2 bytes only) and may carry a cookie
import hashlib as _hl
HRR_RANDOM = _hl.sha256(b"HelloRetryRequest").digest()
hrr_cookie = rb(8)
hrr_exts = b"\x00\x2b" + vec(2, bytes([3, 4])) + b"\x00\x33" + vec(2, b"\x00\x18")
hrr_msg = hs(2, b"\x03\x03" + HRR_RANDOM + b"\x00" + b"\x13\x01" + b"\x00" + vec(2, hrr_exts))
hrr_cookie_msg = hs(2, b"\x03\x03" + HRR_RANDOM + b"\x00" + b"\x13\x01" + b"\x00"
                    + vec(2, hrr_exts + b"\x00\x2c" + vec(2, vec(2, hrr_cookie))))
share_key = rb(40)
out += [
    f'  kcase("hrr-random", S.hex_of(T.tls.hrr_random()), "{HRR_RANDOM.hex()}") <>',
    f'  kcase("hrr-sh-random", S.hex_of(T.tls.sh.random(hm_body(T.tls.hm({lst(hrr_msg)})))), "{HRR_RANDOM.hex()}") <>',
    f'  kcase("hrr-group-24", Nat.show(T.tls.sh.group(hm_body(T.tls.hm({lst(hrr_msg)})))), "24") <>',
    f'  kcase("hrr-cookie", S.hex_of(List.drop(&2, U32, T.tls.ext(T.tls.sh.exts(hm_body(T.tls.hm({lst(hrr_cookie_msg)}))), 44n), 2n)), "{hrr_cookie.hex()}") <>',
    f'  kcase("hrr-no-cookie", Nat.show(List.length(&2, U32, T.tls.ext(T.tls.sh.exts(hm_body(T.tls.hm({lst(hrr_msg)}))), 44n))), "0") <>',
    f'  kcase("share-24", S.hex_of(T.tls.share(24, {lst(share_key)})), "{share(24, share_key).hex()}") <>',
]
out += [
    f'  kcase("sh-cipher", Nat.show(T.tls.sh.cipher(hm_body(T.tls.hm({lst(sh)})))), "4867") <>',
    f'  kcase("sh-key", S.hex_of(T.tls.sh.key(hm_body(T.tls.hm({lst(sh)})))), "{sh_pub.hex()}") <>',
    f'  kcase("sh-group-x25519", Nat.show(T.tls.sh.group(hm_body(T.tls.hm({lst(sh)})))), "29") <>',
    f'  kcase("sh-group-p256", Nat.show(T.tls.sh.group(hm_body(T.tls.hm({lst(sh256)})))), "23") <>',
    f'  kcase("sh-key-p256", S.hex_of(T.tls.sh.key(hm_body(T.tls.hm({lst(sh256)})))), "{sh256_pub.hex()}") <>',
    f'  kcase("sh-group-p384", Nat.show(T.tls.sh.group(hm_body(T.tls.hm({lst(sh384)})))), "24") <>',
    f'  kcase("sh-key-p384", S.hex_of(T.tls.sh.key(hm_body(T.tls.hm({lst(sh384)})))), "{sh384_pub.hex()}") <>',
    f'  kcase("cert-count", Nat.show(List.length(&2, List<&2, U32>, T.tls.certs(hm_body(T.tls.hm({lst(cert_msg)}))))), "2") <>',
    f'  kcase("cert-first", S.hex_of(first(T.tls.certs(hm_body(T.tls.hm({lst(cert_msg)}))))), "{cert_a.hex()}") <>',
    f'  kcase("cert-second", S.hex_of(first(List.drop(&2, List<&2, U32>, T.tls.certs(hm_body(T.tls.hm({lst(cert_msg)}))), 1n))), "{cert_b.hex()}") <>',
    f'  kcase("hm-type-finished", Nat.show(U32.to_nat(hm_type(T.tls.hm({lst(fin_msg)})))), "20") <>',
    f'  kcase("hm-rest-empty", Nat.show(List.length(&2, U32, hm_rest(T.tls.hm({lst(fin_msg)})))), "0") <>',
]

src = '''# tls_tests.bend: TLS 1.3 client encodings (generated by gen_tls_tests.py).
#   bend tls_tests.bend

import Base
import ./sha256.bend as S
import ./tls.bend as T

type Case is Data:
  Case{name: String, got: String, want: String}

def kcase(name: String, +got: String, want: String) -> Case:
  Case{name, got, want}

def first(xs: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case c <> t:
      c

def hm_type(+m: T.HM) -> U32:
  match m:
    case T.HM{t, b, r}:
      t

def hm_body(+m: T.HM) -> List<&2, U32>:
  match m:
    case T.HM{t, b, r}:
      b

def hm_rest(+m: T.HM) -> List<&2, U32>:
  match m:
    case T.HM{t, b, r}:
      r

def cases() -> List<&2, Case>:
''' + "\n".join(out) + '''
  Nil{}

def fails.at(+c: Case, +rest: List<&2, String>) -> List<&2, String>:
  match c:
    case Case{n, +g, +w}:
      Bool.pick(List<&2, String>, String.eq(g, w), rest,
        ("FAIL " ++ n ++ "\\n  got:  " ++ g ++ "\\n  want: " ++ w) <> rest)

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
    IO.print("tls: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("tls_tests.bend", "w").write(src)
print(len(out), "cases")
