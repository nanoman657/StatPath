# Writes fuzz_tls_tests.bend: robustness of the record layer and the message parsers on
# mutated input. A sealed record (both suites) is mutated: every mutation must fail to
# open, and the valid record must open (controls). ServerHello and Certificate bodies
# are mutated: the parsers must return values, not fault the runtime.
#   python3 -I gen_fuzz_tls_tests.py
import random
from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def vec(n, b):
    return len(b).to_bytes(n, "big") + b

rng = random.Random(8446 + 1)

def mutate(b):
    b = bytearray(b)
    op = rng.randrange(5)
    if op == 0:
        for _ in range(rng.randrange(1, 4)):
            b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    elif op == 1:
        b = b[:rng.randrange(len(b))]
    elif op == 2:
        b.insert(rng.randrange(len(b) + 1), rng.randrange(256))
    elif op == 3:
        i = rng.randrange(len(b)); j = min(len(b), i + rng.randrange(1, 40))
        b[i:i] = b[i:j]
    else:
        b[rng.randrange(len(b))] = rng.choice([0, 255, 0x80, 0x7f, 0x30])
    return bytes(b)

def mutated(b):
    m = mutate(b)
    while m == b:
        m = mutate(b)
    return m

def record(aead, key, iv, seq, ctype, pt):
    nonce = bytes(a ^ b for a, b in zip(iv, b"\x00" * 4 + seq.to_bytes(8, "big")))
    inner = pt + bytes([ctype])
    hdr = b"\x17\x03\x03" + (len(inner) + 16).to_bytes(2, "big")
    return hdr + aead(key).encrypt(nonce, inner, hdr), nonce

out = []
def boolcase(name, expr, want):
    out.append(f'  kcase("{name}", Bool.show({expr}), "{want}") <>')

# records: each suite, a valid record (control) and mutations of it
for suite, aead, klen, alg in [("aes", AESGCM, 16, 4865), ("aes256", AESGCM, 32, 4866), ("chacha", ChaCha20Poly1305, 32, 4867)]:
    for i in range(30):
        key = bytes(rng.randrange(256) for _ in range(klen))
        iv = bytes(rng.randrange(256) for _ in range(12))
        seq = rng.randrange(1000)
        pt = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 80)))
        rec, _ = record(aead, key, iv, seq, 22, pt)
        if i < 2:
            boolcase(f"record-{suite}-control-{i}",
                     f"is_some(H.hs.open({alg}n, {lst(list(key))}, {lst(list(iv))}, {seq}n, {lst(list(rec))}))", "True")
        boolcase(f"record-{suite}-mutated-{i}",
                 f"is_some(H.hs.open({alg}n, {lst(list(key))}, {lst(list(iv))}, {seq}n, {lst(list(mutated(rec)))}))", "False")

# ServerHello bodies: the parsers return values (bounded), whatever the bytes
def server_hello():
    rnd = bytes(rng.randrange(256) for _ in range(32))
    pub = bytes(rng.randrange(256) for _ in range(32))
    exts = b"\x00\x2b" + vec(2, bytes([3, 4])) + b"\x00\x33" + vec(2, b"\x00\x1d" + vec(2, pub))
    return b"\x03\x03" + rnd + b"\x00" + b"\x13\x01" + b"\x00" + vec(2, exts)

sh = server_hello()
for i in range(40):
    m = mutated(sh)
    hs_msg = b"\x02" + len(m).to_bytes(3, "big") + m
    boolcase(f"server-hello-{i}",
             f"Nat.is_le(List.length(&2, U32, T.tls.sh.key(body_of(T.tls.hm({lst(list(hs_msg))})))), 100000n)",
             "True")

# Certificate bodies: the entry list parses to a bounded number of entries
def cert_body():
    cert = bytes(rng.randrange(256) for _ in range(120))
    entries = vec(3, cert) + b"\x00\x00"
    return b"\x00" + vec(3, entries)

cb = cert_body()
for i in range(40):
    m = mutated(cb)
    boolcase(f"certificates-{i}",
             f"Nat.is_le(List.length(&2, List<&2, U32>, T.tls.certs({lst(list(m))})), 100000n)", "True")

# garbage keys and signatures of the right lengths: random bytes, which are almost never at
# or past a field prime, so the boundary values are added explicitly below. None of these is
# a valid signature, so each verifies False.
def rb(n):
    return bytes(rng.randrange(256) for _ in range(n))
def lstb(b):
    return lst(list(b))
P256 = 2 ** 256 - 2 ** 224 + 2 ** 192 + 2 ** 96 - 1
P384 = 2 ** 384 - 2 ** 128 - 2 ** 96 + 2 ** 32 - 1
ED_P = 2 ** 255 - 19
ED_L = 2 ** 252 + 27742317777372353535851937790883648493
for i in range(30):
    qx, qy, e, r, s = rb(32), rb(32), rb(32), rb(32), rb(32)
    boolcase(f"garbage-p256-{i}", f"P.p256.verify({lstb(qx)}, {lstb(qy)}, {lstb(e)}, {lstb(r)}, {lstb(s)})", "False")
for i in range(30):
    qx, qy, e, r, s = rb(48), rb(48), rb(48), rb(48), rb(48)
    boolcase(f"garbage-p384-{i}", f"Q.p384.verify({lstb(qx)}, {lstb(qy)}, {lstb(e)}, {lstb(r)}, {lstb(s)})", "False")
for i in range(30):
    pk, msg, sig = rb(32), rb(rng.randrange(0, 60)), rb(64)
    boolcase(f"garbage-ed25519-{i}", f"ED.ed.verify({lstb(pk)}, {lstb(msg)}, {lstb(sig)})", "False")

# boundary values: the prime, the prime plus one, and all ones, in each position of the
# P-256 and P-384 verifiers (one position at a time, the rest random)
for name, fn, n, p in [("p256", "P.p256.verify", 32, P256), ("p384", "Q.p384.verify", 48, P384)]:
    for i, v in enumerate([p, p + 1, 2 ** (8 * n) - 1]):
        b = v.to_bytes(n, "big")
        boolcase(f"edge-{name}-qx-{i}", f"{fn}({lstb(b)}, {lstb(rb(n))}, {lstb(rb(n))}, {lstb(rb(n))}, {lstb(rb(n))})", "False")
        boolcase(f"edge-{name}-qy-{i}", f"{fn}({lstb(rb(n))}, {lstb(b)}, {lstb(rb(n))}, {lstb(rb(n))}, {lstb(rb(n))})", "False")
        boolcase(f"edge-{name}-r-{i}", f"{fn}({lstb(rb(n))}, {lstb(rb(n))}, {lstb(rb(n))}, {lstb(b)}, {lstb(rb(n))})", "False")
        boolcase(f"edge-{name}-s-{i}", f"{fn}({lstb(rb(n))}, {lstb(rb(n))}, {lstb(rb(n))}, {lstb(rb(n))}, {lstb(b)})", "False")

# Ed25519 public keys with y at or past the prime (non-canonical encodings), either sign bit
for i, y in enumerate([ED_P, ED_P + 1, 2 ** 255 - 1]):
    for sign in [0, 1]:
        enc = (y | (sign << 255)).to_bytes(32, "little")
        boolcase(f"edge-ed25519-y-{i}-sign{sign}", f"ED.ed.verify({lstb(enc)}, {lstb(rb(8))}, {lstb(rb(64))})", "False")

# Ed25519 malleability: a valid signature with S replaced by S + L (the same point, not reduced)
# must be refused, and the valid signature must still verify (control)
from cryptography.hazmat.primitives import serialization as ser
from cryptography.hazmat.primitives.asymmetric import ed25519 as ced
sk = ced.Ed25519PrivateKey.generate()
pk = sk.public_key().public_bytes(ser.Encoding.Raw, ser.PublicFormat.Raw)
msg = b"malleability"
sig = sk.sign(msg)
s_plus_l = sig[:32] + (int.from_bytes(sig[32:], "little") + ED_L).to_bytes(32, "little")
boolcase("ed25519-valid-control", f"ED.ed.verify({lstb(pk)}, {lstb(msg)}, {lstb(sig)})", "True")
boolcase("ed25519-s-plus-L", f"ED.ed.verify({lstb(pk)}, {lstb(msg)}, {lstb(s_plus_l)})", "False")

# The cases are split into groups of GROUP: one function holding all of them trips the native
# compiler's arity limit (247).
GROUP = 40
chunks = [out[i:i + GROUP] for i in range(0, len(out), GROUP)]
groups_src = ""
for g, lines_g in enumerate(chunks):
    groups_src += f"def cases.g{g}() -> List<&2, Case>:\n" + "\n".join(lines_g) + "\n  Nil{}\n\n"
chain = f"cases.g{len(chunks) - 1}()"
for g in reversed(range(len(chunks) - 1)):
    chain = f"List.append(&2, Case, cases.g{g}(), {chain})"
groups_src += f"def cases() -> List<&2, Case>:\n  {chain}\n\n"

src = r'''# fuzz_tls_tests.bend: mutated records and messages (generated by gen_fuzz_tls_tests.py).
#   bend fuzz_tls_tests.bend

import Base
import ./handshake.bend as H
import ./tls.bend as T
import ./hkdf.bend as K
import ./p256.bend as P
import ./p384.bend as Q
import ./ed25519.bend as ED

type Case is Data:
  Case{name: String, got: String, want: String}

def kcase(name: String, +got: String, want: String) -> Case:
  Case{name, got, want}

def is_some(+m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case Some{+p}:
      True{}
    case None{}:
      False{}

def body_of(+m: T.HM) -> List<&2, U32>:
  match m:
    case T.HM{+t, +b, +r}:
      b

''' + groups_src + r'''def fails.at(+c: Case, +rest: List<&2, String>) -> List<&2, String>:
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
    IO.print("fuzz-tls: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("fuzz_tls_tests.bend", "w").write(src)
print(len(out), "cases")
