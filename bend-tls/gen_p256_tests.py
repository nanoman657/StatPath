# Writes p256_tests.bend: P-256 field arithmetic, scalar multiplication and ECDSA
# verification with SHA-256. Expected values come from the cryptography package;
# the curve parameters are checked in gen_p256.py.
#   python3 -I gen_p256_tests.py
import hashlib
import random
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature

P = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def be(x, n=32):
    return x.to_bytes(n, "big")

rng = random.Random(256)
def rnd_below(m):
    return rng.randrange(m)

out = []
def kc(name, expr, want):
    out.append(f'  kcase("{name}", {expr}, "{want}") <>')

def boolcase(name, expr, want):
    out.append(f'  kcase("{name}", Bool.show({expr}), "{want}") <>')

def hexof(expr):
    return f"S.hex_of({expr})"

# Field arithmetic: operands in Montgomery form, results read back
def fe(expr):
    return f"P.p256.bytes_be(P.p256.fromm({expr}))"
def tm(x):
    return f"P.p256.tom(P.p256.limbs({lst(be(x))}))"

cases_fe = [(0, 0), (1, 1), (P - 1, P - 1), (P - 1, 2)] + [(rnd_below(P), rnd_below(P)) for _ in range(4)]
for i, (a, b) in enumerate(cases_fe):
    kc(f"fe-mul-{i}", hexof(fe(f"P.p256.mul({tm(a)}, {tm(b)})")), be(a * b % P).hex())
    kc(f"fe-add-{i}", hexof(fe(f"P.p256.add({tm(a)}, {tm(b)})")), be((a + b) % P).hex())
    kc(f"fe-sub-{i}", hexof(fe(f"P.p256.sub({tm(a)}, {tm(b)})")), be((a - b) % P).hex())

# Points: k G for small and random k, and (n - 1) G = -G
G = ec.derive_private_key(1, ec.SECP256R1()).public_key().public_numbers()
def kG_bytes(k):
    pub = ec.derive_private_key(k, ec.SECP256R1()).public_key().public_numbers()
    return be(pub.x) + be(pub.y)
for i, k in enumerate([1, 2, 3, 7, 0xdeadbeef, rnd_below(N - 1) + 1]):
    kc(f"kG-{i}", hexof(f"P.p256.base_mul({lst(be(k))})"), kG_bytes(k).hex())
negG = be(G.x) + be(P - G.y)
kc("kG-minus-G", hexof(f"P.p256.base_mul({lst(be(N - 1))})"), negG.hex())

# ECDH: the shared x coordinate, against cryptography's exchange
for i, (dk, dk2) in enumerate([(0x1234, 0xabcdef), (rnd_below(N - 2) + 1, rnd_below(N - 2) + 1)]):
    a = ec.derive_private_key(dk, ec.SECP256R1())
    b = ec.derive_private_key(dk2, ec.SECP256R1())
    pb = b.public_key().public_numbers()
    shared = a.exchange(ec.ECDH(), b.public_key())
    kc(f"ecdh-{i}", hexof(f"P.p256.ecdh({lst(be(dk))}, {lst(be(pb.x))}, {lst(be(pb.y))})"), shared.hex())
# a peer point off the curve, and a zero scalar, give no secret
boolcase("ecdh-off-curve-empty",
         f"Nat.is_eq(List.length(&2, U32, P.p256.ecdh({lst(be(0x1234))}, {lst(be(pb.x))}, {lst(be(pb.y + 1))})), 0n)",
         "True")
boolcase("ecdh-zero-scalar-empty",
         f"Nat.is_eq(List.length(&2, U32, P.p256.ecdh({lst(be(0))}, {lst(be(pb.x))}, {lst(be(pb.y))})), 0n)",
         "True")
# the private scalar keeps its low 255 bits: the top bit of the first byte is cleared
kc("scalar-clamp", hexof(f"P.p256.scalar({lst([0xff] * 32)})"), bytes([0x7f] + [0xff] * 31).hex())

# ECDSA verification: signatures from cryptography, checked against the digest
def signed(seed):
    priv = ec.derive_private_key(seed, ec.SECP256R1())
    pub = priv.public_key().public_numbers()
    msg = f"message {seed}".encode() * (seed % 3 + 1)
    r, s = decode_dss_signature(priv.sign(msg, ec.ECDSA(hashes.SHA256())))
    e = hashlib.sha256(msg).digest()
    return dict(qx=be(pub.x), qy=be(pub.y), e=e, r=be(r), s=be(s), r_int=r, s_int=s, msg=msg)

sigs = [signed(s) for s in [0x1234567, 0x9abcdef012, rnd_below(N - 2) + 1, 0xfedcba987654321]]
def verify_expr(qx, qy, e, r, s):
    return f"P.p256.verify({lst(qx)}, {lst(qy)}, {lst(e)}, {lst(r)}, {lst(s)})"

for i, d in enumerate(sigs):
    boolcase(f"ecdsa-valid-{i}", verify_expr(d["qx"], d["qy"], d["e"], d["r"], d["s"]), "True")
d = sigs[0]
# the same signature with s replaced by n - s is also valid (ECDSA has no low-s rule)
boolcase("ecdsa-s-negated", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(N - d["s_int"])), "True")
other = sigs[1]
bad_e = bytes([d["e"][0] ^ 1]) + d["e"][1:]
boolcase("ecdsa-other-message", verify_expr(d["qx"], d["qy"], bad_e, d["r"], d["s"]), "False")
boolcase("ecdsa-r-plus-one", verify_expr(d["qx"], d["qy"], d["e"], be(d["r_int"] + 1), d["s"]), "False")
boolcase("ecdsa-s-plus-one", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(d["s_int"] + 1)), "False")
boolcase("ecdsa-r-zero", verify_expr(d["qx"], d["qy"], d["e"], be(0), d["s"]), "False")
boolcase("ecdsa-s-zero", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(0)), "False")
boolcase("ecdsa-r-is-n", verify_expr(d["qx"], d["qy"], d["e"], be(N), d["s"]), "False")
boolcase("ecdsa-s-is-n", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(N)), "False")
boolcase("ecdsa-wrong-key", verify_expr(other["qx"], other["qy"], d["e"], d["r"], d["s"]), "False")
boolcase("ecdsa-q-off-curve", verify_expr(d["qx"], be(int.from_bytes(d["qy"], "big") + 1), d["e"], d["r"], d["s"]), "False")
# the signature of the other message, with its own key and digest, is valid
boolcase("ecdsa-other-valid", verify_expr(other["qx"], other["qy"], other["e"], other["r"], other["s"]), "True")

src = r'''# p256_tests.bend: P-256 field arithmetic, k G, and ECDSA with SHA-256 (generated
# by gen_p256_tests.py). Expected values come from the cryptography package.
#   bend p256_tests.bend

import Base
import ./sha256.bend as S
import ./p256.bend as P

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
    IO.print("p256: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("p256_tests.bend", "w").write(src)
print(len(out), "cases")
