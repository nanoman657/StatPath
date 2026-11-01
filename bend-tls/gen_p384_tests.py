# Writes p384_tests.bend: P-384 field arithmetic, k G, and ECDSA verification with
# SHA-384 digests and with SHA-256 digests (padded to 48 bytes). Expected values come
# from the cryptography package.
#   python3 -I gen_p384_tests.py
import hashlib
import random
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature

P = 2 ** 384 - 2 ** 128 - 2 ** 96 + 2 ** 32 - 1
N = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

def lst(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def be(x, n=48):
    return x.to_bytes(n, "big")

rng = random.Random(384)
def rnd_below(m):
    return rng.randrange(m)

out = []
def kc(name, expr, want):
    out.append(f'  kcase("{name}", {expr}, "{want}") <>')

def boolcase(name, expr, want):
    out.append(f'  kcase("{name}", Bool.show({expr}), "{want}") <>')

def hexof(expr):
    return f"S.hex_of({expr})"

def fe(expr):
    return f"P.p384.bytes_be(P.p384.fromm({expr}))"

def tm(x):
    return f"P.p384.tom(P.p384.limbs({lst(be(x))}))"

cases_fe = [(0, 0), (1, 1), (P - 1, P - 1), (P - 1, 2)] + [(rnd_below(P), rnd_below(P)) for _ in range(3)]
for i, (a, b) in enumerate(cases_fe):
    kc(f"fe-mul-{i}", hexof(fe(f"P.p384.mul({tm(a)}, {tm(b)})")), be(a * b % P).hex())
    kc(f"fe-add-{i}", hexof(fe(f"P.p384.add({tm(a)}, {tm(b)})")), be((a + b) % P).hex())
    kc(f"fe-sub-{i}", hexof(fe(f"P.p384.sub({tm(a)}, {tm(b)})")), be((a - b) % P).hex())

# k G, against cryptography, and (n - 1) G = -G
G = ec.derive_private_key(1, ec.SECP384R1()).public_key().public_numbers()
def kG_bytes(k):
    pub = ec.derive_private_key(k, ec.SECP384R1()).public_key().public_numbers()
    return be(pub.x) + be(pub.y)
for i, k in enumerate([1, 2, 7, 0xdeadbeefcafe, rnd_below(N - 1) + 1]):
    kc(f"kG-{i}", hexof(f"P.p384.base_mul({lst(be(k))})"), kG_bytes(k).hex())
kc("kG-minus-G", hexof(f"P.p384.base_mul({lst(be(N - 1))})"), be(G.x).hex() + be(P - G.y).hex())

# ECDH: the shared x coordinate (48 bytes), against cryptography's exchange
for i, dk in enumerate([0x1234, rnd_below(N - 2) + 1]):
    a = ec.derive_private_key(dk, ec.SECP384R1())
    b = ec.derive_private_key(rnd_below(N - 2) + 1, ec.SECP384R1())
    pb = b.public_key().public_numbers()
    shared = a.exchange(ec.ECDH(), b.public_key())
    kc(f"ecdh-{i}", hexof(f"P.p384.ecdh({lst(be(dk))}, {lst(be(pb.x))}, {lst(be(pb.y))})"), shared.hex())
# a peer point off the curve, a zero scalar and a short scalar give no secret
boolcase("ecdh-off-curve-empty",
         f"Nat.is_eq(List.length(&2, U32, P.p384.ecdh({lst(be(0x1234))}, {lst(be(pb.x))}, {lst(be(pb.y + 1))})), 0n)", "True")
boolcase("ecdh-zero-scalar-empty",
         f"Nat.is_eq(List.length(&2, U32, P.p384.ecdh({lst(be(0))}, {lst(be(pb.x))}, {lst(be(pb.y))})), 0n)", "True")
boolcase("ecdh-short-scalar-empty",
         f"Nat.is_eq(List.length(&2, U32, P.p384.ecdh({lst(be(0x1234, 47))}, {lst(be(pb.x))}, {lst(be(pb.y))})), 0n)", "True")
kc("scalar-clamp", hexof(f"P.p384.scalar({lst([0xff] * 48)})"), bytes([0x7f] + [0xff] * 47).hex())

# ECDSA verification: signatures from cryptography, over SHA-384 and SHA-256 digests
def signed(seed, hash_alg):
    priv = ec.derive_private_key(seed, ec.SECP384R1())
    pub = priv.public_key().public_numbers()
    msg = f"message {seed}".encode() * (seed % 3 + 1)
    r, s = decode_dss_signature(priv.sign(msg, ec.ECDSA(hash_alg())))
    digest = (hashlib.sha384 if hash_alg is hashes.SHA384 else hashlib.sha256)(msg).digest()
    return dict(qx=be(pub.x), qy=be(pub.y), e=digest, r=be(r), s=be(s), r_int=r, s_int=s)

sigs = [signed(0x1234567, hashes.SHA384), signed(0x9abcdef012, hashes.SHA384),
        signed(rnd_below(N - 2) + 1, hashes.SHA384), signed(0xfedcba987654321, hashes.SHA256)]

def verify_expr(qx, qy, e, r, s):
    return f"P.p384.verify({lst(qx)}, {lst(qy)}, {lst(e)}, {lst(r)}, {lst(s)})"

for i, d in enumerate(sigs):
    label = "sha384" if len(d["e"]) == 48 else "sha256-padded"
    boolcase(f"ecdsa-{label}-{i}", verify_expr(d["qx"], d["qy"], d["e"], d["r"], d["s"]), "True")
d = sigs[0]
boolcase("ecdsa-s-negated", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(N - d["s_int"])), "True")
other = sigs[1]
bad_e = bytes([d["e"][0] ^ 1]) + d["e"][1:]
boolcase("ecdsa-other-digest", verify_expr(d["qx"], d["qy"], bad_e, d["r"], d["s"]), "False")
boolcase("ecdsa-r-plus-one", verify_expr(d["qx"], d["qy"], d["e"], be(d["r_int"] + 1), d["s"]), "False")
boolcase("ecdsa-s-plus-one", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(d["s_int"] + 1)), "False")
boolcase("ecdsa-r-zero", verify_expr(d["qx"], d["qy"], d["e"], be(0), d["s"]), "False")
boolcase("ecdsa-s-zero", verify_expr(d["qx"], d["qy"], d["e"], d["r"], be(0)), "False")
boolcase("ecdsa-r-is-n", verify_expr(d["qx"], d["qy"], d["e"], be(N), d["s"]), "False")
boolcase("ecdsa-wrong-key", verify_expr(other["qx"], other["qy"], d["e"], d["r"], d["s"]), "False")
boolcase("ecdsa-q-off-curve", verify_expr(d["qx"], be(int.from_bytes(d["qy"], "big") + 1), d["e"], d["r"], d["s"]), "False")
boolcase("ecdsa-other-valid", verify_expr(other["qx"], other["qy"], other["e"], other["r"], other["s"]), "True")

src = r'''# p384_tests.bend: P-384 field arithmetic, k G, ECDH, and ECDSA with SHA-384 and SHA-256
# digests (generated by gen_p384_tests.py). Expected values come from cryptography.
#   bend p384_tests.bend

import Base
import ./sha256.bend as S
import ./p384.bend as P

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
    IO.print("p384: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
open("p384_tests.bend", "w").write(src)
print(len(out), "cases")
