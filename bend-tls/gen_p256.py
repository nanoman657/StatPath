# Writes p256.bend from p256_body.bend: the constants of NIST P-256 (secp256r1)
# as 18-limb lists of 16-bit limbs (little-endian), and the Montgomery values
# derived from them (R = 2^256). Each constant is checked first: the curve
# parameters against the cryptography package (the generator point and 2G) and
# against this file's own affine arithmetic (n G = infinity, G on the curve).
#   python3 -I gen_p256.py
from cryptography.hazmat.primitives.asymmetric import ec

P = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
N = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
B = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
GX = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
GY = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

def add(p1, p2):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    (x1, y1), (x2, y2) = p1, p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if p1 == p2:
        lam = (3 * x1 * x1 - 3) * pow(2 * y1, -1, P) % P
    else:
        lam = (y2 - y1) * pow(x2 - x1, -1, P) % P
    x3 = (lam * lam - x1 - x2) % P
    return (x3, (lam * (x1 - x3) - y1) % P)

def mul(k, pt):
    acc, base = None, pt
    while k:
        if k & 1:
            acc = add(acc, base)
        base = add(base, base)
        k >>= 1
    return acc

# the checks
G = (GX, GY)
assert (GY * GY - (GX ** 3 - 3 * GX + B)) % P == 0, "G is not on the curve"
assert mul(N, G) is None, "n G is not the point at infinity"
gen_pub = ec.derive_private_key(1, ec.SECP256R1()).public_key().public_numbers()
assert (gen_pub.x, gen_pub.y) == G, "generator differs from cryptography"
two = ec.derive_private_key(2, ec.SECP256R1()).public_key().public_numbers()
assert (two.x, two.y) == mul(2, G), "2G differs from cryptography"
k = 0x1f2e3d4c5b6a7988796a5b4c3d2e1f00
kp = ec.derive_private_key(k, ec.SECP256R1()).public_key().public_numbers()
assert (kp.x, kp.y) == mul(k, G), "kG differs from cryptography"

R = 1 << 256
def limbs(x, count=18):
    assert x < (1 << (16 * count))
    return [(x >> (16 * i)) & 0xffff for i in range(count)]

def n0(m):
    return (-pow(m, -1, 65536)) % 65536

def bend_list(xs):
    return "[" + ", ".join(f"{v}n" for v in xs) + "]"

consts = {
    "P": bend_list(limbs(P)),
    "N": bend_list(limbs(N)),
    "NM2": bend_list(limbs(N - 2)),
    "PM2": bend_list(limbs(P - 2)),
    "BM": bend_list(limbs(B * R % P)),
    "GXM": bend_list(limbs(GX * R % P)),
    "GYM": bend_list(limbs(GY * R % P)),
    "R2P": bend_list(limbs(R * R % P)),
    "R2N": bend_list(limbs(R * R % N)),
    "ONE_P": bend_list(limbs(R % P)),
    "ONE_N": bend_list(limbs(R % N)),
}
scalars = {"P0": n0(P), "N0": n0(N)}
# the Montgomery identities the code relies on
assert (scalars["P0"] * P + 1) % 65536 == 0 and (scalars["N0"] * N + 1) % 65536 == 0

lines = []
for name, lit in consts.items():
    lines.append(f"def p256.{name}() -> List<&2, Nat>:\n  {lit}\n")
for name, v in scalars.items():
    lines.append(f"def p256.{name}() -> Nat:\n  {v}n\n")
block = "\n".join(lines)

body = open("p256_body.bend").read()
assert body.count("#@@CONST@@") == 1
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from bendsort import sort_defs
# the compiler needs each definition after the ones it uses: sort as sortfile.py does
open("p256.bend", "w").write(sort_defs(body.replace("#@@CONST@@", block)))
print("p256.bend: constants checked (curve, generator, 2G, kG, nG = infinity)")
