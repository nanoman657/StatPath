# Writes ed25519.bend from ed25519_body.bend: the constants of Ed25519 (RFC 8032),
# checked first with this file's own affine Edwards arithmetic: the base point is on
# the curve and has order L, d and sqrt(-1) satisfy their definitions, and the
# cryptography package signs and verifies with the same parameters.
#   python3 -I gen_ed25519.py
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives import serialization

p = 2 ** 255 - 19
L = 2 ** 252 + 27742317777372353535851937790883648493
d = (-121665 * pow(121666, p - 2, p)) % p
I = pow(2, (p - 1) // 4, p)
assert (I * I + 1) % p == 0, "sqrt(-1) is wrong"

def inv(x):
    return pow(x, p - 2, p)

def recover_x(y, sign):
    u = (y * y - 1) % p
    v = (d * y * y + 1) % p
    x = u * pow(v, 3, p) * pow(u * pow(v, 7, p) % p, (p - 5) // 8, p) % p
    if (v * x * x - u) % p != 0:
        x = x * I % p
    assert (v * x * x - u) % p == 0
    if x & 1 != sign:
        x = (p - x) % p
    return x

def add(P1, P2):
    x1, y1 = P1
    x2, y2 = P2
    x3 = (x1 * y2 + x2 * y1) * inv(1 + d * x1 * x2 * y1 * y2) % p
    y3 = (y1 * y2 + x1 * x2) * inv(1 - d * x1 * x2 * y1 * y2) % p
    return (x3, y3)

def mul(k, P1):
    acc, base = (0, 1), P1
    while k:
        if k & 1:
            acc = add(acc, base)
        base = add(base, base)
        k >>= 1
    return acc

By = 4 * inv(5) % p
Bx = recover_x(By, 0)
B = (Bx, By)
assert (-Bx * Bx + By * By - 1 - d * Bx * Bx * By * By) % p == 0, "base point is not on the curve"
assert mul(L, B) == (0, 1), "the base point does not have order L"
assert Bx == 15112221349535400772501151409588531511454012693041857206046113283949847762202

# cryptography agrees: the public key of a seed is the encoded point a B, where a is
# the clamped low half of SHA-512(seed) (RFC 8032 5.1.5)
import hashlib

def encode(P1):
    x, y = P1
    return (y | ((x & 1) << 255)).to_bytes(32, "little")

seed = bytes(range(32))
pub = ed25519.Ed25519PrivateKey.from_private_bytes(seed).public_key().public_bytes(
    serialization.Encoding.Raw, serialization.PublicFormat.Raw)
h = bytearray(hashlib.sha512(seed).digest()[:32])
h[0] &= 248
h[31] &= 127
h[31] |= 64
a = int.from_bytes(bytes(h), "little")
assert encode(mul(a, B)) == pub, "the public key does not match cryptography"

def le32(x):
    return [(x >> (8 * i)) & 0xff for i in range(32)]

def limbs18(x):
    return [(x >> (16 * i)) & 0xffff for i in range(18)]

def bend_list(xs, suffix="n"):
    return "[" + ", ".join(f"{v}{suffix}" for v in xs) + "]"

sqrt_exp = (p - 5) // 8
sqrt_bits = [int(b) for b in bin(sqrt_exp)[2:]]
consts = {
    "dbytes": bend_list(le32(d)),
    "d2bytes": bend_list(le32(2 * d % p)),
    "ibytes": bend_list(le32(I)),
    "bxbytes": bend_list(le32(Bx)),
    "bybytes": bend_list(le32(By)),
    "lmb": bend_list(limbs18(L)),
    "sqrt_bits": bend_list(sqrt_bits),
}
lines = []
for name, lit in consts.items():
    lines.append(f"def ed.{name}() -> List<&2, Nat>:\n  {lit}\n")
block = "\n".join(lines)

body = open("ed25519_body.bend").read()
assert body.count("#@@CONST@@") == 1
open("ed25519.bend", "w").write(body.replace("#@@CONST@@", block))
print("ed25519.bend: constants checked (base point of order L, d, sqrt(-1))")
