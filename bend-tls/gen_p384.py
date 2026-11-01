# Writes p384.bend: NIST P-384 (secp384r1) for ECDSA verification. It is p256.bend
# with the sizes changed: 24 limbs of 16 bits (the field is 384 bits), a Montgomery
# factor of 2^384, 48-byte coordinates, and no ECDH. The text of p256_body.bend is the
# source; every size-dependent literal is replaced with a counted replacement, so a
# change in the source that the replacements do not expect stops the generator.
# The P-384 constants are checked first: the curve equation, the order n (n G is the
# point at infinity, by this file's own affine arithmetic), and the generator and k G
# against the cryptography package.
#   python3 -I gen_p384.py
from cryptography.hazmat.primitives.asymmetric import ec

P = 2 ** 384 - 2 ** 128 - 2 ** 96 + 2 ** 32 - 1
N = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
B = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
GX = 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
GY = 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f

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

G = (GX, GY)
assert (GY * GY - (GX ** 3 - 3 * GX + B)) % P == 0, "G is not on the P-384 curve"
assert mul(N, G) is None, "n G is not the point at infinity"
gen_pub = ec.derive_private_key(1, ec.SECP384R1()).public_key().public_numbers()
assert (gen_pub.x, gen_pub.y) == G, "the generator differs from cryptography"
k = 0x1f2e3d4c5b6a79887a6b5c4d3e2f1a0b9c8d7e6f5a4b3c2d1e0f1a2b3c4d5e6f7a8b9c0d1e2f3a4b5c6d
kp = ec.derive_private_key(k, ec.SECP384R1()).public_key().public_numbers()
assert (kp.x, kp.y) == mul(k, G), "kG differs from cryptography"

L = 24                 # limbs of the field
W = L + 2              # the lists carry two spare limbs
R = 1 << (16 * L)      # the Montgomery factor

def limbs(x, count=W):
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
assert (scalars["P0"] * P + 1) % 65536 == 0 and (scalars["N0"] * N + 1) % 65536 == 0
block = "\n".join([f"def p384.{name}() -> List<&2, Nat>:\n  {lit}\n" for name, lit in consts.items()]
                  + [f"def p384.{name}() -> Nat:\n  {v}n\n" for name, v in scalars.items()])

src = open("p256_body.bend").read()

# the ECDH section goes: P-384 is needed for verification only
start = src.index("# ECDH (SEC 1 3.3.1)")
end = src.index("# ECDSA verification (FIPS 186-4 6.4)")
src = src[:start] + src[end:]

def rep(old, new, count):
    global src
    found = src.count(old)
    assert found == count, f"expected {count} of {old!r}, found {found}"
    src = src.replace(old, new)

rep("p256.bend: NIST P-256 (secp256r1) for ECDSA verification with SHA-256.",
    "p384.bend: NIST P-384 (secp384r1) for ECDSA verification. Generated from p256_body.bend by gen_p384.py.", 1)
rep("p256.bend is generated: python3 -I gen_p256.py", "p384.bend is generated: python3 -I gen_p384.py", 1)
rep("The constants come from gen_p256.py, which checks them against cryptography.",
    "The constants come from gen_p384.py, which checks them against cryptography.", 1)
rep("P0(), 16n)", "P0(), 24n)", 3)
rep("N0(), 16n)", "N0(), 24n)", 1)
rep("zeros(17n)", "zeros(25n)", 1)
rep("zeros(18n)", "zeros(26n)", 1)
rep("k, 16n))", "k, 24n))", 1)
rep("p256.bytes.le(x), 32n)", "p256.bytes.le(x), 48n)", 1)
rep("Nat.is_eq(List.length(&2, U32, qx), 32n), Nat.is_eq(List.length(&2, U32, qy), 32n)",
    "Nat.is_eq(List.length(&2, U32, qx), 48n), Nat.is_eq(List.length(&2, U32, qy), 48n)", 1)
rep("Nat.is_eq(List.length(&2, U32, e), 32n), Nat.is_eq(List.length(&2, U32, r), 32n)",
    "Nat.is_le(List.length(&2, U32, e), 48n), Nat.is_eq(List.length(&2, U32, r), 48n)", 1)
rep("Nat.is_eq(List.length(&2, U32, s), 32n)", "Nat.is_eq(List.length(&2, U32, s), 48n)", 1)
rep("p256.reduce_n(p256.limbs(e))", "p256.reduce_n(p256.limbs(p256.lpad(e)))", 1)
rep("# the signature (r, s) on the digest e under the public key (qx, qy); all big-endian\n",
    "# the digest e is at most 48 bytes (SHA-384, or SHA-256 on a P-384 key): it is left-padded to 48\n"
    "# bytes, which keeps its integer value\n"
    "def p256.lpad(+e: List<&2, U32>) -> List<&2, U32>:\n"
    "  List.append(&2, U32, p256.zero32(Nat.sub(48n, List.length(&2, U32, e))), e)\n\n"
    "def p256.zero32(n: Nat) -> List<&2, U32>:\n"
    "  match n:\n"
    "    case 0n:\n"
    "      Nil{}\n"
    "    case 1n+p:\n"
    "      0 <> p256.zero32(p)\n\n"
    "# the signature (r, s) on the digest e under the public key (qx, qy); all big-endian\n", 1)
rep("#@@CONST@@", block, 1)
body = src.replace("p256.", "p384.")
open("p384.bend", "w").write(body)
print("p384.bend: constants checked (curve, order n, generator, kG); sizes 24 limbs / 48 bytes")
