# Writes sha512.bend from sha512_body.bend. The constants of SHA-512 (FIPS 180-4
# 5.3.5 and 4.2.3) are the first 64 bits of the fractional parts of the square
# roots of the first 8 primes (the initial hash value) and the cube roots of the
# first 80 primes (the round constants), computed here with exact integer roots.
# Each word is written as the two 32-bit halves of its value. The constants are
# checked against hashlib before anything is written.
#   python3 -I gen_sha512.py
import hashlib
import sys

def primes(count):
    out, n = [], 2
    while len(out) < count:
        if all(n % p for p in out if p * p <= n):
            out.append(n)
        n += 1
    return out

def icbrt(n):
    lo, hi = 0, 1 << ((n.bit_length() + 2) // 3 + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** 3 <= n:
            lo = mid
        else:
            hi = mid - 1
    return lo

from math import isqrt

P80 = primes(80)
IV = [isqrt(p << 128) & ((1 << 64) - 1) for p in P80[:8]]
# SHA-384's initial value: the square roots of the ninth to sixteenth primes
IV384 = [isqrt(p << 128) & ((1 << 64) - 1) for p in P80[8:16]]
K = [icbrt(p << 192) & ((1 << 64) - 1) for p in P80]

# the check: a plain SHA-512 over these constants agrees with hashlib
def ref_sha512(msg, start=None):
    def rotr(x, n):
        return ((x >> n) | (x << (64 - n))) & ((1 << 64) - 1)
    M = (1 << 64) - 1
    m = msg + b"\x80"
    m += b"\x00" * ((112 - len(m) % 128) % 128)
    m += (8 * len(msg)).to_bytes(16, "big")
    h = list(IV if start is None else start)
    for off in range(0, len(m), 128):
        w = [int.from_bytes(m[off + 8 * i: off + 8 * i + 8], "big") for i in range(16)]
        for t in range(16, 80):
            s0 = rotr(w[t - 15], 1) ^ rotr(w[t - 15], 8) ^ (w[t - 15] >> 7)
            s1 = rotr(w[t - 2], 19) ^ rotr(w[t - 2], 61) ^ (w[t - 2] >> 6)
            w.append((s1 + w[t - 7] + s0 + w[t - 16]) & M)
        a, b, c, d, e, f, g, hh = h
        for t in range(80):
            S1 = rotr(e, 14) ^ rotr(e, 18) ^ rotr(e, 41)
            ch = (e & f) ^ ((~e & M) & g)
            t1 = (hh + S1 + ch + K[t] + w[t]) & M
            S0 = rotr(a, 28) ^ rotr(a, 34) ^ rotr(a, 39)
            maj = (a & b) ^ (a & c) ^ (b & c)
            t2 = (S0 + maj) & M
            a, b, c, d, e, f, g, hh = (t1 + t2) & M, a, b, c, (d + t1) & M, e, f, g
        h = [(x + y) & M for x, y in zip(h, [a, b, c, d, e, f, g, hh])]
    return b"".join(x.to_bytes(8, "big") for x in h)

for msg in [b"", b"abc", b"x" * 111, b"y" * 112, b"z" * 200]:
    assert ref_sha512(msg) == hashlib.sha512(msg).digest(), msg[:8]
    assert ref_sha512(msg, IV384)[:48] == hashlib.sha384(msg).digest(), msg[:8]

def pair(x):
    return f"W{{{(x >> 32) & 0xffffffff}, {x & 0xffffffff}}}"

def lit(xs):
    return "[" + ", ".join(pair(x) for x in xs) + "]"

consts = (f"def sha512.K() -> List<&2, W>:\n  {lit(K)}\n\n"
          f"def sha512.IV() -> ST:\n  ST{{" + ", ".join(pair(x) for x in IV) + "}\n\n"
          f"def sha512.IV384() -> ST:\n  ST{{" + ", ".join(pair(x) for x in IV384) + "}\n")
body = open("sha512_body.bend").read()
assert body.count("#@@CONST@@") == 1
open("sha512.bend", "w").write(body.replace("#@@CONST@@", consts))
print("sha512.bend: constants checked against hashlib (IV and 80 round constants)")
