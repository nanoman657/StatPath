# Writes aes.bend from aes_body.bend. The AES S-box (FIPS 197 5.1.1: the inverse
# in GF(2^8) followed by the affine map) becomes a binary tree of comparisons:
# aes.sbox(x) tests the top bit of the index, then the next, down to the value.
# The values are checked against the FIPS 197 examples before anything is written.
#   python3 -I gen_aes.py
import sys

def gmul(a, b):
    p = 0
    while b:
        if b & 1:
            p ^= a
        a <<= 1
        if a & 0x100:
            a ^= 0x11b
        b >>= 1
    return p

def rotl8(x, s):
    return ((x << s) | (x >> (8 - s))) & 0xff

def sbox_value(x):
    inv = 0
    if x:
        inv, base, e = 1, x, 254
        while e:
            if e & 1:
                inv = gmul(inv, base)
            base = gmul(base, base)
            e >>= 1
    return inv ^ rotl8(inv, 1) ^ rotl8(inv, 2) ^ rotl8(inv, 3) ^ rotl8(inv, 4) ^ 0x63

SBOX = [sbox_value(x) for x in range(256)]
assert SBOX[0x00] == 0x63 and SBOX[0x01] == 0x7c and SBOX[0x53] == 0xed and SBOX[0xff] == 0x16

def node(p):
    return "aes.sbox" + ("." + p if p else "")

def pick(p):
    return "aes.sbpk" + ("." + p if p else "")

def tree(lo, hi, p, out):
    # the function for the values [lo, hi) at path p, and the ones below it
    if hi - lo == 2:
        mid = lo + 1
        out.append(f"""def {node(p)}(+x: U32) -> U32:
  {pick(p)}(U32.is_lt(x, {mid}), x)

def {pick(p)}(c: Bool, +x: U32) -> U32:
  match c:
    case True{{}}:
      {SBOX[lo]}
    case False{{}}:
      {SBOX[lo + 1]}
""")
        return
    mid = (lo + hi) // 2
    out.append(f"""def {node(p)}(+x: U32) -> U32:
  {pick(p)}(U32.is_lt(x, {mid}), x)

def {pick(p)}(c: Bool, x: U32) -> U32:
  match c:
    case True{{}}:
      {node(p + "L")}(x)
    case False{{}}:
      {node(p + "R")}(x)
""")
    tree(lo, mid, p + "L", out)
    tree(mid, hi, p + "R", out)

out = []
tree(0, 256, "", out)
sbox = "\n".join(out)
body = open("aes_body.bend").read()
assert body.count("#@@SBOX@@") == 1
open("aes.bend", "w").write(body.replace("#@@SBOX@@", sbox))
print("aes.bend: S-box tree with", len(out) * 2, "functions")
