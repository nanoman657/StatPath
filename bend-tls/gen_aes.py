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

body = open("aes_body.bend").read()
assert "#@@SBOX@@" not in body
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from bendsort import sort_defs
# the compiler needs each definition after the ones it uses: sort as sortfile.py does
open("aes.bend", "w").write(sort_defs(body))
print("aes.bend: S-box by inversion and the affine map")
