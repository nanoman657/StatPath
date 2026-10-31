# Writes tests.bend: SHA-256 cases with digests from Python's hashlib.
#   python3 -I gen_tests.py
import hashlib

ALPHA = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

def text(n):
    return "".join(ALPHA[(i * 7) % len(ALPHA)] for i in range(n))

FIXED = [
    ("empty", ""),
    ("abc", "abc"),
    ("nist-56", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
]
LENGTHS = [1, 3, 55, 56, 57, 63, 64, 65, 119, 120, 128, 1000]

cases = FIXED + [(f"len-{n}", text(n)) for n in LENGTHS]

import random
random.seed(1)
raw = [random.randrange(256) for _ in range(700)] + list(range(256))
raw_want = hashlib.sha256(bytes(raw)).hexdigest()
raw_lit = "[" + ", ".join(str(b) for b in raw) + "]"

lines = []
for name, s in cases:
    want = hashlib.sha256(s.encode("ascii")).hexdigest()
    lines.append(f'  case_("{name}", "{s}", "{want}") <>')

src = '''# tests.bend: SHA-256 cases. Expected digests come from hashlib (see
# gen_tests.py). Run: bend tests.bend   (and -o tests for native)

import Base
import ./sha256.bend as S

type Case is Data:
  Case{name: String, got: String, want: String}

def case_(name: String, +input: String, want: String) -> Case:
  Case{name, S.sha256_hex(S.bytes_of(input)), want}

def case_raw(name: String, +input: List<&2, U32>, want: String) -> Case:
  Case{name, S.sha256_hex(input), want}

def cases() -> List<&2, Case>:
''' + "\n".join(lines) + '''
  case_raw("raw-bytes", {raw_lit}, "{raw_want}") <>
  Nil{}

def fails.put(n: String, +g: String, +w: String, +rest: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(g, w), rest,
    ("FAIL " ++ n ++ "\\n  got:  " ++ g ++ "\\n  want: " ++ w) <> rest)

def fails.at(+c: Case, rest: List<&2, String>) -> List<&2, String>:
  match c:
    case Case{n, +g, +w}:
      fails.put(n, g, w, rest)

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
    IO.print("sha256: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f) ++ " failed")
'''
src = src.replace('{raw_lit}', raw_lit).replace('{raw_want}', raw_want)
open('tests.bend','w').write(src)
print(len(cases), "cases")
