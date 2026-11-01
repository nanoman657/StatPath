# ct_timing_x25519.bend: one X25519 scalar multiplication per process, for the timing experiment
# in e2e/ct_timing.py. The argument is the scalar as 64 hex digits, the 32 bytes in order (the
# first byte is the least significant, as X25519 reads it; X25519 clamps it). Bytes are read
# directly, so no large Nat is built (the runtime's Nat arithmetic is limited to 2^48 - 1 per
# operation). The output is the first byte of the result, so nothing is optimised away.
#   bend ct_timing_x25519.bend -o ct_timing_x25519
#   ./ct_timing_x25519 <64 hex digits>
import Base
import ./x25519.bend as X

def ct.le(k: Nat, +n: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      U32.from_nat(Nat.mod(n, 256n)) <> ct.le(p, Nat.div(n, 256n))

# one hex digit (0-9, a-f, A-F) as its value
def ct.nib(+c: U32) -> Nat:
  Bool.pick(Nat, U32.is_ge(c, 97), Nat.sub(U32.to_nat(c), 87n),
    Bool.pick(Nat, U32.is_ge(c, 65), Nat.sub(U32.to_nat(c), 55n), Nat.sub(U32.to_nat(c), 48n)))

# the bytes of a hex string, two digits each, in order
def ct.hex(s: String) -> List<&2, U32>:
  match s:
    case SCon{Chr{h}, SCon{Chr{l}, t}}:
      U32.from_nat(Nat.add(Nat.mul(ct.nib(h), 16n), ct.nib(l))) <> ct.hex(t)
    case SCon{Chr{h}, SNil{}}:
      Nil{}
    case SNil{}:
      Nil{}

def ct.first(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> t:
      x

def ct.run(k: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    +u : List<&2, U32> = ct.le(32n, 9n)
    +out : List<&2, U32> = X.x25519(k, u)
    IO.print(Nat.show(U32.to_nat(ct.first(out))))

def ct.start(args: List<String>) -> IO(Unit):
  match args:
    case prog <> (s <> Nil{}):
      ct.run(ct.hex(s))
    case _:
      IO.print("usage: ct_timing_x25519 <64 hex digits>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    ct.start(args)
