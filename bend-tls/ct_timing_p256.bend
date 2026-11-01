# ct_timing_p256.bend: one P-256 ECDH per process (the scalar times the generator), for the timing
# experiment in e2e/ct_timing.py. The argument is the private scalar as 64 hex digits, big-endian
# (the top bit is cleared by p256.scalar only in the client; here the caller passes a scalar below
# n). The output is the first byte of the shared x coordinate, so nothing is optimised away.
#   bend ct_timing_p256.bend -o ct_timing_p256
#   ./ct_timing_p256 <64 hex digits>
import Base
import ./p256.bend as P

def ct.first(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> t:
      x

# one hex digit as its value
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

# the generator of P-256, big-endian
def ct.gx() -> List<&2, U32>:
  [107, 23, 209, 242, 225, 44, 66, 71, 248, 188, 230, 229, 99, 164, 64, 242, 119, 3, 125, 129, 45, 235, 51, 160, 244, 161, 57, 69, 216, 152, 194, 150]
def ct.gy() -> List<&2, U32>:
  [79, 227, 66, 226, 254, 26, 127, 155, 142, 231, 235, 74, 124, 15, 158, 22, 43, 206, 51, 87, 107, 49, 94, 206, 203, 182, 64, 104, 55, 191, 81, 245]
def ct.run(d: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    +out : List<&2, U32> = P.p256.ecdh(d, ct.gx(), ct.gy())
    IO.print(Nat.show(U32.to_nat(ct.first(out))))

def ct.start(args: List<String>) -> IO(Unit):
  match args:
    case prog <> (s <> Nil{}):
      ct.run(ct.hex(s))
    case _:
      IO.print("usage: ct_timing_p256 <64 hex digits>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    ct.start(args)
