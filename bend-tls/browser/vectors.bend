# vectors.bend: frames encoded by the Bend definitions, printed for the JavaScript interop test
# (test/frame_interop.test.ts reads them from test/frame_vectors.json; regenerate with
#   bend vectors.bend > test/frame_vectors.txt  and the converter in test/frame_interop.test.ts).
#   bend vectors.bend
import Base
import ./frame.bend as F

def rep(+n: Nat, +v: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      v <> rep(p, v)

def show(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case +x <> Nil{}:
      Nat.show(x)
    case +x <> t:
      Nat.show(x) ++ "," ++ show(t)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(F.frame.encode(2n, 7n, Nil{}, {==})) ++ "\n")
    IO.print(show(F.frame.encode(12n, 0n, 1n <> 2n <> 3n <> 4n <> 5n <> Nil{}, {==})) ++ "\n")
    IO.print(show(F.frame.encode(1n, 255n, rep(300n, 65n), {==})) ++ "\n")
    IO.print(show(F.frame.encode(11n, 3n, 0n <> 13n <> 65n <> 67n <> Nil{}, {==})) ++ "\n")
