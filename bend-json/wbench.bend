# wbench.bend: writing a value's compact text to a file: print + one
# write, against rope chunks written one by one (no whole String built).
#
#   bend wbench.bend -o wbench && ./wbench <in.json> <outA> <outB>
#
# was: bench.bend
#
#   bend bench.bend <file.json>                 (JS)
#   bend bench.bend -o bench && ./bench <file.json>   (native)
#
# Each phase prints a size computed from its result before the clock is
# read again, so the work cannot move past the measurement.

import Base
import ./value.bend as V
import ./parser.bend as P
import ./printer.bend as Pr
import ./utf8.bend as U
import ./rope.bend as Ro

def read_bytes.got(q: File & Result<&1, &1, U32 & String, List<&2, U32>>) ->
  IO(List<&2, U32>):
  (f, r) = q
  do IO<List<&2, U32>>:
    File.close(f)
    IO.pass(List<&2, U32>, r)

def read_bytes.size(p: File & Result<&1, &1, U32 & String, U32>) ->
  IO(List<&2, U32>):
  (f, r) = p
  do IO<List<&2, U32>>:
    n : U32 <- IO.pass(U32, r)
    q : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, (n + 1 : U32))
    read_bytes.got(q)

def read_bytes(path: String) -> IO(List<&2, U32>):
  do IO<List<&2, U32>>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read_bytes.size(p)

def ms(+a: Nat, +b: Nat) -> String:
  Nat.show(Nat.sub(b, a)) ++ " ms"

def fresh(+s: String) -> V.Json:
  Result.default(&2, &2, P.Err, V.Json, P.parse(s), V.JNull{})

def write_all(q: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, r) = q
  do IO<Unit>:
    u : Unit <- IO.pass(Unit, r)
    File.close(f)

def run(+s: String, +pa: String, +pb: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    fa : File <- IO.try(File, File.open(pa, "w"))
    qa : File & Result<&1, &1, U32 & String, Unit> <- File.write(fa, Pr.print(fresh(s)))
    write_all(qa)
    +t1 : Nat <- IO.now()
    fb : File <- IO.try(File, File.open(pb, "w"))
    fb2 : File <- Ro.Rope.write(Ro.rope(fresh(s)), fb)
    File.close(fb2)
    +t2 : Nat <- IO.now()
    +t3 : Nat <- IO.now()
    IO.print("depth " ++ Nat.show(V.Json.depth(fresh(s))))
    +t4 : Nat <- IO.now()
    IO.print("parse+print+write " ++ ms(t0, t1) ++ ", parse+rope+write " ++ ms(t1, t2) ++ ", parse alone " ++ ms(t3, t4))

def start(args: List<String>) -> IO(Unit):
  match args:
    case prog <> (path <> (pa <> (pb <> rest))):
      do IO<Unit>:
        bs : List<&2, U32> <- read_bytes(path)
        run(Maybe.default(&2, String, U.decode(bs), ""), pa, pb)
    case _:
      IO.print("usage: wbench <in.json> <outA> <outB>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    start(args)
