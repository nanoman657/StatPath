# bench.bend: parse and print timings for one JSON file.
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

def items(r: Result<&2, &2, P.Err, V.Json>) -> String:
  match r:
    case Done{V.JArr{xs}}:
      "array of " ++ Nat.show(List.length(&2, V.Json, xs))
    case Done{v}:
      "a value"
    case Fail{e}:
      "error " ++ P.Err.show(e)

def run(+s: String) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +r : Result<&2, &2, P.Err, V.Json> = P.parse(s)
    IO.print("parse:   " ++ items(r))
    +t1 : Nat <- IO.now()
    +v : V.Json = Result.default(&2, &2, P.Err, V.Json, r, V.JNull{})
    IO.print("compact: " ++ Nat.show(String.length(Pr.print(v))) ++ " chars")
    +t2 : Nat <- IO.now()
    IO.print("pretty:  " ++ Nat.show(String.length(Pr.pretty(2n, v))) ++ " chars")
    +t3 : Nat <- IO.now()
    IO.print("par:     " ++ Nat.show(String.length(Pr.print_par(v))) ++ " chars")
    +t4 : Nat <- IO.now()
    IO.print("rope:    same as print: " ++ Bool.show(String.eq(Ro.print_rope(v), Pr.print(v))))
    +t5 : Nat <- IO.now()
    IO.print("fresh parse + print: " ++ Nat.show(String.length(Pr.print(Result.default(&2, &2, P.Err, V.Json, P.parse(s), V.JNull{})))))
    +t6 : Nat <- IO.now()
    IO.print("fresh parse + rope:  " ++ Nat.show(String.length(Ro.print_rope(Result.default(&2, &2, P.Err, V.Json, P.parse(s), V.JNull{})))))
    +t7 : Nat <- IO.now()
    IO.print("times: parse " ++ ms(t0, t1) ++ ", print " ++ ms(t1, t2) ++ ", pretty "
      ++ ms(t2, t3) ++ ", print_par " ++ ms(t3, t4) ++ ", fresh parse+print " ++ ms(t5, t6)
      ++ ", fresh parse+rope " ++ ms(t6, t7))

def start(args: List<String>) -> IO(Unit):
  match args:
    case prog <> (path <> rest):
      do IO<Unit>:
        bs : List<&2, U32> <- read_bytes(path)
        run(Maybe.default(&2, String, U.decode(bs), ""))
    case _:
      IO.print("usage: bench <file.json>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    start(args)
