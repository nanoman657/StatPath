# corpus.bend: runs JSONTestSuite's test_parsing files.
#
#   bend corpus.bend <dir> <file>...      (JS)
#   ./corpus <dir> <file>...              (native, after -o corpus)
#
# A file is read as bytes and decoded as strict UTF-8 (RFC 8259 8.1): bytes
# that are not UTF-8 count as a rejection. y_ files must parse and n_ files
# must be rejected; i_ files may go either way and are reported.

import Base
import ./value.bend as V
import ./parser.bend as P
import ./utf8.bend as U

type Tally is Data:
  Tally{yp: Nat, yf: Nat, np: Nat, nf: Nat, ia: Nat, ir: Nat}

def accepts.at(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Result.is_done(&2, &2, P.Err, V.Json, P.parse(s))

def accepts(bs: List<&2, U32>) -> Bool:
  accepts.at(U.decode(bs))

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

def tally(t: Tally, kind: Char, ok: Bool) -> Tally:
  match t kind ok:
    case Tally{yp, yf, np, nf, ia, ir} 'y' True{}:
      Tally{1n+yp, yf, np, nf, ia, ir}
    case Tally{yp, yf, np, nf, ia, ir} 'y' False{}:
      Tally{yp, 1n+yf, np, nf, ia, ir}
    case Tally{yp, yf, np, nf, ia, ir} 'n' False{}:
      Tally{yp, yf, 1n+np, nf, ia, ir}
    case Tally{yp, yf, np, nf, ia, ir} 'n' True{}:
      Tally{yp, yf, np, 1n+nf, ia, ir}
    case Tally{yp, yf, np, nf, ia, ir} k True{}:
      Tally{yp, yf, np, nf, 1n+ia, ir}
    case Tally{yp, yf, np, nf, ia, ir} k False{}:
      Tally{yp, yf, np, nf, ia, 1n+ir}

# the line for one file: its verdict and whether it went as required
def verdict.at(k: Char, +name: String, +ok: Bool) -> String:
  match k:
    case 'y':
      Bool.pick(String, ok, "pass ", "FAIL ") ++ name
    case 'n':
      Bool.pick(String, ok, "FAIL ", "pass ") ++ name
    case _:
      Bool.pick(String, ok, "accepted ", "rejected ") ++ name

def verdict(+name: String, +ok: Bool) -> String:
  verdict.at(Maybe.default(&2, Char, String.get(name, 0n), 'i'), name, ok)

def one(+name: String, +ok: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    IO.print(verdict(name, ok))
    return tally(t, Maybe.default(&2, Char, String.get(name, 0n), 'i'), ok)

def one.at(+dir: String, +name: String, t: Tally) -> IO(Tally):
  do IO<Tally>:
    bs : List<&2, U32> <- read_bytes(dir ++ "/" ++ name)
    one(name, accepts(bs), t)

def run(+dir: String, names: List<String>, t: Tally) -> IO(Tally):
  match names:
    case Nil{}:
      IO.pure(Tally, t)
    case name <> rest:
      do IO<Tally>:
        t2 : Tally <- one.at(dir, name, t)
        run(dir, rest, t2)

def report(t: Tally) -> IO(Unit):
  match t:
    case Tally{yp, yf, np, nf, ia, ir}:
      do IO<Unit>:
        IO.print("y_ (must accept): " ++ Nat.show(yp) ++ " accepted, " ++ Nat.show(yf) ++ " rejected")
        IO.print("n_ (must reject): " ++ Nat.show(np) ++ " rejected, " ++ Nat.show(nf) ++ " accepted")
        IO.print("i_ (either way):  " ++ Nat.show(ia) ++ " accepted, " ++ Nat.show(ir) ++ " rejected")

def start(args: List<String>) -> IO(Unit):
  match args:
    case prog <> (dir <> names):
      do IO<Unit>:
        t : Tally <- run(dir, names, Tally{0n, 0n, 0n, 0n, 0n, 0n})
        report(t)
    case _:
      IO.print("usage: corpus <dir> <file>...")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    start(args)
