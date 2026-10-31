# bench.bend: SHA-256 throughput on one file. Prints the digest and ms.
#   bend bench.bend <file>   (JS)    bend bench.bend -o bench && ./bench <file>
import Base
import ./sha256.bend as S

def run(bs: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    +d : String = S.sha256_hex(bs)
    IO.print(d)
    +t1 : Nat <- IO.now()
    IO.print("ms: " ++ Nat.show(Nat.sub(t1, t0)))

def read_bytes.got(q: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(List<&2, U32>):
  (f, r) = q
  do IO<List<&2, U32>>:
    File.close(f)
    IO.pass(List<&2, U32>, r)

def read_bytes.size(p: File & Result<&1, &1, U32 & String, U32>) -> IO(List<&2, U32>):
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

def start(args: List<String>) -> IO(Unit):
  match args:
    case prog <> (path <> rest):
      do IO<Unit>:
        bs : List<&2, U32> <- read_bytes(path)
        run(bs)
    case _:
      IO.print("usage: bench <file>")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    start(args)
