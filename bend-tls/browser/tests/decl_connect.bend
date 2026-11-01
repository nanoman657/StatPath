# a page program: calls WebTCP.connect and prints the errno it answers (38 until the effect is written)
import Base
import ../tcp.bend as W

def show(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Done{s}:
      IO.print("connected\n")
    case Fail{(code, message)}:
      IO.print(Nat.show(U32.to_nat(code)) ++ "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Socket> <- W.WebTCP.connect("127.0.0.1", 9)
    show(r)
