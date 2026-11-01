# a page program: a page cannot listen, and WebTCP.listen answers EOPNOTSUPP (95)
import Base
import ../tcp.bend as W

def show(r: Result<&1, &1, U32 & String, Listener>) -> IO(Unit):
  match r:
    case Done{l}:
      IO.print("listening\n")
    case Fail{(code, message)}:
      IO.print(Nat.show(U32.to_nat(code)) ++ " " ++ message ++ "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Listener> <- W.WebTCP.listen("127.0.0.1", 0)
    show(r)
