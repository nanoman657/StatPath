# A page program: connects to a port nothing listens on (the relay allows it), and prints the failure.
import Base
import ../../tcp.bend as W

def connected(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Fail{(code, message)}:
      IO.print("connect failed: " ++ Nat.show(U32.to_nat(code)) ++ " " ++ message ++ "\n")
    case Done{s}:
      do IO<Unit>:
        closed : Unit <- W.WebTCP.close(s)
        IO.print("connected\n")

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Socket> <- W.WebTCP.connect("127.0.0.1", __REFUSED__)
    connected(r)
