# A page program: a peer that never writes. try_recv gives up after 200 ms and answers Wait.
import Base
import ../../tcp.bend as W

def show(p: Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, String>>, Unit>) -> IO(Unit):
  match p:
    case Ready{r}:
      IO.print("ready\n")
    case Wait{u}:
      IO.print("timeout\n")

def timed(m: Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, String>>, Unit>) -> IO(Unit):
  (s, p) = m
  do IO<Unit>:
    closed : Unit <- W.WebTCP.close(s)
    show(p)

def connected(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Fail{(code, message)}:
      IO.print("connect failed: " ++ Nat.show(U32.to_nat(code)) ++ " " ++ message ++ "\n")
    case Done{s}:
      do IO<Unit>:
        m : Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, String>>, Unit> <- W.WebTCP.try_recv(s, 100, 200)
        timed(m)

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Socket> <- W.WebTCP.connect("127.0.0.1", __SILENT__)
    connected(r)
