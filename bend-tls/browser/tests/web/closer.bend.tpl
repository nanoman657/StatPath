# A page program: a peer that closes at once. recv answers None: the end of what the peer sends.
import Base
import ../../tcp.bend as W

def show(r: Result<&1, &1, U32 & String, Maybe<&1, String>>) -> IO(Unit):
  match r:
    case Fail{(code, message)}:
      IO.print("recv failed: " ++ Nat.show(U32.to_nat(code)) ++ " " ++ message ++ "\n")
    case Done{None{}}:
      IO.print("recv: none\n")
    case Done{Some{text}}:
      IO.print("recv: " ++ text ++ "\n")

def got(m: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>) -> IO(Unit):
  (s, r) = m
  do IO<Unit>:
    closed : Unit <- W.WebTCP.close(s)
    show(r)

def connected(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Fail{(code, message)}:
      IO.print("connect failed: " ++ Nat.show(U32.to_nat(code)) ++ " " ++ message ++ "\n")
    case Done{s}:
      do IO<Unit>:
        g : Socket & Result<&1, &1, U32 & String, Maybe<&1, String>> <- W.WebTCP.recv(s, 100)
        got(g)

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Socket> <- W.WebTCP.connect("127.0.0.1", __CLOSER__)
    connected(r)
