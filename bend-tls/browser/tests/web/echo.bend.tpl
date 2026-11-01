# A page program: connects to the echo peer, sends "hé", and prints what comes back.
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

def sent(m: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (s, r) = m
  match r:
    case Fail{((code, message), rest)}:
      do IO<Unit>:
        closed : Unit <- W.WebTCP.close(s)
        IO.print("send failed: " ++ Nat.show(U32.to_nat(code)) ++ "\n")
    case Done{u}:
      do IO<Unit>:
        g : Socket & Result<&1, &1, U32 & String, Maybe<&1, String>> <- W.WebTCP.recv(s, 100)
        got(g)

def connected(r: Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  match r:
    case Fail{(code, message)}:
      IO.print("connect failed: " ++ Nat.show(U32.to_nat(code)) ++ " " ++ message ++ "\n")
    case Done{s}:
      do IO<Unit>:
        m : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- W.WebTCP.send(s, "hé")
        sent(m)

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, Socket> <- W.WebTCP.connect("127.0.0.1", __ECHO__)
    connected(r)
