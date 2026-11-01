# the effect completes after a host timer, with no file descriptor: the scheduler must not block
import Base

def Wake.later(ms: U32) -> IO(U32):
  import "./wake_later.js"

def main() -> IO(Unit):
  do IO<Unit>:
    a : U32 <- Wake.later(120)
    b : U32 <- Wake.later(40)
    IO.print("a " ++ Nat.show(U32.to_nat(a)) ++ " b " ++ Nat.show(U32.to_nat(b)) ++ "\n")
