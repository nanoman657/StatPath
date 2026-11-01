# sends "hello" through the browser relay to an echo server on port 4444 and prints the bytes back
import Base

def Relay.roundtrip(port: U32) -> IO(U32):
  import "./relay_effects.js"

def main() -> IO(Unit):
  do IO<Unit>:
    n : U32 <- Relay.roundtrip(4444)
    IO.print("echoed " ++ Nat.show(U32.to_nat(n)) ++ "\n")
