# tcp_contract_false.bend: a claim that is false, to show the checker rejects it. It is the bound on
# what the page holds with the chunk term dropped (b + (z + u) == WIN, not WIN + C). It must not check:
#   bend tcp_contract_false.bend     (SOME PROOFS FAIL is the right answer)
import Base
import ./tcp_contract_proof.bend as P

def buffered_too_tight(+T: Nat, +b: Nat, +R: Nat, +G: Nat, +z: Nat, +u: Nat, +WIN: Nat, +C: Nat,
  hI: {Nat.add(R, z) == Nat.add(G, C) : Nat},
  hG: {Nat.add(G, u) == Nat.add(WIN, T) : Nat},
  hB: {Nat.add(T, b) == R : Nat}) ->
  {Nat.add(b, Nat.add(z, u)) == WIN : Nat}:
  P.buffered_bound(T, b, R, G, z, u, WIN, C, hI, hG, hB)
