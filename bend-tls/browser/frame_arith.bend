import Base

def add_zero(m: Nat) -> {m == Nat.add(m, 0n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(p: Nat, +q: Nat) -> {1n+Nat.add(p, q) == Nat.add(p, 1n+q) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+r:
      %add_succ(r, q) : {2n+Nat.add(r, q) == 1n+_ : Nat}
      {==}

def add_comm(+p: Nat, +q: Nat) -> {Nat.add(p, q) == Nat.add(q, p) : Nat}:
  match p:
    case 0n:
      add_zero(q)
    case 1n+r:
      %add_succ(q, r) : {1n+Nat.add(r, q) == _ : Nat}
      %add_comm(r, q) : {1n+Nat.add(r, q) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, b: Nat, c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# a hypothesis about the first pair, moved to the next pair of the invariant
def h_zero(r: Nat, bp: Nat, h: {r == bp : Nat}) -> {Nat.add(r, 0n) == bp : Nat}:
  %add_zero(r) : {_ == bp : Nat}
  h

def h_succ(mp: Nat, r: Nat, bp: Nat, h: {Nat.add(1n+mp, r) == bp : Nat}) -> {Nat.add(mp, 1n+r) == bp : Nat}:
  %add_succ(mp, r) : {_ == bp : Nat}
  h

# the hypothesis r == bp, read the other way
def flip_r(r: Nat, bp: Nat, h: {r == bp : Nat}) -> {bp == r : Nat}:
  %h : {_ == r : Nat}
  {==}

# the quotient step with the remainder r, which equals bp
def step_core(+X: Nat, +bp: Nat, +np: Nat) -> {Nat.add(Nat.add(bp, X), np) == Nat.add(X, Nat.add(np, bp)) : Nat}:
  %add_comm(X, bp) : {Nat.add(_, np) == Nat.add(X, Nat.add(np, bp)) : Nat}
  %add_comm(bp, np) : {Nat.add(Nat.add(X, bp), np) == Nat.add(X, _) : Nat}
  %add_assoc(X, bp, np) : {Nat.add(Nat.add(X, bp), np) == _ : Nat}
  {==}

# the step after a quotient digit, with r == bp: (1+d)*(1+bp) + (np + 0) == d*(1+bp) + (1+np + bp)
def step0(+d: Nat, +bp: Nat, +np: Nat) -> {Nat.add(Nat.mul(1n+d, 1n+bp), Nat.add(np, 0n)) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(1n+np, bp)) : Nat}:
  %add_zero(np) : {Nat.add(Nat.mul(1n+d, 1n+bp), _) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(1n+np, bp)) : Nat}
  %add_succ(Nat.mul(d, 1n+bp), Nat.add(np, bp)) : {Nat.add(Nat.mul(1n+d, 1n+bp), np) == _ : Nat}
  %step_core(Nat.mul(d, 1n+bp), bp, np) : {1n+Nat.add(Nat.add(bp, Nat.mul(d, 1n+bp)), np) == 1n+_ : Nat}
  {==}

def step0r(+d: Nat, +bp: Nat, +np: Nat, +r: Nat, h: {r == bp : Nat}) -> {Nat.add(Nat.mul(1n+d, 1n+bp), Nat.add(np, 0n)) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(1n+np, r)) : Nat}:
  %flip_r(r, bp, h) : {Nat.add(Nat.mul(1n+d, 1n+bp), Nat.add(np, 0n)) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(1n+np, _)) : Nat}
  step0(d, bp, np)

# the rearrangement behind a quotient step: x + (bp + x-part) and the digits commute
def e1(np: Nat, r: Nat) -> {Nat.add(np, 1n+r) == Nat.add(1n+np, r) : Nat}:
  %add_succ(np, r) : {_ == Nat.add(1n+np, r) : Nat}
  {==}

# the invariant of the long division: the quotient times the divisor plus the remainder, plus the
# digits still to read, is the number read so far, and the remainder with the counter is the divisor
def divmod_inv(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) ->
  {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp),
    Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(n, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          %step0r(d, bp, np, r, h) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np, 0n, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(1n+np, 0n, d, r))) == _ : Nat}
          divmod_inv(np, r, 1n+d, 0n, bp, h_zero(r, bp, h))
        case 1n+mp:
          %e1(np, r) : {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(1n+np, 1n+mp, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(1n+np, 1n+mp, d, r))) == Nat.add(Nat.mul(d, 1n+bp), _) : Nat}
          divmod_inv(np, mp, d, 1n+r, bp, h_succ(mp, r, bp, h))

# the division of n by 1+bp, read off the invariant with m = bp, d = 0, r = 0
def h_bp(+bp: Nat) -> {Nat.add(bp, 0n) == bp : Nat}:
  %add_zero(bp) : {_ == bp : Nat}
  {==}

def zero_inv(+n: Nat, +bp: Nat) -> {Nat.add(Nat.mul(0n, 1n+bp), Nat.add(n, 0n)) == n : Nat}:
  %add_zero(n) : {Nat.add(Nat.mul(0n, 1n+bp), _) == n : Nat}
  {==}

# Euclid: the quotient times the divisor, plus the remainder, is the number
def euclid(+n: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(n, 1n+bp), 1n+bp), Nat.mod(n, 1n+bp)) == n : Nat}:
  %zero_inv(n, bp) : {Nat.add(Nat.mul(Nat.div(n, 1n+bp), 1n+bp), Nat.mod(n, 1n+bp)) == _ : Nat}
  divmod_inv(n, bp, 0n, 0n, bp, h_bp(bp))
