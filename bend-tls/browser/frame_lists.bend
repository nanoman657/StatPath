import Base

def len_app(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {List.length(&2, Nat, List.append(&2, Nat, xs, ys)) == Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %len_app(t, ys) : {1n+List.length(&2, Nat, List.append(&2, Nat, t, ys)) == 1n+_ : Nat}
      {==}

def zero_le(+b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def le_add(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      zero_le(b)
    case 1n+p:
      le_add(p, b)

def take0(+ys: List<&2, Nat>) -> {Nil{} == List.take(&2, Nat, ys, 0n) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case +x <> t:
      {==}

def drop0(+ys: List<&2, Nat>) -> {List.drop(&2, Nat, ys, 0n) == ys : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case +x <> t:
      {==}

def take_app(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {xs == List.take(&2, Nat, List.append(&2, Nat, xs, ys), List.length(&2, Nat, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      take0(ys)
    case +x <> t:
      %take_app(t, ys) : {x <> t == x <> _ : List<&2, Nat>}
      {==}

def drop_app(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {List.drop(&2, Nat, List.append(&2, Nat, xs, ys), List.length(&2, Nat, xs)) == ys : List<&2, Nat>}:
  match xs:
    case Nil{}:
      drop0(ys)
    case +x <> t:
      drop_app(t, ys)
