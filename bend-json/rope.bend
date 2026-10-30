# rope.bend: printing into a rope, so forked halves join in O(1).
#
# A String is a linked list: joining two printed halves (String.append)
# copies the left one, which is why print_par cannot beat print. A Rope
# joins with a node instead; one sequential pass (Rope.flat) writes the
# final String. print_rope forks the top-level array in balanced halves.

import Base
import ./value.bend as V
import ./decimal.bend as D
import ./text.bend as T
import ./printer.bend as Pr

type Rope is Data:
  RLeaf{s: String}
  RCat{l: Rope, r: Rope}

# the rope's text in front of acc
def Rope.flat(r: Rope, acc: String) -> String:
  match r:
    case RLeaf{s}:
      String.append(s, acc)
    case RCat{a, b}:
      Rope.flat(a, Rope.flat(b, acc))

def Rope.c(c: Char) -> Rope:
  RLeaf{SCon{c, SNil{}}}

# the same shapes as Pr.go: mode 1n a whole value, 0n an items list
def Rope.go(v: V.Json, mode: Nat) -> Rope:
  match v mode:
    case V.JNull{} _:
      RLeaf{"null"}
    case V.JBool{True{}} _:
      RLeaf{"true"}
    case V.JBool{False{}} _:
      RLeaf{"false"}
    case V.JNum{n} _:
      RLeaf{D.Num.show(n, SNil{})}
    case V.JStr{s} _:
      RLeaf{T.quote(s, SNil{})}
    case V.JArr{xs} 1n+m:
      RCat{Rope.c('['), RCat{Rope.go(V.JArr{xs}, m), Rope.c(']')}}
    case V.JArr{Nil{}} 0n:
      RLeaf{SNil{}}
    case V.JArr{x <> Nil{}} 0n:
      Rope.go(x, 1n)
    case V.JArr{x <> (y <> t)} 0n:
      RCat{Rope.go(x, 1n), RCat{Rope.c(','), Rope.go(V.JArr{y <> t}, 0n)}}
    case V.JObj{ms} 1n+m:
      RCat{Rope.c('{'), RCat{Rope.go(V.JObj{ms}, m), Rope.c('}')}}
    case V.JObj{Nil{}} 0n:
      RLeaf{SNil{}}
    case V.JObj{V.Mem{k, x} <> Nil{}} 0n:
      RCat{RLeaf{T.quote(k, SCon{':', SNil{}})}, Rope.go(x, 1n)}
    case V.JObj{V.Mem{k, x} <> (y <> t)} 0n:
      RCat{RLeaf{T.quote(k, SCon{':', SNil{}})}, RCat{Rope.go(x, 1n),
        RCat{Rope.c(','), Rope.go(V.JObj{y <> t}, 0n)}}}

def Rope.items(xs: List<&2, V.Json>) -> Rope:
  Rope.go(V.JArr{xs}, 0n)

# the items of l then r, from their ropes a and b
def Rope.join(l: List<&2, V.Json>, r: List<&2, V.Json>, a: Rope, b: Rope) -> Rope:
  match l r:
    case Nil{} r0:
      b
    case Con{x, t} Nil{}:
      a
    case Con{x, t} Con{y, u}:
      RCat{a, RCat{Rope.c(','), b}}

# Linear list work: the list is moved, never shared, so parallel lanes
# touch no reference counts.

def Rope.split.cons(x: V.Json, r: List<&2, V.Json> & List<&2, V.Json>) ->
  List<&2, V.Json> & List<&2, V.Json>:
  (l, t) = r
  (x <> l, t)

# the first n items, and the rest
def Rope.split(n: Nat, xs: List<&2, V.Json>) -> List<&2, V.Json> & List<&2, V.Json>:
  match n xs:
    case 0n ys:
      (Nil{}, ys)
    case 1n+p Nil{}:
      (Nil{}, Nil{})
    case 1n+p Con{x, t}:
      Rope.split.cons(x, Rope.split(p, t))

def Rope.len.cons(x: V.Json, r: Nat & List<&2, V.Json>) -> Nat & List<&2, V.Json>:
  (n, t) = r
  (1n+n, x <> t)

# the length, and the list back
def Rope.len(xs: List<&2, V.Json>) -> Nat & List<&2, V.Json>:
  match xs:
    case Nil{}:
      (0n, Nil{})
    case Con{x, t}:
      Rope.len.cons(x, Rope.len(t))

# the items of l then r, of lengths h and m
def Rope.join2(h: Nat, m: Nat, a: Rope, b: Rope) -> Rope:
  match h m:
    case 0n m0:
      b
    case 1n+p 0n:
      a
    case 1n+p 1n+q:
      RCat{a, RCat{Rope.c(','), b}}

# lr: a list of length n split at n / 2; forks d more levels
def Rope.par(d: Nat, +n: Nat, lr: List<&2, V.Json> & List<&2, V.Json>) -> Rope:
  match d:
    case 0n:
      (l, r) = lr
      +h = Nat.div(n, 2n)
      Rope.join2(h, Nat.sub(n, h), RLeaf{Pr.Pr.items(l)}, RLeaf{Pr.Pr.items(r)})
    case 1n++p:
      (l, r) = lr
      +h = Nat.div(n, 2n)
      +m = Nat.sub(n, h)
      a b = Rope.par(p, h, Rope.split(Nat.div(h, 2n), l)) Rope.par(p, m, Rope.split(Nat.div(m, 2n), r))
      Rope.join2(h, m, a, b)

def Rope.depth() -> Nat:
  4n

def rope.arr(r: Nat & List<&2, V.Json>) -> Rope:
  (+n, xs) = r
  RCat{Rope.c('['), RCat{Rope.par(Rope.depth(), n, Rope.split(Nat.div(n, 2n), xs)), Rope.c(']')}}

# the rope of v's compact text, its top-level array forked 2^depth ways
def rope(v: V.Json) -> Rope:
  match v:
    case V.JArr{xs}:
      rope.arr(Rope.len(xs))
    case o:
      Rope.go(o, 1n)

# the compact text of v, built as a rope
def print_rope(v: V.Json) -> String:
  Rope.flat(rope(v), SNil{})

def Rope.write.done(q: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (f, r) = q
  do IO<File>:
    u : Unit <- IO.pass(Unit, r)
    return f

def Rope.write.go(r: Rope, f: File) -> IO(File):
  match r:
    case RLeaf{s}:
      do IO<File>:
        q : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, s)
        Rope.write.done(q)
    case RCat{a, b}:
      do IO<File>:
        f2 : File <- Rope.write.go(a, f)
        Rope.write.go(b, f2)

# writes the rope's text to a file, chunk by chunk, never building it whole
def Rope.write(r: Rope, f: File) -> IO(File):
  Rope.write.go(r, f)
