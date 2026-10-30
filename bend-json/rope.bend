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

# the items of l then r, each printed whole (a leaf)
def Rope.leaf(l: List<&2, V.Json>, r: List<&2, V.Json>) -> Rope:
  match l r:
    case Nil{} r0:
      RLeaf{Pr.Pr.items(r0)}
    case Con{x, t} Nil{}:
      RLeaf{Pr.Pr.items(x <> t)}
    case Con{x, t} Con{y, u}:
      RCat{RLeaf{Pr.Pr.items(x <> t)}, RCat{Rope.c(','), RLeaf{Pr.Pr.items(y <> u)}}}

# the sizes of a list's halves when split at n / 2
def Rope.lo(+n: Nat) -> Nat:
  Nat.div(n, 2n)

def Rope.hi(+n: Nat) -> Nat:
  Nat.sub(n, Nat.div(n, 2n))

# the items of l then r, lr a list split near its middle (n its length);
# forks d more levels. Commas follow the halves' shapes, so the text is
# right for any split point; n only balances the work.
def Rope.par(d: Nat, +n: Nat, lr: List<&2, V.Json> & List<&2, V.Json>) -> Rope:
  match d:
    case 0n:
      (l, r) = lr
      Rope.leaf(l, r)
    case 1n++p:
      (l, r) = lr
      match l r:
        case Nil{} r0:
          Rope.par(p, Rope.hi(n), Rope.split(Nat.div(Rope.hi(n), 2n), r0))
        case Con{x, t} Nil{}:
          Rope.par(p, Rope.lo(n), Rope.split(Nat.div(Rope.lo(n), 2n), x <> t))
        case Con{x, t} Con{y, u}:
          a b = Rope.par(p, Rope.lo(n), Rope.split(Nat.div(Rope.lo(n), 2n), x <> t)) Rope.par(p, Rope.hi(n), Rope.split(Nat.div(Rope.hi(n), 2n), y <> u))
          RCat{a, RCat{Rope.c(','), b}}

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
