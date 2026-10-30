# printer.bend: values to JSON text.
#
# Both printers write in front of an accumulator, so each char is built
# once. mode 1n prints a whole value; mode 0n the items of an array or
# object, without brackets (a self-call on a rebuilt, smaller shell).

import Base
import ./decimal.bend as D
import ./value.bend as V
import ./text.bend as T

def Pr.lit(s: String, acc: String) -> String:
  String.append(s, acc)

# Compact
# -------

def Pr.go(v: V.Json, mode: Nat, acc: String) -> String:
  match v mode:
    case V.JNull{} _:
      Pr.lit("null", acc)
    case V.JBool{True{}} _:
      Pr.lit("true", acc)
    case V.JBool{False{}} _:
      Pr.lit("false", acc)
    case V.JNum{n} _:
      D.Num.show(n, acc)
    case V.JStr{s} _:
      T.quote(s, acc)
    case V.JArr{xs} 1n+m:
      SCon{'[', Pr.go(V.JArr{xs}, m, SCon{']', acc})}
    case V.JArr{Nil{}} 0n:
      acc
    case V.JArr{x <> Nil{}} 0n:
      Pr.go(x, 1n, acc)
    case V.JArr{x <> (y <> t)} 0n:
      Pr.go(x, 1n, SCon{',', Pr.go(V.JArr{y <> t}, 0n, acc)})
    case V.JObj{ms} 1n+m:
      SCon{'{', Pr.go(V.JObj{ms}, m, SCon{'}', acc})}
    case V.JObj{Nil{}} 0n:
      acc
    case V.JObj{V.Mem{k, x} <> Nil{}} 0n:
      T.quote(k, SCon{':', Pr.go(x, 1n, acc)})
    case V.JObj{V.Mem{k, x} <> (y <> t)} 0n:
      T.quote(k, SCon{':', Pr.go(x, 1n, SCon{',', Pr.go(V.JObj{y <> t}, 0n,
        acc)})})

# the compact JSON text of v: no whitespace at all
def print(v: V.Json) -> String:
  Pr.go(v, 1n, SNil{})

# Pretty
# ------

def Pr.spaces(n: Nat, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      SCon{' ', Pr.spaces(p, acc)}

# a newline, then the indent of level lvl
def Pr.nl(+ind: Nat, +lvl: Nat, acc: String) -> String:
  SCon{'\n', Pr.spaces(Nat.mul(lvl, ind), acc)}

# lvl is the level of v's own line; items sit one level deeper
def Pr.pp(v: V.Json, mode: Nat, +ind: Nat, +lvl: Nat, acc: String) -> String:
  match v mode:
    case V.JNull{} _:
      Pr.lit("null", acc)
    case V.JBool{True{}} _:
      Pr.lit("true", acc)
    case V.JBool{False{}} _:
      Pr.lit("false", acc)
    case V.JNum{n} _:
      D.Num.show(n, acc)
    case V.JStr{s} _:
      T.quote(s, acc)
    case V.JArr{Nil{}} 1n+m:
      SCon{'[', SCon{']', acc}}
    case V.JArr{x <> t} 1n+m:
      SCon{'[', Pr.pp(V.JArr{x <> t}, m, ind, 1n+lvl, Pr.nl(ind, lvl,
        SCon{']', acc}))}
    case V.JArr{Nil{}} 0n:
      acc
    case V.JArr{x <> Nil{}} 0n:
      Pr.nl(ind, lvl, Pr.pp(x, 1n, ind, lvl, acc))
    case V.JArr{x <> (y <> t)} 0n:
      Pr.nl(ind, lvl, Pr.pp(x, 1n, ind, lvl, SCon{',', Pr.pp(V.JArr{y <> t},
        0n, ind, lvl, acc)}))
    case V.JObj{Nil{}} 1n+m:
      SCon{'{', SCon{'}', acc}}
    case V.JObj{x <> t} 1n+m:
      SCon{'{', Pr.pp(V.JObj{x <> t}, m, ind, 1n+lvl, Pr.nl(ind, lvl,
        SCon{'}', acc}))}
    case V.JObj{Nil{}} 0n:
      acc
    case V.JObj{V.Mem{k, x} <> Nil{}} 0n:
      Pr.nl(ind, lvl, T.quote(k, SCon{':', SCon{' ', Pr.pp(x, 1n, ind, lvl,
        acc)}}))
    case V.JObj{V.Mem{k, x} <> (y <> t)} 0n:
      Pr.nl(ind, lvl, T.quote(k, SCon{':', SCon{' ', Pr.pp(x, 1n, ind, lvl,
        SCon{',', Pr.pp(V.JObj{y <> t}, 0n, ind, lvl, acc)})}}))

# v over several lines, each nested level indented by ind more spaces
def pretty(+ind: Nat, v: V.Json) -> String:
  Pr.pp(v, 1n, ind, 0n, SNil{})

# the JSON text of a number
def print_number(n: D.Num) -> String:
  D.Num.show(n, SNil{})

# Parallel
# --------
# print_par prints a top-level array in balanced halves, d levels deep,
# each pair of halves forked as one parallel call and joined with a comma.
# The text equals print's (tests.bend checks it); nested values print
# sequentially inside each leaf.

def Pr.halve(+xs: List<&2, V.Json>) -> List<&2, V.Json> & List<&2, V.Json>:
  +n = Nat.div(List.length(&2, V.Json, xs), 2n)
  (List.take(&2, V.Json, xs, n), List.drop(&2, V.Json, xs, n))

# the items of two halves: an empty text is an empty half
def Pr.join(a: String, b: String) -> String:
  match a b:
    case SNil{} y:
      y
    case x SNil{}:
      x
    case SCon{h, t} SCon{h2, t2}:
      String.append(SCon{h, t}, SCon{',', SCon{h2, t2}})

def Pr.par.go(d: Nat, lr: List<&2, V.Json> & List<&2, V.Json>) -> String:
  match d:
    case 0n:
      (l, r) = lr
      Pr.join(Pr.go(V.JArr{l}, 0n, SNil{}), Pr.go(V.JArr{r}, 0n, SNil{}))
    case 1n++p:
      (l, r) = lr
      a b = Pr.par.go(p, Pr.halve(l)) Pr.par.go(p, Pr.halve(r))
      Pr.join(a, b)

def print_par(v: V.Json) -> String:
  match v:
    case V.JArr{xs}:
      SCon{'[', String.append(Pr.par.go(2n, Pr.halve(xs)), "]")}
    case o:
      print(o)
