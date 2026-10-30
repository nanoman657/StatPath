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

# the items text of a list
def Pr.items(xs: List<&2, V.Json>) -> String:
  Pr.go(V.JArr{xs}, 0n, SNil{})

# the items of l then r, given their texts a and b
def Pr.joinl(l: List<&2, V.Json>, r: List<&2, V.Json>, a: String, b: String) -> String:
  match l r:
    case Nil{} r0:
      b
    case Con{x, t} Nil{}:
      a
    case Con{x, t} Con{y, u}:
      String.append(a, SCon{',', b})

# the items of l ++ r: d more levels of balanced, forked halves
def Pr.par.go(d: Nat, +l: List<&2, V.Json>, +r: List<&2, V.Json>) -> String:
  match d:
    case 0n:
      Pr.joinl(l, r, Pr.items(l), Pr.items(r))
    case 1n++p:
      +hl = Nat.div(List.length(&2, V.Json, l), 2n)
      +hr = Nat.div(List.length(&2, V.Json, r), 2n)
      a b = Pr.par.go(p, List.take(&2, V.Json, l, hl), List.drop(&2, V.Json, l, hl)) Pr.par.go(p, List.take(&2, V.Json, r, hr), List.drop(&2, V.Json, r, hr))
      Pr.joinl(l, r, a, b)

def Pr.par.depth() -> Nat:
  2n

def print_par(v: V.Json) -> String:
  match v:
    case V.JArr{+xs}:
      +h = Nat.div(List.length(&2, V.Json, xs), 2n)
      SCon{'[', String.append(Pr.par.go(Pr.par.depth(), List.take(&2, V.Json, xs, h),
        List.drop(&2, V.Json, xs, h)), "]")}
    case o:
      print(o)
