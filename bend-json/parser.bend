# parser.bend: RFC 8259 JSON text to a value.
#
# The parser is one machine fed one char at a time (P.run folds P.step
# over the input), so its recursion is structural on the input and needs no
# fuel. Arrays and objects in progress live on an explicit stack of
# frames, and room counts how many more may open (the nesting limit).
# A number has no end marker, so it is finished by the first char that
# cannot continue it, which the machine then reads as usual.
#
# An error names the 0-based position of the offending char (the input's
# length for an early end) and a short reason.

import Base
import ./decimal.bend as D
import ./value.bend as V
import ./text.bend as T

type Err is Data:
  Err{pos: Nat, msg: String}

# an open array (items so far, last first) or object (members so far, last
# first, and the key whose value is being read)
type Frame is Data:
  FArr{items: List<&2, V.Json>}
  FObj{items: List<&2, V.Member>, key: String}

type Ctx is Data:
  Ctx{stk: List<&2, Frame>, room: Nat}

# a number in progress: digits are kept least significant first
type NumSt is Data:
  NSign{neg: Bool}
  NInt{neg: Bool, acc: List<&2, D.Digit>}
  NFrac{neg: Bool, acc: List<&2, D.Digit>, fl: Nat}
  NExp{neg: Bool, acc: List<&2, D.Digit>, fl: Nat}
  NExpD{neg: Bool, acc: List<&2, D.Digit>, fl: Nat, eneg: Bool,
    e: List<&2, D.Digit>}

type NRes is Data:
  NGo{ns: NumSt}
  NEnd{n: D.Num}
  NBad{msg: String}

# SVal: a value is due (close: or the ']' of an empty array)
# SKey: a key is due (close: or the '}' of an empty object)
type St is Data:
  SVal{close: Bool, c: Ctx}
  SKey{close: Bool, c: Ctx}
  SKStr{c: Ctx, s: T.Str}
  SColon{c: Ctx, key: String}
  SVStr{c: Ctx, s: T.Str}
  SNum{c: Ctx, ns: NumSt}
  SLit{c: Ctx, rest: String, v: V.Json}
  SDone{c: Ctx, v: V.Json}

type Step is Data:
  Go{st: St}
  Stop{msg: String}

# the end of a run: rem counts the chars from the offending one on
type Out is Data:
  OK{st: St}
  BAD{rem: Nat, msg: String}

# Numbers
# -------

def N.int.digit(neg: Bool, acc: List<&2, D.Digit>, d: D.Digit) -> NRes:
  match acc:
    case Con{D.D0{}, Nil{}}:
      NBad{"leading zero in number"}
    case o:
      NGo{NInt{neg, d <> o}}

def N.int.other(neg: Bool, acc: List<&2, D.Digit>, ch: Char) -> NRes:
  match ch:
    case '.':
      NGo{NFrac{neg, acc, 0n}}
    case 'e':
      NGo{NExp{neg, acc, 0n}}
    case 'E':
      NGo{NExp{neg, acc, 0n}}
    case _:
      NEnd{D.Num.make(neg, acc, False{}, Nil{}, 0n)}

def N.frac.other(neg: Bool, acc: List<&2, D.Digit>, fl: Nat, ch: Char) -> NRes:
  match fl:
    case 0n:
      NBad{"expected a digit after '.'"}
    case 1n+f:
      match ch:
        case 'e':
          NGo{NExp{neg, acc, 1n+f}}
        case 'E':
          NGo{NExp{neg, acc, 1n+f}}
        case _:
          NEnd{D.Num.make(neg, acc, False{}, Nil{}, 1n+f)}

def N.exp.other(neg: Bool, acc: List<&2, D.Digit>, fl: Nat, ch: Char) -> NRes:
  match ch:
    case '+':
      NGo{NExpD{neg, acc, fl, False{}, Nil{}}}
    case '-':
      NGo{NExpD{neg, acc, fl, True{}, Nil{}}}
    case _:
      NBad{"expected a digit in exponent"}

def N.expd.other(neg: Bool, acc: List<&2, D.Digit>, fl: Nat, eneg: Bool,
  e: List<&2, D.Digit>) -> NRes:
  match e:
    case Nil{}:
      NBad{"expected a digit in exponent"}
    case h <> t:
      NEnd{D.Num.make(neg, acc, eneg, h <> t, fl)}

def N.step.at(ns: NumSt, ch: Char, m: Maybe<&2, D.Digit>) -> NRes:
  match ns m:
    case NSign{neg} Some{d}:
      NGo{NInt{neg, [d]}}
    case NSign{neg} None{}:
      NBad{"expected a digit"}
    case NInt{neg, acc} Some{d}:
      N.int.digit(neg, acc, d)
    case NInt{neg, acc} None{}:
      N.int.other(neg, acc, ch)
    case NFrac{neg, acc, fl} Some{d}:
      NGo{NFrac{neg, d <> acc, 1n+fl}}
    case NFrac{neg, acc, fl} None{}:
      N.frac.other(neg, acc, fl, ch)
    case NExp{neg, acc, fl} Some{d}:
      NGo{NExpD{neg, acc, fl, False{}, [d]}}
    case NExp{neg, acc, fl} None{}:
      N.exp.other(neg, acc, fl, ch)
    case NExpD{neg, acc, fl, eneg, e} Some{d}:
      NGo{NExpD{neg, acc, fl, eneg, d <> e}}
    case NExpD{neg, acc, fl, eneg, e} None{}:
      N.expd.other(neg, acc, fl, eneg, e)

def N.step(ns: NumSt, +ch: Char) -> NRes:
  N.step.at(ns, ch, D.Digit.of_char(ch))

# the number, if the input may end here
def N.fin(ns: NumSt) -> Maybe<&2, D.Num>:
  match ns:
    case NInt{neg, acc}:
      Some{D.Num.make(neg, acc, False{}, Nil{}, 0n)}
    case NFrac{neg, acc, 1n+f}:
      Some{D.Num.make(neg, acc, False{}, Nil{}, 1n+f)}
    case NExpD{neg, acc, fl, eneg, h <> t}:
      Some{D.Num.make(neg, acc, eneg, h <> t, fl)}
    case _:
      None{}

# Structure
# ---------

def P.push(c: Ctx, f: Frame) -> Maybe<&2, Ctx>:
  match c:
    case Ctx{stk, 0n}:
      None{}
    case Ctx{stk, 1n+r}:
      Some{Ctx{f <> stk, r}}

def P.open_arr(m: Maybe<&2, Ctx>) -> Step:
  match m:
    case None{}:
      Stop{"maximum nesting depth exceeded"}
    case Some{c}:
      Go{SVal{True{}, c}}

def P.open_obj(m: Maybe<&2, Ctx>) -> Step:
  match m:
    case None{}:
      Stop{"maximum nesting depth exceeded"}
    case Some{c}:
      Go{SKey{True{}, c}}

def P.num_go(c: Ctx, r: NRes) -> Step:
  match r:
    case NGo{ns}:
      Go{SNum{c, ns}}
    case NEnd{n}:
      Stop{"unexpected character"}
    case NBad{msg}:
      Stop{msg}

# the first char of a value
def P.start(c: Ctx, ch: Char) -> Step:
  match ch:
    case '[':
      P.open_arr(P.push(c, FArr{Nil{}}))
    case '{':
      P.open_obj(P.push(c, FObj{Nil{}, SNil{}}))
    case '"':
      Go{SVStr{c, T.StrBody{SNil{}}}}
    case 't':
      Go{SLit{c, "rue", V.JBool{True{}}}}
    case 'f':
      Go{SLit{c, "alse", V.JBool{False{}}}}
    case 'n':
      Go{SLit{c, "ull", V.JNull{}}}
    case '-':
      Go{SNum{c, NSign{True{}}}}
    case o:
      P.num_go(c, N.step(NSign{False{}}, o))

def P.comma(c: Ctx, v: V.Json) -> Step:
  match c:
    case Ctx{FArr{items} <> rest, room}:
      Go{SVal{False{}, Ctx{FArr{v <> items} <> rest, room}}}
    case Ctx{FObj{items, key} <> rest, room}:
      Go{SKey{False{}, Ctx{FObj{V.Mem{key, v} <> items, SNil{}} <> rest, room}}}
    case Ctx{Nil{}, room}:
      Stop{"unexpected ',' after the value"}

def P.close_arr(c: Ctx, v: V.Json) -> Step:
  match c:
    case Ctx{FArr{items} <> rest, room}:
      Go{SDone{Ctx{rest, 1n+room}, V.JArr{List.reverse(&2, V.Json, v <> items)}}}
    case _:
      Stop{"unexpected ']'"}

def P.close_obj(c: Ctx, v: V.Json) -> Step:
  match c:
    case Ctx{FObj{items, key} <> rest, room}:
      Go{SDone{Ctx{rest, 1n+room},
        V.JObj{List.reverse(&2, V.Member, V.Mem{key, v} <> items)}}}
    case _:
      Stop{"unexpected '}'"}

def P.junk(c: Ctx) -> Step:
  match c:
    case Ctx{Nil{}, room}:
      Stop{"unexpected character after the value"}
    case Ctx{FArr{items} <> rest, room}:
      Stop{"expected ',' or ']'"}
    case Ctx{FObj{items, key} <> rest, room}:
      Stop{"expected ',' or '}'"}

# the char after a complete value v
def P.after(c: Ctx, v: V.Json, ch: Char) -> Step:
  match ch:
    case ' ':
      Go{SDone{c, v}}
    case '\t':
      Go{SDone{c, v}}
    case '\n':
      Go{SDone{c, v}}
    case '\r':
      Go{SDone{c, v}}
    case ',':
      P.comma(c, v)
    case ']':
      P.close_arr(c, v)
    case '}':
      P.close_obj(c, v)
    case _:
      P.junk(c)

def P.close_empty_arr(c: Ctx) -> Step:
  match c:
    case Ctx{FArr{Nil{}} <> rest, room}:
      Go{SDone{Ctx{rest, 1n+room}, V.JArr{Nil{}}}}
    case _:
      Stop{"unexpected ']'"}

def P.close_empty_obj(c: Ctx) -> Step:
  match c:
    case Ctx{FObj{Nil{}, k} <> rest, room}:
      Go{SDone{Ctx{rest, 1n+room}, V.JObj{Nil{}}}}
    case _:
      Stop{"unexpected '}'"}

def P.val.close(close: Bool, c: Ctx) -> Step:
  match close:
    case True{}:
      P.close_empty_arr(c)
    case False{}:
      Stop{"expected a value"}

def P.val(close: Bool, c: Ctx, ch: Char) -> Step:
  match ch:
    case ' ':
      Go{SVal{close, c}}
    case '\t':
      Go{SVal{close, c}}
    case '\n':
      Go{SVal{close, c}}
    case '\r':
      Go{SVal{close, c}}
    case ']':
      P.val.close(close, c)
    case o:
      P.start(c, o)

def P.key.close(close: Bool, c: Ctx) -> Step:
  match close:
    case True{}:
      P.close_empty_obj(c)
    case False{}:
      Stop{"expected a string key"}

def P.key(close: Bool, c: Ctx, ch: Char) -> Step:
  match ch:
    case ' ':
      Go{SKey{close, c}}
    case '\t':
      Go{SKey{close, c}}
    case '\n':
      Go{SKey{close, c}}
    case '\r':
      Go{SKey{close, c}}
    case '"':
      Go{SKStr{c, T.StrBody{SNil{}}}}
    case '}':
      P.key.close(close, c)
    case _:
      Stop{"expected a string key"}

def P.setkey(c: Ctx, key: String) -> Ctx:
  match c:
    case Ctx{FObj{items, k} <> rest, room}:
      Ctx{FObj{items, key} <> rest, room}
    case o:
      o

def P.colon(c: Ctx, key: String, ch: Char) -> Step:
  match ch:
    case ' ':
      Go{SColon{c, key}}
    case '\t':
      Go{SColon{c, key}}
    case '\n':
      Go{SColon{c, key}}
    case '\r':
      Go{SColon{c, key}}
    case ':':
      Go{SVal{False{}, P.setkey(c, key)}}
    case _:
      Stop{"expected ':'"}

def P.kstr(c: Ctx, r: T.SRes) -> Step:
  match r:
    case T.SCont{s}:
      Go{SKStr{c, s}}
    case T.SFin{k}:
      Go{SColon{c, k}}
    case T.SBad{msg}:
      Stop{msg}

def P.vstr(c: Ctx, r: T.SRes) -> Step:
  match r:
    case T.SCont{s}:
      Go{SVStr{c, s}}
    case T.SFin{x}:
      Go{SDone{c, V.JStr{x}}}
    case T.SBad{msg}:
      Stop{msg}

def P.num(c: Ctx, ch: Char, r: NRes) -> Step:
  match r:
    case NGo{ns}:
      Go{SNum{c, ns}}
    case NEnd{n}:
      P.after(c, V.JNum{n}, ch)
    case NBad{msg}:
      Stop{msg}

def P.lit.at(c: Ctx, v: V.Json, ok: Bool, rt: String) -> Step:
  match ok rt:
    case False{} _:
      Stop{"invalid literal"}
    case True{} SNil{}:
      Go{SDone{c, v}}
    case True{} SCon{h, t}:
      Go{SLit{c, SCon{h, t}, v}}

def P.lit(c: Ctx, rest: String, v: V.Json, ch: Char) -> Step:
  match rest:
    case SNil{}:
      Stop{"invalid literal"}
    case SCon{r, rt}:
      P.lit.at(c, v, Char.is_eq(ch, r), rt)

def P.step(st: St, +ch: Char) -> Step:
  match st:
    case SVal{close, c}:
      P.val(close, c, ch)
    case SKey{close, c}:
      P.key(close, c, ch)
    case SKStr{c, s}:
      P.kstr(c, T.Str.step(s, ch))
    case SColon{c, key}:
      P.colon(c, key, ch)
    case SVStr{c, s}:
      P.vstr(c, T.Str.step(s, ch))
    case SNum{c, ns}:
      P.num(c, ch, N.step(ns, ch))
    case SLit{c, rest, v}:
      P.lit(c, rest, v, ch)
    case SDone{c, v}:
      P.after(c, v, ch)

def P.run(s: String, r: Step) -> Out:
  match s r:
    case t Stop{msg}:
      BAD{1n+String.length(t), msg}
    case SNil{} Go{st}:
      OK{st}
    case SCon{c, t} Go{st}:
      P.run(t, P.step(st, c))

# Entry points
# ------------

def P.eof.num(m: Maybe<&2, D.Num>, +total: Nat) ->
  Result<&2, &2, Err, V.Json>:
  match m:
    case None{}:
      Fail{Err{total, "unexpected end of input in number"}}
    case Some{n}:
      Done{V.JNum{n}}

def P.eof(st: St, +total: Nat) -> Result<&2, &2, Err, V.Json>:
  match st:
    case SDone{Ctx{Nil{}, room}, v}:
      Done{v}
    case SNum{Ctx{Nil{}, room}, ns}:
      P.eof.num(N.fin(ns), total)
    case _:
      Fail{Err{total, "unexpected end of input"}}

def P.out(o: Out, +total: Nat) -> Result<&2, &2, Err, V.Json>:
  match o:
    case OK{st}:
      P.eof(st, total)
    case BAD{rem, msg}:
      Fail{Err{Nat.sub(total, rem), msg}}

def P.init(max: Nat) -> Step:
  Go{SVal{False{}, Ctx{Nil{}, max}}}

# parses a JSON text whose arrays and objects nest at most max deep
def parse_with(max: Nat, +s: String) -> Result<&2, &2, Err, V.Json>:
  P.out(P.run(s, P.init(max)), String.length(s))

def default_depth() -> Nat:
  512n

def parse(+s: String) -> Result<&2, &2, Err, V.Json>:
  parse_with(default_depth(), s)

def parse_number.of(r: Result<&2, &2, Err, V.Json>) -> Maybe<&2, D.Num>:
  match r:
    case Done{V.JNum{n}}:
      Some{n}
    case _:
      None{}

# a JSON text that is one number
def parse_number(+s: String) -> Maybe<&2, D.Num>:
  parse_number.of(parse(s))

def Err.show(e: Err) -> String:
  match e:
    case Err{pos, msg}:
      "at " ++ Nat.show(pos) ++ ": " ++ msg
