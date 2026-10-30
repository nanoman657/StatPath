# text.bend: JSON string escaping and the string decoder.
#
# escape writes the body of a JSON string (no quotes). It escapes " and \,
# writes each control character below 0x20 as \b \t \n \f \r or \u00xx,
# and keeps every other character as it is (including non-ASCII, which
# RFC 8259 allows raw). Both escape and the decoder classify a raw char
# with the same Esc.kind, which is what makes them inverse.
#
# The decoder is a char-at-a-time machine (Str.step) that the parser runs
# inside its own loop. It rejects raw control characters, invalid escapes,
# bad \u digits and lone surrogates, and joins \uD8xx\uDCxx pairs.

import Base

type CKind is Data:
  KPlain{}
  KQuote{}
  KBack{}
  KCtl{}

# the decoder's state; acc holds the decoded chars, last first
type Str is Data:
  StrBody{acc: String}
  StrEsc{acc: String}
  StrHex{acc: String, n: Nat, v: U32}
  StrLow1{acc: String, hi: U32}
  StrLow2{acc: String, hi: U32}
  StrLowHex{acc: String, hi: U32, n: Nat, v: U32}

# a step's outcome: go on, the closing quote (with the decoded string), or
# an error
type SRes is Data:
  SCont{s: Str}
  SFin{str: String}
  SBad{msg: String}

# Classification
# --------------

def Esc.kind.c(b: Bool) -> CKind:
  match b:
    case True{}:
      KBack{}
    case False{}:
      KPlain{}

def Esc.kind.b(+x: U32, q: Bool) -> CKind:
  match q:
    case True{}:
      KQuote{}
    case False{}:
      Esc.kind.c(U32.is_eq(x, 92))

def Esc.kind.a(+x: U32, ctl: Bool) -> CKind:
  match ctl:
    case True{}:
      KCtl{}
    case False{}:
      Esc.kind.b(x, U32.is_eq(x, 34))

# a raw char: a control (below 0x20), the quote, the backslash, or plain
def Esc.kind(+x: U32) -> CKind:
  Esc.kind.a(x, U32.is_lt(x, 32))

# Escaping
# --------

def Hex.digit(+n: U32) -> Char:
  Chr{(n + 48 + Bool.to_u32((n > 9 : U32)) * 39 : U32)}

def Esc.ctl.u(+x: U32, acc: String) -> String:
  SCon{'\\', SCon{'u', SCon{'0', SCon{'0', SCon{Hex.digit((x >> 4n : U32)),
    SCon{Hex.digit((x .&. 15 : U32)), acc}}}}}}

def Esc.ctl.r(+x: U32, acc: String, b: Bool) -> String:
  match b:
    case True{}:
      SCon{'\\', SCon{'r', acc}}
    case False{}:
      Esc.ctl.u(x, acc)

def Esc.ctl.f(+x: U32, acc: String, b: Bool) -> String:
  match b:
    case True{}:
      SCon{'\\', SCon{'f', acc}}
    case False{}:
      Esc.ctl.r(x, acc, U32.is_eq(x, 13))

def Esc.ctl.n(+x: U32, acc: String, b: Bool) -> String:
  match b:
    case True{}:
      SCon{'\\', SCon{'n', acc}}
    case False{}:
      Esc.ctl.f(x, acc, U32.is_eq(x, 12))

def Esc.ctl.t(+x: U32, acc: String, b: Bool) -> String:
  match b:
    case True{}:
      SCon{'\\', SCon{'t', acc}}
    case False{}:
      Esc.ctl.n(x, acc, U32.is_eq(x, 10))

# a control char: the short escape if it has one, else \u00xx
def Esc.ctl.b(+x: U32, acc: String, b: Bool) -> String:
  match b:
    case True{}:
      SCon{'\\', SCon{'b', acc}}
    case False{}:
      Esc.ctl.t(x, acc, U32.is_eq(x, 9))

def Esc.ctl(+x: U32, acc: String) -> String:
  Esc.ctl.b(x, acc, U32.is_eq(x, 8))

def Esc.char.k(+x: U32, k: CKind, acc: String) -> String:
  match k:
    case KPlain{}:
      SCon{Chr{x}, acc}
    case KQuote{}:
      SCon{'\\', SCon{'"', acc}}
    case KBack{}:
      SCon{'\\', SCon{'\\', acc}}
    case KCtl{}:
      Esc.ctl(x, acc)

def Esc.char(c: Char, acc: String) -> String:
  match c:
    case Chr{+x}:
      Esc.char.k(x, Esc.kind(x), acc)

# the escaped body of s, in front of acc
def Esc.go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      Esc.char(c, Esc.go(t, acc))

def escape(s: String) -> String:
  Esc.go(s, SNil{})

# s as a JSON string literal, quotes included, in front of acc
def quote(s: String, acc: String) -> String:
  SCon{'"', Esc.go(s, SCon{'"', acc})}

# Decoding
# --------

def Hex.val(c: Char) -> Maybe<&2, U32>:
  match c:
    case '0':
      Some{0}
    case '1':
      Some{1}
    case '2':
      Some{2}
    case '3':
      Some{3}
    case '4':
      Some{4}
    case '5':
      Some{5}
    case '6':
      Some{6}
    case '7':
      Some{7}
    case '8':
      Some{8}
    case '9':
      Some{9}
    case 'a':
      Some{10}
    case 'b':
      Some{11}
    case 'c':
      Some{12}
    case 'd':
      Some{13}
    case 'e':
      Some{14}
    case 'f':
      Some{15}
    case 'A':
      Some{10}
    case 'B':
      Some{11}
    case 'C':
      Some{12}
    case 'D':
      Some{13}
    case 'E':
      Some{14}
    case 'F':
      Some{15}
    case _:
      None{}

def Str.body(acc: String, x: U32) -> SRes:
  SCont{StrBody{SCon{Chr{x}, acc}}}

def Str.raw(acc: String, +x: U32, k: CKind) -> SRes:
  match k:
    case KPlain{}:
      Str.body(acc, x)
    case KQuote{}:
      SFin{String.reverse(acc)}
    case KBack{}:
      SCont{StrEsc{acc}}
    case KCtl{}:
      SBad{"unescaped control character in string"}

def Str.esc(acc: String, ch: Char) -> SRes:
  match ch:
    case '"':
      Str.body(acc, 34)
    case '\\':
      Str.body(acc, 92)
    case '/':
      Str.body(acc, 47)
    case 'b':
      Str.body(acc, 8)
    case 'f':
      Str.body(acc, 12)
    case 'n':
      Str.body(acc, 10)
    case 'r':
      Str.body(acc, 13)
    case 't':
      Str.body(acc, 9)
    case 'u':
      SCont{StrHex{acc, 4n, 0}}
    case _:
      SBad{"invalid escape in string"}

def Str.unit.b(acc: String, +u: U32, high: Bool) -> SRes:
  match high:
    case True{}:
      SCont{StrLow1{acc, u}}
    case False{}:
      SBad{"lone low surrogate in \\u escape"}

# a \u unit: a high surrogate waits for its low half, a lone low one fails
def Str.unit.a(acc: String, +u: U32, sur: Bool) -> SRes:
  match sur:
    case False{}:
      Str.body(acc, u)
    case True{}:
      Str.unit.b(acc, u, (u <= 56319 : U32))

def Str.unit(acc: String, +u: U32) -> SRes:
  Str.unit.a(acc, u, (u >= 55296 : U32) && (u <= 57343 : U32))

def Str.hex(m: Maybe<&2, U32>, acc: String, n: Nat, +v: U32) -> SRes:
  match m:
    case None{}:
      SBad{"invalid hex digit in \\u escape"}
    case Some{h}:
      match n:
        case 0n:
          SBad{"invalid \\u escape"}
        case 1n:
          Str.unit(acc, ((v << 4n) .|. h : U32))
        case 2n+p:
          SCont{StrHex{acc, 1n+p, ((v << 4n) .|. h : U32)}}

def Str.pair.at(acc: String, +hi: U32, +lo: U32, low: Bool) -> SRes:
  match low:
    case True{}:
      Str.body(acc, (65536 + ((hi - 55296 : U32) << 10n) + (lo - 56320) : U32))
    case False{}:
      SBad{"lone high surrogate in \\u escape"}

def Str.pair(acc: String, +hi: U32, +lo: U32) -> SRes:
  Str.pair.at(acc, hi, lo, (lo >= 56320 : U32) && (lo <= 57343 : U32))

def Str.lowhex(m: Maybe<&2, U32>, acc: String, +hi: U32, n: Nat, +v: U32) ->
  SRes:
  match m:
    case None{}:
      SBad{"invalid hex digit in \\u escape"}
    case Some{h}:
      match n:
        case 0n:
          SBad{"invalid \\u escape"}
        case 1n:
          Str.pair(acc, hi, ((v << 4n) .|. h : U32))
        case 2n+p:
          SCont{StrLowHex{acc, hi, 1n+p, ((v << 4n) .|. h : U32)}}

# one char of a string body
def Str.step(s: Str, ch: Char) -> SRes:
  match s:
    case StrBody{acc}:
      match ch:
        case Chr{+x}:
          Str.raw(acc, x, Esc.kind(x))
    case StrEsc{acc}:
      Str.esc(acc, ch)
    case StrHex{acc, n, v}:
      Str.hex(Hex.val(ch), acc, n, v)
    case StrLow1{acc, hi}:
      match ch:
        case '\\':
          SCont{StrLow2{acc, hi}}
        case _:
          SBad{"lone high surrogate in \\u escape"}
    case StrLow2{acc, hi}:
      match ch:
        case 'u':
          SCont{StrLowHex{acc, hi, 4n, 0}}
        case _:
          SBad{"lone high surrogate in \\u escape"}
    case StrLowHex{acc, hi, n, v}:
      Str.lowhex(Hex.val(ch), acc, hi, n, v)

def Str.run(s: String, r: SRes) -> SRes:
  match s r:
    case SCon{c, t} SCont{st}:
      Str.run(t, Str.step(st, c))
    case SCon{c, t} SFin{x}:
      SBad{"unescaped quote in string"}
    case _ x:
      x

def Str.done(r: SRes) -> Maybe<&2, String>:
  match r:
    case SCont{StrBody{acc}}:
      Some{String.reverse(acc)}
    case _:
      None{}

# decodes the body of a JSON string (no quotes): None if it is not one
def unescape(s: String) -> Maybe<&2, String>:
  Str.done(Str.run(s, SCont{StrBody{SNil{}}}))
