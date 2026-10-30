# utf8.bend: strict UTF-8 bytes to a String (RFC 3629), for reading JSON
# files byte for byte. Overlong forms, surrogates, code points past
# U+10FFFF and truncated sequences are refused.

import Base

# need: continuation bytes still due; lo..hi: the range of the next one
type U8 is Data:
  U8{need: Nat, val: U32, lo: U32, hi: U32, acc: String}
  U8Bad{}

def U8.ok(acc: String) -> U8:
  U8{0n, 0, 128, 191, acc}

def U8.lead4.c(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{3n, 4, 128, 143, acc}
    case False{}:
      U8Bad{}

def U8.lead4.b(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{3n, (b .&. 7 : U32), 128, 191, acc}
    case False{}:
      U8.lead4.c(b, acc, U32.is_eq(b, 244))

def U8.lead4(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{3n, 0, 144, 191, acc}
    case False{}:
      U8.lead4.b(b, acc, (b <= 243 : U32))

def U8.lead3.c(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{2n, (b .&. 15 : U32), 128, 191, acc}
    case False{}:
      U8.lead4(b, acc, U32.is_eq(b, 240))

def U8.lead3.b(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{2n, 13, 128, 159, acc}
    case False{}:
      U8.lead3.c(b, acc, (b <= 239 : U32))

def U8.lead3(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{2n, 0, 160, 191, acc}
    case False{}:
      U8.lead3.b(b, acc, U32.is_eq(b, 237))

def U8.lead.c(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8{1n, (b .&. 31 : U32), 128, 191, acc}
    case False{}:
      U8.lead3(b, acc, U32.is_eq(b, 224))

def U8.lead.b(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8Bad{}
    case False{}:
      U8.lead.c(b, acc, (b <= 223 : U32))

def U8.lead(+b: U32, acc: String, x: Bool) -> U8:
  match x:
    case True{}:
      U8.ok(SCon{Chr{b}, acc})
    case False{}:
      U8.lead.b(b, acc, (b < 194 : U32))

def U8.cont(ok: Bool, p: Nat, +v: U32, acc: String) -> U8:
  match ok p:
    case False{} _:
      U8Bad{}
    case True{} 0n:
      U8.ok(SCon{Chr{v}, acc})
    case True{} 1n+q:
      U8{1n+q, v, 128, 191, acc}

def U8.step(st: U8, +b: U32) -> U8:
  match st:
    case U8Bad{}:
      U8Bad{}
    case U8{0n, val, lo, hi, acc}:
      U8.lead(b, acc, (b < 128 : U32))
    case U8{1n+p, val, +lo, +hi, acc}:
      U8.cont(Bool.and((b >= lo : U32), (b <= hi : U32)), p,
        ((val << 6n) .|. (b .&. 63) : U32), acc)

def U8.go(bs: List<&2, U32>, st: U8) -> U8:
  match bs:
    case Nil{}:
      st
    case b <> t:
      U8.go(t, U8.step(st, b))

def U8.fin(st: U8) -> Maybe<&2, String>:
  match st:
    case U8{0n, val, lo, hi, acc}:
      Some{String.reverse(acc)}
    case _:
      None{}

def decode(bs: List<&2, U32>) -> Maybe<&2, String>:
  U8.fin(U8.go(bs, U8.ok(SNil{})))
