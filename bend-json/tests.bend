# tests.bend: the test table. Each case computes a string and names the
# string it must equal ("err" accepts an error at any position).
#
#   bend tests.bend                 (JS)
#   bend tests.bend -o tests && ./tests   (native)

import Base
import ./decimal.bend as D
import ./value.bend as V
import ./text.bend as T
import ./parser.bend as P
import ./printer.bend as Pr

type Case is Data:
  Case{name: String, got: String, want: String}

def res(r: Result<&2, &2, P.Err, V.Json>) -> String:
  match r:
    case Done{v}:
      "ok " ++ Pr.print(v)
    case Fail{P.Err{pos, msg}}:
      "err@" ++ Nat.show(pos)

# parse, then print compactly
def pc(+input: String, want: String) -> Case:
  Case{input, res(P.parse(input)), want}

def pretty_res(+ind: Nat, r: Result<&2, &2, P.Err, V.Json>) -> String:
  match r:
    case Done{v}:
      Pr.pretty(ind, v)
    case Fail{e}:
      "err"

def pp(+ind: Nat, +input: String, want: String) -> Case:
  Case{input, pretty_res(ind, P.parse(input)), want}

# parse, print, parse again: the same value (both printers)
def rt.at(+input: String, r: Result<&2, &2, P.Err, V.Json>) -> Case:
  match r:
    case Done{+v}:
      Case{"roundtrip " ++ input, Bool.show(Bool.and(
        Result.default(&2, &2, P.Err, Bool, Result.map(&2, &2, P.Err, V.Json, Bool,
          V.Json.is_eq(v), P.parse(Pr.print(v))), False{}),
        Result.default(&2, &2, P.Err, Bool, Result.map(&2, &2, P.Err, V.Json, Bool,
          V.Json.is_eq(v), P.parse(Pr.pretty(3n, v))), False{}))), "True"}
    case Fail{e}:
      Case{"roundtrip " ++ input, "parse failed", "True"}

def rt(+input: String) -> Case:
  rt.at(input, P.parse(input))

def nest(n: Nat) -> String:
  +m = n
  String.repeat("[", m) ++ String.repeat("]", m)

def mres(m: Maybe<&2, String>) -> String:
  Maybe.default(&2, String, m, "None")

def esc(+s: String) -> Case:
  Case{"escape " ++ T.escape(s), Maybe.show(~&2, ~String, ~String.quote,
    T.unescape(T.escape(s))), Maybe.show(~&2, ~String, ~String.quote, Some{s})}

def num(+input: String) -> D.Num:
  Maybe.default(&2, D.Num, P.parse_number(input), D.Num.zero())

def u32s(m: Maybe<&2, U32>) -> String:
  Maybe.show(~&2, ~U32, ~U32.show, m)

def nats(m: Maybe<&2, Nat>) -> String:
  Maybe.show(~&2, ~Nat, ~Nat.show, m)

def f32b(+input: String) -> String:
  U32.show(F32.bits(D.Num.to_f32(num(input))))

def get.at(r: Result<&2, &2, P.Err, V.Json>, +key: String) -> String:
  match r:
    case Done{v}:
      Maybe.show(~&2, ~V.Json, ~Pr.print, V.Json.get(v, key))
    case Fail{e}:
      "err"

def get(+input: String, +key: String) -> String:
  get.at(P.parse(input), key)

def all_ctl(n: Nat, acc: String) -> String:
  match n:
    case 0n:
      SCon{Chr{0}, acc}
    case 1n++p:
      all_ctl(p, SCon{Chr{U32.from_nat(1n+p)}, acc})

def cases_0() -> List<&2, Case>:
  pc("null", "ok null") <>
  pc("true", "ok true") <>
  pc("false", "ok false") <>
  pc(" [1, 2 ,3 ] ", "ok [1,2,3]") <>
  pc("[]", "ok []") <>
  pc("{}", "ok {}") <>
  pc("[[]]", "ok [[]]") <>
  pc("{\"a\":{}}", "ok {\"a\":{}}") <>
  pc("\t\n\r [\n1\r\n]\t", "ok [1]") <>
  pc("{\"a\":1,\"a\":2}", "ok {\"a\":1,\"a\":2}") <>
  pc("{ \"k\" : [ true , null ] }", "ok {\"k\":[true,null]}") <>
  pc("[{\"a\":[{\"b\":[]}]}]", "ok [{\"a\":[{\"b\":[]}]}]") <>
  pc("\"\"", "ok \"\"") <>
  pc("\"abc\"", "ok \"abc\"") <>
  pc("\"\\u0041\"", "ok \"A\"") <>
  pc("\"\\u00e9\"", "ok \"\u{e9}\"") <>
  pc("\"\\ud83d\\ude00\"", "ok \"\u{1f600}\"") <>
  pc("\"\\uD834\\uDD1E\"", "ok \"\u{1d11e}\"") <>
  pc("\"\\\"\\\\\\/\\b\\f\\n\\r\\t\"", "ok \"\\\"\\\\/\\b\\f\\n\\r\\t\"") <>
  pc("\"\\u0000\"", "ok \"\\u0000\"") <>
  pc("\"\\u001F\"", "ok \"\\u001f\"") <>
  pc("\"\\u007f\"", "ok \"\u{7f}\"") <>
  pc("\"\u{e9}\u{1f600}\"", "ok \"\u{e9}\u{1f600}\"") <>
  pc("\"\\uFFFF\"", "ok \"\u{ffff}\"") <>
  pc("0", "ok 0") <>
  pc("-0", "ok 0") <>
  pc("1.5", "ok 1.5") <>
  pc("-1.5e10", "ok -15000000000") <>
  pc("19.99", "ok 19.99") <>
  pc("1E400", "ok 1e+400") <>
  Nil{}

def cases_1() -> List<&2, Case>:
  pc("1e-400", "ok 1e-400") <>
  pc("0.000001", "ok 0.000001") <>
  pc("1.0", "ok 1") <>
  pc("100", "ok 100") <>
  pc("1e2", "ok 100") <>
  pc("123.456e-2", "ok 1.23456") <>
  pc("0e10", "ok 0") <>
  pc("-0.0e-5", "ok 0") <>
  pc("12345678901234567890123456789", "ok 12345678901234567890123456789") <>
  pc("1E+2", "ok 100") <>
  pc("1e02", "ok 100") <>
  pc("0.5", "ok 0.5") <>
  pc("-0.25", "ok -0.25") <>
  pc("1e-7", "ok 1e-7") <>
  pc("10.0e-1", "ok 1") <>
  pc("2.50", "ok 2.5") <>
  pc("1e21", "ok 1e+21") <>
  pc("1e20", "ok 100000000000000000000") <>
  pc("[-1,0.1,2e-3]", "ok [-1,0.1,0.002]") <>
  pc("123456789.123456789e9", "ok 123456789123456789") <>
  pc("0.0000001e7", "ok 1") <>
  pc("4.5e-1000000", "ok 45e-1000001") <>
  pc("", "err@0") <>
  pc("   ", "err@3") <>
  pc("[1,]", "err@3") <>
  pc("[1 2]", "err@3") <>
  pc("{\"a\":1,}", "err@7") <>
  pc("01", "err@1") <>
  pc("-01", "err@2") <>
  pc("00", "err@1") <>
  Nil{}

def cases_2() -> List<&2, Case>:
  pc("1.", "err@2") <>
  pc(".5", "err@0") <>
  pc("1e", "err@2") <>
  pc("1e+", "err@3") <>
  pc("+1", "err@0") <>
  pc("NaN", "err@0") <>
  pc("Infinity", "err@0") <>
  pc("-Infinity", "err@1") <>
  pc("0x10", "err@1") <>
  pc("'a'", "err@0") <>
  pc("[1] x", "err@4") <>
  pc("/* c */ 1", "err@0") <>
  pc("1 // c", "err@2") <>
  pc("\"a\u{1}\"", "err@2") <>
  pc("\"\\x\"", "err@2") <>
  pc("\"\\ud800\"", "err@7") <>
  pc("\"\\udc00\"", "err@6") <>
  pc("\"\\ud800\\u0041\"", "err@12") <>
  pc("\"\\u12\"", "err@5") <>
  pc("[", "err@1") <>
  pc("{\"a\"}", "err@4") <>
  pc("{a:1}", "err@1") <>
  pc("\u{a0}1", "err@0") <>
  pc("\u{c}1", "err@0") <>
  pc("tru", "err@3") <>
  pc("nul", "err@3") <>
  pc("truex", "err@4") <>
  pc("[1,,2]", "err@3") <>
  pc("[,1]", "err@1") <>
  pc("{\"a\":1 \"b\":2}", "err@7") <>
  Nil{}

def cases_3() -> List<&2, Case>:
  pc("{\"a\" 1}", "err@5") <>
  pc("[\"a\tb\"]", "err@3") <>
  pc("\"abc", "err@4") <>
  pc("[1]]", "err@3") <>
  pc("{}}", "err@2") <>
  pc("1 2", "err@2") <>
  pc("{\"a\":}", "err@5") <>
  pc("[-]", "err@2") <>
  pc("-", "err@1") <>
  pc("2.e3", "err@2") <>
  pc("1.5e", "err@4") <>
  pc("[1.]", "err@3") <>
  pc("\"\\u00G0\"", "err@5") <>
  pc("\"\\\"", "err@3") <>
  pc("\u{feff}{}", "err@0") <>
  pc("[1e]", "err@3") <>
  pc("[1e-]", "err@4") <>
  pc("[True]", "err@1") <>
  pc("\"\\U0041\"", "err@2") <>
  pc(nest(512n), "ok " ++ nest(512n)) <>
  pc(nest(513n), "err@512") <>
  Case{"parse_with 2", res(P.parse_with(2n, "[[1]]")), "ok [[1]]"} <>
  Case{"parse_with 2 deep", res(P.parse_with(2n, "[[[1]]]")), "err@2"} <>
  Case{"parse_with 0 scalar", res(P.parse_with(0n, "7")), "ok 7"} <>
  Case{"parse_with 0 obj", res(P.parse_with(0n, "{}")), "err@0"} <>
  pp(2n, "{\"a\":[1,2],\"b\":{},\"c\":[]}", "{\n  \"a\": [\n    1,\n    2\n  ],\n  \"b\": {},\n  \"c\": []\n}") <>
  pp(0n, "[[1]]", "[\n[\n1\n]\n]") <>
  pp(4n, "7", "7") <>
  rt("{\"a\":[1,2.5e-3,{\"b\":null}],\"c\":\"x\\ny\",\"d\":[[],{}],\"a\":-0.0}") <>
  rt("[\"\\u0000\\u001f\\u0020\\\\\\\"\",1e999999999999999999,true,false]") <>
  Nil{}

def cases_4() -> List<&2, Case>:
  esc("") <>
  esc("plain") <>
  esc("q\"b\\s/") <>
  esc(all_ctl(31n, SNil{})) <>
  esc("\u{7f}\u{e9}\u{1f600}\u{10ffff}") <>
  esc(SCon{Chr{55296}, SCon{Chr{57343}, SCon{Chr{1114112}, SNil{}}}}) <>
  Case{"escape ctl", T.escape(SCon{Chr{1}, SCon{Chr{8}, SCon{Chr{31}, "\n"}}}), "\\u0001\\b\\u001f\\n"} <>
  Case{"unescape bad", mres(T.unescape("a\"b")), "None"} <>
  Case{"unescape bad2", mres(T.unescape("a\\")), "None"} <>
  Case{"unescape pair", mres(T.unescape("\\ud83d\\ude00")), "\u{1f600}"} <>
  Case{"get last", get("{\"a\":1,\"b\":2,\"a\":3}", "a"), "Some(3)"} <>
  Case{"get missing", get("{\"a\":1}", "z"), "None"} <>
  Case{"get array", get("[1]", "a"), "None"} <>
  Case{"to_u32 max", u32s(D.Num.to_u32(num("4294967295"))), "Some(4294967295)"} <>
  Case{"to_u32 over", u32s(D.Num.to_u32(num("4294967296"))), "None"} <>
  Case{"to_u32 exp", u32s(D.Num.to_u32(num("4.2e3"))), "Some(4200)"} <>
  Case{"to_u32 frac", u32s(D.Num.to_u32(num("1.5"))), "None"} <>
  Case{"to_u32 neg", u32s(D.Num.to_u32(num("-1"))), "None"} <>
  Case{"to_u32 zero", u32s(D.Num.to_u32(num("-0.0"))), "Some(0)"} <>
  Case{"to_u32 big", u32s(D.Num.to_u32(num("1e400"))), "None"} <>
  Case{"to_nat max", nats(D.Num.to_nat(num("281474976710655"))), "Some(281474976710655)"} <>
  Case{"to_nat over", nats(D.Num.to_nat(num("281474976710656"))), "None"} <>
  Case{"to_nat 1e14", nats(D.Num.to_nat(num("1e14"))), "Some(100000000000000)"} <>
  Case{"from_u32", Pr.print_number(D.Num.from_u32(4294967295)), "4294967295"} <>
  Case{"from_u32 0", Pr.print_number(D.Num.from_u32(0)), "0"} <>
  Case{"from_u32 1000", Pr.print_number(D.Num.from_u32(1000)), "1000"} <>
  Case{"from_nat", Pr.print_number(D.Num.from_nat(U32.to_nat(4000000000))), "4000000000"} <>
  Case{"num eq", Bool.show(D.Num.is_eq(num("1.50"), num("15e-1"))), "True"} <>
  Case{"num ne", Bool.show(D.Num.is_eq(num("1.5"), num("1.51"))), "False"} <>
  Case{"f32 0.1", f32b("0.1"), "1036831949"} <>
  Nil{}

def cases_5() -> List<&2, Case>:
  Case{"f32 -2.5", f32b("-2.5"), "3223322624"} <>
  Case{"f32 tie even", f32b("16777217"), "1266679808"} <>
  Case{"f32 max", f32b("3.4028235e38"), "2139095039"} <>
  Case{"f32 inf", f32b("3.4028236e38"), "2139095040"} <>
  Case{"f32 min normal", f32b("1.17549435e-38"), "8388608"} <>
  Case{"f32 min sub", f32b("1e-45"), "1"} <>
  Case{"f32 sub", f32b("2.5e-45"), "2"} <>
  Case{"f32 underflow", f32b("7e-46"), "0"} <>
  Case{"f32 1e400", f32b("1e400"), "2139095040"} <>
  Case{"f32 -1e-400", f32b("-1e-400"), "2147483648"} <>
  Case{"f32 pi", f32b("3.14159265358979"), "1078530011"} <>
  Case{"f32 above tie", f32b("1.00000005960464477539062500001"), "1065353217"} <>
  Case{"f32 tie", f32b("1.000000059604644775390625"), "1065353216"} <>
  Case{"is_norm parsed", Bool.show(V.Json.is_norm(Result.default(&2, &2, P.Err, V.Json, P.parse("[1.50e3,0.00,-7]"), V.JNull{}))), "True"} <>
  Nil{}

def cases() -> List<&2, Case>:
  List.concat(&2, Case, [cases_0(), cases_1(), cases_2(), cases_3(), cases_4(), cases_5()])

def ok(+c: Case) -> Bool:
  match c:
    case Case{n, +g, +w}:
      String.eq(g, w) || (String.eq(w, "err") && String.starts_with(g, "err@"))

def fails.put(c: Case, good: Bool, rest: List<&2, String>) -> List<&2, String>:
  match c good:
    case c2 True{}:
      rest
    case Case{n, g, w} False{}:
          ("FAIL " ++ String.quote(n) ++ "\n  got:  " ++ String.quote(g)
            ++ "\n  want: " ++ String.quote(w)) <> rest

def fails(cs: List<&2, Case>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      fails.put(c, ok(c), fails(t))

def main() -> IO(Unit):
  +cs = cases()
  +fs = fails(cs)
  +n = List.length(&2, Case, cs)
  +f = List.length(&2, String, fs)
  do IO<Unit>:
    List.for_each(~&2, ~String, ~IO.print, fs)
    IO.print("tests: " ++ Nat.show(Nat.sub(n, f)) ++ " passed, " ++ Nat.show(f)
      ++ " failed")
