# example.bend: parse, inspect, convert and print.
#
#   bend example.bend

import Base
import ./decimal.bend as D
import ./value.bend as V
import ./parser.bend as P
import ./printer.bend as Pr

def show(r: Result<&2, &2, P.Err, V.Json>) -> String:
  match r:
    case Done{+v}:
      Pr.print(v) ++ "\n" ++ Pr.pretty(2n, v) ++ "\nlast \"a\": "
        ++ Maybe.show(~&2, ~V.Json, ~Pr.print, V.Json.get(v, "a"))
    case Fail{e}:
      "error " ++ P.Err.show(e)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(P.parse("{\"a\": 1, \"price\": 19.99, \"a\": [true, null, \"\\u00e9\"]}")))
    IO.print(show(P.parse("[1, 2,]")))
    IO.print(show(P.parse_with(1n, "[[1]]")))
    +n : D.Num = Maybe.default(&2, D.Num, P.parse_number("19.990e1"), D.Num.zero())
    IO.print(Pr.print_number(n) ++ " exact; as U32: "
      ++ Maybe.show(~&2, ~U32, ~U32.show, D.Num.to_u32(n)) ++ "; as F32: "
      ++ F32.show(D.Num.to_f32(n)))
    IO.print(Pr.print_number(Maybe.default(&2, D.Num, P.parse_number("1e400"), D.Num.zero())))
