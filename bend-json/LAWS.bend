# LAWS.bend: what bend-json promises. PROOF.bend proves each law; a law
# without a proof there is an open claim, and `bend PROOF.bend` then
# prints SOME PROOFS FAIL.

import Base
import ./decimal.bend as D
import ./value.bend as V
import ./text.bend as T
import ./parser.bend as P
import ./printer.bend as Pr
import ./SPEC.bend as Spec

# LAW 1: escaping round-trips, for every string (any chars, even lone
# surrogates or codes past U+10FFFF, which escape keeps raw)
law escape_roundtrip:
  for +s: String
  {T.unescape(T.escape(s)) == Some{s} : Maybe<&2, String>}

# LAW 2: a normalized number prints to text that parses back to it
law number_roundtrip:
  for +n: D.Num
  for  h: {D.Num.is_norm(n) == True{} : Bool}
  {P.parse_number(Pr.print_number(n)) == Some{n} : Maybe<&2, D.Num>}

# LAW 3a: the compact text of a value parses back to it, when its numbers
# are normalized and it nests no deeper than the parser allows
law roundtrip_compact:
  for +v: V.Json
  for h1: {V.Json.is_norm(v) == True{} : Bool}
  for h2: {Nat.is_le(V.Json.depth(v), P.default_depth()) == True{} : Bool}
  {P.parse(Pr.print(v)) == Done{v} : Result<&2, &2, P.Err, V.Json>}

# LAW 3b: so does the pretty text, at every indent
law roundtrip_pretty:
  for +ind: Nat
  for +v: V.Json
  for h1: {V.Json.is_norm(v) == True{} : Bool}
  for h2: {Nat.is_le(V.Json.depth(v), P.default_depth()) == True{} : Bool}
  {P.parse(Pr.pretty(ind, v)) == Done{v} : Result<&2, &2, P.Err, V.Json>}

# LAW 4a: compact text never holds a raw control character
law no_control_compact:
  for v: V.Json
  {Spec.ctl_free(Pr.print(v)) == True{} : Bool}

# LAW 4b: pretty text holds none but the newlines between lines
law no_control_pretty:
  for +ind: Nat
  for v: V.Json
  {Spec.ctl_free_nl(Pr.pretty(ind, v)) == True{} : Bool}
