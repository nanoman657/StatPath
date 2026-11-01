# frame_proof.bend: the laws of frame.bend, checked by Bend's kernel.
#   bend frame_proof.bend        (ALL PROOFS CHECK when every law holds)
import Base
import ./frame.bend as F
import ./frame_arith.bend as N
import ./frame_lists.bend as L

# the two bytes of a length below 65536 read back as that length, by Euclid's identity with the
# divisor 256 (written 1 + 255)
def lenfield(+body: List<&2, Nat>) -> {List.length(&2, Nat, body) == F.frame.len(F.frame.hi(List.length(&2, Nat, body)), F.frame.lo(List.length(&2, Nat, body))) : Nat}:
  %N.euclid(List.length(&2, Nat, body), 255n) : {_ == F.frame.len(F.frame.hi(List.length(&2, Nat, body)), F.frame.lo(List.length(&2, Nat, body))) : Nat}
  {==}

def len_app_r(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, ys)) == List.length(&2, Nat, List.append(&2, Nat, xs, ys)) : Nat}:
  %L.len_app(xs, ys) : {_ == List.length(&2, Nat, List.append(&2, Nat, xs, ys)) : Nat}
  {==}

def drop_app_r(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {ys == List.drop(&2, Nat, List.append(&2, Nat, xs, ys), List.length(&2, Nat, xs)) : List<&2, Nat>}:
  %L.drop_app(xs, ys) : {_ == List.drop(&2, Nat, List.append(&2, Nat, xs, ys), List.length(&2, Nat, xs)) : List<&2, Nat>}
  {==}

# the payload length is no more than the bytes that follow the header
def le_app(+body: List<&2, Nat>, +tail: List<&2, Nat>) -> {Nat.is_le(List.length(&2, Nat, body), List.length(&2, Nat, List.append(&2, Nat, body, tail))) == True{} : Bool}:
  %len_app_r(body, tail) : {Nat.is_le(List.length(&2, Nat, body), _) == True{} : Bool}
  L.le_add(List.length(&2, Nat, body), List.length(&2, Nat, tail))

# LAW (round trip): a frame, followed by any bytes, decodes to the frame and those bytes
def frame_roundtrip(op: Nat, id: Nat, +body: List<&2, Nat>, +tail: List<&2, Nat>,
  h: {Nat.is_lt(List.length(&2, Nat, body), 65536n) == True{} : Bool}) ->
  {F.frame.decode(List.append(&2, Nat, F.frame.encode(op, id, body, h), tail))
    == Some{F.Split{F.Frame{op, id, body}, tail}} : Maybe<&2, F.Split>}:
  %lenfield(body) : {Some{F.frame.at(op, id, _, List.append(&2, Nat, body, tail))}
    == Some{F.Split{F.Frame{op, id, body}, tail}} : Maybe<&2, F.Split>}
  %L.take_app(body, tail) : {Some{F.Split{F.Frame{op, id, _}, List.drop(&2, Nat, List.append(&2, Nat, body, tail), List.length(&2, Nat, body))}}
    == Some{F.Split{F.Frame{op, id, body}, tail}} : Maybe<&2, F.Split>}
  %drop_app_r(body, tail) : {Some{F.Split{F.Frame{op, id, body}, _}} == Some{F.Split{F.Frame{op, id, body}, tail}} : Maybe<&2, F.Split>}
  {==}

# LAW (completeness): after a frame, its payload is complete in the bytes that follow it
def frame_complete(op: Nat, id: Nat, +body: List<&2, Nat>, +tail: List<&2, Nat>,
  h: {Nat.is_lt(List.length(&2, Nat, body), 65536n) == True{} : Bool}) ->
  {F.frame.complete(List.append(&2, Nat, F.frame.encode(op, id, body, h), tail)) == True{} : Bool}:
  %lenfield(body) : {Nat.is_le(_, List.length(&2, Nat, List.append(&2, Nat, body, tail))) == True{} : Bool}
  le_app(body, tail)
