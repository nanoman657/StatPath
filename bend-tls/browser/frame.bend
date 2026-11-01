# frame.bend: the relay's wire frames, as Bend code over byte values (Nat, 0..255).
#
# A frame is one byte of op, one byte of connection id, the payload length in two bytes (high
# byte, then low byte, big-endian), and the payload. The encoder takes a payload shorter than
# 65536 bytes as a precondition. The decoder reads the header and returns the frame it names; it
# does not check that the payload has all arrived: frame.complete does that, and the stream
# reader calls decode only for complete frames.
#
#   bend frame.bend      (checks that the definitions are well formed; the proofs are in frame_proof.bend)

import Base

type Frame is Data:
  Frame{op: Nat, id: Nat, body: List<&2, Nat>}

type Split is Data:
  Split{frame: Frame, rest: List<&2, Nat>}

def frame.hi(n: Nat) -> Nat:
  Nat.div(n, 256n)

def frame.lo(n: Nat) -> Nat:
  Nat.mod(n, 256n)

# the payload length a header says
def frame.len(hi: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(hi, 256n), lo)

# the bytes of a frame, the payload being body
def frame.encode(op: Nat, id: Nat, +body: List<&2, Nat>,
  h: {Nat.is_lt(List.length(&2, Nat, body), 65536n) == True{} : Bool}) -> List<&2, Nat>:
  op <> id <> frame.hi(List.length(&2, Nat, body)) <> frame.lo(List.length(&2, Nat, body)) <> body

# the frame that the header op, id and length n names, and the bytes after its payload
def frame.at(+op: Nat, +id: Nat, +n: Nat, +rest: List<&2, Nat>) -> Split:
  Split{Frame{op, id, List.take(&2, Nat, rest, n)}, List.drop(&2, Nat, rest, n)}

# the frame at the front of bs; None when bs is shorter than a header
def frame.decode(+bs: List<&2, Nat>) -> Maybe<&2, Split>:
  match bs:
    case Nil{}:
      None{}
    case +op <> t1:
      match t1:
        case Nil{}:
          None{}
        case +id <> t2:
          match t2:
            case Nil{}:
              None{}
            case +hi <> t3:
              match t3:
                case Nil{}:
                  None{}
                case +lo <> rest:
                  Some{frame.at(op, id, frame.len(hi, lo), rest)}

# whether the whole frame at the front of bs has arrived
def frame.complete(+bs: List<&2, Nat>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case +op <> t1:
      match t1:
        case Nil{}:
          False{}
        case +id <> t2:
          match t2:
            case Nil{}:
              False{}
            case +hi <> t3:
              match t3:
                case Nil{}:
                  False{}
                case +lo <> rest:
                  Nat.is_le(frame.len(hi, lo), List.length(&2, Nat, rest))
