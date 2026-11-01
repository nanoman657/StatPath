# asn1.bend: reading DER (ITU-T X.690) elements, as far as X.509 needs them.
# A byte list is List<&2, U32>; a TLV is one element with its tag, its content
# bytes, its whole encoding and the bytes after it. Lengths up to 2^32 - 1.

import Base

type TLV is Data:
  TLV{tag: U32, val: List<&2, U32>, raw: List<&2, U32>, rest: List<&2, U32>}

type Hd is Data:
  Hd{len: Nat, hdr: Nat}

# the k-byte big-endian number at the front of bs
def asn1.be(k: Nat, +bs: List<&2, U32>) -> Nat:
  match k:
    case 0n:
      0n
    case 1n++p:
      match bs:
        case Nil{}:
          0n
        case b <> t:
          Nat.add(Nat.mul(U32.to_nat(b), Nat.pow(256n, p)), asn1.be(p, t))

# the header of the element at the front of bs: its content length and the
# header's own length
def asn1.hd.at(+l: U32, +r: List<&2, U32>, short: Bool) -> Hd:
  match short:
    case True{}:
      Hd{U32.to_nat(l), 2n}
    case False{}:
      Hd{asn1.be(Nat.sub(U32.to_nat(l), 128n), r), Nat.add(2n, Nat.sub(U32.to_nat(l), 128n))}

def asn1.hd(+bs: List<&2, U32>) -> Hd:
  match bs:
    case Nil{}:
      Hd{0n, 0n}
    case t <> r:
      match r:
        case Nil{}:
          Hd{0n, 0n}
        case l <> r2:
          asn1.hd.at(l, r2, U32.is_lt(l, 128))

# the whole length of the element at the front of bs (header and content)
def asn1.total.at(+h: Hd) -> Nat:
  match h:
    case Hd{len, hdr}:
      Nat.add(len, hdr)

def asn1.total(+bs: List<&2, U32>) -> Nat:
  asn1.total.at(asn1.hd(bs))

# the element at the front of bs, given its header
def asn1.tag(bs: List<&2, U32>) -> U32:
  match bs:
    case Nil{}:
      0
    case t <> r:
      t

# the k-th element of a sequence of elements (its content bytes)
def asn1.read.at(+h: Hd, +bs: List<&2, U32>) -> TLV:
  match h:
    case Hd{len, hdr}:
      TLV{asn1.tag(bs), List.take(&2, U32, List.drop(&2, U32, bs, hdr), len),
        List.take(&2, U32, bs, Nat.add(len, hdr)), List.drop(&2, U32, bs, Nat.add(len, hdr))}

# the element at the front of bs
def asn1.read(+bs: List<&2, U32>) -> TLV:
  asn1.read.at(asn1.hd(bs), bs)

def asn1.nth(k: Nat, +bs: List<&2, U32>) -> TLV:
  match k:
    case 0n:
      asn1.read(bs)
    case 1n+p:
      asn1.nth(p, List.drop(&2, U32, bs, asn1.total(bs)))

# the number of elements in a sequence of elements; fuel bounds the walk, so
# malformed input cannot loop
def asn1.count.fuel(fuel: Nat, +bs: List<&2, U32>, acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      match bs:
        case Nil{}:
          acc
        case t <> r:
          asn1.count.fuel(p, List.drop(&2, U32, bs, asn1.total(bs)), 1n+acc)

def asn1.count(+bs: List<&2, U32>) -> Nat:
  asn1.count.fuel(1000000n, bs, 0n)
