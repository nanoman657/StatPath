# The key order of the merge: skey_cmp (merge.bend) is the string order of ORDER.bend, so the sorted-map
# layer can use the string facts directly. Checked by PROOF.bend.
import Base
import ./ORDER.bend as Ord
import ./merge.bend as Merge

# the rebuilding step of String.cmp keeps the comparison it is given
law Key.rec_cmp:
  for h1: Char
  for h2: Char
  for rr: (String & String) & Cmp
  {Merge.cmp_of(String.cmp.rec(h1, h2, rr)) == Merge.cmp_of(rr) : Cmp}

def Key.rec_cmp(h1, h2, rr):
  match rr:
    case ((t1b, t2b), r):
      {==}

# the character step of String.cmp: with the order c of the two chars, the order of the strings is go(t1, t2, c)
law Key.fin_step:
  for +x: U32
  for +y: U32
  for +t1: String
  for +t2: String
  for +c: Cmp
  for ih: {Merge.skey_cmp(t1, t2) == String.order(t1, t2) : Cmp}
  {Merge.cmp_of(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))) == String.order.go(t1, t2, c) : Cmp}

def Key.fin_step(x, y, t1, t2, c, ih):
  match c:
    case LT{}:
      Equal.trans(Cmp,
        Merge.cmp_of(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), LT{}))),
        LT{},
        String.order.go(t1, t2, LT{}),
        {==},
        Equal.sym(Cmp, String.order.go(t1, t2, LT{}), LT{}, Ord.String.order.go_lt(t1, t2)))
    case EQ{}:
      Equal.trans(Cmp,
        Merge.cmp_of(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), EQ{}))),
        Merge.cmp_of(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
        String.order.go(t1, t2, EQ{}),
        {==},
        Equal.trans(Cmp,
          Merge.cmp_of(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
          Merge.cmp_of(String.cmp(t1, t2)),
          String.order.go(t1, t2, EQ{}),
          Key.rec_cmp(Chr{x}, Chr{y}, String.cmp(t1, t2)),
          ih))
    case GT{}:
      Equal.trans(Cmp,
        Merge.cmp_of(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), GT{}))),
        GT{},
        String.order.go(t1, t2, GT{}),
        {==},
        Equal.sym(Cmp, String.order.go(t1, t2, GT{}), GT{}, Ord.String.order.go_gt(t1, t2)))

# the key order of merge.bend is the string order
law Key.skey_eq_order:
  for a: String
  for b: String
  {Merge.skey_cmp(a, b) == String.order(a, b) : Cmp}

def Key.skey_eq_order(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{_}, +t}:
      {==}
    case SCon{Chr{_}, +t} SNil{}:
      {==}
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      Key.fin_step(x, y, t1, t2, U32.cmp(x, y), Key.skey_eq_order(t1, t2))

# a U32 compared with itself is EQ
law Key.U32_cmp_self:
  for +a: U32
  {U32.cmp(a, a) == EQ{} : Cmp}

def Key.U32_cmp_self(a):
  match a:
    case U32{+x}:
      Ord.IsEQ.of(Word.cmp(32n, x, x), Ord.Word.cmp_self(32n, x))

# a string compared with itself is EQ
law Key.order_self:
  for +a: String
  {String.order(a, a) == EQ{} : Cmp}

def Key.order_self(a):
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, +t}:
      Equal.trans(Cmp,
        String.order(SCon{Chr{x}, t}, SCon{Chr{x}, t}),
        String.order.go(t, t, U32.cmp(x, x)),
        EQ{},
        {==},
        Equal.trans(Cmp,
          String.order.go(t, t, U32.cmp(x, x)),
          String.order.go(t, t, EQ{}),
          EQ{},
          Equal.cong(Cmp, Cmp, c => String.order.go(t, t, c), U32.cmp(x, x), EQ{}, Key.U32_cmp_self(x)),
          Key.order_self(t)))
