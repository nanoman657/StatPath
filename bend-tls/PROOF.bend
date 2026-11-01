# PROOF.bend: the proofs of LAWS.bend. Run `bend PROOF.bend`.
#
# The Nat identities are proved by induction. A rewrite %e : T takes the induction hypothesis
# e : {a == b} and turns each b in the goal into a, where T is the goal with the hole _ at b.
# A mismatched-length arm is impossible: h is {False == True} there, and the motive BM turns the
# goal into Unit.

import Base
import ./SPEC.bend as Spec
import ./bigint.bend as B
import ./LAWS.bend as Laws

# a motive picked by a Bool: t when b is True, f when it is False
def BM(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def mul_zero(m: Nat) -> {0n == Nat.mul(m, 0n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %mul_zero(p) : {0n == _ : Nat}
      {==}

def mul_one(m: Nat) -> {m == Nat.mul(m, 1n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %mul_one(p) : {1n+p == Nat.add(1n, _) : Nat}
      {==}

def add_zero(m: Nat) -> {m == Nat.add(m, 0n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

# the limb of bi.sel at s = 1: u * 1 + v * 0 is u
def limb_one(+u: Nat, +v: Nat) -> {u == Nat.add(Nat.mul(u, 1n), Nat.mul(v, Nat.sub(1n, 1n))) : Nat}:
  %mul_zero(v) : {u == Nat.add(Nat.mul(u, 1n), _) : Nat}
  %add_zero(Nat.mul(u, 1n)) : {u == _ : Nat}
  mul_one(u)

# the limb of bi.sel at s = 0: u * 0 + v * 1 is v
def limb_zero(+u: Nat, +v: Nat) -> {v == Nat.add(Nat.mul(u, 0n), Nat.mul(v, Nat.sub(1n, 0n))) : Nat}:
  %mul_zero(u) : {v == Nat.add(_, Nat.mul(v, 1n)) : Nat}
  mul_one(v)

# the scalar laws: a * (1 - s) + b * s, at s = 0 and s = 1
def Laws.sel_nat_zero(a, b):
  %mul_zero(b) : {a == Nat.add(Nat.mul(a, 1n), _) : Nat}
  %add_zero(Nat.mul(a, 1n)) : {a == _ : Nat}
  mul_one(a)

def Laws.sel_nat_one(a, b):
  %mul_zero(a) : {b == Nat.add(_, Nat.mul(b, 1n)) : Nat}
  mul_one(b)

def Laws.bi_sel_one(x, y, h):
  match x:
    case Nil{}:
      {==}
    case +u <> ut:
      match y:
        case Nil{}:
          %h : BM(_, {u <> ut == Nil{} : List<&2, Nat>}, Unit)
          Unit{}
        case +v <> vt:
          %limb_one(u, v) : {u <> ut == _ <> B.bi.sel(1n, ut, vt) : List<&2, Nat>}
          %Laws.bi_sel_one(ut, vt, h) : {u <> ut == u <> _ : List<&2, Nat>}
          {==}

def Laws.bi_sel_zero(x, y, h):
  match x:
    case Nil{}:
      match y:
        case Nil{}:
          {==}
        case +v <> vt:
          %h : BM(_, {v <> vt == Nil{} : List<&2, Nat>}, Unit)
          Unit{}
    case +u <> ut:
      match y:
        case Nil{}:
          {==}
        case +v <> vt:
          %limb_zero(u, v) : {v <> vt == _ <> B.bi.sel(0n, ut, vt) : List<&2, Nat>}
          %Laws.bi_sel_zero(ut, vt, h) : {v <> vt == v <> _ : List<&2, Nat>}
          {==}
