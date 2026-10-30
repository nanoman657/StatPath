# value.bend: the JSON value.
#
# An object is its members in order, duplicates kept; get answers the last
# member with the key, as JavaScript's JSON.parse does.

import Base
import ./decimal.bend as D

type Json is Data:
  JNull{}
  JBool{value: Bool}
  JNum{value: D.Num}
  JStr{value: String}
  JArr{items: List<&2, Json>}
  JObj{items: List<&2, Member>}

type Member is Data:
  Mem{key: String, value: Json}

def Json.get.pick(+k: String, +key: String, +x: Json, found: Maybe<&2, Json>) ->
  Maybe<&2, Json>:
  Bool.pick(Maybe<&2, Json>, String.eq(k, key), Some{x}, found)

def Json.get.go(ms: List<&2, Member>, +key: String, found: Maybe<&2, Json>) ->
  Maybe<&2, Json>:
  match ms:
    case Nil{}:
      found
    case Mem{k, x} <> t:
      Json.get.go(t, key, Json.get.pick(k, key, x, found))

# the value of the last member named key, if v is an object that has one
def Json.get(v: Json, +key: String) -> Maybe<&2, Json>:
  match v:
    case JObj{ms}:
      Json.get.go(ms, key, None{})
    case _:
      None{}

# the n-th item of an array
def Json.at(v: Json, n: Nat) -> Maybe<&2, Json>:
  match v:
    case JArr{xs}:
      List.get(&2, Json, xs, n)
    case _:
      None{}

# deep equality; numbers compare as normalized values
def Json.is_eq(a: Json, b: Json) -> Bool:
  match a b:
    case JNull{} JNull{}:
      True{}
    case JBool{x} JBool{y}:
      D.Bool.is_eq(x, y)
    case JNum{x} JNum{y}:
      D.Num.is_eq(x, y)
    case JStr{x} JStr{y}:
      String.eq(x, y)
    case JArr{Nil{}} JArr{Nil{}}:
      True{}
    case JArr{x <> xs} JArr{y <> ys}:
      Json.is_eq(x, y) && Json.is_eq(JArr{xs}, JArr{ys})
    case JObj{Nil{}} JObj{Nil{}}:
      True{}
    case JObj{Mem{k1, x} <> xs} JObj{Mem{k2, y} <> ys}:
      String.eq(k1, k2) && Json.is_eq(x, y) && Json.is_eq(JObj{xs}, JObj{ys})
    case _ _:
      False{}

# how many arrays and objects nest: 0 for a scalar, 1 for [] or [1]
def Json.depth(v: Json) -> Nat:
  match v:
    case JArr{Nil{}}:
      1n
    case JArr{x <> xs}:
      Nat.max(1n+Json.depth(x), Json.depth(JArr{xs}))
    case JObj{Nil{}}:
      1n
    case JObj{Mem{k, x} <> xs}:
      Nat.max(1n+Json.depth(x), Json.depth(JObj{xs}))
    case _:
      0n

# whether every number is normalized
def Json.is_norm(v: Json) -> Bool:
  match v:
    case JNum{n}:
      D.Num.is_norm(n)
    case JArr{Nil{}}:
      True{}
    case JArr{x <> xs}:
      Json.is_norm(x) && Json.is_norm(JArr{xs})
    case JObj{Nil{}}:
      True{}
    case JObj{Mem{k, x} <> xs}:
      Json.is_norm(x) && Json.is_norm(JObj{xs})
    case _:
      True{}

def Json.num(n: D.Num) -> Json:
  JNum{n}

def Json.u32(x: U32) -> Json:
  JNum{D.Num.from_u32(x)}

def Json.nat(x: Nat) -> Json:
  JNum{D.Num.from_nat(x)}
