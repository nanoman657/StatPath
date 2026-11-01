import Base

# the two lists have the same number of elements (checked pairwise, so the induction is direct)
def same_shape(x: List<&2, Nat>, y: List<&2, Nat>) -> Bool:
  match x:
    case Nil{}:
      match y:
        case Nil{}:
          True{}
        case +v <> vt:
          False{}
    case +u <> ut:
      match y:
        case Nil{}:
          False{}
        case +v <> vt:
          same_shape(ut, vt)
