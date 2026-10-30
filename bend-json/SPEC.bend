# SPEC.bend: helpers for LAWS.bend, not part of the library.

import Base

# no char of s is a control character (below U+0020)
def ctl_free(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{x}, t}:
      Bool.and(U32.is_ge(x, 32), ctl_free(t))

# the only control character in s, if any, is the newline
def ctl_free_nl(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{+x}, t}:
      Bool.and(Bool.or(U32.is_ge(x, 32), U32.is_eq(x, 10)), ctl_free_nl(t))
