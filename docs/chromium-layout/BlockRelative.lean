/-
  BlockRelative.lean: relative positioning insets resolution (CSS 2.1 §9.4.3 / CSS Position 3),
  written from relative_utils_test.cc (`RelativeUtilsTest.HorizontalTB`). Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockRelative

/-- Physical relative insets (top, right, bottom, left) in pixels. -/
structure Insets where
  top : Int
  right : Int
  bottom : Int
  left : Int
  deriving DecidableEq, Repr

/-- Resolve an opposing pair of insets (e.g. left and right, or top and bottom).
    If both are auto (none), both are 0.
    If one is auto, it becomes the negation of the other.
    If both are specified, both values are preserved in the insets struct. -/
def resolveOpposing (startVal endVal : Option Int) : Int × Int :=
  match startVal, endVal with
  | none, none => (0, 0)
  | some s, none => (s, -s)
  | none, some e => (-e, e)
  | some s, some e => (s, e)

/-- Compute relative insets for four optional lengths (none = auto)
    (relative_utils_test.cc: `RelativeUtilsTest.HorizontalTB`). -/
def computeRelativeInsets (top right bottom left : Option Int) : Insets :=
  let (l, r) := resolveOpposing left right
  let (t, b) := resolveOpposing top bottom
  ⟨t, r, b, l⟩

/-- When only one opposing side is specified, the resolved insets sum to zero. -/
theorem opposing_sum_zero (v : Int) :
    let (s, e) := resolveOpposing (some v) none
    s + e = 0 := by
  dsimp [resolveOpposing]
  omega

/-- When only the end side is specified, the resolved insets sum to zero. -/
theorem opposing_sum_zero_right (v : Int) :
    let (s, e) := resolveOpposing none (some v)
    s + e = 0 := by
  dsimp [resolveOpposing]
  omega

end BlockRelative
end ChromiumLayout
