import BlockWritingModeConverter
/-
  BlockBoxSides.lean: which box sides are present, physical vs logical, written from
  geometry/box_sides_test.cc. Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockBoxSides
open BlockWritingModeConverter

/-- Present sides as (inline-start, inline-end, block-start, block-end). Physical sides are given
    as (top, right, bottom, left). CSS Writing Modes 4 §6.2 (abstract-to-physical mappings). -/
def toLogical (wm : WM) (d : Dir) (top right bottom left : Bool) : Bool × Bool × Bool × Bool :=
  let sw := fun (c : Bool) (p : Bool × Bool) => if c then (p.2, p.1) else p
  let i := sw (flips wm d).1 (if vertical wm then (top, bottom) else (left, right))
  let b := sw (flips wm d).2 (if vertical wm then (left, right) else (top, bottom))
  (i.1, i.2, b.1, b.2)

/-- Line-relative sides (line-left, line-right) from inline sides: rtl swaps them.
    CSS Writing Modes 4 §6.3 (line-relative directions). -/
def lineSides (d : Dir) (inlineStart inlineEnd : Bool) : Bool × Bool :=
  if d == .rtl then (inlineEnd, inlineStart) else (inlineStart, inlineEnd)

/-- Law: converting never creates or loses a side on an axis (the inline pair is the physical
    pair, possibly swapped): an inline side is present iff a physical side on that axis is. -/
theorem toLogical_inline_or (wm : WM) (d : Dir) (t r b l : Bool) :
    ((toLogical wm d t r b l).1 || (toLogical wm d t r b l).2.1) =
      (if vertical wm then t || b else l || r) := by
  cases wm <;> cases d <;> cases t <;> cases r <;> cases b <;> cases l <;> rfl

end BlockBoxSides
end ChromiumLayout
