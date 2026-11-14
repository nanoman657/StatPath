import BlockWritingMode
/-
  BlockAxis.lean: sets of logical axes and physical axes and their mapping, written from
  geometry/axis_test.cc. Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockAxis
open BlockWritingMode

/-- A set of axes as (first, second): logical (inline, block) or physical (horizontal, vertical). -/
abbrev Axes := Bool × Bool

/-- Logical axes to physical axes: inline is horizontal in horizontal writing modes and vertical in
    vertical ones. CSS Writing Modes 4 §6.1 (abstract dimensions). The same swap is its own
    inverse, so it also maps physical to logical. -/
def mapAxes (wm : WritingMode) (a : Axes) : Axes :=
  if isVertical wm then (a.2, a.1) else a

/-- Law: mapping to physical axes and back is the identity for every writing mode and axis set
    (`ToPhysicalAxes`, `ToLogicalAxes`). -/
theorem mapAxes_mapAxes (wm : WritingMode) (a : Axes) : mapAxes wm (mapAxes wm a) = a := by
  cases wm <;> simp [mapAxes, isVertical]

end BlockAxis
end ChromiumLayout
