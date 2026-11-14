import BlockAxis

namespace TestsBlock

open ChromiumLayout.BlockWritingMode ChromiumLayout.BlockAxis

-- None = (false, false), first = (true, false), second = (false, true), Both = (true, true)

-- geometry/axis_test.cc:213 AxisTest.ToPhysicalAxes and :239 AxisTest.ToLogicalAxes: the two tests
-- list the same eight (axes, writing mode) -> axes pairs, because the mapping is an involution.
theorem AxisMap_vectors :
    mapAxes .horizontalTb (false, false) = (false, false) ∧ mapAxes .verticalRl (false, false) = (false, false) ∧
    mapAxes .horizontalTb (true, true) = (true, true) ∧ mapAxes .verticalRl (true, true) = (true, true) ∧
    mapAxes .horizontalTb (true, false) = (true, false) ∧ mapAxes .verticalRl (true, false) = (false, true) ∧
    mapAxes .horizontalTb (false, true) = (false, true) ∧ mapAxes .verticalRl (false, true) = (true, false) := by
  decide

end TestsBlock
