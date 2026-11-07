/-
  Vectors transcribed from layout_block_flow_test.cc.
-/
import BlockNode

namespace ChromiumLayout
namespace TestsBlock
open BlockNode

/-- `IsInsideMulticol` (line 38): ancestors' `columns` flags from nearest to farthest, for
    `#outer > #inner > #container > #child` (ancestors above `#outer` have no columns). -/
theorem IsInsideMulticol_vectors :
    -- #inner columns:3
    (isInsideMulticol [] = false ∧ isInsideMulticol [false] = false ∧
     isInsideMulticol [false, true] = true ∧ isInsideMulticol [false, false, true] = true) ∧
    -- #inner columns:auto
    (isInsideMulticol [false] = false ∧ isInsideMulticol [false, false] = false ∧
     isInsideMulticol [false, false, false] = false) ∧
    -- #outer columns:3, #inner columns:3
    (isInsideMulticol [] = false ∧ isInsideMulticol [true] = true ∧
     isInsideMulticol [true, true] = true ∧ isInsideMulticol [true, true, true] = true) ∧
    -- #outer columns:3, #inner columns:auto
    (isInsideMulticol [true] = true ∧ isInsideMulticol [true, false] = true ∧
     isInsideMulticol [true, false, false] = true) := by decide

/-- `AnonymousContainer` (line 109): inline children of a multicol need a wrapper; none without
    multicol. -/
theorem AnonymousContainer_vectors :
    needsAnonymousWrapper true [.text, .text] = true ∧
    needsAnonymousWrapper false [.text, .text] = false := by decide

/-- `NoAnonymousContainer` (line 165): block children need no wrapper. -/
theorem NoAnonymousContainer_vectors :
    needsAnonymousWrapper true [.block, .block] = false := by decide

end TestsBlock
end ChromiumLayout
