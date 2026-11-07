/-
  Vectors transcribed from block_child_iterator_test.cc. Children are numbered 1..n in sibling
  order; token lists name the children whose break tokens are in the parent token.
-/
import BlockNode

namespace ChromiumLayout
namespace TestsBlock
open BlockNode

/-- `NullFirstChild` (line 43): no first child yields no entries. -/
theorem NullFirstChild_vectors : iterate [] [] false = [] := by decide

/-- `NoBreakToken` (line 48): three children, no parent token. -/
theorem NoBreakToken_vectors :
    iterate [1, 2, 3] [] false = [⟨1, false⟩, ⟨2, false⟩, ⟨3, false⟩] := by decide

/-- `BreakTokens` (line 66): four children, the four token sets the test builds. -/
theorem BreakTokens_vectors :
    iterate [1, 2, 3, 4] [1] false = [⟨1, true⟩, ⟨2, false⟩, ⟨3, false⟩, ⟨4, false⟩] ∧
    iterate [1, 2, 3, 4] [1, 2] false = [⟨1, true⟩, ⟨2, true⟩, ⟨3, false⟩, ⟨4, false⟩] ∧
    iterate [1, 2, 3, 4] [2, 3] false = [⟨2, true⟩, ⟨3, true⟩, ⟨4, false⟩] ∧
    iterate [1, 2, 3, 4] [1, 3] false = [⟨1, true⟩, ⟨3, true⟩, ⟨4, false⟩] := by decide

/-- `SeenAllChildren` (line 140): with all children seen, only children that have a token are
    returned. -/
theorem SeenAllChildren_vectors :
    iterate [1, 2] [1] true = [⟨1, true⟩] ∧ iterate [1, 2] [] true = [] := by decide

/-- `DeleteNodeWhileIteration` (line 177): after child 1 is returned, child 2 is removed; the
    iterator then returns child 3 and ends. -/
theorem DeleteNodeWhileIteration_vectors :
    nextChild [1, 2, 3] none = some 1 ∧
    nextChild [1, 3] (some 1) = some 3 ∧
    nextChild [1, 3] (some 3) = none := by decide

end TestsBlock
end ChromiumLayout
