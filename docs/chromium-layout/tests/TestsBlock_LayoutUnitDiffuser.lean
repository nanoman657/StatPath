import BlockDiffuser

namespace TestsBlock

open ChromiumLayout.BlockDiffuser

private def run (t n : Nat) : List Nat := (List.range (n + 1)).map (share t n)

-- geometry/layout_unit_diffuser_test.cc:14: LayoutUnitDiffuserTest.ThreeBuckets
-- (raw units: 7 = 448, 8 = 512; base = floor(total / 3) = 149 resp. 170, epsilon = 1)
theorem ThreeBuckets_vectors :
    run 448 3 = [149, 150, 149, 0] ∧ run 512 3 = [171, 170, 171, 0] := by decide

-- :35 FourBuckets (totals of 1, 2, 3 epsilons)
theorem FourBuckets_vectors :
    run 1 4 = [0, 1, 0, 0, 0] ∧ run 2 4 = [1, 0, 1, 0, 0] ∧ run 3 4 = [1, 1, 0, 1, 0] := by decide

-- :69 SevenBuckets (totals of 1..6 epsilons)
theorem SevenBuckets_vectors :
    run 1 7 = [0, 0, 0, 1, 0, 0, 0, 0] ∧ run 2 7 = [0, 1, 0, 0, 0, 1, 0, 0] ∧
    run 3 7 = [0, 1, 0, 1, 0, 1, 0, 0] ∧ run 4 7 = [1, 0, 1, 0, 1, 0, 1, 0] ∧
    run 5 7 = [1, 0, 1, 1, 1, 0, 1, 0] ∧ run 6 7 = [1, 1, 1, 0, 1, 1, 1, 0] := by decide

end TestsBlock
