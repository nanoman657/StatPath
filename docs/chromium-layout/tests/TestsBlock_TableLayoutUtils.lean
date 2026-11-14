import TableLayout

namespace ChromiumLayout
namespace TestsBlock

open TableLayout

-- table_layout_utils_test.cc:55: DistributeColspanAutoPercent
theorem DistributeColspanAutoPercent_vectors :
    -- Columns: 10px, 20px, 30% -> distribute 60%: col 0 gets 10%, col 1 gets 20%
    distributeColspanPercent [10, 20, 10] [none, none, some 30] 60 = [10, 20] ∧
    -- Columns: 0px, 0px, 10% -> distribute 60%: 25%, 25%
    distributeColspanPercent [0, 0, 10] [none, none, some 10] 60 = [25, 25] := by
  decide

-- table_layout_utils_test.cc:93: DistributeColspanAutoSizeUnconstrained
theorem DistributeColspanAutoSizeUnconstrained_vectors :
    -- Columns min/max: 0/10, 0/10, 0/20 -> distribute 100: 25, 25, 50
    distributeColspanAuto [10, 10, 20] 100 = [25, 25, 50] := by
  decide

-- table_layout_utils_test.cc:121: DistributeColspanAutoSizeConstrained
theorem DistributeColspanAutoSizeConstrained_vectors :
    -- Constrained columns: distribute 100 over max sizes 10, 10, 20: 25, 25, 50
    distributeColspanAuto [10, 10, 20] 100 = [25, 25, 50] := by
  decide

-- table_layout_utils_test.cc:149: DistributeColspanAutoExactMaxSize
-- When assignable table size matches the sum of column max sizes, column sizes are preserved exactly.
-- CSS Table 3 §3, CSS 2.1 §17.5.2.
theorem DistributeColspanAutoExactMaxSize_vectors :
    let cols : List Nat := [1, 22, 34, 2000]
    synchronizeColumns (cols.foldl (·+·) 0) cols = [1, 22, 34, 2000] := by
  decide

-- table_layout_utils_test.cc:187: ComputeGridInlineMinMax
-- Table grid inline min/max sizes with and without percent columns across layout and measure passes.
-- CSS Table 3 §3, CSS 2.1 §17.5.2.1.
theorem ComputeGridInlineMinMax_vectors :
    -- Case 1: no percentages, sums up min/max
    let cols1 : List TableColConstraint := [
      { minSize := 10, maxSize := 100 },
      { minSize := 20, maxSize := 200 },
      { minSize := 30, maxSize := 300 }
    ]
    -- Case 2 & 3: 99px/10% column
    let cols2 : List TableColConstraint := [
      { minSize := 10, maxSize := 99, pct := some 10 },
      { minSize := 10, maxSize := 10 },
      { minSize := 10, maxSize := 10 }
    ]
    -- Case 4: total 20% and non-percent 800px
    let cols3 : List TableColConstraint := [
      { minSize := 10, maxSize := 100, pct := some 10 },
      { minSize := 10, maxSize := 10, pct := some 10 },
      { minSize := 10, maxSize := 800 }
    ]
    computeGridInlineMinMax cols1 true = (60, 600) ∧
    computeGridInlineMinMax cols2 true = (30, 990) ∧
    computeGridInlineMinMax cols2 false = (30, 119) ∧
    computeGridInlineMinMax cols3 true = (30, 1000) := by
  decide

-- table_layout_utils_test.cc:280: DistributeSectionFixedBlockSizeToRows
theorem DistributeSectionFixedBlockSizeToRows_vectors :
    -- Row 1 has 50% of 1000 -> 500, rows 0 and 2 get 250 each
    distributeSectionBlockSizeToRows [100, 100, 100] [none, some 50, none] 1000 = [250, 500, 250] := by
  decide

-- table_layout_utils_test.cc:294: DistributeTableBlockSizeToSections
theorem DistributeTableBlockSizeToSections_vectors :
    -- Section 0 has 90% of 1000 -> 900, section 1 gets 100
    distributeTableBlockSizeToSections [(100, some 90), (100, none)] 1000 = [900, 100] := by
  decide

end TestsBlock
end ChromiumLayout
