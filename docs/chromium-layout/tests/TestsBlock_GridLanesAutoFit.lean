import GridLanes

namespace TestsBlock

open ChromiumLayout.GridLanes

-- Container is 1000 along the grid axis (columns: LogicalSize(1000, 200); rows: height 1000px).
-- Rows are the same model with axes swapped.
private def hundreds (n : Nat) : List Nat := List.replicate n 100

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:797 ColumnAutoFitAutoPlacement; :1138 RowAutoFitAutoPlacement
theorem AutoFitAutoPlacement_vectors :
    laneSizes 1000 [.autoFit 100] [none, none, none, none, none] = hundreds 5 := by decide +kernel

-- :837 ColumnAutoFitAutoAndExplicitPlacement; :1180 RowAutoFitAutoAndExplicitPlacement
theorem AutoFitAutoAndExplicitPlacement_vectors :
    laneSizes 1000 [.autoFit 100] [none, none, some 4, some 6, none] = hundreds 5 := by decide +kernel

-- :877 ColumnAutoFillAutoFitAutoPlacement; :1222 RowAutoFillAutoFitAutoPlacement
theorem AutoFillAutoFitAutoPlacement_vectors :
    laneSizes 1000 [.fixed 5 100, .autoFit 100] [none, none, none, none, none, none] = hundreds 6 := by decide +kernel

-- :919 ColumnAutoFillAutoFitNoCollapse; :1266 RowAutoFillAutoFitNoCollapse
theorem AutoFillAutoFitNoCollapse_vectors :
    laneSizes 1000 [.autoFit 100, .fixed 5 100] [none, none, none, none, none] = hundreds 10 := by decide +kernel

-- :962 ColumnAutoFitAutoSizeAutoPlacement; :1311 RowAutoFitAutoSizeAutoPlacement
theorem AutoFitAutoSizeAutoPlacement_vectors :
    laneSizes 1000 [.autoFitAuto 100] [some 1, some 3, none, none, none, none] = [250, 250, 250, 250] := by decide +kernel

-- :1005 ColumnAutoFitAutoSizeAndAutoAndExplicitPlacement; :1356 RowAutoFitAutoSizeAndAutoAndExplicitPlacement
theorem AutoFitAutoSizeAndAutoAndExplicitPlacement_vectors :
    laneSizes 1000 [.autoFitAuto 100] [none, none, some 4, some 6, none] = [200, 200, 200, 200, 200] := by decide +kernel

-- :1050 ColumnAutoFillAutoFitAutoAndAutoPlacement (:1401 is a held-out row: not transcribed)
theorem ColumnAutoFillAutoFitAutoAndAutoPlacement_vectors :
    laneSizes 1000 [.fixed 5 100, .autoFitAuto 100] [none, none, none, none, none, none] =
      [100, 100, 100, 100, 100, 500] := by decide +kernel

-- :1095 ColumnAutoFillAutoFitAutoNoCollapse (width: auto -> 0); :1447 RowAutoFillAutoFitAutoNoCollapse (height: 100px)
theorem AutoFillAutoFitAutoNoCollapse_vectors :
    laneSizes 1000 [.autoFitAuto 0, .fixed 5 100] [none, none, none, none, none] = hundreds 10 ∧
    laneSizes 1000 [.autoFitAuto 100, .fixed 5 100] [none, none, none, none, none] = hundreds 10 := by decide +kernel

end TestsBlock
