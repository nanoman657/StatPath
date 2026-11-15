import GridLanes

namespace TestsBlock

open ChromiumLayout.GridLanes

-- All eight tests: items are 100 along the stacking axis; the container is 1000 along the grid axis
-- (columns: LogicalSize(1000, 200); rows: height 1000px). Rows are the same model with axes swapped.
private def auto : Option Nat × Nat := (none, 100)
private def at_ (l : Nat) : Option Nat × Nat := (some l, 100)
private def hundreds (n : Nat) : List Nat := List.replicate n 100

-- grid_lanes/grid_lanes_layout_algorithm_test.cc:797 ColumnAutoFitAutoPlacement; :1138 RowAutoFitAutoPlacement
theorem AutoFitAutoPlacement_vectors :
    laneSizes 1000 [.autoFit 100] [auto, auto, auto, auto, auto] = hundreds 5 := by decide

-- :837 ColumnAutoFitAutoAndExplicitPlacement; :1180 RowAutoFitAutoAndExplicitPlacement
theorem AutoFitAutoAndExplicitPlacement_vectors :
    laneSizes 1000 [.autoFit 100] [auto, auto, at_ 4, at_ 6, auto] = hundreds 5 := by decide

-- :877 ColumnAutoFillAutoFitAutoPlacement; :1222 RowAutoFillAutoFitAutoPlacement
-- (repeat(5, 100px) repeat(auto-fit, 100px), six items)
theorem AutoFillAutoFitAutoPlacement_vectors :
    laneSizes 1000 [.fixed 5 100, .autoFit 100] [auto, auto, auto, auto, auto, auto] = hundreds 6 := by decide

-- :919 ColumnAutoFillAutoFitNoCollapse; :1266 RowAutoFillAutoFitNoCollapse
-- (repeat(auto-fit, 100px) repeat(5, 100px), five items: the fixed tracks never collapse)
theorem AutoFillAutoFitNoCollapse_vectors :
    laneSizes 1000 [.autoFit 100, .fixed 5 100] [auto, auto, auto, auto, auto] = hundreds 10 := by decide

end TestsBlock
