import ColumnBreakAppeal

namespace TestsBlock

open ChromiumLayout.ColumnBreakAppeal

-- All tests in column_layout_algorithm_test.cc:5723..6451 use #parent { columns: 3; column-gap: 10px;
-- column-fill: auto; width: 320px; height: 100px } -> colW = 100, gap = 10, fragH = 100.

-- column_layout_algorithm_test.cc:5723 AvoidBreakBetween
theorem AvoidBreakBetween_vectors :
    layoutAppeal 100 [.leaf 81 30, .leaf 82 30, .leaf 83 30, .leaf 84 30 true] =
      ([(0, 81, 30, []), (30, 82, 30, [])], [(0, 83, 30, []), (30, 84, 30, [])]) := by rfl

-- :5762 AvoidAndForceBreakBetween
theorem AvoidAndForceBreakBetween_vectors :
    layoutAppeal 100 [.leaf 81 30, .leaf 82 30, .leaf 83 30 false false true, .leaf 84 30 true] =
      ([(0, 81, 30, []), (30, 82, 30, []), (60, 83, 30, [])], [(0, 84, 30, [])]) := by rfl

-- :5800 AvoidBreakBetweenInFloat (parallel float flow + 150px in-flow sibling)
theorem AvoidBreakBetweenInFloat_vectors :
    layoutAppeal 100 [.box 100 [(81, 30, false), (82, 30, false), (83, 30, false), (84, 30, true)]] =
      ([(0, 100, 100, [(0, 81, 30), (30, 82, 30)])],
       [(0, 100, 60, [(0, 83, 30), (30, 84, 30)])]) ∧
    layoutAppeal 100 [.leaf 100 150] = ([(0, 100, 100, [])], [(0, 100, 50, [])]) := ⟨rfl, rfl⟩

-- :5845 IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid
theorem IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid_vectors :
    layoutAppeal 100 [.leaf 81 30, .leaf 82 30 true, .leaf 83 30 true, .leaf 84 30 true] =
      ([(0, 81, 30, []), (30, 82, 30, []), (60, 83, 30, []), (90, 84, 10, [])],
       [(0, 84, 20, [])]) := by rfl

-- :5892 AvoidBreakBetweenAndInsideIgnoreInside
theorem AvoidBreakBetweenAndInsideIgnoreInside_vectors :
    layoutAppeal 100 [.box 100 [(80, 20, false), (81, 30, false), (82, 30, false), (83, 30, true)] false false true] =
      ([(0, 100, 100, [(0, 80, 20), (20, 81, 30)])],
       [(0, 100, 60, [(0, 82, 30), (30, 83, 30)])]) := by rfl

-- :5938 AvoidBreakBetweenAndInside
theorem AvoidBreakBetweenAndInside_vectors :
    layoutAppeal 100 [.leaf 32 20,
                      .box 100 [(33, 20, false), (34, 20, false), (35, 20, false), (36, 20, false)] false true true,
                      .leaf 37 20] =
      ([(0, 32, 20, [])],
       [(0, 100, 80, [(0, 33, 20), (20, 34, 20), (40, 35, 20), (60, 36, 20)]), (80, 37, 20, [])]) := by rfl

-- :5984 AvoidBreakBetweenInsideBreakableParent
theorem AvoidBreakBetweenInsideBreakableParent_vectors :
    layoutAppeal 100 [.box 100 [(33, 20, false), (34, 20, false)],
                      .box 100 [(35, 20, false), (36, 20, true), (37, 20, true), (38, 20, true)]] =
      ([(0, 100, 40, [(0, 33, 20), (20, 34, 20)])],
       [(0, 100, 80, [(0, 35, 20), (20, 36, 20), (40, 37, 20), (60, 38, 20)])]) := by rfl

-- :6037 AvoidBreakBetweenAfterBreakableSibling
theorem AvoidBreakBetweenAfterBreakableSibling_vectors :
    layoutAppeal 100 [.box 100 [(33, 20, false), (34, 20, false), (35, 20, false), (36, 20, true)] false true,
                      .box 100 [(37, 20, false), (38, 20, true)]] =
      ([(0, 100, 100, [(0, 33, 20), (20, 34, 20)])],
       [(0, 100, 40, [(0, 35, 20), (20, 36, 20)]), (40, 100, 40, [(0, 37, 20), (20, 38, 20)])]) := by rfl

-- :6092 AvoidBreakBetweenBreakInsidePreviousSibling
theorem AvoidBreakBetweenBreakInsidePreviousSibling_vectors :
    layoutAppeal 100 [.leaf 32 20,
                      .box 100 [(33, 20, false), (34, 20, false), (35, 20, false), (36, 20, false)] false true,
                      .leaf 37 20] =
      ([(0, 32, 20, []), (20, 100, 80, [(0, 33, 20), (20, 34, 20), (40, 35, 20)])],
       [(0, 100, 20, [(0, 36, 20)]), (20, 37, 20, [])]) := by rfl

-- :6136 AvoidBreakBetweenHonorOrphansWidows
theorem AvoidBreakBetweenHonorOrphansWidows_vectors :
    layoutAppeal 100 [.box 100 (List.replicate 4 (0, 20, false)) false false false 2 2, .leaf 100 30 true] =
      ([(0, 100, 100, [(0, 0, 20), (20, 0, 20)])],
       [(0, 100, 40, [(0, 0, 20), (20, 0, 20)]), (40, 100, 30, [])]) := by rfl

-- :6182 AvoidBreakBetweenHonorOrphansWidows2
theorem AvoidBreakBetweenHonorOrphansWidows2_vectors :
    layoutAppeal 100 [.leaf 100 40, .box 100 (List.replicate 2 (0, 20, false)) false false false 2 2, .leaf 100 30 true] =
      ([(0, 100, 40, [])],
       [(0, 100, 40, [(0, 0, 20), (20, 0, 20)]), (40, 100, 30, [])]) := by rfl

-- :6225 AvoidBreakBetweenHonorOrphansWidows3
theorem AvoidBreakBetweenHonorOrphansWidows3_vectors :
    layoutAppeal 100 [.box 100 (List.replicate 4 (0, 20, false)) false false false 2 2,
                      .box 100 (List.replicate 3 (0, 20, false)) true false false 2 2] =
      ([(0, 100, 100, [(0, 0, 20), (20, 0, 20)])],
       [(0, 100, 40, [(0, 0, 20), (20, 0, 20)]), (40, 100, 60, [(0, 0, 20), (20, 0, 20), (40, 0, 20)])]) := by rfl

-- :6281 AvoidBreakBetweenIgnoreOrphansWidows
theorem AvoidBreakBetweenIgnoreOrphansWidows_vectors :
    layoutAppeal 100 [.leaf 100 40 false true, .box 100 (List.replicate 2 (0, 20, false)) false false false 2 2,
                      .leaf 100 30 true] =
      ([(0, 100, 40, []), (40, 100, 60, [(0, 0, 20)])],
       [(0, 100, 20, [(0, 0, 20)]), (20, 100, 30, [])]) := by rfl

-- :6326 AvoidBreakBetweenLinesInsideBreakAvoid
theorem AvoidBreakBetweenLinesInsideBreakAvoid_vectors :
    layoutAppeal 100 [.leaf 33 20, .leaf 34 20, .box 35 (List.replicate 2 (0, 20, false)) false false true,
                      .leaf 36 30 true] =
      ([(0, 33, 20, []), (20, 34, 20, [])],
       [(0, 35, 40, [(0, 0, 20), (20, 0, 20)]), (40, 36, 30, [])]) := by rfl

-- :6375 AvoidBreakBetweenBreakAtEarlyClassC
theorem AvoidBreakBetweenBreakAtEarlyClassC_vectors :
    layoutAppeal 100 [.box 22 [(33, 20, false), (44, 20, false)], .leaf 55 70 true] =
      ([(0, 22, 100, [(0, 33, 20)])],
       [(0, 22, 20, [(0, 44, 20)]), (20, 55, 70, [])]) := by rfl

-- :6416 AvoidBreakBeforeBlockReplacedContent and :6451 TallReplacedContent
theorem AvoidBreakReplacedContent_vectors :
    layoutAppeal 100 [.leaf 22 40, .leaf 33 50, .leaf 44 50 true false false true] =
      ([(0, 22, 40, [])], [(0, 33, 50, []), (50, 44, 50, [])]) ∧
    layoutAppeal 100 [.leaf 44 150 false false false true] =
      ([(0, 44, 150, [])], []) := ⟨rfl, rfl⟩

-- column_layout_algorithm_test.cc:5246 ForcedBreakBetweenSpanners, :5279 ForcedBreakBetweenSpanners2,
-- :5424 SoftBreakBetweenSpanners, :5458 SoftBreakBetweenSpanners2,
-- :5530 AvoidSoftBreakBetweenSpanners2, :5574 AvoidSoftBreakBetweenSpanners3
theorem AvoidSoftBreakBetweenSpanners_vectors :
    layoutAppeal 100 [.leaf 55 40 false false true, .leaf 66 40] =
      ([(0, 55, 40, [])], [(0, 66, 40, [])]) ∧
    layoutAppeal 100 [.leaf 55 60, .leaf 66 60] =
      ([(0, 55, 60, [])], [(0, 66, 60, [])]) ∧
    layoutAppeal 100 [.box 11 [(22, 20, false), (33, 20, false), (44, 20, false)], .leaf 55 60 true] =
      ([(0, 11, 100, [(0, 22, 20), (20, 33, 20)])],
       [(0, 11, 20, [(0, 44, 20)]), (20, 55, 60, [])]) ∧
    layoutAppeal 100 [.box 11 (List.replicate 3 (0, 20, false)) false false false 3 3, .leaf 55 60 true] =
      ([(0, 11, 100, [(0, 0, 20), (20, 0, 20)])],
       [(0, 11, 20, [(0, 0, 20)]), (20, 55, 60, [])]) := ⟨rfl, rfl, rfl, rfl⟩

end TestsBlock
