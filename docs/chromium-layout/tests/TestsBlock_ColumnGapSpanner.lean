import ColumnGapSpanner
/-
  TestsBlock_ColumnGapSpanner.lean: Formalized multi-column spanner fragmentation, invalid spanner BFC,
  and gap decoration test vectors from
  third_party/blink/renderer/core/layout/column_layout_algorithm_test.cc.
-/

namespace ChromiumLayout
namespace TestsBlock_ColumnGapSpanner

open ColumnGapSpanner

-- column_layout_algorithm_test.cc:4980
-- ColumnLayoutAlgorithmTest.MarginAndBorderTopWithSpanner
theorem marginAndBorderTopWithSpanner :
    layoutMarginBorderWithSpanner 100 10 3 22 200 100 33 100 300 =
      (500,
       (0, 0, 100, 300),
       (0, 200, 22, 100),
       (0, 300, 33, 100),
       [(0, 400, 100, 100), (110, 400, 100, 100), (220, 400, 100, 100)]) :=
  rfl
#print axioms marginAndBorderTopWithSpanner

-- column_layout_algorithm_test.cc:5054
-- ColumnLayoutAlgorithmTest.InvalidSpanners
theorem invalidSpanners :
    layoutInvalidSpannersInBfc 100 10 3 1 10 30 =
      ((322, 12),
       [((1, 1, 100, 10), (0, 0, 10, 10), (10, 0, 90, 10)),
        ((111, 1, 100, 10), (0, 0, 10, 10), (10, 0, 90, 10)),
        ((221, 1, 100, 10), (0, 0, 10, 10), (10, 0, 90, 10))]) :=
  rfl
#print axioms invalidSpanners

-- column_layout_algorithm_test.cc:5101
-- ColumnLayoutAlgorithmTest.BreakInsideSpanner
theorem breakInsideSpanner :
    fragmentInnerSpanner 50 20 100 1 20 35 false =
      ([9, 26], (26, 24), 22) :=
  rfl
#print axioms breakInsideSpanner

-- column_layout_algorithm_test.cc:5148
-- ColumnLayoutAlgorithmTest.BreakInsideSpannerTwice
theorem breakInsideSpannerTwice :
    fragmentInnerSpanner 50 20 150 1 20 85 false =
      ([9, 50, 26], (26, 24), 22) :=
  rfl
#print axioms breakInsideSpannerTwice

-- column_layout_algorithm_test.cc:5198
-- ColumnLayoutAlgorithmTest.BreakInsideSpannerWithContent
theorem breakInsideSpannerWithContent :
    fragmentInnerSpanner 50 0 98 1 20 49 true =
      ([29, 20], (20, 29), 0) :=
  rfl
#print axioms breakInsideSpannerWithContent

-- column_layout_algorithm_test.cc:6480
-- ColumnLayoutAlgorithmTest.GapDecorationBasic
theorem gapDecorationBasic :
    crossGaps 2 60 10 3 = [(67, 2), (137, 2)] ∧
    contentInlineBounds 2 200 60 10 3 = (2, 202) ∧
    accumulateMainGaps 2 0 0 3 [.cols 600] = ([], 202) :=
  ⟨rfl, rfl, rfl⟩
#print axioms gapDecorationBasic

-- column_layout_algorithm_test.cc:6553
-- ColumnLayoutAlgorithmTest.GapDecorationContentEndPastContainer
theorem gapDecorationContentEndPastContainer :
    (crossGaps 2 60 10 5).length = 4 ∧
    contentInlineBounds 2 200 60 10 5 = (2, 277) ∧
    accumulateMainGaps 2 0 0 5 [.cols 1000] = ([], 202) :=
  ⟨rfl, rfl, rfl⟩
#print axioms gapDecorationContentEndPastContainer

-- column_layout_algorithm_test.cc:6619
-- ColumnLayoutAlgorithmTest.GapDecorationColumnWrapOneColumn
theorem gapDecorationColumnWrapOneColumn :
    crossGaps 2 60 10 1 = [] ∧
    contentInlineBounds 2 200 60 10 1 = (2, 202) ∧
    (accumulateMainGaps 2 60 10 1 [.cols 120, .spanner 1, .cols 60]).1 =
      [(67, .none), (137, .none), (142, .startSpanner), (143, .endSpanner), (207, .none)] :=
  ⟨rfl, rfl, rfl⟩
#print axioms gapDecorationColumnWrapOneColumn

-- column_layout_algorithm_test.cc:6711
-- ColumnLayoutAlgorithmTest.GapDecorationColumnWrapBasic
theorem gapDecorationColumnWrapBasic :
    crossGaps 2 60 10 3 = [(67, 2), (137, 2)] ∧
    contentInlineBounds 2 200 60 10 3 = (2, 202) ∧
    accumulateMainGaps 2 60 10 3 [.cols 360] = ([(67, .none)], 132) :=
  ⟨rfl, rfl, rfl⟩
#print axioms gapDecorationColumnWrapBasic

-- column_layout_algorithm_test.cc:6798
-- ColumnLayoutAlgorithmTest.GapDecorationColumnWrapAndSpanner
theorem gapDecorationColumnWrapAndSpanner :
    crossGaps 2 60 10 3 = [(67, 2), (137, 2)] ∧
    contentInlineBounds 2 200 60 10 3 = (2, 202) ∧
    (accumulateMainGaps 2 80 10 3 [.cols 120, .spanner 10, .cols 240]).1 =
      [(42, .startSpanner), (52, .endSpanner), (87, .none)] :=
  ⟨rfl, rfl, rfl⟩
#print axioms gapDecorationColumnWrapAndSpanner

-- column_layout_algorithm_test.cc:6951
-- ColumnLayoutAlgorithmTest.GapDecorationTwoSpanners
theorem gapDecorationTwoSpanners :
    crossGaps 2 60 10 3 = [(67, 2), (137, 2)] ∧
    (accumulateMainGaps 128 0 640 3
      [.cols 6400, .spanner 64, .cols 9600, .spanner 64, .cols 9600]).1 =
      [(2262, .startSpanner), (2326, .endSpanner),
       (5526, .startSpanner), (5590, .endSpanner)] :=
  ⟨rfl, rfl⟩
#print axioms gapDecorationTwoSpanners

end TestsBlock_ColumnGapSpanner
end ChromiumLayout
