import ColumnNested

namespace TestsBlock

open ChromiumLayout
open ChromiumLayout.ColumnLayout
open ChromiumLayout.ColumnNested

-- column_layout_algorithm_test.cc:3163 ColumnBalancingSingleLineInNested and
-- :3195 ColumnBalancingSingleLineInNestedSpanner
theorem ColumnBalancingSingleLineNested_vectors :
    let outer := layoutBalancedMulticol {
      cols := 3, gap := 10, width := 320, step := 20, children := [⟨0, .px 100, 20⟩]
    }
    let inner := layoutBalancedMulticol {
      cols := 2, gap := 10, width := 100, step := 20, children := [⟨0, .px 0, 20⟩]
    }
    let spannerInner := layoutMulticolWithSpanners {
      cols := 2, gap := 0, width := 100, items := [{ isSpanner := true, height := 20 }]
    }
    (outer.w, outer.h, outer.columns.map fun c => (c.relX, c.relY, c.w, c.h)) =
      (320, 20, [(0, 0, 100, 20)]) ∧
    (inner.w, inner.h, inner.columns.map fun c => (c.relX, c.relY, c.w, c.h)) =
      (100, 20, [(0, 0, 45, 20)]) ∧
    (spannerInner.w, spannerInner.h,
     spannerInner.fragments.map fun f => (f.isSpanner, f.relX, f.relY, f.w, f.h)) =
      (100, 20, [(false, 0, 0, 50, 0), (true, 0, 0, 100, 20)]) := ⟨rfl, rfl, rfl⟩

-- column_layout_algorithm_test.cc:3931 Nested, :4019 NestedNoInnerContent,
-- :4051 NestedSomeInnerContent
theorem ColumnNestedPaddingItems_vectors :
    layoutNestedItems 50 100 2 10 1 20 20 (some 100) [10, 20, 30, 40, 50, 60, 70] =
      [(20, 100, 30, [(1, 1, 44, 29, [(0, 0, 10, 20)]), (55, 1, 44, 29, [(0, 0, 20, 20)])]),
       (0, 100, 50, [(1, 0, 44, 50, [(0, 0, 30, 20), (0, 20, 40, 20)]),
                     (55, 0, 44, 50, [(0, 0, 50, 20), (0, 20, 60, 20)])]),
       (0, 100, 22, [(1, 0, 44, 21, [(0, 0, 70, 20)])])] ∧
    layoutNestedItems 50 100 2 10 1 20 20 (some 100) [] =
      [(20, 100, 30, [(1, 1, 44, 29, [])]),
       (0, 100, 50, []),
       (0, 100, 22, [])] ∧
    layoutNestedItems 50 100 2 10 1 20 20 (some 100) [6] =
      [(20, 100, 30, [(1, 1, 44, 29, [(0, 0, 6, 20)])]),
       (0, 100, 50, []),
       (0, 100, 22, [])] := ⟨rfl, rfl, rfl⟩

-- column_layout_algorithm_test.cc:4086 NestedLimitedHeight,
-- :4179 NestedUnbalancedInnerAutoHeight, :5671 SpannerAsMulticol
theorem ColumnNestedOverflowAndAuto_vectors :
    layoutNestedItems 50 100 2 10 0 20 20 (some 80) [10, 20, 30, 40, 50, 60, 70, 80, 90] =
      [(20, 100, 30, [(0, 0, 45, 30, [(0, 0, 10, 20)]), (55, 0, 45, 30, [(0, 0, 20, 20)])]),
       (0, 100, 50, [(0, 0, 45, 50, [(0, 0, 30, 20), (0, 20, 40, 20)]),
                     (55, 0, 45, 50, [(0, 0, 50, 20), (0, 20, 60, 20)]),
                     (110, 0, 45, 50, [(0, 0, 70, 20), (0, 20, 80, 20)]),
                     (165, 0, 45, 50, [(0, 0, 90, 20)])])] ∧
    layoutNestedItems 50 100 2 10 0 20 0 none (List.replicate 6 45) =
      [(0, 100, 50, [(0, 0, 45, 50, [(0, 0, 45, 20), (0, 20, 45, 20)]),
                     (55, 0, 45, 50, [(0, 0, 45, 20), (0, 20, 45, 20)])]),
       (0, 100, 40, [(0, 0, 45, 50, [(0, 0, 45, 20), (0, 20, 45, 20)])])] ∧
    layoutNestedItems 50 100 2 10 0 20 0 (some 80) [131, 132, 133, 134, 135, 136] =
      [(0, 100, 50, [(0, 0, 45, 50, [(0, 0, 131, 20), (0, 20, 132, 20)]),
                     (55, 0, 45, 50, [(0, 0, 133, 20), (0, 20, 134, 20)])]),
       (0, 100, 30, [(0, 0, 45, 30, [(0, 0, 135, 20)]),
                     (55, 0, 45, 30, [(0, 0, 136, 20)])])] := ⟨rfl, rfl, rfl⟩

-- column_layout_algorithm_test.cc:4143 NestedLimitedHeightWithPadding,
-- :4225 NestedAtOuterBoundary, :4258 NestedZeroHeightAtOuterBoundary,
-- :4321 NestedWithTallBorder, :4353 NestedWithTallSpanner
theorem ColumnNestedBlockChrome_vectors :
    layoutNestedBlock 100 100 10 0 50 (some 100) 22 200 =
      [(0, 100, 100, [(0, 50, 45, 50, (0, 0, 22, 50)), (55, 50, 45, 50, (0, 0, 22, 50))]),
       (0, 100, 50, [(0, 0, 45, 50, (0, 0, 22, 50)), (55, 0, 45, 50, (0, 0, 22, 50))])] ∧
    layoutNestedBlock 100 100 10 100 0 (some 50) 22 70 =
      [(0, 100, 50, [(0, 0, 45, 50, (0, 0, 22, 50)), (55, 0, 45, 50, (0, 0, 22, 20))])] ∧
    layoutNestedBlock 100 100 10 100 0 none 22 0 =
      [(100, 100, 0, [(0, 0, 45, 0, (0, 0, 22, 0))])] ∧
    layoutNestedBlock 100 100 10 0 100 (some 50) 22 70 =
      [(0, 100, 100, []),
       (0, 100, 50, [(0, 0, 45, 50, (0, 0, 22, 50)), (55, 0, 45, 50, (0, 0, 22, 20))])] ∧
    layoutNestedBlock 100 100 10 0 100 none 22 70 =
      [(0, 100, 100, []),
       (0, 100, 35, [(0, 0, 45, 35, (0, 0, 22, 35)), (55, 0, 45, 35, (0, 0, 22, 35))])] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- fragmentation_test.cc:68 MultipleFragmentsAndColumnSpanner,
-- :132 MultipleFragmentsNestedMulticol, :187 HasSeenAllChildrenIfc
theorem FragmentationNestedAndSpanner_vectors :
    let sp := layoutMulticolWithSpanners {
      cols := 3, gap := 10, width := 620,
      items := List.replicate 4 { height := 20, avoid := true } ++
               [{ isSpanner := true, height := 0 }] ++
               List.replicate 5 { height := 20, avoid := true } ++
               [{ isSpanner := true, height := 0 }] ++
               List.replicate 7 { height := 20, avoid := true }
    }
    (sp.w, sp.h, sp.fragments.map fun f => (f.isSpanner, f.w, (f.slices.map (·.h)).sum)) =
      (620, 140, [(false, 200, 40), (false, 200, 40), (true, 620, 0),
                  (false, 200, 40), (false, 200, 40), (false, 200, 20), (true, 620, 0),
                  (false, 200, 60), (false, 200, 60), (false, 200, 20)]) ∧
    sliceStream 100 [(11, 350), (22, 350)] =
      [[(11, 100), (11, 100), (11, 100), (11, 50)],
       [(22, 50), (22, 100), (22, 100), (22, 100)]] ∧
    ifcBreakTokensHasSeenAll 50 300 20 7 = [false, false, false, true, true] := ⟨rfl, rfl, rfl⟩

end TestsBlock
