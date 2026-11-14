import GridLayout

namespace ChromiumLayout
namespace TestsBlock

open GridLayout

-- grid_layout_algorithm_test.cc:1356: FixedSizePositioning
def fixedSizePositioning_spec : GridSpec :=
  { columns := [100, 100], rows := [100, 100], width := some 200, height := some 200 }

def fixedSizePositioning_items : List GridItem :=
  [ { w := some 100, h := some 100 },
    { w := some 100, h := some 100 },
    { w := some 100, h := some 100 },
    { w := some 100, h := some 100 } ]

theorem FixedSizePositioning_vectors :
    let res := layoutGrid fixedSizePositioning_spec fixedSizePositioning_items
    res.w = 200 ∧ res.h = 200 ∧ res.items.length = 4 ∧
    (res.items[0]!).x = 0 ∧ (res.items[0]!).y = 0 ∧ (res.items[0]!).w = 100 ∧ (res.items[0]!).h = 100 ∧
    (res.items[1]!).x = 100 ∧ (res.items[1]!).y = 0 ∧ (res.items[1]!).w = 100 ∧ (res.items[1]!).h = 100 ∧
    (res.items[2]!).x = 0 ∧ (res.items[2]!).y = 100 ∧ (res.items[2]!).w = 100 ∧ (res.items[2]!).h = 100 ∧
    (res.items[3]!).x = 100 ∧ (res.items[3]!).y = 100 ∧ (res.items[3]!).w = 100 ∧ (res.items[3]!).h = 100 := by
  decide

-- grid_layout_algorithm_test.cc:1405: FixedSizePositioningAutoRows
def fixedSizePositioningAutoRows_spec : GridSpec :=
  { columns := [100, 100], rows := [100, 100], width := some 200, height := some 200 }

def fixedSizePositioningAutoRows_items : List GridItem :=
  [ { w := some 100, h := some 100 },
    { col := some 1, w := some 100, h := some 100 },
    { w := some 100, h := some 100 },
    { w := some 100, h := some 100 } ]

theorem FixedSizePositioningAutoRows_vectors :
    let res := layoutGrid fixedSizePositioningAutoRows_spec fixedSizePositioningAutoRows_items
    res.w = 200 ∧ res.h = 200 ∧ res.items.length = 4 ∧
    (res.items[0]!).x = 0 ∧ (res.items[0]!).y = 0 ∧ (res.items[0]!).w = 100 ∧ (res.items[0]!).h = 100 ∧
    (res.items[1]!).x = 100 ∧ (res.items[1]!).y = 0 ∧ (res.items[1]!).w = 100 ∧ (res.items[1]!).h = 100 ∧
    (res.items[2]!).x = 0 ∧ (res.items[2]!).y = 100 ∧ (res.items[2]!).w = 100 ∧ (res.items[2]!).h = 100 ∧
    (res.items[3]!).x = 100 ∧ (res.items[3]!).y = 100 ∧ (res.items[3]!).w = 100 ∧ (res.items[3]!).h = 100 := by
  decide

-- grid_layout_algorithm_test.cc:1462: SpecifiedPositionsOutOfOrder
def specifiedPositionsOutOfOrder_spec : GridSpec :=
  { columns := [100, 100], rows := [100, 100], width := some 400, height := some 400 }

def specifiedPositionsOutOfOrder_items : List GridItem :=
  [ { col := some 1, row := some 1, w := some 100, h := some 100 },
    { col := some 0, row := some 0, w := some 90, h := some 90 },
    { col := some 1, row := some 0, w := some 80, h := some 80 },
    { col := some 0, row := some 1, w := some 70, h := some 70 } ]

theorem SpecifiedPositionsOutOfOrder_vectors :
    let res := layoutGrid specifiedPositionsOutOfOrder_spec specifiedPositionsOutOfOrder_items
    (res.items[0]!).x = 100 ∧ (res.items[0]!).y = 100 ∧ (res.items[0]!).w = 100 ∧ (res.items[0]!).h = 100 ∧
    (res.items[1]!).x = 0 ∧ (res.items[1]!).y = 0 ∧ (res.items[1]!).w = 90 ∧ (res.items[1]!).h = 90 ∧
    (res.items[2]!).x = 100 ∧ (res.items[2]!).y = 0 ∧ (res.items[2]!).w = 80 ∧ (res.items[2]!).h = 80 ∧
    (res.items[3]!).x = 0 ∧ (res.items[3]!).y = 100 ∧ (res.items[3]!).w = 70 ∧ (res.items[3]!).h = 70 := by
  decide

-- grid_layout_algorithm_test.cc:1536: GridWithGap
def gridWithGap_spec : GridSpec :=
  { columns := [100, 100], rows := [100, 100], colGap := 10, rowGap := 10, width := some 200, height := some 200 }

def gridWithGap_items : List GridItem :=
  [ { w := some 100, h := some 100 },
    { w := some 100, h := some 100 },
    { w := some 100, h := some 100 },
    { w := some 100, h := some 100 } ]

theorem GridWithGap_vectors :
    let res := layoutGrid gridWithGap_spec gridWithGap_items
    (res.items[0]!).x = 0 ∧ (res.items[0]!).y = 0 ∧
    (res.items[1]!).x = 110 ∧ (res.items[1]!).y = 0 ∧
    (res.items[2]!).x = 0 ∧ (res.items[2]!).y = 110 ∧
    (res.items[3]!).x = 110 ∧ (res.items[3]!).y = 110 := by
  decide

-- grid_layout_algorithm_test.cc:1586: GridWithPercentGap
-- Percentage gaps resolve against container inline/block dimensions (50% of 100px = 50px, 75% of 50px = 37.5px = 2400 LU).
-- CSS Grid 1 §10.1, CSS Box Alignment 3 §8.
theorem GridWithPercentGap_vectors :
    -- grid-column-gap: 50% of 100px width = 50px
    resolveGapPercent 50 (some 100) = 50 ∧
    -- grid-row-gap: 75% of 50px height = 37.5px = 2400 LU
    resolveGapPercentLU 75 (some 50) = 2400 := by
  decide

-- grid_layout_algorithm_test.cc:1640: AutoSizedGridWithGap
def autoSizedGridWithGap_spec : GridSpec :=
  { columns := [100, 200], rows := [100, 100], colGap := 50, rowGap := 75 }

def autoSizedGridWithGap_items : List GridItem :=
  [ { w := some 100, h := some 100 },
    { w := some 200, h := some 100 },
    { w := some 100, h := some 100 },
    { w := some 200, h := some 100 } ]

theorem AutoSizedGridWithGap_vectors :
    let res := layoutGrid autoSizedGridWithGap_spec autoSizedGridWithGap_items
    res.h = 275 ∧
    (res.items[0]!).x = 0 ∧ (res.items[0]!).y = 0 ∧ (res.items[0]!).w = 100 ∧ (res.items[0]!).h = 100 ∧
    (res.items[1]!).x = 150 ∧ (res.items[1]!).y = 0 ∧ (res.items[1]!).w = 200 ∧ (res.items[1]!).h = 100 ∧
    (res.items[2]!).x = 0 ∧ (res.items[2]!).y = 175 ∧ (res.items[2]!).w = 100 ∧ (res.items[2]!).h = 100 ∧
    (res.items[3]!).x = 150 ∧ (res.items[3]!).y = 175 ∧ (res.items[3]!).w = 200 ∧ (res.items[3]!).h = 100 := by
  decide

-- grid_layout_algorithm_test.cc:1739: ItemsSizeWithGap
def itemsSizeWithGap_spec : GridSpec :=
  { columns := [100, 100, 100], rows := [100], colGap := 20, width := some 340, height := some 100 }

def itemsSizeWithGap_items : List GridItem :=
  [ { col := some 0, row := some 0 },
    { col := some 1, row := some 0 },
    { col := some 2, row := some 0 } ]

theorem ItemsSizeWithGap_vectors :
    let res := layoutGrid itemsSizeWithGap_spec itemsSizeWithGap_items
    res.w = 340 ∧ res.h = 100 ∧
    (res.items[0]!).x = 0 ∧ (res.items[0]!).w = 100 ∧
    (res.items[1]!).x = 120 ∧ (res.items[1]!).w = 100 ∧
    (res.items[2]!).x = 240 ∧ (res.items[2]!).w = 100 := by
  decide

end TestsBlock
end ChromiumLayout
