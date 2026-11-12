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

-- grid_layout_algorithm_test.cc:209: GridLayoutAlgorithmGapGeometry
-- Checks midpoints, gap counts and content edges. The GapGeometry container type and gap-size
-- accessors are Blink API and are not modelled.
def gapGeometry_cols : List Nat := [80, 120, 90]
def gapGeometry_rows : List Nat := [90, 130, 110, 140]

theorem GridLayoutAlgorithmGapGeometry_vectors :
    gapMidpoint 12 gapGeometry_rows 0 = 96 ∧ gapMidpoint 12 gapGeometry_rows 1 = 238 ∧
    gapMidpoint 12 gapGeometry_rows 2 = 360 ∧
    gapGeometry_rows.length - 1 = 3 ∧
    gapMidpoint 14 gapGeometry_cols 0 = 87 ∧ gapMidpoint 14 gapGeometry_cols 1 = 221 ∧
    gapGeometry_cols.length - 1 = 2 ∧
    trackOffset 14 gapGeometry_cols 0 = 0 ∧ trackOffset 12 gapGeometry_rows 0 = 0 ∧
    gridContentSize 14 gapGeometry_cols = 318 ∧ gridContentSize 12 gapGeometry_rows = 506 := by
  decide

-- grid_layout_algorithm_test.cc:290: GapGeomoetryWithSpanningItems (name as in the source)
-- The three auto rows (zero base size) are stretched to fill the 320px height, so each is
-- `stretchedAutoSize 320 10 3`. Single-cell items are omitted: they never cross a gap.
def spanningGaps_tracks : List Nat := List.replicate 3 (stretchedAutoSize 320 10 3)
def spanningGaps_items : List GapItem :=
  [ { rowLo := 0, rowHi := 1, colLo := 0, colHi := 2 },   -- item1: columns 1-2, row 1
    { rowLo := 0, rowHi := 2, colLo := 2, colHi := 3 },   -- item3: column 3, rows 1-2
    { rowLo := 2, rowHi := 3, colLo := 1, colHi := 3 } ]  -- item8: columns 2-3, row 3

theorem GapGeomoetryWithSpanningItems_vectors :
    stretchedAutoSize 320 10 3 = 100 ∧
    gapMidpoint 10 spanningGaps_tracks 0 = 105 ∧ gapMidpoint 10 spanningGaps_tracks 1 = 215 ∧
    gridContentSize 10 spanningGaps_tracks = 320 ∧
    -- Blocked ranges under the default `column-rule-break: spanning-item` (CSS Gap Decorations:
    -- decorations do not paint behind a spanning item): the items that cover both tracks of the gap.
    (spanningGaps_items.filterMap fun it =>
      if it.colLo ≤ 0 && 0 + 1 < it.colHi then some (it.rowLo, it.rowHi) else none) = [(0, 1)] ∧
    (spanningGaps_items.filterMap fun it =>
      if it.colLo ≤ 1 && 1 + 1 < it.colHi then some (it.rowLo, it.rowHi) else none) = [(2, 3)] ∧
    (spanningGaps_items.filterMap fun it =>
      if it.rowLo ≤ 0 && 0 + 1 < it.rowHi then some (it.colLo, it.colHi) else none) = [(2, 3)] ∧
    (spanningGaps_items.filterMap fun it =>
      if it.rowLo ≤ 1 && 1 + 1 < it.rowHi then some (it.colLo, it.colHi) else none) = [] := by
  decide

end TestsBlock
end ChromiumLayout
