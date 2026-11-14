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

-- grid_layout_algorithm_test.cc:209: GridLayoutAlgorithmGapGeometry
-- Midpoints of row and column gaps for CSS grid decorations.
-- CSS Gap Decorations Level 1 §3.2, §3.3, CSS Box Alignment 3 §8.
theorem GridLayoutAlgorithmGapGeometry_vectors :
    let colTracks := [80, 120, 90]
    let rowTracks := [90, 130, 110, 140]
    let colGap := 14
    let rowGap := 12
    let geom := computeGridGapGeometry colGap rowGap colTracks rowTracks
    geom.inlineGap = 14 ∧
    geom.blockGap = 12 ∧
    geom.mainGaps = [96, 238, 360] ∧
    geom.crossGaps = [87, 221] ∧
    geom.contentInlineStart = 0 ∧
    geom.contentBlockStart = 0 ∧
    geom.contentInlineEnd = 318 ∧
    geom.contentBlockEnd = 506 := by
  decide

-- grid_layout_algorithm_test.cc:290: GapGeomoetryWithSpanningItems
-- Cross and main gap blocked segment state ranges created by spanning grid items.
-- CSS Gap Decorations Level 1 §3.2, §3.3.
theorem GapGeomoetryWithSpanningItems_vectors :
    let grid : List (List (Option Nat)) := [
      [some 1, some 1, some 3],
      [some 4, some 5, some 3],
      [some 6, some 8, some 8]
    ]
    crossGapRanges 0 grid = [⟨0, 1, .blocked⟩] ∧
    crossGapRanges 1 grid = [⟨2, 3, .blocked⟩] ∧
    mainGapRanges 0 3 grid = [⟨2, 3, .blocked⟩] ∧
    mainGapRanges 1 3 grid = [] := by
  decide

-- grid_layout_algorithm_test.cc:421: GapGeometryWithEmptyCellsAndSpanningItems
-- Gap segment state ranges with empty cells (emptyBefore, emptyAfter, emptyBoth) and spanning items.
-- CSS Gap Decorations Level 1 §3.2, §3.3.
theorem GapGeometryWithEmptyCellsAndSpanningItems_vectors :
    let grid : List (List (Option Nat)) := [
      [some 1, some 1, some 3],
      [some 2, none, some 3],
      [none, none, some 3]
    ]
    crossGapRanges 0 grid = [⟨0, 1, .blocked⟩, ⟨1, 2, .emptyAfter⟩, ⟨2, 3, .emptyBoth⟩] ∧
    crossGapRanges 1 grid = [⟨1, 3, .emptyBefore⟩] ∧
    mainGapRanges 0 3 grid = [⟨1, 2, .emptyAfter⟩, ⟨2, 3, .blocked⟩] ∧
    mainGapRanges 1 3 grid = [⟨0, 1, .emptyAfter⟩, ⟨1, 2, .emptyBoth⟩, ⟨2, 3, .blocked⟩] := by
  decide

-- grid_layout_algorithm_test.cc:171: GridLayoutAlgorithmTest.GridLayoutAlgorithmAvailableRowSizes
-- Available row size for grid items spanning rows [1/2, 2/4, 3/5, 6/7, 4/6] with grid-gap: 10px
-- across track sizes [0, 0, 100, 100, 0, 100].
-- CSS Grid Layout Module Level 1 §11.5, §11.6.
theorem GridLayoutAlgorithmAvailableRowSizes_vectors :
    let tracks := [0, 0, 100, 100, 0, 100]
    let gap := 10
    itemAvailableTrackSize tracks gap 1 2 = 0 ∧
    itemAvailableTrackSize tracks gap 2 4 = 110 ∧
    itemAvailableTrackSize tracks gap 3 5 = 210 ∧
    itemAvailableTrackSize tracks gap 6 7 = 100 ∧
    itemAvailableTrackSize tracks gap 4 6 = 110 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- grid_layout_algorithm_test.cc:603: GridLayoutAlgorithmTest.GridLayoutAlgorithmRanges
-- CSS Grid Layout Module Level 1 §7.2.3, §7.6.
theorem GridLayoutAlgorithmRanges_vectors :
    let rowRanges := gridRangesFromBreakpoints [0, 1, 1000]
    let colRanges := gridRangesFromBreakpoints [0, 1, 2, 3, 4, 8]
    rowRanges = [⟨0, 1, false⟩, ⟨1, 999, false⟩] ∧
    colRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨2, 1, false⟩, ⟨3, 1, false⟩, ⟨4, 4, false⟩] := by
  exact ⟨rfl, rfl⟩

-- grid_layout_algorithm_test.cc:650: GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesWithAutoRepeater
-- CSS Grid Layout Module Level 1 §7.2.3, §7.6.
theorem GridLayoutAlgorithmRangesWithAutoRepeater_vectors :
    let rowRanges := gridRangesFromBreakpoints [0, 1, 20, 21, 22]
    let colRanges := gridRangesFromBreakpoints [0, 1, 2, 3, 4, 5, 6, 7]
    rowRanges = [⟨0, 1, false⟩, ⟨1, 19, false⟩, ⟨20, 1, false⟩, ⟨21, 1, false⟩] ∧
    colRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨2, 1, false⟩, ⟨3, 1, false⟩, ⟨4, 1, false⟩, ⟨5, 1, false⟩, ⟨6, 1, false⟩] := by
  exact ⟨rfl, rfl⟩

-- grid_layout_algorithm_test.cc:701: GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicit
-- CSS Grid Layout Module Level 1 §7.2.3, §7.6.
theorem GridLayoutAlgorithmRangesImplicit_vectors :
    let colRanges := gridRangesFromBreakpoints [0, 1, 2, 4]
    let rowRanges := gridRangesFromBreakpoints [0, 1, 2]
    colRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨2, 2, false⟩] ∧
    rowRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩] := by
  exact ⟨rfl, rfl⟩

-- grid_layout_algorithm_test.cc:764: GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitAutoColumns
-- CSS Grid Layout Module Level 1 §7.2.3, §7.6.
theorem GridLayoutAlgorithmRangesImplicitAutoColumns_vectors :
    let colRanges := gridRangesFromBreakpoints [0, 1, 2]
    let rowRanges := gridRangesFromBreakpoints [0, 1, 2]
    colRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩] ∧
    rowRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩] := by
  exact ⟨rfl, rfl⟩

-- grid_layout_algorithm_test.cc:822: GridLayoutAlgorithmTest.GridLayoutAlgorithmRangesImplicitAutoRows
-- CSS Grid Layout Module Level 1 §7.2.3, §7.6.
theorem GridLayoutAlgorithmRangesImplicitAutoRows_vectors :
    let colRanges := gridRangesFromBreakpoints [0, 1, 2, 4]
    let rowRanges := gridRangesFromBreakpoints [0, 1, 2]
    colRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩, ⟨2, 2, false⟩] ∧
    rowRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩] := by
  exact ⟨rfl, rfl⟩

-- grid_layout_algorithm_test.cc:1159: GridLayoutAlgorithmTest.GridLayoutAlgorithmGridPositions
-- CSS Grid Layout Module Level 1 §7.2.3, §7.6, §8.3.
theorem GridLayoutAlgorithmGridPositions_vectors :
    let colRanges := gridRangesFromBreakpoints [0, 1, 2]
    let rowRanges := gridRangesFromBreakpoints [0, 1, 3, 4, 5, 6]
    colRanges = [⟨0, 1, false⟩, ⟨1, 1, false⟩] ∧
    rowRanges = [⟨0, 1, false⟩, ⟨1, 2, false⟩, ⟨3, 1, false⟩, ⟨4, 1, false⟩, ⟨5, 1, false⟩] := by
  exact ⟨rfl, rfl⟩

-- grid_layout_algorithm_test.cc:929: GridLayoutAlgorithmTest.GridLayoutAlgorithmAutoGridPositions
-- Grid auto-placement resolves grid areas for items with definite and auto positions.
-- item1: row 2, col 2 -> [1..2, 1..2]
-- item2: auto -> [1..2, 0..1]
-- item3: auto -> [0..1, 1..2]
-- item4: row 1, col 1 -> [0..1, 0..1]
-- CSS Grid Layout Module Level 1 §8.5.
theorem GridLayoutAlgorithmAutoGridPositions_vectors :
    let items : List GridPlacementItem := [
      { id := 1, col := some (1, 2), row := some (1, 2) },
      { id := 2 },
      { id := 3 },
      { id := 4, col := some (0, 1), row := some (0, 1) }
    ]
    let areas := resolveAutoGridPositions 2 items false
    areas = [
      ⟨1, 2, 1, 2⟩,
      ⟨1, 2, 0, 1⟩,
      ⟨0, 1, 1, 2⟩,
      ⟨0, 1, 0, 1⟩
    ] := by
  exact rfl

-- grid_layout_algorithm_test.cc:1003: GridLayoutAlgorithmTest.GridLayoutAlgorithmAutoDense
-- Grid dense auto-placement resolves grid areas for 16 items with multi-track spans and fixed/auto positions.
-- CSS Grid Layout Module Level 1 §8.5.
theorem GridLayoutAlgorithmAutoDense_vectors :
    let items : List GridPlacementItem := [
      { id := 0, col := some (0, 2), row := some (0, 2) },
      { id := 1, col := some (3, 7), row := some (0, 3) },
      { id := 2, col := some (8, 10), row := some (0, 1) },
      { id := 3, col := some (0, 2), row := some (3, 5) },
      { id := 4, col := some (3, 5), row := some (3, 4) },
      { id := 5, col := some (6, 9), row := some (4, 5) },
      { id := 6, col := some (5, 6), row := some (7, 8) },
      { id := 7, col := some (5, 7), rowSpan := 2 },
      { id := 8, row := some (3, 4), colSpan := 2 },
      { id := 9, col := some (5, 6) },
      { id := 10, colSpan := 5, rowSpan := 5 },
      { id := 11, rowSpan := 9 },
      { id := 12, colSpan := 2, rowSpan := 3 },
      { id := 13, rowSpan := 5 },
      { id := 14 },
      { id := 15 }
    ]
    let areas := resolveAutoGridPositions 10 items true
    areas = [
      ⟨0, 2, 0, 2⟩,
      ⟨3, 7, 0, 3⟩,
      ⟨8, 10, 0, 1⟩,
      ⟨0, 2, 3, 5⟩,
      ⟨3, 5, 3, 4⟩,
      ⟨6, 9, 4, 5⟩,
      ⟨5, 6, 7, 8⟩,
      ⟨5, 7, 5, 7⟩,
      ⟨5, 7, 3, 4⟩,
      ⟨5, 6, 4, 5⟩,
      ⟨0, 5, 5, 10⟩,
      ⟨9, 10, 1, 10⟩,
      ⟨7, 9, 1, 4⟩,
      ⟨2, 3, 0, 5⟩,
      ⟨7, 8, 0, 1⟩,
      ⟨0, 1, 2, 3⟩
    ] := by
  exact rfl

end TestsBlock
end ChromiumLayout
