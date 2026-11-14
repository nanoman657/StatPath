import TableLayout

namespace ChromiumLayout
namespace TestsBlock

open TableLayout

-- layout_table_test.cc:230: CloseToMaxWidth
theorem CloseToMaxWidth_vectors :
    -- Table with width 999999px remains 999999px
    clampTableWidth 999999 = 999999 ∧
    -- and is bounded by clampTableWidth_le
    clampTableWidth 999999 ≤ kMaxTableWidth := by
  decide

-- layout_table_test.cc:250: PaddingWithCollapsedBorder
theorem PaddingWithCollapsedBorder_vectors :
    -- Padding for table with border-collapse: collapse is 0
    tablePadding true 20 = 0 := by
  decide

-- layout_table_test.cc:260: OutOfOrderHeadAndBody
theorem OutOfOrderHeadAndBody_vectors :
    -- Empty thead has rowCount 0, so only tbody is in the section order
    let sections : List TableSectionSpec := [
      { id := 1, secType := .tbody, rowCount := 1 },
      { id := 2, secType := .thead, rowCount := 0 }
    ]
    let ordered := orderTableSections sections
    ordered.length = 1 ∧
    (ordered[0]!).secType = .tbody := by
  decide

-- layout_table_test.cc:279: OutOfOrderFootAndBody
theorem OutOfOrderFootAndBody_vectors :
    -- Empty tfoot has rowCount 0, so only tbody is in the section order
    let sections : List TableSectionSpec := [
      { id := 1, secType := .tfoot, rowCount := 0 },
      { id := 2, secType := .tbody, rowCount := 1 }
    ]
    let ordered := orderTableSections sections
    ordered.length = 1 ∧
    (ordered[0]!).secType = .tbody := by
  decide

-- layout_table_test.cc:298: OutOfOrderHeadFootAndBody
theorem OutOfOrderHeadFootAndBody_vectors :
    -- Sections in HTML: tfoot, thead, tbody.
    -- In layout section order: thead first, tbody middle, tfoot last.
    let sections : List TableSectionSpec := [
      { id := 1, secType := .tfoot, rowCount := 1 },
      { id := 2, secType := .thead, rowCount := 1 },
      { id := 3, secType := .tbody, rowCount := 1 }
    ]
    let ordered := orderTableSections sections
    ordered.length = 3 ∧
    (ordered[0]!).secType = .thead ∧
    (ordered[1]!).secType = .tbody ∧
    (ordered[2]!).secType = .tfoot := by
  decide

-- layout_table_test.cc:88: CollapsedBorders
-- Collapsed border outsets on table edges resolved via conflict resolution.
-- CSS 2.1 §17.6.2, §17.6.2.1.
theorem CollapsedBorders_vectors :
    -- Table 1: top hidden (0), bottom 8px (4px = 256 LU), left hidden (0), right 10px (5px = 320 LU)
    collapsedBorderOutsetLU [{ width := 0, isHidden := true }] = 0 ∧
    collapsedBorderOutsetLU [{ width := 8, isHidden := false }] = 256 ∧
    collapsedBorderOutsetLU [{ width := 0, isHidden := true }] = 0 ∧
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }] = 320 ∧
    -- Table 2: cells have hidden border -> all edges resolve to 0
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 0, isHidden := true }] = 0 ∧
    -- Table 3: widest border wins: top 15px (7.5px = 480 LU), bottom 40px (20px = 1280 LU), left 30px (15px = 960 LU), right 40px (20px = 1280 LU)
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 15, isHidden := false }] = 480 ∧
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 40, isHidden := false }] = 1280 ∧
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 30, isHidden := false }] = 960 ∧
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 40, isHidden := false }] = 1280 := by
  decide

-- layout_table_test.cc:143: CollapsedBordersWithCol
-- Combined cell, col, and table collapsed borders.
-- CSS 2.1 §17.6.2, §17.6.2.1.
theorem CollapsedBordersWithCol_vectors :
    -- Table 1: table has hidden border -> all edges resolve to 0
    collapsedBorderOutsetLU [{ width := 20, isHidden := false }, { width := 0, isHidden := true }] = 0 ∧
    -- Table 2: cells have hidden border -> all edges resolve to 0
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 20, isHidden := false }, { width := 0, isHidden := true }] = 0 ∧
    -- Table 3: combined cell and col: top 20px (10px = 640 LU), bottom 20px (10px = 640 LU), left 12px (6px = 384 LU), right 20px (10px = 640 LU)
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 20, isHidden := false }] = 640 ∧
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 20, isHidden := false }] = 640 ∧
    collapsedBorderOutsetLU [{ width := 10, isHidden := false }, { width := 12, isHidden := false }] = 384 ∧
    collapsedBorderOutsetLU [{ width := 20, isHidden := false }, { width := 16, isHidden := false }] = 640 := by
  decide

end TestsBlock
end ChromiumLayout
