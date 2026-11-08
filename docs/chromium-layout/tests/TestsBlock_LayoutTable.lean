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

end TestsBlock
end ChromiumLayout
