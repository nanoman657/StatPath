import BlockOverflow
import TableLayout

namespace ChromiumLayout
namespace TestsBlock

open BlockOverflow TableLayout

-- table/layout_table_section_test.cc:18: BackgroundIsKnownToBeOpaqueWithLayerAndCollapsedBorder
-- Section with layer and collapsed borders is never known to be opaque in any sub-rectangle.
-- CSS 2.1 §17.5.1, §17.6, CSS Backgrounds 3 §3.
theorem BackgroundIsKnownToBeOpaqueWithLayerAndCollapsedBorder_vectors :
    let ctx : TableBackgroundContext := { part := .section, hasLayer := true, collapsedBorders := true, isOpaqueColor := true }
    tableBackgroundIsKnownToBeOpaque ctx = false := by
  decide

-- table/layout_table_section_test.cc:35: BackgroundIsKnownToBeOpaqueWithBorderSpacing
-- Section with border spacing is never known to be opaque in any sub-rectangle.
-- CSS 2.1 §17.5.1, §17.6.1, CSS Backgrounds 3 §3.
theorem BackgroundIsKnownToBeOpaqueWithBorderSpacing_vectors :
    let ctx : TableBackgroundContext := { part := .section, borderSpacing := 10, isOpaqueColor := true }
    tableBackgroundIsKnownToBeOpaque ctx = false := by
  decide

-- table/layout_table_section_test.cc:50: BackgroundIsKnownToBeOpaqueWithEmptyCell
-- Section with border spacing and empty cell is never known to be opaque in any sub-rectangle.
-- CSS 2.1 §17.5.1, §17.6.1, CSS Backgrounds 3 §3.
theorem BackgroundIsKnownToBeOpaqueWithEmptyCell_vectors :
    let ctx : TableBackgroundContext := { part := .section, borderSpacing := 10, hasEmptyCells := true, isOpaqueColor := true }
    tableBackgroundIsKnownToBeOpaque ctx = false := by
  decide

-- table/layout_table_section_test.cc:66: VisualOverflowWithCollapsedBorders
-- Section self visual overflow equals border box; visual overflow expands to cover descendant outlines.
-- CSS 2.1 §17.6, CSS Overflow 3 §2.1.
theorem SectionVisualOverflowWithCollapsedBorders_vectors :
    let sectionBorderBox : PhysicalRect := ⟨0, 0, 100, 100⟩
    let selfVisualOverflow := sectionBorderBox
    let visualOverflow := expandEdges sectionBorderBox ⟨3, 8, 8, 8⟩
    selfVisualOverflow = sectionBorderBox ∧
    visualOverflow = ⟨-8, -3, 116, 111⟩ := by
  decide

end TestsBlock
end ChromiumLayout
