import BlockOverflow

namespace ChromiumLayout
namespace TestsBlock

open BlockOverflow

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
