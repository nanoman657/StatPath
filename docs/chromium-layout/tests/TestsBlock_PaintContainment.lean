import BlockOverflow

namespace ChromiumLayout
namespace TestsBlock

open BlockOverflow

-- paint_containment_test.cc:34: BlockPaintContainment
-- CSS Containment Level 2 §3.3 Paint Containment:
-- An element with `contain: paint` creates an independent formatting context,
-- does not create a scroll container, acts as containing block for fixed position objects,
-- and clips overflow along both axes.
theorem BlockPaintContainment_vectors :
    createsNewFormattingContext .visible .visible true = true ∧
    isScrollContainer .visible .visible = false ∧
    canContainFixedPositionObjects true = true ∧
    clipsAxis .visible true = true := by
  decide

end TestsBlock
end ChromiumLayout
