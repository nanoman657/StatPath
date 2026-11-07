import BlockWritingMode

namespace TestsBlock

open ChromiumLayout.BlockWritingMode

-- constraint_space_builder_test.cc:17: AvailableSizeFromHorizontalICB
-- PhysicalSize icb_size{kIndefiniteSize, LayoutUnit(51)};
-- indefinite inline size becomes icb_size.height (51)
def AvailableSizeFromHorizontalICB_available : Nat :=
  resolveConstraintSpaceInlineSize none 51

def AvailableSizeFromHorizontalICB_percentage : Nat :=
  resolveConstraintSpaceInlineSize none 51

theorem AvailableSizeFromHorizontalICB_vectors :
    AvailableSizeFromHorizontalICB_available = 51 ∧
    AvailableSizeFromHorizontalICB_percentage = 51 := ⟨rfl, rfl⟩

-- constraint_space_builder_test.cc:49: AvailableSizeFromVerticalICB
-- PhysicalSize icb_size{LayoutUnit(51), kIndefiniteSize};
-- indefinite inline size becomes icb_size.width (51)
def AvailableSizeFromVerticalICB_available : Nat :=
  resolveConstraintSpaceInlineSize none 51

def AvailableSizeFromVerticalICB_percentage : Nat :=
  resolveConstraintSpaceInlineSize none 51

theorem AvailableSizeFromVerticalICB_vectors :
    AvailableSizeFromVerticalICB_available = 51 ∧
    AvailableSizeFromVerticalICB_percentage = 51 := ⟨rfl, rfl⟩

end TestsBlock
