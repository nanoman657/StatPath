import BlockSticky
import ColumnWidth
import BlockFragmentation

namespace TestsBlock

open ChromiumLayout.BlockSticky
open ChromiumLayout.ColumnWidth
open ChromiumLayout.BlockFlow

-- physical_fragment_test.cc:84: StickyAxisEnabled
theorem StickyAxisEnabled_vectors :
    propagateSingleAxis .vertical .vertical = ⟨.vertical, .none⟩ ∧
    propagateSingleAxis .vertical .horizontal = ⟨.none, .horizontal⟩ ∧
    propagateSingleAxis .vertical .both = ⟨.vertical, .horizontal⟩ ∧
    propagateSingleAxis .both .horizontal = ⟨.horizontal, .none⟩ := by
  decide

-- physical_fragment_test.cc:113: StickyAxisDisabled
theorem StickyAxisDisabled_vectors :
    propagateLegacy .vertical = ⟨.both, .none⟩ ∧
    propagateLegacy .horizontal = ⟨.both, .none⟩ ∧
    propagateLegacy .both = ⟨.both, .none⟩ := by
  decide

-- physical_fragment_test.cc:134: DumpFragmentTreeBasic
def DumpFragmentTreeBasic_body_size : Nat × Nat := (800 - 16, 0)
def DumpFragmentTreeBasic_block_size : Nat × Nat := (800 - 16, 0)

theorem DumpFragmentTreeBasic_vectors :
    DumpFragmentTreeBasic_body_size = (784, 0) ∧
    DumpFragmentTreeBasic_block_size = (784, 0) := by
  decide

-- physical_fragment_test.cc:149: DumpFragmentTreeWithAbspos
def DumpFragmentTreeWithAbspos_offset : Nat × Nat := (8, 8)
def DumpFragmentTreeWithAbspos_size : Nat × Nat := (0, 0)

theorem DumpFragmentTreeWithAbspos_vectors :
    DumpFragmentTreeWithAbspos_offset = (8, 8) ∧
    DumpFragmentTreeWithAbspos_size = (0, 0) := by
  decide

-- physical_fragment_test.cc:165: DumpFragmentTreeWithAbsposInRelpos
def DumpFragmentTreeWithAbsposInRelpos_offset : Nat × Nat := (10, 20)
def DumpFragmentTreeWithAbsposInRelpos_size : Nat × Nat := (0, 0)

theorem DumpFragmentTreeWithAbsposInRelpos_vectors :
    DumpFragmentTreeWithAbsposInRelpos_offset = (10, 20) ∧
    DumpFragmentTreeWithAbsposInRelpos_size = (0, 0) := by
  decide

-- physical_fragment_test.cc:213: DumpFragmentTreeWithTargetInsideColumn
def DumpFragmentTreeWithTargetInsideColumn_col_width : Nat := usedWidth 3 0 10 320
def DumpFragmentTreeWithTargetInsideColumn_col_count : Nat := usedCount 3 0 10 320
def DumpFragmentTreeWithTargetInsideColumn_col_offsets : List Nat :=
  let w := DumpFragmentTreeWithTargetInsideColumn_col_width
  let g := 10
  [0, w + g, w + g + w + g]

theorem DumpFragmentTreeWithTargetInsideColumn_vectors :
    DumpFragmentTreeWithTargetInsideColumn_col_width = 100 ∧
    DumpFragmentTreeWithTargetInsideColumn_col_count = 3 ∧
    DumpFragmentTreeWithTargetInsideColumn_col_offsets = [0, 110, 220] ∧
    sliceSize 50 0 150 0 = 50 ∧
    sliceSize 50 0 150 1 = 50 ∧
    sliceSize 50 0 150 2 = 50 := by
  decide

end TestsBlock
