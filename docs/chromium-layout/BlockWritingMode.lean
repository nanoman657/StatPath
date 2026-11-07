/-
  BlockWritingMode.lean: physical <-> logical box-strut mapping, written from length_utils_test.cc
  (`TestBorders`, `TestPadding`). Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockWritingMode

/-- `writing-mode` (horizontal-tb, vertical-lr, vertical-rl); direction is ltr. -/
inductive WritingMode where
  | horizontalTb
  | verticalLr
  | verticalRl

/-- Four physical edge values. -/
structure Phys where
  top : Nat
  right : Nat
  bottom : Nat
  left : Nat
  deriving DecidableEq, Repr

/-- Four logical edge values. -/
structure Logical where
  inlineStart : Nat
  inlineEnd : Nat
  blockStart : Nat
  blockEnd : Nat
  deriving DecidableEq, Repr

/-- Physical to logical edges (`TestBorders`: vertical-lr gives block-start = left, inline-end =
    bottom, block-end = right, inline-start = top; `TestPadding`: vertical-rl gives block-start =
    right, block-end = left). -/
def toLogical : WritingMode → Phys → Logical
  | .horizontalTb, p => ⟨p.left, p.right, p.top, p.bottom⟩
  | .verticalLr, p => ⟨p.top, p.bottom, p.left, p.right⟩
  | .verticalRl, p => ⟨p.top, p.bottom, p.right, p.left⟩

/-- Logical to physical edges (inverse of `toLogical`). -/
def toPhysical : WritingMode → Logical → Phys
  | .horizontalTb, l => ⟨l.blockStart, l.inlineEnd, l.blockEnd, l.inlineStart⟩
  | .verticalLr, l => ⟨l.inlineStart, l.blockEnd, l.inlineEnd, l.blockStart⟩
  | .verticalRl, l => ⟨l.inlineStart, l.blockStart, l.inlineEnd, l.blockEnd⟩

/-- The two mappings are inverse for every writing mode (justifies reading `TestBorders` and
    `TestPadding` as one rule). -/
theorem toPhysical_toLogical (wm : WritingMode) (p : Phys) : toPhysical wm (toLogical wm p) = p := by
  cases wm <;> rfl

/-- Converse direction. -/
theorem toLogical_toPhysical (wm : WritingMode) (l : Logical) : toLogical wm (toPhysical wm l) = l := by
  cases wm <;> rfl

end BlockWritingMode
end ChromiumLayout
