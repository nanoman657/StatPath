/-
  OutOfFlowCB.lean: containing block of a fixed-position box, written from layout_block_test.cc
  (`ContainmentStyleChange`) and the out-of-flow tests. Owned by the block lane (OutOfFlow*).
-/
namespace ChromiumLayout
namespace OutOfFlowCB

/-- Index (0 = nearest) of the ancestor that is the containing block of a `position:fixed` box, or
    `none` for the viewport (`LayoutView`). `ancestorsLayoutContain` lists, nearest first, whether
    each ancestor has layout containment (`contain: strict/layout/paint/content`). Required by
    layout_block_test.cc:101 `ContainmentStyleChange`. -/
def fixedContainingBlockFrom : List Bool → Nat → Option Nat
  | [], _ => none
  | b :: bs, i => if b then some i else fixedContainingBlockFrom bs (i + 1)

/-- `fixedContainingBlockFrom` starting at the nearest ancestor. -/
def fixedContainingBlock (ancestorsLayoutContain : List Bool) : Option Nat :=
  fixedContainingBlockFrom ancestorsLayoutContain 0

/-- When no ancestor has layout containment, fixed-position containing block is viewport (none)
    (out_of_flow_layout_part_test.cc: `FixedInsideAbs`). -/
theorem fixed_no_containment (bs : List Bool) (h : ∀ b ∈ bs, b = false) :
    fixedContainingBlock bs = none := by
  unfold fixedContainingBlock
  generalize 0 = i
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
      dsimp [fixedContainingBlockFrom]
      have hb : b = false := h b (List.Mem.head _)
      rw [hb]
      dsimp
      apply ih
      intro b' hb'
      exact h b' (List.Mem.tail _ hb')

end OutOfFlowCB
end ChromiumLayout
