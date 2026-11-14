/-
  BlockSticky.lean: CSS Positioned Layout Level 3 sticky positioning algorithm,
  written from CSS Positioned Layout Module Level 3 §2.3 (Sticky positioning)
  and checked against layout_box_model_object_test.cc (StickyPositionNested,
  StickyPositionChildHasLargerTop, StickyPositionParentHasLargerTop,
  StickyPositionChildPushingOutsideParent, StickyPositionTripleNestedDiv).
  Owned by the block lane (Block*).
-/

namespace ChromiumLayout
namespace BlockSticky

/-- Specification of a sticky box constraint in the block axis. CSS Positioned Layout 3 §2.3. -/
structure StickyConstraint where
  top : Option Nat := none
  inFlowTop : Nat := 0
  height : Nat := 0
  cbHeight : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- 1D constraint interval (top, height). CSS Positioned Layout 3 §2.3. -/
structure StickyInterval where
  top : Nat := 0
  height : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Compute scroller-relative containing block interval from container geometry.
    CSS Positioned Layout Module Level 3 §2.3. -/
def containingBlockInterval (containerTop containerPadding containerBorder containerHeight : Nat)
    (isBorderBox : Bool) : StickyInterval :=
  let cbTop := containerTop + containerBorder + containerPadding
  let bpTotal := 2 * (containerBorder + containerPadding)
  let cbHeight := if isBorderBox then containerHeight - bpTotal else containerHeight
  ⟨cbTop, cbHeight⟩

/-- Compute scroller-relative sticky box interval.
    CSS Positioned Layout Module Level 3 §2.3. -/
def stickyBoxInterval (cbTop offsetInCb stickyHeight : Nat) : StickyInterval :=
  ⟨cbTop + offsetInCb, stickyHeight⟩

/-- Compute the sticky offset along the block axis given scroll offset and ancestor shifts.
    CSS Positioned Layout Module Level 3 §2.3:
    The sticky box shifts to remain at `top` relative to the scroll container,
    constrained to never push outside its containing block (`cbHeight - height`). -/
def computeStickyOffset (c : StickyConstraint) (scrollPos : Nat) (ancestorShift : Nat) : Nat :=
  match c.top with
  | none => 0
  | some topInset =>
      let targetPos := scrollPos + topInset
      let startPos := c.inFlowTop + ancestorShift
      if targetPos ≤ startPos then 0
      else
        let desiredShift := targetPos - startPos
        let maxShift := if c.cbHeight ≥ c.height then c.cbHeight - c.height else 0
        Nat.min desiredShift maxShift

/-- Law: Sticky offset is always bounded by the containing block headroom (cbHeight - height).
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_offset_le_max_shift (c : StickyConstraint) (scrollPos ancShift : Nat)
    (hcb : c.cbHeight ≥ c.height) :
    computeStickyOffset c scrollPos ancShift ≤ c.cbHeight - c.height := by
  dsimp [computeStickyOffset]
  split
  · omega
  · split
    · omega
    · apply Nat.min_le_right

/-- Law: If no top inset is specified, sticky offset is 0.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_offset_none (c : StickyConstraint) (h : c.top = none) (scrollPos ancShift : Nat) :
    computeStickyOffset c scrollPos ancShift = 0 := by
  dsimp [computeStickyOffset]
  rw [h]

/-- Law: If target position is at or before starting position, sticky offset is 0.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_offset_unscrolled (c : StickyConstraint) (topInset : Nat) (h : c.top = some topInset)
    (scrollPos ancShift : Nat) (hunscrolled : scrollPos + topInset ≤ c.inFlowTop + ancShift) :
    computeStickyOffset c scrollPos ancShift = 0 := by
  dsimp [computeStickyOffset]
  rw [h]
  have hcond : scrollPos + topInset ≤ c.inFlowTop + ancShift := hunscrolled
  simp [hcond]

/-- Law: Sticky box start is always at or after containing block start.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_box_ge_cb_top (cbTop off h : Nat) :
    (stickyBoxInterval cbTop off h).top ≥ cbTop := by
  dsimp [stickyBoxInterval]
  omega

/-- Law: Containing block top is monotonic with container top offset.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem cb_interval_top_monotone (t1 t2 p b h : Nat) (isBb : Bool) (ht : t1 ≤ t2) :
    (containingBlockInterval t1 p b h isBb).top ≤ (containingBlockInterval t2 p b h isBb).top := by
  dsimp [containingBlockInterval]
  omega

end BlockSticky
end ChromiumLayout
