/-
  Feasibility spike: vertical stacking of two in-flow CSS 2.1 block boxes.
  Mirrors `docs/chromium-layout/spike/stack.bend` function by function and
  models Blink LayoutNG's `BlockLayoutAlgorithm::ComputeInflowPosition`,
  `MarginStrut::Append` / `MarginStrut::Sum` (for non-negative margins),
  and BFC block-offset resolution in:
    `third_party/blink/renderer/core/layout/block_layout_algorithm.cc`
    `third_party/blink/renderer/core/layout/geometry/margin_strut.cc`

  Checked with Lean 4.34.0 (core only, no Mathlib, no `sorry`).
-/

namespace ChromiumLayout.Spike

/-- An in-flow block box with block-axis box-model metrics (in LayoutUnits). -/
structure BlockBox where
  marginStart : Nat
  borderStart : Nat
  contentSize : Nat
  borderEnd   : Nat
  marginEnd   : Nat
  deriving DecidableEq, Repr

/-- Output fragment geometry for two vertically stacked sibling block boxes
    inside a BFC-root block container. -/
structure StackLayout where
  y1            : Nat
  h1            : Nat
  collapsedGap  : Nat
  y2            : Nat
  h2            : Nat
  containerSize : Nat
  deriving DecidableEq, Repr

/-- Collapse two adjacent non-negative vertical margins (`MarginStrut::Sum`). -/
def collapseMargins (m1 m2 : Nat) : Nat :=
  Nat.max m1 m2

/-- Border-box block-size of a `BlockBox`: `borderStart + contentSize + borderEnd`. -/
def boxBorderSize (b : BlockBox) : Nat :=
  (b.borderStart + b.contentSize) + b.borderEnd

/-- Compute the BFC block-offset of the second box given the first box's
    border-box end offset (`y1End = y1 + h1`) and the two adjacent margins. -/
def nextBorderEdge (y1End m1End m2Start : Nat) : Nat :=
  y1End + collapseMargins m1End m2Start

/-- Stack two in-flow block boxes vertically inside a block container with
    block-start/block-end border+padding `padStart` and `padEnd`. -/
def stackTwo (padStart padEnd : Nat) (b1 b2 : BlockBox) : StackLayout :=
  let y1  := padStart + b1.marginStart
  let h1  := boxBorderSize b1
  let y1e := y1 + h1
  let gap := collapseMargins b1.marginEnd b2.marginStart
  let y2  := y1e + gap
  let h2  := boxBorderSize b2
  let y2e := y2 + h2
  let csz := y2e + (b2.marginEnd + padEnd)
  { y1 := y1, h1 := h1, collapsedGap := gap, y2 := y2, h2 := h2, containerSize := csz }

/-- Theorem 1: Margin collapsing is idempotent (`MarginStrut` of two equal margins equals that margin). -/
theorem collapseMargins_idem (m : Nat) :
    collapseMargins m m = m := by
  simp [collapseMargins]

/-- Theorem 2: Margin collapsing is commutative (`MarginStrut` order-independence for two adjacent margins). -/
theorem collapseMargins_comm (a b : Nat) :
    collapseMargins a b = collapseMargins b a := by
  simp [collapseMargins, Nat.max_comm]

/-- Theorem 3: Margin collapsing is associative (`MarginStrut` across self-collapsing intermediate struts). -/
theorem collapseMargins_assoc (a b c : Nat) :
    collapseMargins (collapseMargins a b) c = collapseMargins a (collapseMargins b c) := by
  simp [collapseMargins, Nat.max_assoc]

/-- Theorem 4: For any two stacked block boxes `b1` and `b2`, the second box's BFC block-offset `y2`
    equals the first box's border-box end (`y1 + boxBorderSize b1`) plus the collapsed margin
    `max(b1.marginEnd, b2.marginStart)`. -/
theorem stackTwo_y2_eq (padStart padEnd : Nat) (b1 b2 : BlockBox) :
    (stackTwo padStart padEnd b1 b2).y2 =
      (stackTwo padStart padEnd b1 b2).y1 + boxBorderSize b1 +
        collapseMargins b1.marginEnd b2.marginStart := by
  rfl

/-- Theorem 5: Vertical monotonicity / sibling non-overlap: the second block box's border-box
    starts at or after the first block box's border-box end (`y1 + h1 ≤ y2`), and the gap
    between them is at least `b1.marginEnd` and at least `b2.marginStart`. -/
theorem stackTwo_non_overlap (padStart padEnd : Nat) (b1 b2 : BlockBox) :
    let out := stackTwo padStart padEnd b1 b2
    out.y1 + out.h1 ≤ out.y2 ∧
    out.y1 + out.h1 + b1.marginEnd ≤ out.y2 ∧
    out.y1 + out.h1 + b2.marginStart ≤ out.y2 := by
  dsimp [stackTwo, collapseMargins]
  have hL : b1.marginEnd ≤ Nat.max b1.marginEnd b2.marginStart := Nat.le_max_left _ _
  have hR : b2.marginStart ≤ Nat.max b1.marginEnd b2.marginStart := Nat.le_max_right _ _
  omega

/-- Theorem 6: Container intrinsic block-size conservation: the container's intrinsic block-size
    is at least the second child's border-box end (`y2 + h2`) and equals the exact sum of
    parent border/padding, both children's border-box sizes, outer margins, and the collapsed inner margin. -/
theorem stackTwo_container_size (padStart padEnd : Nat) (b1 b2 : BlockBox) :
    let out := stackTwo padStart padEnd b1 b2
    out.y2 + out.h2 ≤ out.containerSize ∧
    out.containerSize =
      padStart + b1.marginStart + boxBorderSize b1 +
        Nat.max b1.marginEnd b2.marginStart +
        boxBorderSize b2 + b2.marginEnd + padEnd := by
  dsimp [stackTwo, collapseMargins, boxBorderSize]
  omega

#print axioms collapseMargins_idem
#print axioms collapseMargins_comm
#print axioms collapseMargins_assoc
#print axioms stackTwo_y2_eq
#print axioms stackTwo_non_overlap
#print axioms stackTwo_container_size

/-! ## M1 Extension: Signed `MarginStrut` (`geometry/margin_strut.h:16-58`, `geometry/margin_strut.cc:11-46`) -/

/-- Signed `MarginStrut` (`geometry/margin_strut.h:16-18`) storing the maximum positive margin (`pos`)
    and maximum negative margin magnitude (`neg`). -/
structure SignedMarginStrut where
  pos : Nat
  neg : Nat
  deriving DecidableEq, Repr

/-- `MarginStrut::Append` (`geometry/margin_strut.cc:11-30`, non-quirky case). -/
def appendMarginStrut (s1 s2 : SignedMarginStrut) : SignedMarginStrut :=
  { pos := Nat.max s1.pos s2.pos, neg := Nat.max s1.neg s2.neg }

/-- `MarginStrut::Sum` (`geometry/margin_strut.h:40-44`, clamped to `Nat`). -/
def sumMarginStrut (s : SignedMarginStrut) : Nat :=
  s.pos - s.neg

/-- Apply a signed `MarginStrut` offset (`+ s.pos - s.neg`) to a block offset `y` (`geometry/margin_strut.h:40-44`). -/
def applyMarginStrut (y : Nat) (s : SignedMarginStrut) : Nat :=
  (y + s.pos) - s.neg

/-- A block box with signed block-start and block-end margin struts. -/
structure SignedBlockBox where
  marginStart : SignedMarginStrut
  borderStart : Nat
  contentSize : Nat
  borderEnd   : Nat
  marginEnd   : SignedMarginStrut
  deriving DecidableEq, Repr

/-- Stack two in-flow block boxes with signed margins vertically inside a BFC-root container. -/
def stackTwoSigned (padStart padEnd : Nat) (b1 b2 : SignedBlockBox) : StackLayout :=
  let y1   := applyMarginStrut padStart b1.marginStart
  let h1   := (b1.borderStart + b1.contentSize) + b1.borderEnd
  let y1e  := y1 + h1
  let mGap := appendMarginStrut b1.marginEnd b2.marginStart
  let gap  := sumMarginStrut mGap
  let y2   := applyMarginStrut y1e mGap
  let h2   := (b2.borderStart + b2.contentSize) + b2.borderEnd
  let y2e  := y2 + h2
  let csz  := applyMarginStrut y2e b2.marginEnd + padEnd
  { y1 := y1, h1 := h1, collapsedGap := gap, y2 := y2, h2 := h2, containerSize := csz }

/-- Theorem 7: Signed `MarginStrut` append is idempotent. -/
theorem appendMarginStrut_idem (s : SignedMarginStrut) :
    appendMarginStrut s s = s := by
  cases s
  simp [appendMarginStrut]

/-- Theorem 8: Signed `MarginStrut` append is commutative. -/
theorem appendMarginStrut_comm (s1 s2 : SignedMarginStrut) :
    appendMarginStrut s1 s2 = appendMarginStrut s2 s1 := by
  cases s1
  cases s2
  simp [appendMarginStrut, Nat.max_comm]

/-- Theorem 9: Signed `MarginStrut` append is associative. -/
theorem appendMarginStrut_assoc (s1 s2 s3 : SignedMarginStrut) :
    appendMarginStrut (appendMarginStrut s1 s2) s3 =
      appendMarginStrut s1 (appendMarginStrut s2 s3) := by
  cases s1
  cases s2
  cases s3
  simp [appendMarginStrut, Nat.max_assoc]

/-- Theorem 10: Signed `MarginStrut` forms a join-semilattice (Law 1 on `SignedMarginStrut`). -/
theorem signed_margin_strut_semilattice (s1 s2 s3 : SignedMarginStrut) :
    appendMarginStrut (appendMarginStrut s1 s2) s3 =
      appendMarginStrut s1 (appendMarginStrut s2 s3) ∧
    appendMarginStrut s1 s2 = appendMarginStrut s2 s1 ∧
    appendMarginStrut s1 s1 = s1 := by
  exact ⟨appendMarginStrut_assoc s1 s2 s3, appendMarginStrut_comm s1 s2, appendMarginStrut_idem s1⟩

/-- Theorem 11: When negative margin components are zero, `stackTwoSigned` agrees with `stackTwo`. -/
theorem stackTwoSigned_nonneg_eq (padStart padEnd : Nat) (b1 b2 : BlockBox) :
    let sb1 : SignedBlockBox :=
      { marginStart := ⟨b1.marginStart, 0⟩
      , borderStart := b1.borderStart
      , contentSize := b1.contentSize
      , borderEnd   := b1.borderEnd
      , marginEnd   := ⟨b1.marginEnd, 0⟩ }
    let sb2 : SignedBlockBox :=
      { marginStart := ⟨b2.marginStart, 0⟩
      , borderStart := b2.borderStart
      , contentSize := b2.contentSize
      , borderEnd   := b2.borderEnd
      , marginEnd   := ⟨b2.marginEnd, 0⟩ }
    stackTwoSigned padStart padEnd sb1 sb2 = stackTwo padStart padEnd b1 b2 := by
  simp [stackTwoSigned, stackTwo, applyMarginStrut, appendMarginStrut, sumMarginStrut,
    collapseMargins, boxBorderSize, Nat.add_assoc]

#print axioms appendMarginStrut_idem
#print axioms appendMarginStrut_comm
#print axioms appendMarginStrut_assoc
#print axioms signed_margin_strut_semilattice
#print axioms stackTwoSigned_nonneg_eq

end ChromiumLayout.Spike
