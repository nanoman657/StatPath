/-
  docs/chromium-layout/LayoutBlock.lean

  M2 proofs of Law 2 (`block_siblings_monotonic_non_overlapping`),
  Law 3 (`bfc_intrinsic_block_size_conservation`), and Blink M2 test vectors.
-/
import LayoutTypes

namespace ChromiumLayout

/-! ## 7. M2 Proofs: In-Flow Block Layout, Law 2, and Law 3 -/

/-- When the right-hand margin strut has zero negative margin (`m.neg = 0`),
    appending `m` to any `s` never decreases `s.sum`. -/
theorem MarginStrut.sum_le_append_of_neg_eq_zero (s m : MarginStrut) (hm : m.neg = 0) :
    s.sum ≤ (MarginStrut.append s m).sum := by
  cases s with
  | mk sp sn =>
    cases m with
    | mk mp mn =>
      dsimp at hm
      subst hm
      simp only [MarginStrut.append, MarginStrut.sum, Nat.max_zero]
      have hmax : sp ≤ Nat.max sp mp := Nat.le_max_left sp mp
      omega

theorem LayoutInputNode.startMarginStrut_neg_eq_zero
    (c : LayoutInputNode) (h : ChildMarginsNonNegative c) :
    c.startMarginStrut.neg = 0 := by
  cases c with
  | blockChild id b p m ew eh isBfc csz hasC iStart iEnd =>
    dsimp [ChildMarginsNonNegative] at h
    dsimp [LayoutInputNode.startMarginStrut, MarginStrut.append]
    split
    · rfl
    · simp [h.1]
  | inlineChild id b p m ew eh strut items =>
    rfl

theorem LayoutInputNode.endMarginStrut_neg_eq_zero
    (c : LayoutInputNode) (h : ChildMarginsNonNegative c) :
    c.endMarginStrut.neg = 0 := by
  cases c with
  | blockChild id b p m ew eh isBfc csz hasC iStart iEnd =>
    dsimp [ChildMarginsNonNegative] at h
    dsimp [LayoutInputNode.endMarginStrut, MarginStrut.append]
    split
    · rfl
    · simp [h.2]
  | inlineChild id b p m ew eh strut items =>
    rfl

/-- Cursor lower bound on the next placed child's `blockOffset` in `layoutChildren`. -/
def cursorBound (bfcResolved : Bool) (pos : Nat) (strut : MarginStrut) : Nat :=
  if bfcResolved then pos + strut.sum else 0

/-- Lemma A: Every fragment emitted by `layoutChildren` has `offset.blockOffset ≥ cursorBound`. -/
theorem layoutChildren_offset_ge_bound
    (avail : Nat) :
    ∀ (cs : List LayoutInputNode) (bfcResolved : Bool) (pos : Nat) (strut : MarginStrut),
      (bfcResolved = false → pos = 0) →
      (∀ c ∈ cs, ChildMarginsNonNegative c) →
      ∀ f ∈ (layoutChildren avail bfcResolved pos strut cs).fragments,
        cursorBound bfcResolved pos strut ≤ f.offset.blockOffset
  | [], _, _, _, _, _, f, hf => by
    simp [layoutChildren] at hf
  | c :: rest, bfcResolved, pos, strut, hPos, hNonNeg, f, hf => by
    have hc : ChildMarginsNonNegative c := hNonNeg c (List.Mem.head rest)
    have hRest : ∀ x ∈ rest, ChildMarginsNonNegative x :=
      fun x hx => hNonNeg x (List.Mem.tail c hx)
    have hStartNeg : c.startMarginStrut.neg = 0 :=
      LayoutInputNode.startMarginStrut_neg_eq_zero c hc
    have hEndNeg : c.endMarginStrut.neg = 0 :=
      LayoutInputNode.endMarginStrut_neg_eq_zero c hc
    have hStrutLeStart : strut.sum ≤ (MarginStrut.append strut c.startMarginStrut).sum :=
      MarginStrut.sum_le_append_of_neg_eq_zero strut c.startMarginStrut hStartNeg
    have hStartLeNext :
        (MarginStrut.append strut c.startMarginStrut).sum ≤
          (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut).sum :=
      MarginStrut.sum_le_append_of_neg_eq_zero
        (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut hEndNeg
    dsimp [layoutChildren] at hf
    split at hf
    · simp only [List.mem_cons] at hf
      rcases hf with rfl | hfTail
      · dsimp [cursorBound]
        cases bfcResolved <;> simp <;> omega
      · have ih := layoutChildren_offset_ge_bound avail rest bfcResolved pos
          (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
          hPos hRest f hfTail
        dsimp [cursorBound] at ih ⊢
        cases bfcResolved <;> simp at ih ⊢ <;> omega
    · simp only [List.mem_cons] at hf
      rcases hf with rfl | hfTail
      · dsimp [cursorBound]
        cases bfcResolved <;> simp <;> omega
      · have ih := layoutChildren_offset_ge_bound avail rest true
          ((if bfcResolved then pos + (MarginStrut.append strut c.startMarginStrut).sum else 0) +
            c.borderBoxBlockSize)
          c.endMarginStrut
          (by intro h; cases h) hRest f hfTail
        dsimp [cursorBound] at ih ⊢
        cases bfcResolved <;> simp at ih ⊢ <;> omega

/-- Lemma B: Any two sibling fragments at indices `i < j` in `layoutChildren` have
    monotonically non-overlapping block intervals. -/
theorem layoutChildren_siblings_non_overlapping
    (avail : Nat) :
    ∀ (cs : List LayoutInputNode) (bfcResolved : Bool) (pos : Nat) (strut : MarginStrut)
      (_hPos : bfcResolved = false → pos = 0)
      (_hNonNeg : ∀ c ∈ cs, ChildMarginsNonNegative c)
      (i j : Nat) (hij : i < j)
      (hj : j < (layoutChildren avail bfcResolved pos strut cs).fragments.length),
      let fs := (layoutChildren avail bfcResolved pos strut cs).fragments
      let fi := fs[i]'(Nat.lt_trans hij hj)
      let fj := fs[j]'hj
      fi.offset.blockOffset + fi.borderBoxSize.blockSize ≤ fj.offset.blockOffset
  | [], _, _, _, _, _, _, _, _, hj => by
    simp [layoutChildren] at hj
  | c :: rest, bfcResolved, pos, strut, hPos, hNonNeg, i, j, hij, hj => by
    have hc : ChildMarginsNonNegative c := hNonNeg c (List.Mem.head rest)
    have hRest : ∀ x ∈ rest, ChildMarginsNonNegative x :=
      fun x hx => hNonNeg x (List.Mem.tail c hx)
    have hStartNeg : c.startMarginStrut.neg = 0 :=
      LayoutInputNode.startMarginStrut_neg_eq_zero c hc
    have hEndNeg : c.endMarginStrut.neg = 0 :=
      LayoutInputNode.endMarginStrut_neg_eq_zero c hc
    have hStartLeNext :
        (MarginStrut.append strut c.startMarginStrut).sum ≤
          (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut).sum :=
      MarginStrut.sum_le_append_of_neg_eq_zero
        (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut hEndNeg
    by_cases hSelf : c.isSelfCollapsing = true
    · cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          have hj' : j' < (layoutChildren avail bfcResolved pos
              (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
              rest).fragments.length := by
            simpa [layoutChildren, hSelf] using hj
          have hMem : (layoutChildren avail bfcResolved pos
              (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
              rest).fragments[j'] ∈
            (layoutChildren avail bfcResolved pos
              (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
              rest).fragments := List.getElem_mem hj'
          have hBound := layoutChildren_offset_ge_bound avail rest bfcResolved pos
            (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
            hPos hRest _ hMem
          simp only [layoutChildren, hSelf, ↓reduceIte, List.getElem_cons_zero,
            List.getElem_cons_succ]
          dsimp [cursorBound] at hBound
          cases bfcResolved <;> simp at hBound ⊢ <;> omega
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          have hij' : i' < j' := Nat.lt_of_succ_lt_succ hij
          have hj' : j' < (layoutChildren avail bfcResolved pos
              (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
              rest).fragments.length := by
            simpa [layoutChildren, hSelf] using hj
          have ih := layoutChildren_siblings_non_overlapping avail rest bfcResolved pos
            (MarginStrut.append (MarginStrut.append strut c.startMarginStrut) c.endMarginStrut)
            hPos hRest i' j' hij' hj'
          simpa [layoutChildren, hSelf] using ih
    · have hSelfF : c.isSelfCollapsing = false := Bool.eq_false_iff.mpr hSelf
      let nextPos := (if bfcResolved then pos + (MarginStrut.append strut c.startMarginStrut).sum else 0) +
        c.borderBoxBlockSize
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          have hj' : j' < (layoutChildren avail true nextPos c.endMarginStrut rest).fragments.length := by
            simpa [layoutChildren, hSelfF, nextPos] using hj
          have hMem : (layoutChildren avail true nextPos c.endMarginStrut rest).fragments[j'] ∈
              (layoutChildren avail true nextPos c.endMarginStrut rest).fragments :=
            List.getElem_mem hj'
          have hBound := layoutChildren_offset_ge_bound avail rest true nextPos c.endMarginStrut
            (by intro h; cases h) hRest _ hMem
          simp only [layoutChildren, hSelfF, Bool.false_eq_true, ↓reduceIte,
            List.getElem_cons_zero, List.getElem_cons_succ]
          dsimp [cursorBound, nextPos] at hBound
          omega
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          have hij' : i' < j' := Nat.lt_of_succ_lt_succ hij
          have hj' : j' < (layoutChildren avail true nextPos c.endMarginStrut rest).fragments.length := by
            simpa [layoutChildren, hSelfF, nextPos] using hj
          have ih := layoutChildren_siblings_non_overlapping avail rest true nextPos c.endMarginStrut
            (by intro h; cases h) hRest i' j' hij' hj'
          simpa [layoutChildren, hSelfF, nextPos] using ih

theorem layoutBlock_children_eq (space : ConstraintSpace) (node : BlockContainerNode) :
    let borderBoxInline :=
      node.explicitInlineSize.getD (space.availableInlineSize - node.margin.inlineSum)
    let childAvailInline := borderBoxInline - (node.border.inlineSum + node.padding.inlineSum)
    let contentStart := node.border.blockStart + node.padding.blockStart
    let hasStartEdge := (contentStart > 0) || space.isNewBfc || node.isNewBfc
    let initResolved := hasStartEdge
    let initPos := if hasStartEdge then contentStart else 0
    let initStrut := if hasStartEdge then MarginStrut.empty else space.marginStrut
    (layoutBlock space node).fragment.children =
      (layoutChildren childAvailInline initResolved initPos initStrut node.children).fragments := by
  rfl

/-- Law 2 (`block_siblings_monotonic_non_overlapping`, `SCOPE.md` §4):
    In `BlockLayoutAlgorithm::Layout` (`block_layout_algorithm.cc`), for any
    block container laid out with non-negative margins, the placed child box
    fragments `c_0, c_1, ..., c_{n-1}` have monotonically non-decreasing
    block offsets and pairwise disjoint border-box block intervals:
    for all `i < j`, `c_i.offset.blockOffset + c_i.borderBoxSize.blockSize ≤ c_j.offset.blockOffset`. -/
theorem block_siblings_monotonic_non_overlapping
    (space : ConstraintSpace) (node : BlockContainerNode)
    (hNonNeg : AllMarginsNonNegative node)
    (i j : Nat) (hij : i < j)
    (hj : j < (layoutBlock space node).fragment.children.length) :
    let cs := (layoutBlock space node).fragment.children
    let ci := cs[i]'(Nat.lt_trans hij hj)
    let cj := cs[j]'hj
    ci.offset.blockOffset + ci.borderBoxSize.blockSize ≤ cj.offset.blockOffset := by
  let borderBoxInline :=
    node.explicitInlineSize.getD (space.availableInlineSize - node.margin.inlineSum)
  let childAvailInline := borderBoxInline - (node.border.inlineSum + node.padding.inlineSum)
  let contentStart := node.border.blockStart + node.padding.blockStart
  let hasStartEdge := (contentStart > 0) || space.isNewBfc || node.isNewBfc
  let initResolved := hasStartEdge
  let initPos := if hasStartEdge then contentStart else 0
  let initStrut := if hasStartEdge then MarginStrut.empty else space.marginStrut
  have hEq : (layoutBlock space node).fragment.children =
      (layoutChildren childAvailInline initResolved initPos initStrut node.children).fragments :=
    layoutBlock_children_eq space node
  have hInitPos : initResolved = false → initPos = 0 := by
    intro h
    dsimp [initPos, initResolved] at h ⊢
    simp [h]
  have hj' : j < (layoutChildren childAvailInline initResolved initPos initStrut node.children).fragments.length := by
    rw [← hEq]
    exact hj
  have hMain := layoutChildren_siblings_non_overlapping
    childAvailInline node.children initResolved initPos initStrut hInitPos hNonNeg i j hij hj'
  dsimp only
  simp only [hEq]
  exact hMain

/-- Lemma C: Conservation of `logicalBlockOffset + marginStrut.sum` across non-self-collapsing children. -/
theorem layoutChildren_flow_conservation
    (avail : Nat) :
    ∀ (cs : List LayoutInputNode) (pos : Nat) (strut : MarginStrut),
      (∀ c ∈ cs, c.isSelfCollapsing = false ∧ ChildMarginsNonNegative c) →
      let st := layoutChildren avail true pos strut cs
      st.bfcResolved = true ∧
      st.logicalBlockOffset + st.marginStrut.sum =
        pos + collapsedFlowBlockSizeFrom strut cs
  | [], pos, strut, _ => by
    simp [layoutChildren, collapsedFlowBlockSizeFrom]
  | c :: rest, pos, strut, hAll => by
    have hc : c.isSelfCollapsing = false := (hAll c (List.Mem.head rest)).1
    have hRest : ∀ x ∈ rest, x.isSelfCollapsing = false ∧ ChildMarginsNonNegative x :=
      fun x hx => hAll x (List.Mem.tail c hx)
    have ih := layoutChildren_flow_conservation avail rest
      ((pos + (MarginStrut.append strut c.startMarginStrut).sum) + c.borderBoxBlockSize)
      c.endMarginStrut hRest
    dsimp [layoutChildren, collapsedFlowBlockSizeFrom]
    simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ih.1, ?_⟩
    omega

/-- Law 3 (`bfc_intrinsic_block_size_conservation`, `SCOPE.md` §4):
    For a BFC-root block container with `explicitBlockSize = none` and `n`
    non-self-collapsing children with non-negative margins, the container's
    `intrinsicBlockSize` equals its block-start border+padding, plus the sum
    of all children's border-box block sizes, plus the collapsed margins before
    the first child, between each adjacent pair `(k, k+1)`, and after the last
    child, plus its block-end border+padding. -/
theorem bfc_intrinsic_block_size_conservation
    (space : ConstraintSpace) (node : BlockContainerNode)
    (hBfc : node.isNewBfc = true) (_hAuto : node.explicitBlockSize = none)
    (hNonSelf : AllChildrenNonSelfCollapsing node) :
    (layoutBlock space node).intrinsicBlockSize =
      node.border.blockStart + node.padding.blockStart +
      totalCollapsedFlowBlockSize node.children +
      node.padding.blockEnd + node.border.blockEnd := by
  let borderBoxInline :=
    node.explicitInlineSize.getD (space.availableInlineSize - node.margin.inlineSum)
  let childAvailInline := borderBoxInline - (node.border.inlineSum + node.padding.inlineSum)
  let contentStart := node.border.blockStart + node.padding.blockStart
  have hCons := layoutChildren_flow_conservation
    childAvailInline node.children contentStart MarginStrut.empty hNonSelf
  rcases hCons with ⟨hRes, hSum⟩
  dsimp only [childAvailInline, borderBoxInline, contentStart] at hRes hSum
  unfold layoutBlock totalCollapsedFlowBlockSize
  simp only [hBfc, Bool.or_true, ↓reduceIte, hRes, Bool.not_true, Bool.false_eq_true]
  omega

/-- Transcribed Blink M2 unit test vectors (`block_layout_algorithm_test.cc:568-900`). -/
def blinkM2TestVectors : List (Nat × Nat) :=
  let case3Child : LayoutInputNode :=
    .blockChild 2 {} {} { blockStart := 200 } (some 100) (some 50) false 50 true
      MarginStrut.empty MarginStrut.empty
  let case3Parent : BlockContainerNode :=
    { nodeId := 1, margin := { blockStart := 20 }, explicitInlineSize := some 100
    , isNewBfc := false, children := [case3Child] }
  let case3Space : ConstraintSpace :=
    { availableInlineSize := 800, marginStrut := { pos := 20, neg := 0 }, isNewBfc := false }
  let case3Res := layoutBlock case3Space case3Parent

  let case6Child1 : LayoutInputNode :=
    .blockChild 2 {} {} { blockStart := 10, blockEnd := 20 } (some 100) (some 30) false 30 true
      MarginStrut.empty MarginStrut.empty
  let case6Child2 : LayoutInputNode :=
    .blockChild 3 {} {} { blockStart := 40, blockEnd := 50 } (some 100) (some 60) false 60 true
      MarginStrut.empty MarginStrut.empty
  let case6Parent : BlockContainerNode :=
    { nodeId := 1, padding := { blockStart := 2 }, explicitInlineSize := some 100
    , isNewBfc := false, children := [case6Child1, case6Child2] }
  let case6Res := layoutBlock { availableInlineSize := 800, isNewBfc := false } case6Parent

  let selfCollapseRes := layoutBlock
    { availableInlineSize := 800, marginStrut := { pos := 15, neg := 0 }, isNewBfc := false }
    { nodeId := 4, explicitInlineSize := some 100, isNewBfc := false, children := [] }

  let bfcParent : BlockContainerNode :=
    { nodeId := 5
    , border := { blockStart := 3, blockEnd := 11 }
    , padding := { blockStart := 5, blockEnd := 7 }
    , isNewBfc := true
    , children := [case6Child1, case6Child2] }
  let bfcRes := layoutBlock { availableInlineSize := 800 } bfcParent

  [ (case3Res.bfcBlockOffset.getD 0, 200)
  , (case3Res.intrinsicBlockSize, 50)
  , (case6Res.intrinsicBlockSize, 142)
  , (case6Res.endMarginStrut.pos, 50)
  , (selfCollapseRes.intrinsicBlockSize, 0)
  , (selfCollapseRes.endMarginStrut.pos, 15)
  , (bfcRes.intrinsicBlockSize, 216)
  , (3 + 5 + totalCollapsedFlowBlockSize [case6Child1, case6Child2] + 7 + 11, 216)
  ]

theorem blink_m2_test_vectors_pass :
    ∀ p ∈ blinkM2TestVectors, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

end ChromiumLayout
