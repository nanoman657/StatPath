/-
  docs/chromium-layout/LayoutInline.lean

  M3 & M4 proofs of Law 4 (`line_breaker_progress_and_partition`),
  Law 5 (`line_box_height_encloses_items`), `applyBoxStateStack_eq_accumulateLineMetrics`,
  `stackLineBoxes_monotonic_non_overlapping`, and Blink M3/M4 test vectors.
-/
import LayoutTypes

namespace ChromiumLayout

/-! ## 8. M3 Proofs: Greedy Line Breaking, Termination Argument, and Law 4 -/

/-- Auxiliary partition lemma: `takeLineAux` partitions `more` into `subItems ++ rem = more`. -/
theorem takeLineAux_partition (avail : Nat) :
    ∀ (more : List InlineItem) (curWidth pendingSpace nonBreakCount : Nat),
      let res := takeLineAux avail curWidth pendingSpace nonBreakCount more
      res.1 ++ res.2.2.2 = more
  | [], _, _, _ => by
    simp [takeLineAux]
  | next :: more, curWidth, pendingSpace, nonBreakCount => by
    cases next with
    | ForcedBreak id =>
      simp [takeLineAux]
    | TextSeg id w m cb isTs =>
      cases isTs with
      | true =>
        dsimp [takeLineAux]
        split
        · have ih := takeLineAux_partition avail more curWidth (pendingSpace + w) (nonBreakCount + 1)
          simp only [List.cons_append]
          exact congrArg (List.cons _) ih
        · rfl
      | false =>
        dsimp [takeLineAux]
        split
        · have ih := takeLineAux_partition avail more (curWidth + pendingSpace + w) 0 (nonBreakCount + 1)
          simp only [List.cons_append]
          exact congrArg (List.cons _) ih
        · rfl
    | AtomicInline id sz m asc =>
      dsimp [takeLineAux]
      split
      · have ih := takeLineAux_partition avail more
          (curWidth + pendingSpace + (InlineItem.AtomicInline id sz m asc).rawInlineSize) 0 (nonBreakCount + 1)
        simp only [List.cons_append]
        exact congrArg (List.cons _) ih
      · rfl
    | OpenTag id bp s =>
      dsimp [takeLineAux]
      split
      · have ih := takeLineAux_partition avail more
          (curWidth + pendingSpace + (InlineItem.OpenTag id bp s).rawInlineSize) 0 (nonBreakCount + 1)
        simp only [List.cons_append]
        exact congrArg (List.cons _) ih
      · rfl
    | CloseTag id bp =>
      dsimp [takeLineAux]
      split
      · have ih := takeLineAux_partition avail more
          (curWidth + pendingSpace + (InlineItem.CloseTag id bp).rawInlineSize) 0 (nonBreakCount + 1)
        simp only [List.cons_append]
        exact congrArg (List.cons _) ih
      · rfl

theorem takeLine_partition (avail : Nat) (first : InlineItem) (rest : List InlineItem) :
    (takeLine avail first rest).1.items ++ (takeLine avail first rest).2 = first :: rest := by
  cases first with
  | ForcedBreak id =>
    simp [takeLine]
  | TextSeg id w m cb isTs =>
    cases isTs with
    | true =>
      dsimp [takeLine]
      exact congrArg (List.cons _) (takeLineAux_partition avail rest 0 w 1)
    | false =>
      dsimp [takeLine, InlineItem.rawInlineSize]
      exact congrArg (List.cons _) (takeLineAux_partition avail rest w 0 1)
  | AtomicInline id sz m asc =>
    dsimp [takeLine]
    exact congrArg (List.cons _)
      (takeLineAux_partition avail rest (InlineItem.AtomicInline id sz m asc).rawInlineSize 0 1)
  | OpenTag id bp s =>
    dsimp [takeLine]
    exact congrArg (List.cons _)
      (takeLineAux_partition avail rest (InlineItem.OpenTag id bp s).rawInlineSize 0 1)
  | CloseTag id bp =>
    dsimp [takeLine]
    exact congrArg (List.cons _)
      (takeLineAux_partition avail rest (InlineItem.CloseTag id bp).rawInlineSize 0 1)

/-- Auxiliary length bound: `takeLineAux` never increases the length of the remaining item list. -/
theorem takeLineAux_rem_length_le (avail : Nat)
    (more : List InlineItem) (curWidth pendingSpace nonBreakCount : Nat) :
    (takeLineAux avail curWidth pendingSpace nonBreakCount more).2.2.2.length ≤ more.length := by
  have h := congrArg List.length (takeLineAux_partition avail more curWidth pendingSpace nonBreakCount)
  simp only [List.length_append] at h
  omega

/-- Explicit termination measure decrease for `takeLine` (`ROADMAP.md` Phase 3 exit criterion):
    Every call to `takeLine avail first rest` consumes at least `first`, so the remaining list
    `(takeLine avail first rest).2` has length `≤ rest.length < (first :: rest).length`. -/
theorem takeLine_rem_length_le (avail : Nat) (first : InlineItem) (rest : List InlineItem) :
    (takeLine avail first rest).2.length ≤ rest.length := by
  cases first with
  | ForcedBreak id =>
    simp [takeLine]
  | TextSeg id w m cb isTs =>
    cases isTs with
    | true =>
      simpa [takeLine] using takeLineAux_rem_length_le avail rest 0 w 1
    | false =>
      simpa [takeLine, InlineItem.rawInlineSize] using takeLineAux_rem_length_le avail rest w 0 1
  | AtomicInline id sz m asc =>
    simpa [takeLine] using
      takeLineAux_rem_length_le avail rest (InlineItem.AtomicInline id sz m asc).rawInlineSize 0 1
  | OpenTag id bp s =>
    simpa [takeLine] using
      takeLineAux_rem_length_le avail rest (InlineItem.OpenTag id bp s).rawInlineSize 0 1
  | CloseTag id bp =>
    simpa [takeLine] using
      takeLineAux_rem_length_le avail rest (InlineItem.CloseTag id bp).rawInlineSize 0 1

theorem takeLine_termination_measure_lt (avail : Nat) (first : InlineItem) (rest : List InlineItem) :
    (takeLine avail first rest).2.length < (first :: rest).length := by
  have h := takeLine_rem_length_le avail first rest
  simp only [List.length_cons]
  omega

/-- Auxiliary width/single-item fallback invariant for `takeLineAux`. -/
theorem takeLineAux_fit (avail : Nat) :
    ∀ (more : List InlineItem) (curWidth pendingSpace nonBreakCount : Nat),
      (nonBreakCount ≤ 1 ∨ curWidth ≤ avail) →
      let res := takeLineAux avail curWidth pendingSpace nonBreakCount more
      res.2.2.1 ≤ 1 ∨ res.2.1 ≤ avail
  | [], curWidth, pendingSpace, nonBreakCount, hInv => by
    simpa [takeLineAux] using hInv
  | next :: more, curWidth, pendingSpace, nonBreakCount, hInv => by
    cases next with
    | ForcedBreak id =>
      simpa [takeLineAux] using hInv
    | TextSeg id w m cb isTs =>
      cases isTs with
      | true =>
        dsimp [takeLineAux]
        split
        · rename_i hFit
          exact takeLineAux_fit avail more curWidth (pendingSpace + w) (nonBreakCount + 1) (Or.inr hFit)
        · exact hInv
      | false =>
        dsimp [takeLineAux]
        split
        · rename_i hFit
          exact takeLineAux_fit avail more (curWidth + pendingSpace + w) 0 (nonBreakCount + 1) (Or.inr hFit)
        · exact hInv
    | AtomicInline id sz m asc =>
      dsimp [takeLineAux]
      split
      · rename_i hFit
        exact takeLineAux_fit avail more
          (curWidth + pendingSpace + (InlineItem.AtomicInline id sz m asc).rawInlineSize) 0 (nonBreakCount + 1)
          (Or.inr hFit)
      · exact hInv
    | OpenTag id bp s =>
      dsimp [takeLineAux]
      split
      · rename_i hFit
        exact takeLineAux_fit avail more
          (curWidth + pendingSpace + (InlineItem.OpenTag id bp s).rawInlineSize) 0 (nonBreakCount + 1)
          (Or.inr hFit)
      · exact hInv
    | CloseTag id bp =>
      dsimp [takeLineAux]
      split
      · rename_i hFit
        exact takeLineAux_fit avail more
          (curWidth + pendingSpace + (InlineItem.CloseTag id bp).rawInlineSize) 0 (nonBreakCount + 1)
          (Or.inr hFit)
      · exact hInv

theorem takeLine_fit (avail : Nat) (first : InlineItem) (rest : List InlineItem) :
    let line := (takeLine avail first rest).1
    line.nonBreakItemCount ≤ 1 ∨ line.inlineSize ≤ avail := by
  have hOne : (1 : Nat) ≤ 1 := Nat.le_refl 1
  cases first with
  | ForcedBreak id =>
    simp [takeLine]
  | TextSeg id w m cb isTs =>
    cases isTs with
    | true =>
      simpa [takeLine] using takeLineAux_fit avail rest 0 w 1 (Or.inl hOne)
    | false =>
      simpa [takeLine, InlineItem.rawInlineSize] using takeLineAux_fit avail rest w 0 1 (Or.inl hOne)
  | AtomicInline id sz m asc =>
    simpa [takeLine] using
      takeLineAux_fit avail rest (InlineItem.AtomicInline id sz m asc).rawInlineSize 0 1 (Or.inl hOne)
  | OpenTag id bp s =>
    simpa [takeLine] using
      takeLineAux_fit avail rest (InlineItem.OpenTag id bp s).rawInlineSize 0 1 (Or.inl hOne)
  | CloseTag id bp =>
    simpa [takeLine] using
      takeLineAux_fit avail rest (InlineItem.CloseTag id bp).rawInlineSize 0 1 (Or.inl hOne)

/-- Inductive specification of `breakLinesFuel` for any `fuel ≥ items.length`. -/
theorem breakLinesFuel_spec (avail : Nat) :
    ∀ (fuel : Nat) (items : List InlineItem),
      items.length ≤ fuel →
      (breakLinesFuel fuel avail items).length ≤ items.length ∧
      (breakLinesFuel fuel avail items).flatMap LineInfo.items = items ∧
      ∀ line ∈ breakLinesFuel fuel avail items,
        line.nonBreakItemCount ≤ 1 ∨ line.inlineSize ≤ avail
  | 0, items, hFuel => by
    cases items with
    | nil =>
      simp [breakLinesFuel]
    | cons first rest =>
      simp only [List.length_cons] at hFuel
      omega
  | fuel + 1, [], _ => by
    simp [breakLinesFuel]
  | fuel + 1, first :: rest, hFuel => by
    have hRemLe : (takeLine avail first rest).2.length ≤ rest.length :=
      takeLine_rem_length_le avail first rest
    have hRemFuel : (takeLine avail first rest).2.length ≤ fuel := by
      simp only [List.length_cons] at hFuel
      omega
    have ih := breakLinesFuel_spec avail fuel (takeLine avail first rest).2 hRemFuel
    rcases ih with ⟨ihLen, ihPart, ihFit⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp [breakLinesFuel]
      omega
    · dsimp [breakLinesFuel]
      simp only [List.flatMap_cons, ihPart]
      exact takeLine_partition avail first rest
    · intro line hMem
      dsimp [breakLinesFuel] at hMem
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · exact takeLine_fit avail first rest
      · exact ihFit line hTail

/-- Law 4 (`line_breaker_progress_and_partition`, `SCOPE.md` §4):
    For any non-empty input `items : List InlineItem` and `availableInlineSize : Nat`:
    1. **Progress & termination**: `breakLines` consumes at least one item per line,
       terminates in at most `items.length` lines (`(breakLines avail items).length ≤ items.length`).
    2. **Order-preserving partition**: `(breakLines avail items).flatMap LineInfo.items = items`.
    3. **Non-overflow (or single-item fallback)**: every produced line satisfies
       `line.nonBreakItemCount ≤ 1 ∨ line.inlineSize ≤ avail`. -/
theorem line_breaker_progress_and_partition (avail : Nat) (items : List InlineItem) :
    (breakLines avail items).length ≤ items.length ∧
    (breakLines avail items).flatMap LineInfo.items = items ∧
    ∀ line ∈ breakLines avail items,
      line.nonBreakItemCount ≤ 1 ∨ line.inlineSize ≤ avail :=
  breakLinesFuel_spec avail items.length items (Nat.le_refl items.length)

/-- Transcribed Blink M3 line-breaking unit test vectors (`inline/line_breaker_test.cc`,
    `inline/inline_layout_algorithm_test.cc`). -/
def blinkM3TestVectors : List (Nat × Nat) :=
  let fh : FontHeight := { ascent := 10, descent := 4 }
  let w1 : InlineItem := .TextSeg 1 40 fh true false
  let sp : InlineItem := .TextSeg 2 10 fh true true
  let w2 : InlineItem := .TextSeg 3 40 fh true false
  let w3 : InlineItem := .TextSeg 4 40 fh true false
  let lines1 := breakLines 100 [w1, sp, w2, w3]

  let w95 : InlineItem := .TextSeg 5 95 fh true false
  let sp20 : InlineItem := .TextSeg 6 20 fh true true
  let lines2 := breakLines 100 [w95, sp20]

  let br : InlineItem := .ForcedBreak 7
  let lines3 := breakLines 100 [w1, br, w2]

  let w150 : InlineItem := .TextSeg 8 150 fh true false
  let lines4 := breakLines 100 [w150, w1]

  [ (lines1.length, 2)
  , ((lines1.headD {}).inlineSize, 90)
  , (lines2.length, 1)
  , ((lines2.headD {}).inlineSize, 95)
  , (lines3.length, 2)
  , (lines4.length, 2)
  , ((lines4.headD {}).nonBreakItemCount, 1)
  , ((lines4.headD {}).inlineSize, 150)
  ]

theorem blink_m3_test_vectors_pass :
    ∀ p ∈ blinkM3TestVectors, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

/-! ## 9. M4 Proofs: Inline Box State, Line Boxes, Law 5, and Blink Test Vectors -/

/-- Explicit `Nat.max` order lemmas required by the Phase 4 exit criterion (`ROADMAP.md` Phase 4). -/
theorem nat_le_max_left (a b : Nat) : a ≤ Nat.max a b :=
  Nat.le_max_left a b

theorem nat_le_max_right (a b : Nat) : b ≤ Nat.max a b :=
  Nat.le_max_right a b

theorem FontHeight.merge_assoc (a b c : FontHeight) :
    FontHeight.merge (FontHeight.merge a b) c =
      FontHeight.merge a (FontHeight.merge b c) := by
  cases a
  cases b
  cases c
  simp [FontHeight.merge, Nat.max_assoc]

theorem FontHeight.merge_comm (a b : FontHeight) :
    FontHeight.merge a b = FontHeight.merge b a := by
  cases a
  cases b
  simp [FontHeight.merge, Nat.max_comm]

theorem FontHeight.merge_idem (a : FontHeight) :
    FontHeight.merge a a = a := by
  cases a
  simp [FontHeight.merge]

theorem FontHeight.merge_zero_left (a : FontHeight) :
    FontHeight.merge { ascent := 0, descent := 0 } a = a := by
  cases a
  simp [FontHeight.merge]

theorem FontHeight.merge_zero_right (a : FontHeight) :
    FontHeight.merge a { ascent := 0, descent := 0 } = a := by
  cases a
  simp [FontHeight.merge]

theorem flushBoxStateStack_merge (active extra : FontHeight) :
    ∀ (stack : List FontHeight),
      flushBoxStateStack (FontHeight.merge active extra) stack =
        FontHeight.merge (flushBoxStateStack active stack) extra
  | [] => rfl
  | parent :: rest => by
    dsimp [flushBoxStateStack]
    rw [← FontHeight.merge_assoc parent active extra]
    exact flushBoxStateStack_merge (FontHeight.merge parent active) extra rest

theorem stepBoxStateStack_flush (active : FontHeight) (stack : List FontHeight) (it : InlineItem) :
    let (nextActive, nextStack) := stepBoxStateStack active stack it
    flushBoxStateStack nextActive nextStack =
      FontHeight.merge it.fontHeight (flushBoxStateStack active stack) := by
  cases it with
  | OpenTag id bp s =>
    dsimp [stepBoxStateStack, flushBoxStateStack, InlineItem.fontHeight]
    rw [flushBoxStateStack_merge active s stack, FontHeight.merge_comm]
  | CloseTag id bp =>
    cases stack with
    | nil =>
      dsimp [stepBoxStateStack, flushBoxStateStack, InlineItem.fontHeight]
      rw [FontHeight.merge_zero_left]
    | cons parent rest =>
      dsimp [stepBoxStateStack, flushBoxStateStack, InlineItem.fontHeight]
      rw [FontHeight.merge_zero_left]
  | TextSeg id w m cb isTs =>
    dsimp [stepBoxStateStack, InlineItem.fontHeight]
    rw [flushBoxStateStack_merge active m stack, FontHeight.merge_comm]
  | AtomicInline id sz m asc =>
    dsimp [stepBoxStateStack, InlineItem.fontHeight]
    rw [flushBoxStateStack_merge active _ stack, FontHeight.merge_comm]
  | ForcedBreak id =>
    dsimp [stepBoxStateStack, InlineItem.fontHeight]
    rw [flushBoxStateStack_merge active _ stack, FontHeight.merge_comm]

theorem runBoxStateStack_flush :
    ∀ (items : List InlineItem) (active : FontHeight) (stack : List FontHeight),
      let (finalActive, finalStack) := runBoxStateStack active stack items
      flushBoxStateStack finalActive finalStack =
        accumulateLineMetrics (flushBoxStateStack active stack) items
  | [], active, stack => rfl
  | it :: rest, active, stack => by
    dsimp [runBoxStateStack, accumulateLineMetrics]
    have ih := runBoxStateStack_flush rest (stepBoxStateStack active stack it).1 (stepBoxStateStack active stack it).2
    have hStep := stepBoxStateStack_flush active stack it
    dsimp at ih hStep
    rw [ih, hStep]
    clear ih hStep
    induction rest with
    | nil =>
      dsimp [accumulateLineMetrics]
    | cons r rs ihRest =>
      dsimp [accumulateLineMetrics]
      rw [ihRest, ← FontHeight.merge_assoc, FontHeight.merge_comm r.fontHeight it.fontHeight, FontHeight.merge_assoc]

/-- Equivalence of `InlineLayoutStateStack` push/pop accumulation (`applyBoxStateStack`)
    and `accumulateLineMetrics` for arbitrary inline box nesting depth (`ROADMAP.md` P0.1 Q3 & Phase 4). -/
theorem applyBoxStateStack_eq_accumulateLineMetrics (strut : FontHeight) (items : List InlineItem) :
    applyBoxStateStack strut items = accumulateLineMetrics strut items :=
  runBoxStateStack_flush items strut []

/-- Every item on a line has its `ascent` and `descent` bounded by `accumulateLineMetrics`. -/
theorem accumulateLineMetrics_encloses (strut : FontHeight) :
    ∀ (items : List InlineItem) (it : InlineItem),
      it ∈ items →
      it.fontHeight.ascent ≤ (accumulateLineMetrics strut items).ascent ∧
      it.fontHeight.descent ≤ (accumulateLineMetrics strut items).descent
  | [], _, hMem => by
    cases hMem
  | head :: tail, it, hMem => by
    simp only [List.mem_cons] at hMem
    dsimp [accumulateLineMetrics, FontHeight.merge]
    rcases hMem with rfl | hTail
    · exact ⟨nat_le_max_left _ _, nat_le_max_left _ _⟩
    · rcases accumulateLineMetrics_encloses strut tail it hTail with ⟨hAsc, hDesc⟩
      exact ⟨Nat.le_trans hAsc (nat_le_max_right _ _), Nat.le_trans hDesc (nat_le_max_right _ _)⟩

/-- Every `PlacedInlineItem` emitted by `placeLineItems` fits vertically within `lineMetrics`. -/
theorem placeLineItems_encloses (lineMetrics : FontHeight) :
    ∀ (items : List InlineItem) (inlineOff : Nat),
      (∀ it ∈ items,
        it.fontHeight.ascent ≤ lineMetrics.ascent ∧
        it.fontHeight.descent ≤ lineMetrics.descent) →
      ∀ placed ∈ placeLineItems lineMetrics inlineOff items,
        placed.blockOffset + placed.blockSize ≤ lineMetrics.ascent + lineMetrics.descent
  | [], _, _, placed, hMem => by
    cases hMem
  | it :: rest, inlineOff, hBounds, placed, hMem => by
    dsimp [placeLineItems] at hMem
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hTail
    · rcases hBounds it (List.Mem.head rest) with ⟨hAsc, hDesc⟩
      dsimp
      omega
    · exact placeLineItems_encloses lineMetrics rest (inlineOff + it.rawInlineSize)
        (fun x hx => hBounds x (List.Mem.tail it hx)) placed hTail

/-- Law 5 (`line_box_height_encloses_items`, `SCOPE.md` §4):
    In `InlineLayoutAlgorithm::CreateLine` (`inline/inline_layout_algorithm.cc:378-430`)
    and `InlineLayoutStateStack::OnEndPlaceItems` (`inline/inline_box_state.cc:426-445`),
    for any line box constructed from baseline-aligned inline items with per-item
    `FontHeight(ascent_i, descent_i)` and initial line strut `strut`, the line box's
    computed `FontHeight(ascent, descent)` satisfies `ascent ≥ ascent_i` and
    `descent ≥ descent_i` for every item on the line, so every item's vertical extent
    `[ascent - ascent_i, (ascent - ascent_i) + (ascent_i + descent_i)]` lies within
    `[0, ascent + descent]`. -/
theorem line_box_height_encloses_items
    (strut : FontHeight) (lineInfo : LineInfo)
    (item : PlacedInlineItem)
    (hMem : item ∈ (createLineBox strut lineInfo).items) :
    let line := createLineBox strut lineInfo
    item.blockOffset + item.blockSize ≤ line.metrics.ascent + line.metrics.descent := by
  dsimp [createLineBox] at hMem ⊢
  exact placeLineItems_encloses
    (accumulateLineMetrics strut lineInfo.items)
    lineInfo.items 0
    (fun it hit => accumulateLineMetrics_encloses strut lineInfo.items it hit)
    item hMem

/-- Every line box emitted by `stackLineBoxes` has `bfcOffset.blockOffset ≥ blockOff`. -/
theorem stackLineBoxes_offset_ge (strut : FontHeight) :
    ∀ (lines : List LineInfo) (blockOff : Nat) (lf : LineBoxFragment),
      lf ∈ (stackLineBoxes strut blockOff lines).1 →
      blockOff ≤ lf.bfcOffset.blockOffset
  | [], _, _, hMem => by
    simp [stackLineBoxes] at hMem
  | li :: rest, blockOff, lf, hMem => by
    dsimp [stackLineBoxes] at hMem
    simp only [List.mem_cons] at hMem
    rcases hMem with rfl | hTail
    · exact Nat.le_refl blockOff
    · have ih := stackLineBoxes_offset_ge strut rest
        (blockOff + (createLineBox strut li).metrics.lineHeight) lf hTail
      omega

/-- Vertical non-overlapping stacking of line boxes inside an enclosing block (`ROADMAP.md` Phase 4). -/
theorem stackLineBoxes_monotonic_non_overlapping (strut : FontHeight) :
    ∀ (lines : List LineInfo) (blockOff : Nat)
      (i j : Nat) (hij : i < j)
      (hj : j < (stackLineBoxes strut blockOff lines).1.length),
      let lfs := (stackLineBoxes strut blockOff lines).1
      let li := lfs[i]'(Nat.lt_trans hij hj)
      let lj := lfs[j]'hj
      li.bfcOffset.blockOffset + li.metrics.lineHeight ≤ lj.bfcOffset.blockOffset
  | [], _, _, _, _, hj => by
    simp [stackLineBoxes] at hj
  | l :: rest, blockOff, i, j, hij, hj => by
    let lh := (createLineBox strut l).metrics.lineHeight
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : j' < (stackLineBoxes strut (blockOff + lh) rest).1.length := by
          simpa [stackLineBoxes, lh] using hj
        have hMem : (stackLineBoxes strut (blockOff + lh) rest).1[j'] ∈
            (stackLineBoxes strut (blockOff + lh) rest).1 :=
          List.getElem_mem hj'
        have hGe := stackLineBoxes_offset_ge strut rest (blockOff + lh) _ hMem
        simpa [stackLineBoxes, lh] using hGe
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hij' : i' < j' := Nat.lt_of_succ_lt_succ hij
        have hj' : j' < (stackLineBoxes strut (blockOff + lh) rest).1.length := by
          simpa [stackLineBoxes, lh] using hj
        have ih := stackLineBoxes_monotonic_non_overlapping strut rest (blockOff + lh) i' j' hij' hj'
        simpa [stackLineBoxes, lh] using ih

/-- Transcribed Blink M4 inline box state and line box unit test vectors
    (`inline/inline_layout_algorithm_test.cc`, `inline/inline_box_state.cc:277-445`). -/
def blinkM4TestVectors : List (Nat × Nat) :=
  let strut : FontHeight := { ascent := 10, descent := 4 }
  let t1 : InlineItem := .TextSeg 1 30 { ascent := 12, descent := 3 } true false
  let openSpan : InlineItem := .OpenTag 2 2 { ascent := 16, descent := 6 }
  let t2 : InlineItem := .TextSeg 3 40 { ascent := 14, descent := 5 } true false
  let closeSpan : InlineItem := .CloseTag 4 2
  let li1 : LineInfo := { items := [t1, openSpan, t2, closeSpan], inlineSize := 74, nonBreakItemCount := 4 }
  let lb1 := createLineBox strut li1
  let stackMetrics := applyBoxStateStack strut li1.items
  let firstPlaced := lb1.items.headD {}

  let li0 : LineInfo := { items := [t1], inlineSize := 30, nonBreakItemCount := 1 }
  let (stacked, totalBs) := stackLineBoxes strut 5 [li0, li1]

  [ (lb1.metrics.ascent, 16)
  , (lb1.metrics.descent, 6)
  , (stackMetrics.ascent, 16)
  , (stackMetrics.descent, 6)
  , (firstPlaced.blockOffset, 4)
  , (firstPlaced.blockSize, 15)
  , (stacked.length, 2)
  , ((stacked.headD {}).bfcOffset.blockOffset, 5)
  , ((stacked.getD 1 {}).bfcOffset.blockOffset, 21)
  , (totalBs, 43)
  ]

theorem blink_m4_test_vectors_pass :
    ∀ p ∈ blinkM4TestVectors, p.1 = p.2 :=
  pairs_eq_of_all_beq rfl

end ChromiumLayout
