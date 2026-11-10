/-
  BlockFloat.lean: general CSS 2.1 §9.5 float placement, clearance, and BFC float avoidance,
  written from block_layout_algorithm_test.cc (`NewFcAvoidsFloats`, `PositionFragmentsWithClear`,
  `NewFcBlockWithAdjoiningFloatCollapsesMargins`, `PositionFloatFragments`, `CollapsingMarginsCase1WithFloats`).
  Owned by the block lane (Block*).
-/
namespace ChromiumLayout
namespace BlockFloat

/-- Float type: none, float left, or float right (CSS 2.1 §9.5.1). -/
inductive FloatType where
  | none
  | left
  | right
  deriving DecidableEq, Repr

/-- Clearance type: none, clear left, clear right, or clear both (CSS 2.1 §9.5.2). -/
inductive ClearType where
  | none
  | left
  | right
  | both
  deriving DecidableEq, Repr

/-- A box participating in block layout with floats. -/
structure FloatItem where
  id : Nat := 0
  w : Nat := 0
  h : Nat := 0
  marginTop : Int := 0
  marginRight : Int := 0
  marginBottom : Int := 0
  marginLeft : Int := 0
  float : FloatType := .none
  clear : ClearType := .none
  isNewFc : Bool := false
  autoMarginLeft : Bool := false
  autoMarginRight : Bool := false
  isRtl : Bool := false
  deriving DecidableEq, Repr

/-- Placed layout output fragment. -/
structure PlacedBox where
  id : Nat := 0
  x : Int := 0
  y : Int := 0
  w : Nat := 0
  h : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Outer bottom of a float box (y + h + marginBottom). -/
def floatBottom (f : Int × Int × Nat × Nat) : Int :=
  f.2.1 + (f.2.2.2 : Int)

/-- Maximum bottom edge of a list of placed floats. -/
def maxBottom (floats : List (Int × Int × Nat × Nat)) : Int :=
  floats.foldl (fun m f => max m (floatBottom f)) 0

/-- Clearance offset: pushes y to clear preceding left and/or right floats. -/
def applyClearance (c : ClearType) (lefts rights : List (Int × Int × Nat × Nat)) (y : Int) : Int :=
  match c with
  | .none => y
  | .left => max y (maxBottom lefts)
  | .right => max y (maxBottom rights)
  | .both => max y (max (maxBottom lefts) (maxBottom rights))

/-- Active left float width at a given vertical position y. -/
def leftFloatWidthAt (lefts : List (Int × Int × Nat × Nat)) (y : Int) : Int :=
  lefts.foldl (fun w f => if f.2.1 ≤ y && y < floatBottom f then max w (f.1 + (f.2.2.1 : Int)) else w) 0

/-- Active right float width at a given vertical position y. -/
def rightFloatWidthAt (containerW : Nat) (rights : List (Int × Int × Nat × Nat)) (y : Int) : Int :=
  rights.foldl (fun w f => if f.2.1 ≤ y && y < floatBottom f then max w ((containerW : Int) - f.1) else w) 0

/-- Filter and translate ancestor floats that intrude into a descendant block container box.
    CSS 2.1 §9.5. -/
def intrudeFloats (blockY : Int) (floats : List (Int × Int × Nat × Nat)) : List (Int × Int × Nat × Nat) :=
  floats.filterMap (fun (x, y, w, h) =>
    if y + (h : Int) > blockY then some (x, y - blockY, w, h) else none)

/-- General CSS 2.1 block layout with floats, clearance, and BFC avoidance.
    CSS 2.1 §9.5 (floats and intruding floats), §9.5.2 (clearance). -/
def layoutBlockWithFloats (containerW : Nat) (items : List FloatItem)
    (initLefts initRights : List (Int × Int × Nat × Nat) := []) : List PlacedBox :=
  let rec loop (items : List FloatItem) (lefts rights : List (Int × Int × Nat × Nat))
               (flowY : Int) (prevMarginBottom : Int) (isFirstInFlow : Bool)
               (acc : List PlacedBox) : List PlacedBox :=
    match items with
    | [] => acc.reverse
    | item :: rest =>
        let cW : Int := containerW
        let outerW : Int := (item.w : Int) + item.marginLeft + item.marginRight
        let outerH : Int := (item.h : Int) + item.marginTop + item.marginBottom
        match item.float with
        | .left =>
            let startY := if isFirstInFlow then flowY else flowY + prevMarginBottom
            let curLeft := leftFloatWidthAt lefts startY
            let (placeX, placeY) :=
              if curLeft + outerW ≤ cW - rightFloatWidthAt containerW rights startY then
                (curLeft + item.marginLeft, startY + item.marginTop)
              else
                let dropY := maxBottom lefts
                (leftFloatWidthAt lefts dropY + item.marginLeft, dropY + item.marginTop)
            let newFloat := (placeX - item.marginLeft, placeY - item.marginTop, outerW.toNat, outerH.toNat)
            let box : PlacedBox := ⟨item.id, placeX, placeY, item.w, item.h⟩
            loop rest (newFloat :: lefts) rights flowY prevMarginBottom isFirstInFlow (box :: acc)
        | .right =>
            let startY := if isFirstInFlow then flowY else flowY + prevMarginBottom
            let curRight := rightFloatWidthAt containerW rights startY
            let (placeX, placeY) :=
              if leftFloatWidthAt lefts startY + outerW ≤ cW - curRight then
                (cW - curRight - outerW + item.marginLeft, startY + item.marginTop)
              else
                let dropY := maxBottom rights
                (cW - outerW + item.marginLeft, dropY + item.marginTop)
            let newFloat := (placeX - item.marginLeft, placeY - item.marginTop, outerW.toNat, outerH.toNat)
            let box : PlacedBox := ⟨item.id, placeX, placeY, item.w, item.h⟩
            loop rest lefts (newFloat :: rights) flowY prevMarginBottom isFirstInFlow (box :: acc)
        | .none =>
            if item.isNewFc then
              -- New Formatting Context (e.g. display: flow-root): avoids floats (CSS 2.1 §9.5, §10.3.3)
              let curLeft := leftFloatWidthAt lefts flowY
              let curRight := rightFloatWidthAt containerW rights flowY
              let (placeX, placeY) :=
                if curLeft + (item.w : Int) ≤ cW - curRight then
                  let avail := cW - curRight - curLeft
                  let x :=
                    if item.autoMarginLeft && item.autoMarginRight then
                      curLeft + (avail - (item.w : Int)) / 2
                    else if item.autoMarginRight then
                      curLeft + item.marginLeft
                    else if item.autoMarginLeft then
                      cW - curRight - (item.w : Int) - item.marginRight
                    else if item.isRtl then
                      cW - curRight - (item.w : Int) - item.marginRight
                    else
                      curLeft + item.marginLeft
                  (x, flowY)
                else
                  let dropY := max (maxBottom lefts) (maxBottom rights)
                  let x := if item.isRtl then cW - (item.w : Int) - item.marginRight else item.marginLeft
                  (x, dropY)
              let box : PlacedBox := ⟨item.id, placeX, placeY, item.w, item.h⟩
              let nextY := placeY + (item.h : Int) + item.marginBottom
              loop rest lefts rights nextY item.marginBottom false (box :: acc)
            else
              -- Normal in-flow box with margin collapsing and clearance (CSS 2.1 §9.5.2)
              let normalMargin := if isFirstInFlow then 0 else max prevMarginBottom item.marginTop
              let normalY := flowY + normalMargin
              let placeY := applyClearance item.clear lefts rights normalY
              let placeX := item.marginLeft
              let box : PlacedBox := ⟨item.id, placeX, placeY, item.w, item.h⟩
              let nextY := placeY + (item.h : Int)
              loop rest lefts rights nextY item.marginBottom false (box :: acc)
  loop items initLefts initRights 0 0 true []

/-- Law: Intruding float clearance inside a block is at least the float's intrusion extent.
    CSS 2.1 §9.5, §9.5.2. -/
theorem clear_intrude_pos (blockY : Int) (f : Int × Int × Nat × Nat) (hf : floatBottom f > blockY) :
    maxBottom (intrudeFloats blockY [f]) = floatBottom f - blockY := by
  dsimp [intrudeFloats, List.filterMap]
  have hcond : f.2.1 + (f.2.2.2 : Int) > blockY := hf
  rw [if_pos hcond]
  dsimp [maxBottom, List.foldl]
  have hfb : floatBottom (f.1, f.2.1 - blockY, f.2.2.1, f.2.2.2) = floatBottom f - blockY := by
    dsimp [floatBottom]; omega
  rw [hfb]
  dsimp [max]
  split <;> omega

/-- Law: Clearance ensures the placed box's top edge is never above the cleared float's bottom. -/
theorem clearance_respects_left_floats (lefts rights : List (Int × Int × Nat × Nat)) (y : Int) :
    applyClearance .left lefts rights y ≥ maxBottom lefts := by
  dsimp [applyClearance]
  change (if y ≤ maxBottom lefts then maxBottom lefts else y) ≥ maxBottom lefts
  split <;> omega

/-- Law: Clearance for right floats ensures top edge is never above right floats bottom. -/
theorem clearance_respects_right_floats (lefts rights : List (Int × Int × Nat × Nat)) (y : Int) :
    applyClearance .right lefts rights y ≥ maxBottom rights := by
  dsimp [applyClearance]
  change (if y ≤ maxBottom rights then maxBottom rights else y) ≥ maxBottom rights
  split <;> omega

/-- Law: Clearance for both floats ensures top edge is at or below both left and right float bottoms. -/
theorem clearance_respects_both_floats (lefts rights : List (Int × Int × Nat × Nat)) (y : Int) :
    applyClearance .both lefts rights y ≥ maxBottom lefts ∧
    applyClearance .both lefts rights y ≥ maxBottom rights := by
  dsimp [applyClearance]
  let a := maxBottom lefts
  let b := maxBottom rights
  change (if y ≤ (if a ≤ b then b else a) then (if a ≤ b then b else a) else y) ≥ a ∧
         (if y ≤ (if a ≤ b then b else a) then (if a ≤ b then b else a) else y) ≥ b
  split <;> split <;> omega

/-- Whether a clear value clears the left floats. -/
def clearsLeft : ClearType → Bool
  | .left => true
  | .both => true
  | _ => false

/-- Whether a clear value clears the right floats. -/
def clearsRight : ClearType → Bool
  | .right => true
  | .both => true
  | _ => false

/-- Min-content and max-content inline sizes of a block whose in-flow children are floats only
    (`ComputeMinMaxContentFloats`, `ComputeMinMaxContentFloatsClearance`). Min-content is the widest
    float's outer width. Max-content is the widest run of floats that share a line: left and right
    floats accumulate, and a float that clears a side starts a new run, so the floats before it are
    closed off. This run rule is the model's own; the two tests are its only checks. -/
def minMaxFloats (items : List FloatItem) : Int × Int :=
  let step : Int × Int × Int × Int → FloatItem → Int × Int × Int × Int :=
    fun (st : Int × Int × Int × Int) (it : FloatItem) =>
      let mn := st.1
      let mx := st.2.1
      let l := st.2.2.1
      let r := st.2.2.2
      let outer : Int := (it.w : Int) + it.marginLeft + it.marginRight
      let cL := clearsLeft it.clear
      let cR := clearsRight it.clear
      let mx' := if cL || cR then max mx (l + r) else mx
      let l' := if cL then 0 else l
      let r' := if cR then 0 else r
      let mn' := max mn outer
      match it.float with
      | .left => (mn', mx', l' + outer, r')
      | .right => (mn', mx', l', r' + outer)
      | .none => (mn', mx', l', r')
  let fin := items.foldl step (0, 0, 0, 0)
  (fin.1, max fin.2.1 (fin.2.2.1 + fin.2.2.2))
/-- Law: An element with auto margins centered between left and right floats starts at least at the left float edge.
    CSS 2.1 §9.5, §10.3.3. -/
theorem new_fc_auto_margin (cW curLeft curRight w : Int) (hw : w ≤ cW - curRight - curLeft) :
    let avail := cW - curRight - curLeft
    curLeft ≤ curLeft + (avail - w) / 2 := by
  dsimp
  omega

/-- Result of min/max content inline sizing (CSS Intrinsic Sizing Level 3 §4,
    CSS 2.1 §10.3.5). -/
structure MinMaxSizes where
  minSize : Nat := 0
  maxSize : Nat := 0
  deriving DecidableEq, Repr

/-- Helper loop for min/max content inline sizing across floats and clearance.
    CSS Intrinsic Sizing Level 3 §4.1; CSS 2.1 §9.5, §9.5.1, §9.5.2, §10.3.5. -/
def minMaxLoop (rest : List FloatItem) (fl : Int) (fr : Int) (minS maxS : Int) : Int × Int :=
  match rest with
  | [] => (minS, maxS)
  | item :: xs =>
    let (flClear, frClear, curMax) :=
      if item.float != .none || item.isNewFc then
        let lineF := fl + fr
        let m := if item.clear != .none then max maxS lineF else maxS
        let fl1 := if item.clear == .both || item.clear == .left then 0 else fl
        let fr1 := if item.clear == .both || item.clear == .right then 0 else fr
        (fl1, fr1, m)
      else
        (fl, fr, maxS)

    let itemMargin := item.marginLeft + item.marginRight
    let itemW : Int := item.w

    let (nextFl, nextFr, maxContrib) :=
      match item.float with
      | .left =>
        let fsize := itemW + itemMargin
        let newFl := if fsize > 0 then flClear + fsize else flClear
        (newFl, frClear, newFl + frClear)
      | .right =>
        let fsize := itemW + itemMargin
        let newFr := if fsize > 0 then frClear + fsize else frClear
        (flClear, newFr, flClear + newFr)
      | .none =>
        if item.isNewFc then
          let lineLeftInset :=
            if item.marginLeft > 0 then max flClear item.marginLeft
            else flClear + item.marginLeft
          let lineRightInset :=
            if item.marginRight > 0 then max frClear item.marginRight
            else frClear + item.marginRight
          (0, 0, itemW + lineLeftInset + lineRightInset)
        else
          (0, 0, itemW + itemMargin)

    let newMaxS := max curMax maxContrib
    let minContrib := itemW + itemMargin
    let newMinS := max minS minContrib
    minMaxLoop xs nextFl nextFr newMinS newMaxS

/-- Compute intrinsic min-content and max-content inline sizes for a list of items
    with floats, clearance, and new-FC elements.
    CSS Intrinsic & Retargeted Sizing Module Level 3 §4.1;
    CSS 2.1 §9.5, §9.5.1 (floats), §9.5.2 (clearance), §10.3.5 (shrink-to-fit). -/
def computeMinMaxSizes (items : List FloatItem) (hpad : Nat := 0) : MinMaxSizes :=
  let (rawMin, rawMax) := minMaxLoop items 0 0 0 0
  let finalMin := (max 0 rawMin).toNat + hpad
  let finalMax := (max 0 rawMax).toNat + hpad
  ⟨finalMin, finalMax⟩

/-- Law: A single float with zero margins has equal min-content and max-content
    inline size equal to its specified width plus horizontal padding.
    CSS Intrinsic & Retargeted Sizing Module Level 3 §4.1; CSS 2.1 §10.3.5. -/
theorem single_float_min_max (w hpad : Nat) :
    computeMinMaxSizes [{ w := w, float := .left }] hpad = ⟨w + hpad, w + hpad⟩ := by
  dsimp [computeMinMaxSizes, minMaxLoop]
  congr 1 <;> (try split) <;> omega

/-- Law: Two consecutive left floats without clearance sit side by side in max-content sizing,
    yielding a max-content size equal to the sum of their widths plus padding.
    CSS Intrinsic & Retargeted Sizing Module Level 3 §4.1; CSS 2.1 §9.5.1, §10.3.5. -/
theorem floats_max_content (w1 w2 hpad : Nat) :
    (computeMinMaxSizes [{ w := w1, float := .left }, { w := w2, float := .left }] hpad).maxSize =
    w1 + w2 + hpad := by
  dsimp [computeMinMaxSizes, minMaxLoop]
  split <;> split <;> omega

/-- Law: Clearance between left floats breaks the accumulation line: with clearance,
    the max-content size is max(w1, w2) + hpad instead of w1 + w2 + hpad.
    CSS Intrinsic Sizing Level 3 §4.1; CSS 2.1 §9.5.2 clearance. -/
theorem clear_breaks_line (w1 w2 hpad : Nat) :
    (computeMinMaxSizes [{ w := w1, float := .left }, { w := w2, float := .left, clear := .left }] hpad).maxSize =
    max w1 w2 + hpad := by
  dsimp [computeMinMaxSizes, minMaxLoop]
  split <;> split <;> omega

/-- Law: Clearance for `clear: left` is zero when there are no left floats.
    CSS 2.1 §9.5.2 Clearance. -/
theorem clear_left_no_left (rights : List (Int × Int × Nat × Nat)) (y : Int) (hy : 0 ≤ y) :
    applyClearance .left [] rights y = y := by
  dsimp [applyClearance, maxBottom]
  omega

/-- Law: Clearance for `clear: right` is zero when there are no right floats.
    CSS 2.1 §9.5.2 Clearance. -/
theorem clear_right_no_right (lefts : List (Int × Int × Nat × Nat)) (y : Int) (hy : 0 ≤ y) :
    applyClearance .right lefts [] y = y := by
  dsimp [applyClearance, maxBottom]
  omega

/-- Law: When the sum of outer widths of a left float and a right float does not exceed
    the containing block width, their placed positions do not overlap horizontally.
    CSS 2.1 §9.5.1 Rule 7 (non-overlapping floating boxes). -/
theorem float_no_overlap (cW : Nat) (wL wR : Nat) (mlL mrL mlR mrR : Int)
    (h_fit : (wL : Int) + mlL + mrL + (wR : Int) + mlR + mrR ≤ cW)
    (h_mrL : 0 ≤ mrL) (h_mlR : 0 ≤ mlR) :
    mlL + (wL : Int) ≤ (cW : Int) - ((wR : Int) + mlR + mrR) + mlR := by
  omega

/-- Display category for descendant boxes in paint order propagation.
    CSS 2.1 §9.5, §9.7, Appendix E.2. -/
inductive BoxDisplay where
  | block
  | inlineBlock
  | flowRoot
  deriving DecidableEq, Repr

/-- A box descendant tree representation for floating descendant propagation.
    CSS 2.1 §9.5 (floats), Appendix E.2 (paint order step 5: floats). -/
inductive BoxDescendant where
  | mk (id : Nat) (display : BoxDisplay) (isFloat : Bool) (children : List BoxDescendant)
  deriving Repr

instance : Inhabited BoxDescendant := ⟨.mk 0 .block false []⟩

/-- Leaf box constructor. -/
def BoxDescendant.leaf (id : Nat) (disp : BoxDisplay := .block) (isFloat : Bool := false) : BoxDescendant :=
  .mk id disp isFloat []

/-- Container box constructor. -/
def BoxDescendant.node (id : Nat) (disp : BoxDisplay) (kids : List BoxDescendant) : BoxDescendant :=
  .mk id disp false kids

/-- Whether a box fragment has floating descendants for paint.
    CSS 2.1 §9.5 (floats), Appendix E.2 (paint order step 5: floats).
    Floating descendants propagate across block boundaries (including new BFCs and abspos),
    but do NOT cross inline-block boundaries (which establish independent atomic formatting contexts). -/
def hasFloatingDescendants : Nat → BoxDescendant → Bool
  | 0, _ => false
  | _, .mk _ _ true _ => true
  | _, .mk _ .inlineBlock false _ => false
  | fuel + 1, .mk _ _ false kids => kids.any (hasFloatingDescendants fuel)

/-- Whether a list of child boxes contains or propagates floating descendants for paint.
    CSS 2.1 §9.5, Appendix E.2. -/
def listHasFloats (fuel : Nat) (kids : List BoxDescendant) : Bool :=
  kids.any (hasFloatingDescendants fuel)

/-- Law: An inline-block descendant never propagates floating descendants to its parent.
    CSS 2.1 §9.5, Appendix E.2. -/
theorem ib_no_float_prop (fuel id : Nat) (kids : List BoxDescendant) :
    hasFloatingDescendants (fuel + 1) (.mk id .inlineBlock false kids) = false := by
  rfl

/-- Law: A box marked as a float always has floating descendants true.
    CSS 2.1 §9.5. -/
theorem direct_float_has (fuel id : Nat) (disp : BoxDisplay) (kids : List BoxDescendant) :
    hasFloatingDescendants (fuel + 1) (.mk id disp true kids) = true := by
  rfl

/-- Law: A new block formatting context propagates floating descendants if its children have floats.
    CSS 2.1 §9.5. -/
theorem flow_root_propagates (fuel id : Nat) (c : BoxDescendant) (rest : List BoxDescendant)
    (h : hasFloatingDescendants fuel c = true) :
    hasFloatingDescendants (fuel + 1) (.mk id .flowRoot false (c :: rest)) = true := by
  dsimp [hasFloatingDescendants, List.any]
  rw [h]
  rfl

end BlockFloat
end ChromiumLayout
