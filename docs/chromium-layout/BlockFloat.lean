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

/-- General CSS 2.1 block layout with floats, clearance, and BFC avoidance. -/
def layoutBlockWithFloats (containerW : Nat) (items : List FloatItem) : List PlacedBox :=
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
            let startY := flowY
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
            let startY := flowY
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
              -- New Formatting Context (e.g. display: flow-root): avoids floats (CSS 2.1 §9.5)
              let curLeft := leftFloatWidthAt lefts flowY
              let curRight := rightFloatWidthAt containerW rights flowY
              let (placeX, placeY) :=
                if curLeft + (item.w : Int) ≤ cW - curRight then
                  (curLeft + item.marginLeft, flowY)
                else
                  let dropY := max (maxBottom lefts) (maxBottom rights)
                  (item.marginLeft, dropY)
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
  loop items [] [] 0 0 true []

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

end BlockFloat
end ChromiumLayout
