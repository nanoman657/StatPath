/-
  FlexLayout.lean: CSS Flexible Box Layout Level 1 algorithms,
  written from CSS Flexible Box Layout Module Level 1 (W3C Candidate Recommendation Snapshot)
  §5 (Flex Flow), §7 (Flexibility), §8 (Alignment), §9 (Flex Layout Algorithm)
  and checked against flex_layout_algorithm_test.cc.
  Owned by the block lane (Flex*).
-/

namespace ChromiumLayout
namespace FlexLayout

/-- Flex direction: row (inline axis) or column (block axis). CSS Flexbox 1 §5.1. -/
inductive FlexDirection where
  | row
  | rowReverse
  | column
  | columnReverse
  deriving Inhabited, DecidableEq, Repr

/-- Flex wrap: single-line (nowrap) or multi-line (wrap, wrap-reverse). CSS Flexbox 1 §5.2. -/
inductive FlexWrap where
  | nowrap
  | wrap
  | wrapReverse
  deriving Inhabited, DecidableEq, Repr

/-- A flex item specification. CSS Flexbox 1 §4. -/
structure FlexItem where
  id : Nat := 0
  mainSize : Nat := 0
  crossSize : Nat := 0
  grow : Nat := 0
  shrink : Nat := 1
  basis : Option Nat := none
  minMain : Option Nat := none
  maxMain : Option Nat := none
  marginMainStart : Nat := 0
  marginMainEnd : Nat := 0
  marginCrossStart : Nat := 0
  marginCrossEnd : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- A flex container specification. CSS Flexbox 1 §3, §5. -/
structure FlexContainer where
  direction : FlexDirection := .row
  wrap : FlexWrap := .nowrap
  mainSize : Option Nat := none
  crossSize : Option Nat := none
  gapMain : Nat := 0
  gapCross : Nat := 0
  borderCrossStart : Nat := 0
  borderCrossEnd : Nat := 0
  borderMainStart : Nat := 0
  borderMainEnd : Nat := 0
  paddingCrossStart : Nat := 0
  paddingCrossEnd : Nat := 0
  paddingMainStart : Nat := 0
  paddingMainEnd : Nat := 0
  items : List FlexItem := []
  deriving Inhabited, DecidableEq, Repr

/-- Laid-out flex item with resolved physical/logical geometry. -/
structure LaidOutItem where
  id : Nat
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Inhabited, DecidableEq, Repr

/-- Laid-out flex line containing items. CSS Flexbox 1 §6. -/
structure LaidOutLine where
  lineIdx : Nat
  crossPos : Nat
  crossSize : Nat
  items : List LaidOutItem
  deriving Inhabited, DecidableEq, Repr

/-- Result of laying out a flex container. CSS Flexbox 1 §9. -/
structure FlexResult where
  w : Nat
  h : Nat
  lines : List LaidOutLine
  deriving Inhabited, DecidableEq, Repr

/-- Item base main size. CSS Flexbox 1 §9.2. -/
def itemBaseSize (it : FlexItem) : Nat :=
  match it.basis with
  | some b => b
  | none => it.mainSize

/-- Item outer base main size including margins. CSS Flexbox 1 §9.2. -/
def itemOuterBaseSize (it : FlexItem) : Nat :=
  let base := itemBaseSize it
  let minClamped := match it.minMain with | some m => Nat.max base m | none => base
  it.marginMainStart + minClamped + it.marginMainEnd

/-- Collect items into flex lines. CSS Flexbox 1 §9.3. -/
def collectFlexLines (fwrap : FlexWrap) (innerMain : Option Nat) (gap : Nat) (items : List FlexItem) : List (List FlexItem) :=
  if items.isEmpty then []
  else
    match fwrap with
    | .nowrap => [items]
    | _ =>
      match innerMain with
      | none => [items]
      | some limit =>
        let rec loop (items : List FlexItem) (currLine : List FlexItem) (currLineSize : Nat)
                     (acc : List (List FlexItem)) : List (List FlexItem) :=
          match items with
          | [] => if currLine.isEmpty then acc.reverse else (currLine.reverse :: acc).reverse
          | it :: rest =>
            let itSize := itemOuterBaseSize it
            let needed := if currLine.isEmpty then itSize else currLineSize + gap + itSize
            if currLine.isEmpty || needed ≤ limit then
              loop rest (it :: currLine) needed acc
            else
              loop rest [it] itSize (currLine.reverse :: acc)
        loop items [] 0 []

/-- Resolve flexible lengths for items within a flex line. CSS Flexbox 1 §9.7. -/
def resolveFlexLineMainSizes (innerMain : Option Nat) (gap : Nat) (items : List FlexItem) : List (FlexItem × Nat) :=
  let count := items.length
  let totalGap := if count > 1 then (count - 1) * gap else 0
  let totalOuterBase := (items.map itemOuterBaseSize).foldl (·+·) 0 + totalGap
  match innerMain with
  | none => items.map (fun it => (it, itemOuterBaseSize it))
  | some limit =>
    if limit ≥ totalOuterBase then
      let freeSpace := limit - totalOuterBase
      let totalGrow := (items.map (·.grow)).foldl (·+·) 0
      items.map (fun it =>
        let base := itemOuterBaseSize it
        let extra := if totalGrow > 0 then freeSpace * it.grow / totalGrow else 0
        let sz := base + extra
        let clamped := match it.maxMain with | some m => Nat.min sz (it.marginMainStart + m + it.marginMainEnd) | none => sz
        (it, clamped))
    else
      let overflow := totalOuterBase - limit
      let totalScaledShrink := (items.map (fun it => it.shrink * itemBaseSize it)).foldl (·+·) 0
      items.map (fun it =>
        let base := itemOuterBaseSize it
        let shrinkAmt :=
          if totalScaledShrink > 0 then
            overflow * (it.shrink * itemBaseSize it) / totalScaledShrink
          else 0
        let sz := if base ≥ shrinkAmt then base - shrinkAmt else 0
        let clamped := match it.minMain with | some m => Nat.max sz (it.marginMainStart + m + it.marginMainEnd) | none => sz
        (it, clamped))

/-- Process a single flex line into positioned items. CSS Flexbox 1 §9.4, §9.5, §9.6. -/
def layoutFlexLine (isRow : Bool) (innerMain : Option Nat) (gapMain : Nat) (bpMainStart : Nat)
                   (lineIdx : Nat) (currCross : Nat) (lItems : List FlexItem) : LaidOutLine × Nat :=
  let sized := resolveFlexLineMainSizes innerMain gapMain lItems
  let lineCross := (sized.map (fun (it, _) => it.marginCrossStart + it.crossSize + it.marginCrossEnd)).foldl max 0
  let (laidItems, lineMainUsed) := sized.foldl (fun (pair : List LaidOutItem × Nat) (it, itMain) =>
    let (itAcc, curPos) := pair
    let itCross := if it.crossSize > 0 then it.crossSize else lineCross
    let (ix, iy, iw, ih) :=
      if isRow then
        (curPos, currCross + it.marginCrossStart, itMain, itCross)
      else
        (currCross + it.marginCrossStart, curPos, itCross, itMain)
    let itemOut : LaidOutItem := ⟨it.id, ix, iy, iw, ih⟩
    (itAcc ++ [itemOut], curPos + itMain + gapMain)) ([], bpMainStart)
  let actualLineMain := if lItems.isEmpty then 0 else lineMainUsed - gapMain - bpMainStart
  (⟨lineIdx, currCross, lineCross, laidItems⟩, actualLineMain)

/-- Lay out a flex container according to CSS Flexible Box Layout Level 1 §9. -/
def layoutFlex (c : FlexContainer) : FlexResult :=
  let isRow := match c.direction with | .row | .rowReverse => true | _ => false
  let innerMain := c.mainSize
  let innerCross := c.crossSize
  let linesRaw := collectFlexLines c.wrap innerMain c.gapMain c.items
  let bpMainStart := c.borderMainStart + c.paddingMainStart
  let bpCrossStart := c.borderCrossStart + c.paddingCrossStart
  let bpMainEnd := c.borderMainEnd + c.paddingMainEnd
  let bpCrossEnd := c.borderCrossEnd + c.paddingCrossEnd

  let rec processLines (lines : List (List FlexItem)) (lineIdx : Nat) (currCross : Nat) (maxMainUsed : Nat)
                       (acc : List LaidOutLine) : List LaidOutLine × Nat × Nat :=
    match lines with
    | [] => (acc.reverse, currCross, maxMainUsed)
    | lItems :: rest =>
      let (laidLine, lineMain) := layoutFlexLine isRow innerMain c.gapMain bpMainStart lineIdx currCross lItems
      processLines rest (lineIdx + 1) (currCross + laidLine.crossSize + c.gapCross) (max maxMainUsed lineMain) (laidLine :: acc)

  let (laidLines, totalCrossUsed, maxMainUsed) := processLines linesRaw 0 bpCrossStart 0 []
  let totalMain := match innerMain with
    | some m => m + bpMainStart + bpMainEnd
    | none => maxMainUsed + bpMainStart + bpMainEnd
  let totalCross := match innerCross with
    | some c => c + bpCrossStart + bpCrossEnd
    | none => totalCrossUsed + bpCrossEnd

  let (w, h) := if isRow then (totalMain, totalCross) else (totalCross, totalMain)
  ⟨w, h, laidLines⟩

/-- Law: An empty flex container produces no lines.
    CSS Flexible Box Layout Level 1 §9.3. -/
theorem flex_empty_no_lines (fwrap : FlexWrap) (innerMain : Option Nat) (gap : Nat) :
    collectFlexLines fwrap innerMain gap [] = [] := by
  rfl

/-- Law: A flex container with flex-wrap: nowrap always generates at most one line of items.
    CSS Flexible Box Layout Level 1 §5.2. -/
theorem flex_nowrap_at_most_one_line (innerMain : Option Nat) (gap : Nat) (items : List FlexItem) :
    (collectFlexLines .nowrap innerMain gap items).length ≤ 1 := by
  dsimp [collectFlexLines]
  split
  · simp
  · simp

/-- Law: Layout of an empty flex container produces no laid out lines.
    CSS Flexible Box Layout Level 1 §9.3. -/
theorem flex_empty_container_lines (c : FlexContainer) (h : c.items = []) :
    (layoutFlex c).lines = [] := by
  dsimp [layoutFlex]
  have hlines : collectFlexLines c.wrap c.mainSize c.gapMain c.items = [] := by
    rw [h]
    rfl
  rw [hlines]
  rfl

end FlexLayout
end ChromiumLayout
