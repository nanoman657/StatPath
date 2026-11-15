import LayoutTypes
import LayoutBlock

/-!
# Incremental Layout Result Caching (`layout_utils.cc`)

Formalizes the ConstraintSpace and BFC layout-result caching rules in
`CalculateSizeBasedLayoutCacheStatus` and
`MaySkipLayoutWithinBlockFormattingContext` (`layout_utils.cc`, CSS 2.1 §8.3.1,
§9.5, §10.3.5, CSS Sizing 3, CSS Fragmentation 3 §3.1).
-/

namespace BlockResultCache

/-- BFC cache check (`MaySkipLayoutWithinBlockFormattingContext`, `layout_utils.cc:458`).
    Returns `some resolvedNewBfc` on a cache hit (`kHit`) and `none` on `kNeedsLayout`. -/
def checkBfcCache
    (boxH clearSide : Nat) (subtreeModStrut hasInflowAboveStart : Bool)
    (oldBfc oldStrut oldCL oldCR newBfc newStrut newCL newCR : Nat) : Option Nat :=
  let oldHasFloats := oldCL > 0 || oldCR > 0
  let newHasFloats := newCL > 0 || newCR > 0
  if hasInflowAboveStart && (oldHasFloats || newHasFloats) then none
  else if subtreeModStrut && oldStrut != newStrut then none
  else
    let clearOf := fun s cL cR =>
      if s == 1 then cL else if s == 2 then cR else if s == 3 then max cL cR else 0
    let oldClear := clearOf clearSide oldCL oldCR
    let newClear := clearOf clearSide newCL newCR
    let oldBoth := max oldCL oldCR
    let newBoth := max newCL newCR
    let oldPos := oldBfc + oldStrut
    let newPos := newBfc + newStrut
    let pushed := clearSide > 0 && oldClear > oldPos
    if pushed then
      if oldStrut != newStrut then none
      else if oldClear - oldBfc > newClear - newBfc then none
      else if oldClear < oldBoth || newClear < newBoth then none
      else some newClear
    else if oldPos < oldBoth || newPos < newBoth then none
    else some newPos

theorem checkBfcCache_aboveStart_floats
    (boxH clearSide : Nat) (subtreeMod : Bool)
    (oldBfc oldStrut oldCL oldCR newBfc newStrut newCL newCR : Nat)
    (hF : (oldCL > 0 || oldCR > 0) = true) :
    checkBfcCache boxH clearSide subtreeMod true
      oldBfc oldStrut oldCL oldCR newBfc newStrut newCL newCR = none := by
  simp [checkBfcCache, hF]

/-- Exclusion space layout opportunities `(xStart, yStart, yEnd)` after shifting a cached
    block containing a float `(f2W, f2H)` at `newBfc + padTop` below a float `(f1W, f1End)`. -/
def shiftedExclusionOpportunities (f1W f1End newBfc padTop f2H maxEnd : Nat) :=
  [(f1W, 0, maxEnd), (0, f1End, newBfc + padTop), (0, newBfc + padTop + f2H, maxEnd)]

/-- Optimistic float placement in a self-collapsing block (`layout_utils.cc:533`):
    no forced BFC block-offset is needed when expected BFC offset clears floats. -/
def forcedBfcForSelfCollapsing (expectedBfc clearBoth : Nat) : Option Nat :=
  if expectedBfc < clearBoth then some clearBoth else none

/-- Shrink-to-fit / float inline-size cache check (`InlineLengthMayChange` &
    `CalculateSizeBasedLayoutCacheStatusWithGeometry`, `layout_utils.cc:27,184`). -/
def checkShrinkToFitCache (minC maxC marginStart minPctW oldAvailW newAvailW : Nat) : Bool :=
  let resolve := fun aw => max (minPctW * aw / 100) (min maxC (max minC (aw - marginStart)))
  resolve oldAvailW == resolve newAvailW &&
    (oldAvailW == newAvailW || (minPctW == 0 && marginStart == 0))

theorem checkShrinkToFitCache_same_avail (minC maxC marginStart minPctW aw : Nat) :
    checkShrinkToFitCache minC maxC marginStart minPctW aw aw = true := by
  simp [checkShrinkToFitCache]

/-- Size and percentage-block-size / quirks-mode cache check
    (`SizeMayChange` & `CalculateSizeBasedLayoutCacheStatusWithGeometry`, `layout_utils.cc:117`).
    - `fixedW` / `fixedH`: explicit pixel width/height (`0` if auto/percentage)
    - `pctW` / `pctH`: percentage width (`min-width` or `width`) / percentage height
    - `minH`: explicit `min-height`
    - `intrinsicH`: content intrinsic block size
    - `quirksPctChild`: in-flow percentage-height descendant in quirks mode
    - `isFlexOrGrid` / `isTable`: whether the box is a flex/grid or table formatting context
    - `oldIndef` / `newIndef`: whether initial block-size is indefinite in old/new space
    - `needsLayout`: whether `SetNeedsLayout` was marked on the node -/
def checkSizeAndQuirksCache
    (fixedW pctW fixedH pctH minH intrinsicH : Nat)
    (quirksPctChild hasPctChild isFlexOrGrid isTable oldIndef newIndef needsLayout : Bool)
    (oldW oldH newW newH : Nat) : Bool :=
  if needsLayout then false
  else
    let resW := fun w => max (pctW * w / 100) (if fixedW > 0 then fixedW else w)
    let resH := fun h indef =>
      let ph := if pctH > 0 && (!indef || !isTable) then pctH * h / 100 else 0
      max minH (if fixedH > 0 then fixedH else max ph intrinsicH)
    let wSame := resW oldW == resW newW && (pctW == 0 || oldW == newW)
    let oldBoxH := resH oldH oldIndef
    let newBoxH := resH newH newIndef
    let hSame := oldBoxH == newBoxH && (!isTable || (oldH == newH && oldIndef == newIndef))
    let indefChangeMiss := oldIndef != newIndef && (isFlexOrGrid || hasPctChild)
    let quirksMiss := quirksPctChild && fixedH == 0 && oldBoxH == 0 && oldH != newH
    wSame && hSame && !indefChangeMiss && !quirksMiss

theorem checkSizeAndQuirksCache_dirty
    (fixedW pctW fixedH pctH minH intrinsicH : Nat)
    (q p fg tb oi ni : Bool) (ow oh nw nh : Nat) :
    checkSizeAndQuirksCache fixedW pctW fixedH pctH minH intrinsicH
      q p fg tb oi ni true ow oh nw nh = false := rfl

/-- Flex and table-cell `kMeasure` (`0`) vs `kLayout` (`1`) cache-slot resolution
    (`layout_result_caching_test.cc:1380–1685`).
    Returns `(activeSlot, measureEqualsLayout)`. -/
def checkMeasureLayoutSlot (stretchedOrAligned baselineChanged : Bool) : Nat × Bool :=
  if stretchedOrAligned || baselineChanged then (1, false) else (0, true)

/-- Table row (`<tr>`) and section (`<tbody>`) cache hit check: hits iff the table's
    resolved column widths are unchanged (`layout_result_caching_test.cc:1718–1842`). -/
def checkTableRowSectionCache (colsTest colsSrc : List Nat) : Bool :=
  colsTest == colsSrc

/-- Fragmentation cache check (`layout_result_caching_test.cc:1844–2064`). -/
def checkFragmentationCache
    (hasBreakToken isInitialBalancePass : Bool)
    (boxH oldFragH newFragH oldOff newOff : Nat) : Bool :=
  if isInitialBalancePass then oldFragH == newFragH
  else if hasBreakToken then oldFragH == newFragH && oldOff == newOff
  else oldFragH == newFragH && oldOff + boxH <= oldFragH && newOff + boxH <= newFragH

theorem checkFragmentationCache_overflow
    (boxH fragH oldOff newOff : Nat) (hOver : ¬ newOff + boxH <= fragH) :
    checkFragmentationCache false false boxH fragH fragH oldOff newOff = false := by
  simp [checkFragmentationCache, hOver]

end BlockResultCache
