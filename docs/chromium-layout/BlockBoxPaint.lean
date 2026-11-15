/-
  Chromium Layout — Box Background Paint, Overflow Propagation & Hit Testing
  Formalizes:
  1. Background & foreground opacity/obscuration queries and physical background
     rectangles (CSS Backgrounds and Borders Level 3 §3, LayoutBox::PhysicalBackgroundRect).
  2. Scroller background paint location selection between contents space,
     border-box space, and both spaces (LayoutBox::GetBackgroundPaintLocation).
  3. Contents visual overflow propagation across writing modes, overflow clip
     margin & resizer hit-testing, and layer reflection/overflow invalidation.
-/

namespace BlockBoxPaint

/-- Check whether `inner` covers `outer` in 2D physical coordinates. -/
def rectCovers (outer inner : Int × Int × Int × Int) : Bool :=
  let (ox, oy, ow, oh) := outer
  let (ix, iy, iw, ih) := inner
  ix ≤ ox && iy ≤ oy && ox + ow ≤ ix + iw && oy + oh ≤ iy + ih

/-- Whether a box's background is known to be completely obscured by an
    unclipped, visible, opaque child (`layout_box_test.cc:45`, `:59`, `:88`). -/
def backgroundKnownObscured (boxW boxH childW childH : Int)
    (childOpaque childVisVisible hasCssClipOrAncestorClip : Bool) : Bool :=
  !hasCssClipOrAncestorClip && childOpaque && childVisVisible &&
    childW ≥ boxW && childH ≥ boxH

/-- Whether a box's foreground is known to be opaque in a query rectangle
    (`layout_box_test.cc:127`, `:161`). -/
def foregroundKnownOpaqueInRect (qx qy qw qh boxW childBlockOffset childW childH : Int)
    (isVerticalRl childOpaque isDirectLayerlessChild : Bool) : Bool :=
  if !childOpaque || !isDirectLayerlessChild then false
  else
    let cx := if isVerticalRl then boxW - childBlockOffset - childW else 0
    let cy := if isVerticalRl then 0 else childBlockOffset
    rectCovers (qx, qy, qw, qh) (cx, cy, childW, childH)

/-- Physical rectangle for a box level (`0` = content-box, `1` = padding-box,
    `2` = border-box). -/
def boxLevelRect (border padding contentW contentH level : Nat) :
    Nat × Nat × Nat × Nat :=
  if level == 0 then
    (border + padding, border + padding, contentW, contentH)
  else if level == 1 then
    (border, border, contentW + 2 * padding, contentH + 2 * padding)
  else
    (0, 0, contentW + 2 * padding + 2 * border, contentH + 2 * padding + 2 * border)

/-- Physical background rectangles `(knownOpaqueRect, paintedExtent)` for a box
    (`layout_box_test.cc:197`).
    Clip codes: `0` = content-box, `1` = padding-box, `2` = border-box, `3` = text. -/
def physicalBackgroundRects (border padding contentW contentH : Nat)
    (hasColor colorOpaque hasBlend colorLocal : Bool) (colorClip : Nat)
    (hasImage : Bool) (imageClip : Nat) (borderOpaque : Bool) :
    (Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) :=
  let knownOpaque :=
    if !hasColor || !colorOpaque || hasBlend || colorClip == 3 then (0, 0, 0, 0)
    else if colorClip == 0 then boxLevelRect border padding contentW contentH 0
    else if colorClip == 1 || colorLocal || borderOpaque then
      boxLevelRect border padding contentW contentH 1
    else boxLevelRect border padding contentW contentH 2
  let painted :=
    if !hasColor && !hasImage then (0, 0, 0, 0)
    else
      let colorLevel :=
        if !hasColor then 0
        else if colorLocal then 1
        else if colorClip == 2 || colorClip == 3 then (if borderOpaque then 1 else 2)
        else colorClip
      let imageLevel :=
        if !hasImage then 0
        else if imageClip == 2 then (if borderOpaque then 1 else 2)
        else imageClip
      boxLevelRect border padding contentW contentH (max colorLevel imageLevel)
  (knownOpaque, painted)

/-- Background paint location for a scroller (`layout_box_test.cc:2245`–`:2560`):
    `1` = `kBackgroundPaintInContentsSpace`,
    `2` = `kBackgroundPaintInBorderBoxSpace`,
    `3` = `kBackgroundPaintInBothSpaces`. -/
def backgroundPaintLocation (hasImage imageLocal colorLocal colorTranslucent : Bool)
    (colorClip : Nat) (hasPadding hasBorder borderOpaque borderDashed : Bool)
    (hasBorderShape hasInsetShadow hasBorderImage hasCustomScrollbar : Bool)
    (elasticOverscrollShiftsContent overscrollBehaviorNone : Bool) : Nat :=
  if hasBorderShape || hasInsetShadow || hasBorderImage then 2
  else if hasImage && !imageLocal then 2
  else if !colorLocal && colorClip == 0 && hasPadding then 2
  else
    let borderBleeds := !colorLocal && colorClip == 2 && hasBorder && (!borderOpaque || borderDashed)
    let overscrollBleeds := elasticOverscrollShiftsContent && !colorLocal && !overscrollBehaviorNone
    if hasCustomScrollbar || borderBleeds || overscrollBleeds then
      if colorTranslucent then 2 else 3
    else 1

/-- Bounding-box union of two non-empty physical rectangles `(x, y, w, h)`
    (`layout_box_test.cc:670`). -/
def rectUnion (r1 r2 : Int × Int × Int × Int) : Int × Int × Int × Int :=
  let (x1, y1, w1, h1) := r1
  let (x2, y2, w2, h2) := r2
  let minX := min x1 x2
  let minY := min y1 y2
  let maxX := max (x1 + w1) (x2 + w2)
  let maxY := max (y1 + h1) (y2 + h2)
  (minX, minY, maxX - minX, maxY - minY)

/-- Shift a physical rectangle by `(dx, dy)` (`layout_box_test.cc:670`). -/
def offsetRect (dx dy : Int) (r : Int × Int × Int × Int) : Int × Int × Int × Int :=
  let (x, y, w, h) := r
  (x + dx, y + dy, w, h)

/-- Hit-test target code for a container with optional overflow clip margin and
    resizer control (`layout_box_test.cc:717`, `:737`, `:1775`):
    `1` = documentElement, `2` = body, `3` = container, `4` = child. -/
def hitTestBoxWithClipAndResizer (boxX boxY boxW boxH clipMargin childW childH resizerSize qx qy : Int)
    (clipsOverflow : Bool) : Nat :=
  if resizerSize > 0 && qx ≥ boxX + boxW - resizerSize && qx < boxX + boxW &&
      qy ≥ boxY + boxH - resizerSize && qy < boxY + boxH then 3
  else if clipsOverflow && (qx < boxX || qy < boxY ||
      qx ≥ boxX + boxW + clipMargin || qy ≥ boxY + boxH + clipMargin) then
    if qx ≥ boxX && qy ≥ boxY && qy < boxY + boxH then 2 else 1
  else if qx ≥ boxX && qx < boxX + childW && qy ≥ boxY && qy < boxY + childH then 4
  else if qx ≥ boxX && qx < boxX + boxW && qy ≥ boxY && qy < boxY + boxH then 3
  else if qx ≥ boxX && qy ≥ boxY && qy < boxY + boxH then 2
  else 1

/-- Location container resolution and flipped-blocks child offset for SVG
    `<foreignObject>` (`layout_box_test.cc:356`, `:435`). -/
def resolveLocationContainer (parentId enclosingBoxId : Nat)
    (isParentInline isSvgForeignObject : Bool) : Nat :=
  if isSvgForeignObject then 0
  else if isParentInline then enclosingBoxId
  else parentId

/-- Animated image paint invalidation state `(shouldDoFull, hasImageReason, shouldDelay)`
    (`layout_box_test.cc:816`, `:849`). -/
def imageChangedInvalidation (isAnimated canDefer isRootBackground : Bool) :
    Bool × Bool × Bool :=
  if isRootBackground then (false, true, false)
  else if isAnimated && canDefer then (false, true, true)
  else (true, true, false)

/-- Whether a layout object supports PaintLayer and `-webkit-box-reflect`
    (`layout_box_test.cc:1664`). -/
def supportsLayerAndReflection (isTableColOrGroup isNonRootSvgChild : Bool) : Bool :=
  !isTableColOrGroup && !isNonRootSvgChild

/-- Overflow recalculation flags `(selfNeedsScrollable, layerNeedsVisual)` when
    `transform` is toggled (`layout_box_test.cc:1709`, `:1732`). -/
def overflowRecalcOnTransformChange (hadTransform hasTransform : Bool) : Bool × Bool :=
  (false, hadTransform != hasTransform)

/-- A CSS-clipped child or ancestor never obscures its parent's background. -/
theorem backgroundKnownObscured_false_when_clipped
    (boxW boxH childW childH : Int) (childOpaque childVisVisible : Bool) :
    backgroundKnownObscured boxW boxH childW childH childOpaque childVisVisible true = false := by
  simp [backgroundKnownObscured]

/-- Any border-shape, inset box-shadow, or border-image forces background
    painting into border-box space (`2`). -/
theorem backgroundPaintLocation_borderShape_borderBox
    (hasImage imageLocal colorLocal colorTranslucent : Bool)
    (colorClip : Nat) (hasPadding hasBorder borderOpaque borderDashed : Bool)
    (hasInsetShadow hasBorderImage hasCustomScrollbar : Bool)
    (elasticOverscrollShiftsContent overscrollBehaviorNone : Bool) :
    backgroundPaintLocation hasImage imageLocal colorLocal colorTranslucent
      colorClip hasPadding hasBorder borderOpaque borderDashed
      true hasInsetShadow hasBorderImage hasCustomScrollbar
      elasticOverscrollShiftsContent overscrollBehaviorNone = 2 := by
  rfl

/-- Locally attached image and color backgrounds without border-space-only
    decorations or custom scrollbars always paint in scrolling contents space (`1`). -/
theorem backgroundPaintLocation_local_contentsSpace
    (hasImage colorTranslucent : Bool) (colorClip : Nat)
    (hasPadding hasBorder borderOpaque borderDashed : Bool)
    (elasticOverscrollShiftsContent overscrollBehaviorNone : Bool) :
    backgroundPaintLocation hasImage true true colorTranslucent
      colorClip hasPadding hasBorder borderOpaque borderDashed
      false false false false
      elasticOverscrollShiftsContent overscrollBehaviorNone = 1 := by
  simp [backgroundPaintLocation]

/-- Bounding-box union of two physical rectangles is commutative. -/
theorem rectUnion_comm (r1 r2 : Int × Int × Int × Int) :
    rectUnion r1 r2 = rectUnion r2 r1 := by
  rcases r1 with ⟨x1, y1, w1, h1⟩
  rcases r2 with ⟨x2, y2, w2, h2⟩
  simp only [rectUnion, Prod.mk.injEq]
  refine ⟨by omega, by omega, by omega, by omega⟩

end BlockBoxPaint
