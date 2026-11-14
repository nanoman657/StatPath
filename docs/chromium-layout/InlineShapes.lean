/-
  docs/chromium-layout/InlineShapes.lean

  Formal model for CSS Shapes Module Level 1 §3
  (`third_party/blink/renderer/core/layout/shapes/`).

  Owns:
  - LineSegment (`shape.h`)
  - BoxShape (`box_shape.h`)
  - EllipseShape (`ellipse_shape.h`)
  - Shape margin calculations, bounding boxes, and excluded interval intersections.
-/
import LayoutTypes
import LayoutInline
import InlineGeometry

namespace ChromiumLayout

/-! ## 1. Line Segment and Excluded Interval (CSS Shapes 1 §3) -/

/-- Horizontal line segment within a line box (`LineSegment`). -/
structure LineSegment where
  isValid : Bool := false
  logicalLeft : Int := 0
  logicalRight : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Box Shape Geometry (CSS Shapes 1 §3.1 & box_shape.h) -/

/-- CSS Shapes 1 §3.1 & Blink BoxShape:
    A box shape defined by logical rounded rectangle bounds and a shape margin. -/
structure BoxShape where
  bounds : LayoutUnitRect
  shapeMargin : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Check if box shape bounds are empty (zero width or height). -/
def BoxShape.isEmpty (s : BoxShape) : Bool :=
  s.bounds.width == 0 || s.bounds.height == 0

/-- Compute shape-margin logical bounding box expanding bounds by shape-margin on all four sides. -/
def BoxShape.shapeMarginLogicalBoundingBox (s : BoxShape) : LayoutUnitRect :=
  { x := s.bounds.x - s.shapeMargin,
    y := s.bounds.y - s.shapeMargin,
    width := s.bounds.width + 2 * s.shapeMargin,
    height := s.bounds.height + 2 * s.shapeMargin }

/-- Test whether a horizontal line [lineTop, lineTop + lineHeight) overlaps the shape margin bounds. -/
def BoxShape.lineOverlapsShapeMarginBounds (s : BoxShape) (lineTop lineHeight : Int) : Bool :=
  let bbox := s.shapeMarginLogicalBoundingBox
  let lineBottom := lineTop + lineHeight
  let shapeBottom := bbox.y + bbox.height
  if lineHeight == 0 then
    lineTop ≥ bbox.y && lineTop ≤ shapeBottom
  else
    lineTop < shapeBottom && lineBottom > bbox.y

/-- Compute the excluded interval along a line where inline flow content is prohibited. -/
def BoxShape.getExcludedInterval (s : BoxShape) (lineTop lineHeight : Int)
    (overrideLeftRight : Option (Int × Int) := none) : LineSegment :=
  if s.isEmpty || !s.lineOverlapsShapeMarginBounds lineTop lineHeight then
    { isValid := false }
  else
    match overrideLeftRight with
    | some (l, r) => { isValid := true, logicalLeft := l, logicalRight := r }
    | none =>
      let bbox := s.shapeMarginLogicalBoundingBox
      { isValid := true, logicalLeft := bbox.x, logicalRight := bbox.x + bbox.width }

/-! ## 3. Ellipse Shape Geometry (CSS Shapes 1 §3.2 & ellipse_shape.h) -/

/-- CSS Shapes 1 §3.2 & Blink EllipseShape:
    An ellipse shape defined by center point, inline/block radii, and shape margin. -/
structure EllipseShape where
  centerX : Int := 0
  centerY : Int := 0
  radiusInline : Int := 0
  radiusBlock : Int := 0
  shapeMargin : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Check if ellipse shape is empty (zero inline or block radius). -/
def EllipseShape.isEmpty (s : EllipseShape) : Bool :=
  s.radiusInline == 0 || s.radiusBlock == 0

/-- Effective inline and block radii including shape margin. -/
def EllipseShape.effectiveRadii (s : EllipseShape) : Int × Int :=
  (s.radiusInline + s.shapeMargin, s.radiusBlock + s.shapeMargin)

/-- Compute shape-margin logical bounding box for the ellipse. -/
def EllipseShape.shapeMarginLogicalBoundingBox (s : EllipseShape) : LayoutUnitRect :=
  let (rInline, rBlock) := s.effectiveRadii
  { x := s.centerX - rInline,
    y := s.centerY - rBlock,
    width := 2 * rInline,
    height := 2 * rBlock }

/-- Compute excluded interval for an ellipse shape. -/
def EllipseShape.getExcludedInterval (s : EllipseShape) (lineTop lineHeight : Int)
    (overrideLeftRight : Option (Int × Int) := none) : LineSegment :=
  let (rInline, rBlock) := s.effectiveRadii
  if rInline == 0 || rBlock == 0 then
    { isValid := false }
  else
    let lineBottom := lineTop + lineHeight
    let top := s.centerY - rBlock
    let bottom := s.centerY + rBlock
    if lineBottom < top || lineTop ≥ bottom then
      { isValid := false }
    else
      match overrideLeftRight with
      | some (l, r) => { isValid := true, logicalLeft := l, logicalRight := r }
      | none =>
        { isValid := true, logicalLeft := s.centerX - rInline, logicalRight := s.centerX + rInline }

/-! ## 4. General Laws for Shapes -/

/-- CSS Shapes 1 §3.1 Law: With zero shape-margin, BoxShape bounding box equals its bounds. -/
theorem boxShape_zero_margin (b : LayoutUnitRect) :
    (BoxShape.mk b 0).shapeMarginLogicalBoundingBox =
      { x := b.x, y := b.y, width := b.width, height := b.height } := by
  dsimp [BoxShape.shapeMarginLogicalBoundingBox]
  simp

/-- CSS Shapes 1 §3.2 Law: EllipseShape with zero inline radius is always empty. -/
theorem ellipseShape_zero_inline_radius_empty (cx cy rb m : Int) :
    (EllipseShape.mk cx cy 0 rb m).isEmpty = true := by
  rfl

/-- CSS Shapes 1 §3.2 Law: EllipseShape with zero block radius is always empty. -/
theorem ellipseShape_zero_block_radius_empty (cx cy ri m : Int) :
    (EllipseShape.mk cx cy ri 0 m).isEmpty = true := by
  dsimp [EllipseShape.isEmpty]
  simp

/-- CSS Shapes 1 §3.2 Law: EllipseShape bounding box width equals twice the effective inline radius. -/
theorem ellipseShape_bounding_box_width (cx cy ri rb m : Int) :
    (EllipseShape.mk cx cy ri rb m).shapeMarginLogicalBoundingBox.width = 2 * (ri + m) := by
  rfl

end ChromiumLayout
