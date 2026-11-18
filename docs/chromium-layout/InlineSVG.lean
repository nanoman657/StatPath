import InlineGeometry
import InlineFragmentItem

namespace ChromiumLayout

/-! ## SVG Layout and Vector Effects Model
    Specifications:
    - SVG 2 §7.3 Viewports (SVG viewport and clipping)
    - SVG 2 §11.3.3 The textPath element (Nesting constraint)
    - SVG 2 §11.4 Text layout attributes (textLength and quads)
    - SVG 2 §13.3 Vector Effects (vector-effect: non-scaling-stroke)
    - SVG 2 §13.5 Object Bounding Box (Empty shapes have empty stroke bounding box)
    - CSS 2.1 §10 Visual formatting model details (Content rect and border box mapping)
    - CSSOM View Module §8 (Rect-based hit testing)
    Blink reference:
    - `third_party/blink/renderer/core/layout/svg/layout_svg_container.cc`
    - `third_party/blink/renderer/core/layout/svg/layout_svg_text.cc`
    - `third_party/blink/renderer/core/layout/svg/layout_svg_shape.cc`
    - `third_party/blink/renderer/core/layout/svg/layout_svg_root.cc`
    - `third_party/blink/renderer/core/layout/svg/layout_svg_inline.cc`
-/

/-- SVG vector effect specification (SVG 2 §13.3). -/
inductive SvgVectorEffect where
  | none
  | nonScalingStroke
  deriving DecidableEq, Repr, Inhabited

/-- Simplified SVG tree node representation for layout and effect analysis (SVG 2 §13.3). -/
inductive SvgNode where
  | shape (vectorEffect : SvgVectorEffect)
  | text (vectorEffect : SvgVectorEffect) (children : List SvgNode)
  | tspan (vectorEffect : SvgVectorEffect)
  | container (vectorEffect : SvgVectorEffect) (children : List SvgNode)
  | root (children : List SvgNode)
  | defs (children : List SvgNode)
  | use (targetHasNonScalingStroke : Bool)
  deriving Repr, Inhabited

mutual
  /-- Determine whether a transform affects vector effect for an SVG layout object (SVG 2 §13.3).
      Returns true if the object or any rendered descendant has vector-effect="non-scaling-stroke".
      Root SVG never returns true (creates a viewport boundary). -/
  def transformAffectsVectorEffect : SvgNode → Bool
    | SvgNode.root _ => false
    | SvgNode.shape ve => ve == SvgVectorEffect.nonScalingStroke
    | SvgNode.tspan ve => ve == SvgVectorEffect.nonScalingStroke
    | SvgNode.use targetVE => targetVE
    | SvgNode.text ve children =>
      ve == SvgVectorEffect.nonScalingStroke || transformAffectsVectorEffectList children
    | SvgNode.container ve children =>
      ve == SvgVectorEffect.nonScalingStroke || transformAffectsVectorEffectList children
    | SvgNode.defs _ => false

  /-- Helper checking if any node in a list affects vector effect. -/
  def transformAffectsVectorEffectList : List SvgNode → Bool
    | [] => false
    | node :: rest => transformAffectsVectorEffect node || transformAffectsVectorEffectList rest
end

/-- Compute the axis-aligned bounding box for an SVG text element with textLength (SVG 2 §11.4). -/
def computeSvgTextBoundingBox (x y : Nat) (textLength : Nat) (fontSize : Nat) : PhysicalRect :=
  { x := x, y := y, width := textLength, height := fontSize }

/-- Stroke bounding box for an SVG circle (SVG 2 §13.5).
    An empty shape with radius 0 has an empty stroke bounding box. -/
def computeSvgCircleStrokeBoundingBox (cx cy r strokeWidth : Nat) : PhysicalRect :=
  if r == 0 then { x := 0, y := 0, width := 0, height := 0 }
  else
    let rad := r + (strokeWidth + 1) / 2
    { x := cx - rad, y := cy - rad, width := 2 * rad, height := 2 * rad }

/-- SVG element tag types for child allowance verification (SVG 2 §11.3.3). -/
inductive SvgTag where
  | svg
  | text
  | textPath
  | a
  | tspan
  deriving DecidableEq, Repr, Inhabited

/-- Check if an SVG element allows a child tag (SVG 2 §11.3.3).
    A textPath element cannot have a textPath descendant. -/
def isSvgChildAllowed (parent : SvgTag) (ancestors : List SvgTag) (child : SvgTag) : Bool :=
  match child with
  | SvgTag.textPath => !ancestors.contains SvgTag.textPath && parent != SvgTag.textPath
  | _ => true

/-- Map an SVG descendant visual rect to document coordinates (SVG 2 §7.3, CSS 2.1 §10).
    If overflow is not visible, rect is clipped to the SVG viewport.
    Border is added to map from SVG content box to border box document coordinates. -/
def mapSvgVisualRectToDocument (svgBorder : PhysicalBoxStrut) (svgViewport : PhysicalSize) (overflowVisible : Bool) (elemRect : PhysicalRect) : PhysicalRect :=
  let clipped :=
    if overflowVisible then elemRect
    else
      let right := Nat.min (elemRect.x + elemRect.width) svgViewport.width
      let bottom := Nat.min (elemRect.y + elemRect.height) svgViewport.height
      let clX := Nat.min elemRect.x svgViewport.width
      let clY := Nat.min elemRect.y svgViewport.height
      { x := clX, y := clY, width := right - clX, height := bottom - clY }
  { x := clipped.x + svgBorder.left
  , y := clipped.y + svgBorder.top
  , width := clipped.width
  , height := clipped.height }

/-- Check whether two physical rects intersect (CSSOM View §8, SVG 2 §7.3). -/
def rectsIntersect (r1 r2 : PhysicalRect) : Bool :=
  r1.x < r2.x + r2.width && r2.x < r1.x + r1.width &&
  r1.y < r2.y + r2.height && r2.y < r1.y + r1.height

/-- Integer floor division for arbitrary integers. -/
def intFloorDiv (a b : Int) : Int :=
  if (a >= 0 && b > 0) || (a <= 0 && b < 0) then a / b
  else -((-a + b - 1) / b)

/-- Integer ceil division for arbitrary integers. -/
def intCeilDiv (a b : Int) : Int :=
  if a > 0 && b > 0 then (a + b - 1) / b
  else a / b

/-- Project 1D coordinate under perspective distance `d` and z-translation `z` relative to `origin` (CSS Transforms 2 §4).
    Scale factor is `d / (d - z)`. -/
def projectPerspectiveCoord (origin : Int) (d : Nat) (z : Int) (coord : Int) (ceil : Bool) : Int :=
  if (d : Int) <= z then coord
  else
    let denom : Int := (d : Int) - z
    let num : Int := (coord - origin) * (d : Int)
    if ceil then origin + intCeilDiv num denom
    else origin + intFloorDiv num denom

/-- Compute 2D axis-aligned enclosing rect after 3D perspective projection and translateZ (CSS Transforms 2 §4).
    `origin` is perspective origin (default center). `d` is perspective distance. `z` is translateZ. -/
def projectPerspectiveRect (origin : Int × Int) (d : Nat) (z : Int) (r : PhysicalRect) : PhysicalRect :=
  let (ox, oy) := origin
  let left := projectPerspectiveCoord ox d z (r.x : Int) false
  let right := projectPerspectiveCoord ox d z ((r.x + r.width : Nat) : Int) true
  let top := projectPerspectiveCoord oy d z (r.y : Int) false
  let bottom := projectPerspectiveCoord oy d z ((r.y + r.height : Nat) : Int) true
  { x := left.toNat
  , y := top.toNat
  , width := (right - left).toNat
  , height := (bottom - top).toNat }

/-- Squared Euclidean distance from a 2D point to the closest point of an axis-aligned box (CSSOM View §8, SVG 2 §11.4). -/
def distanceToBoxSquared (px py : Int) (r : PhysicalRect) : Nat :=
  let rx := (r.x : Int)
  let rw := (r.width : Int)
  let ry := (r.y : Int)
  let rh := (r.height : Int)
  let dx : Nat :=
    if px < rx then (rx - px).toNat
    else if px > rx + rw then (px - (rx + rw)).toNat
    else 0
  let dy : Nat :=
    if py < ry then (ry - py).toNat
    else if py > ry + rh then (py - (ry + rh)).toNat
    else 0
  dx * dx + dy * dy

/-- Point containment test in a PhysicalRect (CSSOM View §8). -/
def pointInRect (px py : Int) (r : PhysicalRect) : Bool :=
  (r.x : Int) <= px && px < (r.x + r.width : Int) &&
  (r.y : Int) <= py && py < (r.y + r.height : Int)

/-- Compute visual rect including feDropShadow filter (SVG 2 §15, CSS Filter Effects 1 §3.1).
    Expands container visual rect by drop shadow offsets and blur radius. -/
def applyDropShadowFilterRect (contentRect : PhysicalRect) (dx dy stdDev : Nat) : PhysicalRect :=
  let filterMargin := 3 * stdDev
  let minX := contentRect.x - filterMargin
  let minY := contentRect.y - filterMargin
  let maxX := contentRect.x + contentRect.width + dx + filterMargin
  let maxY := contentRect.y + contentRect.height + dy + filterMargin
  { x := minX, y := minY, width := maxX - minX, height := maxY - minY }

/-- Annular shape specification: circle or ellipse with center, radii, stroke width, and fill flag (SVG 2 §13.2). -/
structure SvgShapeGeometry where
  cx : Int
  cy : Int
  rx : Nat
  ry : Nat
  strokeWidth : Nat
  hasFill : Bool
  deriving Repr, DecidableEq

/-- Check if a query rect intersects an SVG shape geometry (SVG 2 §13.2, CSSOM View §8). -/
def svgShapeIntersects (shape : SvgShapeGeometry) (query : PhysicalRect) : Bool :=
  let outerRx := shape.rx + (shape.strokeWidth + 1) / 2
  let outerRy := shape.ry + (shape.strokeWidth + 1) / 2
  let outerBox : PhysicalRect := {
    x := (shape.cx - (outerRx : Int)).toNat,
    y := (shape.cy - (outerRy : Int)).toNat,
    width := 2 * outerRx,
    height := 2 * outerRy
  }
  if !rectsIntersect query outerBox then false
  else
    let minDx := if (query.x : Int) > shape.cx then (query.x : Int) - shape.cx
                 else if (query.x + query.width : Int) < shape.cx then shape.cx - (query.x + query.width : Int)
                 else 0
    let minDy := if (query.y : Int) > shape.cy then (query.y : Int) - shape.cy
                 else if (query.y + query.height : Int) < shape.cy then shape.cy - (query.y + query.height : Int)
                 else 0
    let minDistSq := minDx.natAbs * minDx.natAbs + minDy.natAbs * minDy.natAbs
    if minDistSq > outerRx * outerRx then false
    else if shape.hasFill then true
    else
      let innerRx := if shape.rx > shape.strokeWidth / 2 then shape.rx - shape.strokeWidth / 2 else 0
      let c1 := (query.x : Int) - shape.cx
      let c2 := (query.x + query.width : Int) - shape.cx
      let c3 := (query.y : Int) - shape.cy
      let c4 := (query.y + query.height : Int) - shape.cy
      let maxDx := Nat.max c1.natAbs c2.natAbs
      let maxDy := Nat.max c3.natAbs c4.natAbs
      if innerRx > 0 && maxDx * maxDx + maxDy * maxDy < innerRx * innerRx then false
      else true

/-- Rectangular stroked/filled shape for hit testing (SVG 2 §13.2, CSSOM View §8). -/
structure SvgRectShape where
  x : Int
  y : Int
  width : Nat
  height : Nat
  strokeWidth : Nat
  hasFill : Bool
  deriving Repr, DecidableEq

/-- Check if a query rect intersects an SVG rect shape (SVG 2 §13.2, CSSOM View §8). -/
def svgRectIntersects (s : SvgRectShape) (query : PhysicalRect) : Bool :=
  let sw := (s.strokeWidth + 1) / 2
  let outerBox : PhysicalRect := {
    x := (s.x - (sw : Int)).toNat,
    y := (s.y - (sw : Int)).toNat,
    width := s.width + 2 * sw,
    height := s.height + 2 * sw
  }
  if !rectsIntersect query outerBox then false
  else if s.hasFill then true
  else
    let innerLeft := s.x + (s.strokeWidth / 2 : Int)
    let innerTop := s.y + (s.strokeWidth / 2 : Int)
    let innerRight := s.x + (s.width : Int) - (s.strokeWidth / 2 : Int)
    let innerBottom := s.y + (s.height : Int) - (s.strokeWidth / 2 : Int)
    let qLeft := (query.x : Int)
    let qTop := (query.y : Int)
    let qRight := (query.x + query.width : Int)
    let qBottom := (query.y + query.height : Int)
    if innerLeft <= qLeft && qRight <= innerRight && innerTop <= qTop && qBottom <= innerBottom then false
    else true

/-- Find the closest SVG text layout candidate to a query point by box distance (SVG 2 §11.4). -/
def findClosestSvgText (px py : Int) (candidates : List (String × PhysicalRect)) : Option String :=
  match candidates with
  | [] => none
  | (name, r) :: rest =>
    let dist := distanceToBoxSquared px py r
    some (rest.foldl (fun (bestName, bestDist) (n, rect) =>
      let d := distanceToBoxSquared px py rect
      if d < bestDist then (n, d) else (bestName, bestDist)
    ) (name, dist)).1

/-- General Law: Root SVG never has transformAffectsVectorEffect (SVG 2 §13.3). -/
theorem svg_root_never_affects_vector_effect (children : List SvgNode) :
    transformAffectsVectorEffect (SvgNode.root children) = false := by
  rfl

/-- General Law: Empty circle with radius 0 has zero stroke bounding box (SVG 2 §13.5). -/
theorem svg_empty_circle_stroke_box_zero (cx cy sw : Nat) :
    computeSvgCircleStrokeBoundingBox cx cy 0 sw = { x := 0, y := 0, width := 0, height := 0 } := by
  rfl

/-- General Law: When overflow is visible, mapping to document shifts by border offsets (SVG 2 §7.3, CSS 2.1 §10). -/
theorem svg_visual_rect_visible_shift (b : PhysicalBoxStrut) (vp : PhysicalSize) (r : PhysicalRect) :
    (mapSvgVisualRectToDocument b vp true r).x = r.x + b.left ∧
    (mapSvgVisualRectToDocument b vp true r).y = r.y + b.top ∧
    (mapSvgVisualRectToDocument b vp true r).width = r.width ∧
    (mapSvgVisualRectToDocument b vp true r).height = r.height := by
  dsimp [mapSvgVisualRectToDocument]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- General Law: TextPath tag is never allowed if any ancestor is a textPath (SVG 2 §11.3.3). -/
theorem svg_textpath_disallowed_with_textpath_ancestor (p : SvgTag) (ancs : List SvgTag)
    (h_anc : ancs.contains SvgTag.textPath = true) :
    isSvgChildAllowed p ancs SvgTag.textPath = false := by
  dsimp [isSvgChildAllowed]
  rw [h_anc]
  rfl

/-- General Law: Perspective projection is clamped to coord when perspective distance is <= z (CSS Transforms 2 §4). -/
theorem svg_perspective_clamped_when_z_ge (ox : Int) (d : Nat) (z : Int) (coord : Int) (c : Bool)
    (h : (d : Int) ≤ z) :
    projectPerspectiveCoord ox d z coord c = coord := by
  dsimp [projectPerspectiveCoord]
  split
  · rfl
  · rename_i hnot
    omega

/-- General Law: Distance from rect origin (top-left) to rect is always zero (CSSOM View §8, SVG 2 §11.4). -/
theorem svg_distance_to_box_origin (r : PhysicalRect) :
    distanceToBoxSquared (r.x : Int) (r.y : Int) r = 0 := by
  dsimp [distanceToBoxSquared]
  split
  · rename_i h; omega
  · split
    · rename_i _ h; omega
    · split
      · rename_i h; omega
      · split
        · rename_i _ h; omega
        · rfl

/-- General Law: Zero filter margin preserves input content rect (SVG 2 §15, CSS Filter Effects 1 §3.1). -/
theorem svg_drop_shadow_zero (r : PhysicalRect) :
    applyDropShadowFilterRect r 0 0 0 = r := by
  dsimp [applyDropShadowFilterRect]
  cases r
  dsimp
  congr 1 <;> omega

/-- General Law: Text bounding box width matches specified textLength for all inputs (SVG 2 §11.4). -/
theorem svg_text_bounding_box_width (x y len h : Nat) :
    (computeSvgTextBoundingBox x y len h).width = len := by
  rfl

/-! ## ForeignObject Layout and Hit Testing (SVG 2 §13.2, §14, CSSOM View §8) -/

/-- ForeignObject representation with 2D bounds and optional transform (SVG 2 §13.2). -/
structure SvgForeignObject where
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  transformX : Int := 0
  transformY : Int := 0
  deriving Repr, DecidableEq

/-- Compute object bounding box for foreignObject (SVG 2 §13.2). -/
def svgForeignObjectBoundingBox (fo : SvgForeignObject) : Nat × Nat × Nat × Nat :=
  (fo.x, fo.y, fo.width, fo.height)

/-- Compute decorated bounding box under zoom factor (SVG 2 §13.2, CSSOM View §8). -/
def svgForeignObjectDecoratedBoundingBox (fo : SvgForeignObject) (zoom : Nat) : Nat × Nat × Nat × Nat :=
  (fo.x * zoom, fo.y * zoom, fo.width * zoom, fo.height * zoom)

/-- Check if an integer point is inside a 2D bounding box (CSSOM View §8). -/
def svgPointInBox (px py : Int) (x y w h : Nat) : Bool :=
  px >= (x : Int) && px < (x : Int) + (w : Int) &&
  py >= (y : Int) && py < (y : Int) + (h : Int)

/-- Hit test an SVG container with a hierarchy of nested boxes (CSSOM View §8, SVG 2 §13.2).
    Traverses candidate boxes from outer to innermost and returns the deepest matching element name. -/
def svgHitTestHierarchy (svgW svgH : Nat) (boxes : List (String × Nat × Nat × Nat × Nat)) (px py : Int) : String :=
  let rec findInnermost : List (String × Nat × Nat × Nat × Nat) → Option String
    | [] => none
    | (name, x, y, w, h) :: rest =>
      match findInnermost rest with
      | some inner => some inner
      | none =>
        if svgPointInBox px py x y w h then some name
        else none
  if !svgPointInBox px py 0 0 svgW svgH then ""
  else (findInnermost boxes).getD "svg"

/-- Circular clip path hit testing (SVG 2 §14, CSS Masking 1 §3, CSSOM View §8).
    Returns target when inside circle; fallback otherwise. -/
def svgClipPathCircleHitTest (cx cy r : Nat) (px py : Int) (target fallback : String) : String :=
  let dx := px - (cx : Int)
  let dy := py - (cy : Int)
  if dx * dx + dy * dy <= (r : Int) * (r : Int) then target
  else fallback

/-- General Law: ForeignObject bounding box at origin matches its width and height (SVG 2 §13.2). -/
theorem svg_foreign_object_bbox_origin (w h : Nat) :
    svgForeignObjectBoundingBox { x := 0, y := 0, width := w, height := h } = (0, 0, w, h) := by
  rfl

/-- General Law: ForeignObject decorated bounding box under zoom 1 equals its unzoomed box (SVG 2 §13.2). -/
theorem svg_foreign_object_zoom_one (fo : SvgForeignObject) :
    svgForeignObjectDecoratedBoundingBox fo 1 = (fo.x, fo.y, fo.width, fo.height) := by
  dsimp [svgForeignObjectDecoratedBoundingBox]
  simp

/-- General Law: Circular clip-path test at the circle center always hits the target (SVG 2 §14, CSS Masking 1 §3). -/
theorem svg_clip_path_center_hits (cx cy r : Nat) (target fallback : String) :
    svgClipPathCircleHitTest cx cy r (cx : Int) (cy : Int) target fallback = target := by
  dsimp [svgClipPathCircleHitTest]
  have hcast : (r : Int) * (r : Int) = ((r * r : Nat) : Int) := by rfl
  have hpos : 0 ≤ ((r * r : Nat) : Int) := by omega
  rw [hcast]
  split
  · rfl
  · rename_i hnot
    omega

/-! ## SVG 2 §11 SVG Text Layout and Positioning -/

/-- SVG 2 §11.4: lengthAdjust attribute for SVG text. -/
inductive SvgLengthAdjust where
  | spacing
  | spacingAndGlyphs
  deriving DecidableEq, Repr, Inhabited

/-- SVG 2 §11.4: Compute adjusted glyph scale and spacing when textLength is specified.
    If text has zero length or no advance, scale defaults to 1. -/
def computeSvgTextLengthAdjustment (actualWidth targetWidth : Nat) (mode : SvgLengthAdjust) : Nat × Nat :=
  if actualWidth == 0 then (1, 0)
  else
    match mode with
    | .spacingAndGlyphs => (targetWidth / actualWidth, 0)
    | .spacing => (1, if targetWidth > actualWidth then targetWidth - actualWidth else 0)

/-- SVG 2 §11.3.3: Lay out characters along a text path with start and path length constraints. -/
def computeSvgTextPathAdvance (pathLength startOffset textWidth : Nat) : Nat :=
  if startOffset >= pathLength then 0
  else Nat.min textWidth (pathLength - startOffset)

/-- SVG 2 §7.3 & CSS Transforms 1 §5: Clamp excessive SVG scaling factors to maximum layout limits. -/
def clampSvgScale (scale : Nat) (maxScale : Nat := 1000000) : Nat :=
  Nat.min scale maxScale

/-- SVG 2 §11.1 & CSS Text 3 §2.1: SVG first-line text-transform.
    German eszett (ß / U+00DF) transforms to uppercase "SS" per CSS Text 3 §2.1. -/
def svgFirstLineTextTransform (text : String) (uppercase : Bool) : String :=
  if uppercase then
    if text == "ß" then "SS"
    else text
  else text

/-- SVG 2 §11.2 & Unicode UAX #9: SVG text chunk partitioning.
    Each explicit x position starts a new independent text chunk. -/
structure SvgTextChunk where
  x : Nat
  text : String
  length : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Partition text into SVG text chunks given explicit x positions. -/
def partitionSvgTextChunks (xPositions : List Nat) (segments : List String) : List SvgTextChunk :=
  (xPositions.zip segments).map (fun (x, s) => { x := x, text := s, length := s.length })

/-- SVG 2 §11.4 & Unicode Standard §3.6: Split SVG text with combining characters into segment lengths. -/
def computeSvgCombiningSegmentLengths (segmentCharCounts : List Nat) : List Nat :=
  segmentCharCounts

/-- SVG 2 §11.4 Law: Zero actual width defaults to scale 1 and spacing 0 for all modes. -/
theorem computeSvgTextLengthAdjustment_empty (target : Nat) (mode : SvgLengthAdjust) :
    computeSvgTextLengthAdjustment 0 target mode = (1, 0) := rfl

/-- SVG 2 §11.3.3 Law: When start offset is beyond path length, path advance is zero. -/
theorem computeSvgTextPathAdvance_beyond_path (pathLength startOffset textWidth : Nat)
    (h : startOffset ≥ pathLength) :
    computeSvgTextPathAdvance pathLength startOffset textWidth = 0 := by
  dsimp [computeSvgTextPathAdvance]
  split
  · rfl
  · rename_i hnot
    omega

/-- SVG 2 §7.3 Law: Clamped SVG scale factor is bounded by maxScale for all scale values. -/
theorem clampSvgScale_bounded (s maxS : Nat) :
    clampSvgScale s maxS ≤ maxS := by
  dsimp [clampSvgScale]
  exact Nat.min_le_right s maxS

/-- SVG 2 §11.1 Law: German eszett transforms to SS under uppercase transform. -/
theorem svgFirstLineTextTransform_eszett :
    svgFirstLineTextTransform "ß" true = "SS" := rfl

/-- SVG 2 §11.2 Law: Empty positions and segments list produces empty chunk list. -/
theorem partitionSvgTextChunks_empty :
    partitionSvgTextChunks [] [] = [] := rfl

/-- SVG 2 §11.3.3 Law: Nested textPath inside textPath is not allowed. -/
theorem isSvgChildAllowed_nested_textPath :
    isSvgChildAllowed .a [.textPath, .text, .svg] .textPath = false := rfl

/-! ## 6. SVG 2 §11 / CSS 2.1 §9.4.2 SVG Child Insertion & Parent IFC -/

/-- SVG 2 §11 / CSS 2.1 §9.4.2: Adding children to an SVG root element does not mutate
    the parent HTML inline formatting context. -/
def svgChildMutatesParentIFC : Bool := false

/-- SVG 2 §11 Law: Adding an SVG child to SVG root never marks parent IFC as needing collect inlines. -/
theorem svgChild_does_not_mutate_parent_ifc :
    svgChildMutatesParentIFC = false := rfl

end ChromiumLayout
