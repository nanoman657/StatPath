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

end ChromiumLayout
