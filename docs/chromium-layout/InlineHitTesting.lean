import InlineGeometry
import InlineFragmentItem
import InlineSVG

namespace ChromiumLayout

/-! ## Hit Testing and Occlusion Model
    Specifications:
    - CSSOM View Module §8 Hit Testing (Rect-based hit testing, occlusion testing)
    - CSS 2.1 §9.9 & Appendix E Layered Presentation (Paint order, stacking contexts)
    - CSS Transforms Module Level 2 §4 (3D Transforms, `preserve-3d`, flattening, perspective projection)
    - CSS Masking Module Level 1 §3 (Clipping paths and hit testing: `clip-path`)
    - CSS Backgrounds and Borders Module Level 3 §7.1 (Border shapes hit testing)
    - CSS Filter Effects Module Level 1 §3.1 (Filter margins, visual overflow rect)
    - CSS Overflow Module Level 3 §3 (Scrolling, line boxes hit testing)
    Blink reference:
    - `third_party/blink/renderer/core/layout/hit_testing_test.cc`
    - `third_party/blink/renderer/core/input/event_handler.cc`
    - `third_party/blink/renderer/core/layout/layout_box.cc`
-/

/-- Transform style for 3D stacking contexts (CSS Transforms 2 §4). -/
inductive TransformStyle where
  | flat
  | preserve3d
  deriving DecidableEq, Repr, Inhabited

/-- Integer clamp helper. -/
def intClamp (val low high : Int) : Int :=
  if val < low then low
  else if val > high then high
  else val

/-- 2D box occlusion test (CSSOM View §8, CSS 2.1 §9.9).
    When an occluder box lies in front of target in stacking/DOM order,
    it occludes target if their visual rects intersect. -/
def occludes2D (target occluder : PhysicalRect) : Bool :=
  rectsIntersect target occluder

/-- Circular clip-path occlusion test (CSS Masking 1 §3, CSSOM View §8).
    Checks if occluder clipped by circle(cx, cy, r) intersects target. -/
def occludesWithClipCircle (target occ : PhysicalRect) (cx cy r : Nat) : Bool :=
  if !rectsIntersect target occ then false
  else
    let x_min := Nat.max target.x occ.x
    let x_max := Nat.min (target.x + target.width) (occ.x + occ.width)
    let y_min := Nat.max target.y occ.y
    let y_max := Nat.min (target.y + target.height) (occ.y + occ.height)
    let center_x : Int := (occ.x : Int) + (cx : Int)
    let center_y : Int := (occ.y : Int) + (cy : Int)
    let clamped_x := intClamp center_x (x_min : Int) (x_max : Int)
    let clamped_y := intClamp center_y (y_min : Int) (y_max : Int)
    let dx := center_x - clamped_x
    let dy := center_y - clamped_y
    (dx * dx + dy * dy : Int) <= (r : Int) * (r : Int)

/-- Circular border-shape stroke mode occlusion test (CSS Backgrounds and Borders 3 §7.1, CSSOM View §8). -/
def occludesWithBorderShapeCircle (target occ : PhysicalRect) (cx cy outerRadius : Nat) : Bool :=
  let center_x : Int := (occ.x : Int) + (cx : Int)
  let center_y : Int := (occ.y : Int) + (cy : Int)
  let clamped_x := intClamp center_x (target.x : Int) ((target.x + target.width : Nat) : Int)
  let clamped_y := intClamp center_y (target.y : Int) ((target.y + target.height : Nat) : Int)
  let dx := center_x - clamped_x
  let dy := center_y - clamped_y
  (dx * dx + dy * dy : Int) <= (outerRadius : Int) * (outerRadius : Int)

/-- Diamond border-shape fill mode occlusion test (CSS Backgrounds and Borders 3 §7.1, CSSOM View §8). -/
def occludesWithBorderShapeDiamond (target occ : PhysicalRect) (threshold : Nat) : Bool :=
  let cx := (occ.x : Int) + 50
  let cy := (occ.y : Int) + 50
  let tx := if ((target.x + target.width : Nat) : Int) < cx then ((target.x + target.width : Nat) : Int) else cx
  let ty := if ((target.y + target.height : Nat) : Int) < cy then ((target.y + target.height : Nat) : Int) else cy
  let d := (cx - tx).natAbs + (cy - ty).natAbs
  d <= threshold

/-- List-based hit testing with stopper callback (CSSOM View §8).
    Stops hit testing upon reaching `stopNode`. -/
def hitTestWithStopper (candidates : List String) (stopNode : String) : List String × Bool :=
  let rec loop (acc : List String) : List String → List String × Bool
    | [] => (acc.reverse, false)
    | x :: xs =>
      if x == stopNode then
        ((x :: acc).reverse, true)
      else
        loop (x :: acc) xs
  loop [] candidates

/-- Prefix length sum for text line hit testing. -/
def sumPrefixLengths : Nat → List Nat → Nat
  | _, [] => 0
  | 0, _ => 0
  | n + 1, l :: ls => l + sumPrefixLengths n ls

/-- Hit test a scrolled inline text container (CSS Overflow 3 §3, CSSOM View §8).
    Translates query point by scrollTop, determines the line index from lineHeight,
    and returns the character start offset of that line. -/
def hitTestScrolledLine (scrollTop : Nat) (queryY : Nat) (lineHeight : Nat) (lineLengths : List Nat) : Nat :=
  let scrolledY := queryY + scrollTop
  let lineIdx := if lineHeight > 0 then scrolledY / lineHeight else 0
  sumPrefixLengths lineIdx lineLengths

/-- Visual overflow rect including filter effects (CSS Filter Effects 1 §3.1).
    Computes visual overflow by applying filter margin expansion to content rect. -/
def filterVisualOverflowRect (content : PhysicalRect) (margin : Int) : Int × Int × Nat × Nat :=
  let x := (content.x : Int) - margin
  let y := (content.y : Int) - margin
  let w := (content.width : Int) + 2 * margin
  let h := (content.height : Int) + 2 * margin
  (x, y, w.toNat, h.toNat)

/-- Compute max z coordinate under translation and Y rotation (CSS Transforms 2 §4).
    `z_max = translateZ + halfWidth * sinNum / sinDenom`. -/
def maxZUnderYRotation (translateZ : Int) (halfWidth : Nat) (sinNum sinDenom : Nat) : Int :=
  if halfWidth == 0 || sinDenom == 0 then translateZ
  else translateZ + ((halfWidth : Int) * (sinNum : Int)) / (sinDenom : Int)

/-- 3D Occlusion hit testing (CSS Transforms 2 §4, CSS 2.1 §9.9, CSSOM View §8).
    In a 3D context (preserve-3d), an occluder in front (maxZ > 0) occludes target.
    In a flat context, 3D translations are flattened to 2D (z=0), so DOM/paint order
    determines occlusion when 2D rects intersect. -/
def occludes3D (parentStyle : TransformStyle) (occluderLaterInDOM : Bool)
    (rect2DOverlap : Bool) (translateZ : Int) (halfWidth : Nat) (sinNum sinDenom : Nat) : Bool :=
  if !rect2DOverlap then false
  else match parentStyle with
  | TransformStyle.flat => occluderLaterInDOM
  | TransformStyle.preserve3d =>
    maxZUnderYRotation translateZ halfWidth sinNum sinDenom > 0

/-! ## General Laws for Hit Testing and Occlusion -/

/-- For an empty candidate list, stopper hit testing returns empty results and didStop = false. -/
theorem hit_test_with_stopper_empty (stopNode : String) :
    hitTestWithStopper [] stopNode = ([], false) := by
  rfl

/-- With zero filter margin, visual overflow rect coincides with content rect. -/
theorem filter_visual_overflow_zero (content : PhysicalRect) :
    filterVisualOverflowRect content 0 = ((content.x : Int), (content.y : Int), content.width, content.height) := by
  dsimp [filterVisualOverflowRect]
  simp

/-- In a flat context with 2D overlap and later DOM order, occluder always occludes regardless of z translation. -/
theorem occludes_3d_zero_offset (tz : Int) (hw sn sd : Nat) :
    occludes3D TransformStyle.flat true true tz hw sn sd = true := by
  rfl

/-- At the scroll origin (scrollTop = 0), querying a point before the first line break yields character offset 0. -/
theorem hit_test_scrolled_line_origin (qy lh : Nat) (h : qy < lh) (lines : List Nat) :
    hitTestScrolledLine 0 qy lh lines = 0 := by
  dsimp [hitTestScrolledLine]
  have hpos : lh > 0 := by omega
  have hdiv : qy / lh = 0 := Nat.div_eq_of_lt h
  split
  · rw [hdiv]
    cases lines <;> rfl
  · contradiction

/-! ## 6. CSS Filter Effects 1 §3.1 & SVG 2 §15.2 Occluding SVG Text Hit Testing -/

/-- Compute physical rect of filtered visual overflow bounding box. -/
def filteredVisualOverflowPhysicalRect (content : PhysicalRect) (filterMargin : Nat) : PhysicalRect :=
  let (fx, fy, fw, fh) := filterVisualOverflowRect content filterMargin
  { x := if fx < 0 then 0 else fx.toNat,
    y := if fy < 0 then 0 else fy.toNat,
    width := fw, height := fh }

/-- CSS Filter Effects 1 §3.1, CSS 2.1 §9.9 & SVG 2 §15.2:
    Hit testing an SVG text element occluded by a filtered element.
    When an occluder's filtered visual overflow rect intersects the target rect,
    the inner text node of the occluder is identified as the occluding node. -/
def hitTestOccludingSvgTextNode (targetRect occluderContent : PhysicalRect) (filterMargin : Nat) (textNodeId : String) : Option String :=
  let filteredRect := filteredVisualOverflowPhysicalRect occluderContent filterMargin
  if rectsIntersect targetRect filteredRect then some textNodeId
  else none

/-- CSS Filter Effects 1 §3.1 & SVG 2 §15.2 Law: Occluding SVG text with intersecting filter overflow returns occluder text node. -/
theorem hitTestOccludingSvgTextNode_intersects (target occ : PhysicalRect) (fm : Nat) (id : String)
    (h : rectsIntersect target (filteredVisualOverflowPhysicalRect occ fm) = true) :
    hitTestOccludingSvgTextNode target occ fm id = some id := by
  dsimp [hitTestOccludingSvgTextNode]
  rw [h]
  rfl

end ChromiumLayout
