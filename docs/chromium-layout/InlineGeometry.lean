/-
  docs/chromium-layout/InlineGeometry.lean

  Formal model for Blink Layout Geometry
  (`third_party/blink/renderer/core/layout/geometry/`).

  Owns:
  - LogicalAxes and PhysicalAxes conversions (`axis.h`)
  - BoxSides mapping between physical and logical directions (`box_sides.h`)
  - BoxEdge 1D geometry (`box_edge.h`)
  - BoxStrut and PhysicalBoxStrut coordinate transformations (`box_strut.h`)
  - WritingModeConverter 2D offset mapping (`writing_mode_converter.h`)
  - LogicalRect and PhysicalRect 2D geometric operations (`logical_rect.h`, `physical_rect.h`)
  - LayoutUnitDiffuser fractional distribution (`layout_unit_diffuser.h`)
-/
import LayoutTypes
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 0. Writing Mode and Direction -/

inductive WritingMode where
  | horizontalTb
  | verticalRl
  | verticalLr
  | sidewaysRl
  | sidewaysLr
  deriving DecidableEq, Repr, Inhabited

inductive TextDirection where
  | ltr
  | rtl
  deriving DecidableEq, Repr, Inhabited

/-! ## 1. Axes Model (`geometry/axis.h`) -/

inductive LogicalAxes where
  | none
  | inline
  | block
  | both
  deriving DecidableEq, Repr, Inhabited

inductive PhysicalAxes where
  | none
  | horizontal
  | vertical
  | both
  deriving DecidableEq, Repr, Inhabited

/-- Convert LogicalAxes to PhysicalAxes for a given writing mode (`ToPhysicalAxes`). -/
def toPhysicalAxes (axes : LogicalAxes) (wm : WritingMode) : PhysicalAxes :=
  match wm with
  | .horizontalTb =>
    match axes with
    | .none => .none
    | .inline => .horizontal
    | .block => .vertical
    | .both => .both
  | .verticalRl | .verticalLr | .sidewaysRl | .sidewaysLr =>
    match axes with
    | .none => .none
    | .inline => .vertical
    | .block => .horizontal
    | .both => .both

/-- Convert PhysicalAxes to LogicalAxes for a given writing mode (`ToLogicalAxes`). -/
def toLogicalAxes (axes : PhysicalAxes) (wm : WritingMode) : LogicalAxes :=
  match wm with
  | .horizontalTb =>
    match axes with
    | .none => .none
    | .horizontal => .inline
    | .vertical => .block
    | .both => .both
  | .verticalRl | .verticalLr | .sidewaysRl | .sidewaysLr =>
    match axes with
    | .none => .none
    | .horizontal => .block
    | .vertical => .inline
    | .both => .both

/-! ## 1b. Axes Bitwise Operators (`geometry/axis.h`) -/

def LogicalAxes.hasInline (a : LogicalAxes) : Bool :=
  a == .inline || a == .both

def LogicalAxes.hasBlock (a : LogicalAxes) : Bool :=
  a == .block || a == .both

def LogicalAxes.fromBools (i b : Bool) : LogicalAxes :=
  match i, b with
  | false, false => .none
  | true, false => .inline
  | false, true => .block
  | true, true => .both

def LogicalAxes.or (a1 a2 : LogicalAxes) : LogicalAxes :=
  LogicalAxes.fromBools (a1.hasInline || a2.hasInline) (a1.hasBlock || a2.hasBlock)

def LogicalAxes.and (a1 a2 : LogicalAxes) : LogicalAxes :=
  LogicalAxes.fromBools (a1.hasInline && a2.hasInline) (a1.hasBlock && a2.hasBlock)

def LogicalAxes.xor (a1 a2 : LogicalAxes) : LogicalAxes :=
  LogicalAxes.fromBools (a1.hasInline != a2.hasInline) (a1.hasBlock != a2.hasBlock)

def LogicalAxes.sub (a1 a2 : LogicalAxes) : LogicalAxes :=
  LogicalAxes.fromBools (a1.hasInline && !a2.hasInline) (a1.hasBlock && !a2.hasBlock)

instance : HOr LogicalAxes LogicalAxes LogicalAxes where hOr := LogicalAxes.or
instance : HAnd LogicalAxes LogicalAxes LogicalAxes where hAnd := LogicalAxes.and
instance : HXor LogicalAxes LogicalAxes LogicalAxes where hXor := LogicalAxes.xor
instance : HSub LogicalAxes LogicalAxes LogicalAxes where hSub := LogicalAxes.sub

def PhysicalAxes.hasHorizontal (a : PhysicalAxes) : Bool :=
  a == .horizontal || a == .both

def PhysicalAxes.hasVertical (a : PhysicalAxes) : Bool :=
  a == .vertical || a == .both

def PhysicalAxes.fromBools (h v : Bool) : PhysicalAxes :=
  match h, v with
  | false, false => .none
  | true, false => .horizontal
  | false, true => .vertical
  | true, true => .both

def PhysicalAxes.or (a1 a2 : PhysicalAxes) : PhysicalAxes :=
  PhysicalAxes.fromBools (a1.hasHorizontal || a2.hasHorizontal) (a1.hasVertical || a2.hasVertical)

def PhysicalAxes.and (a1 a2 : PhysicalAxes) : PhysicalAxes :=
  PhysicalAxes.fromBools (a1.hasHorizontal && a2.hasHorizontal) (a1.hasVertical && a2.hasVertical)

def PhysicalAxes.xor (a1 a2 : PhysicalAxes) : PhysicalAxes :=
  PhysicalAxes.fromBools (a1.hasHorizontal != a2.hasHorizontal) (a1.hasVertical != a2.hasVertical)

def PhysicalAxes.sub (a1 a2 : PhysicalAxes) : PhysicalAxes :=
  PhysicalAxes.fromBools (a1.hasHorizontal && !a2.hasHorizontal) (a1.hasVertical && !a2.hasVertical)

instance : HOr PhysicalAxes PhysicalAxes PhysicalAxes where hOr := PhysicalAxes.or
instance : HAnd PhysicalAxes PhysicalAxes PhysicalAxes where hAnd := PhysicalAxes.and
instance : HXor PhysicalAxes PhysicalAxes PhysicalAxes where hXor := PhysicalAxes.xor
instance : HSub PhysicalAxes PhysicalAxes PhysicalAxes where hSub := PhysicalAxes.sub

/-- General Law: LogicalAxes and operation distributes over or. -/
theorem logicalAxes_and_distrib_or (a b c : LogicalAxes) :
    a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- General Law: PhysicalAxes and operation distributes over or. -/
theorem physicalAxes_and_distrib_or (a b c : PhysicalAxes) :
    a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- General Law: LogicalAxes difference with itself is none. -/
theorem logicalAxes_sub_self (a : LogicalAxes) :
    a - a = .none := by
  cases a <;> rfl

/-- General Law: PhysicalAxes difference with itself is none. -/
theorem physicalAxes_sub_self (a : PhysicalAxes) :
    a - a = .none := by
  cases a <;> rfl

/-! ## 2. Box Sides Model (`geometry/box_sides.h`) -/

structure LogicalBoxSides where
  inlineStart : Bool := true
  inlineEnd : Bool := true
  blockStart : Bool := true
  blockEnd : Bool := true
  deriving DecidableEq, Repr, Inhabited

structure PhysicalBoxSides where
  top : Bool := true
  right : Bool := true
  bottom : Bool := true
  left : Bool := true
  deriving DecidableEq, Repr, Inhabited

structure LineLogicalBoxSides where
  lineLeft : Bool := true
  lineRight : Bool := true
  blockStart : Bool := true
  blockEnd : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Convert LogicalBoxSides to LineLogicalBoxSides (`LineLogicalBoxSides(sides, direction)`). -/
def logicalBoxSidesToLineLogical (sides : LogicalBoxSides) (dir : TextDirection) : LineLogicalBoxSides :=
  match dir with
  | .ltr => { lineLeft := sides.inlineStart, lineRight := sides.inlineEnd, blockStart := sides.blockStart, blockEnd := sides.blockEnd }
  | .rtl => { lineLeft := sides.inlineEnd, lineRight := sides.inlineStart, blockStart := sides.blockStart, blockEnd := sides.blockEnd }

/-- Convert PhysicalBoxSides to LogicalBoxSides (`PhysicalBoxSides::ToLogical`). -/
def physicalBoxSidesToLogical (sides : PhysicalBoxSides) (wm : WritingMode) (dir : TextDirection) : LogicalBoxSides :=
  match wm with
  | .horizontalTb =>
    match dir with
    | .ltr => { inlineStart := sides.left, inlineEnd := sides.right, blockStart := sides.top, blockEnd := sides.bottom }
    | .rtl => { inlineStart := sides.right, inlineEnd := sides.left, blockStart := sides.top, blockEnd := sides.bottom }
  | .verticalRl =>
    match dir with
    | .ltr => { inlineStart := sides.top, inlineEnd := sides.bottom, blockStart := sides.right, blockEnd := sides.left }
    | .rtl => { inlineStart := sides.bottom, inlineEnd := sides.top, blockStart := sides.right, blockEnd := sides.left }
  | .verticalLr =>
    match dir with
    | .ltr => { inlineStart := sides.top, inlineEnd := sides.bottom, blockStart := sides.left, blockEnd := sides.right }
    | .rtl => { inlineStart := sides.bottom, inlineEnd := sides.top, blockStart := sides.left, blockEnd := sides.right }
  | .sidewaysRl =>
    match dir with
    | .ltr => { inlineStart := sides.top, inlineEnd := sides.bottom, blockStart := sides.right, blockEnd := sides.left }
    | .rtl => { inlineStart := sides.bottom, inlineEnd := sides.top, blockStart := sides.right, blockEnd := sides.left }
  | .sidewaysLr =>
    match dir with
    | .ltr => { inlineStart := sides.bottom, inlineEnd := sides.top, blockStart := sides.left, blockEnd := sides.right }
    | .rtl => { inlineStart := sides.top, inlineEnd := sides.bottom, blockStart := sides.left, blockEnd := sides.right }

/-! ## 3. Box Edge Model (`geometry/box_edge.h`) -/

structure BoxEdge where
  offset : Int := 0
  size : Int := 0
  deriving DecidableEq, Repr, Inhabited

def BoxEdge.endOffset (e : BoxEdge) : Int :=
  e.offset + e.size

def BoxEdge.isEmpty (e : BoxEdge) : Bool :=
  e.size ≤ 0

def BoxEdge.move (e : BoxEdge) (delta : Int) : BoxEdge :=
  { e with offset := e.offset + delta }

/-! ## 4. Box Strut Model (`geometry/box_strut.h`) -/

structure PhysicalBoxStrut where
  top : Nat := 0
  right : Nat := 0
  bottom : Nat := 0
  left : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Convert PhysicalBoxStrut to BoxStrut (`PhysicalBoxStrut::ConvertToLogical`). -/
def physicalStrutToLogical (strut : PhysicalBoxStrut) (wm : WritingMode) (dir : TextDirection) : BoxStrut :=
  match wm with
  | .horizontalTb =>
    match dir with
    | .ltr => { inlineStart := strut.left, inlineEnd := strut.right, blockStart := strut.top, blockEnd := strut.bottom }
    | .rtl => { inlineStart := strut.right, inlineEnd := strut.left, blockStart := strut.top, blockEnd := strut.bottom }
  | .verticalRl =>
    match dir with
    | .ltr => { inlineStart := strut.top, inlineEnd := strut.bottom, blockStart := strut.right, blockEnd := strut.left }
    | .rtl => { inlineStart := strut.bottom, inlineEnd := strut.top, blockStart := strut.right, blockEnd := strut.left }
  | .verticalLr =>
    match dir with
    | .ltr => { inlineStart := strut.top, inlineEnd := strut.bottom, blockStart := strut.left, blockEnd := strut.right }
    | .rtl => { inlineStart := strut.bottom, inlineEnd := strut.top, blockStart := strut.left, blockEnd := strut.right }
  | .sidewaysRl =>
    match dir with
    | .ltr => { inlineStart := strut.top, inlineEnd := strut.bottom, blockStart := strut.right, blockEnd := strut.left }
    | .rtl => { inlineStart := strut.bottom, inlineEnd := strut.top, blockStart := strut.right, blockEnd := strut.left }
  | .sidewaysLr =>
    match dir with
    | .ltr => { inlineStart := strut.bottom, inlineEnd := strut.top, blockStart := strut.left, blockEnd := strut.right }
    | .rtl => { inlineStart := strut.top, inlineEnd := strut.bottom, blockStart := strut.left, blockEnd := strut.right }

/-- Convert BoxStrut to PhysicalBoxStrut (`BoxStrut::ConvertToPhysical`). -/
def logicalStrutToPhysical (strut : BoxStrut) (wm : WritingMode) (dir : TextDirection) : PhysicalBoxStrut :=
  match wm with
  | .horizontalTb =>
    match dir with
    | .ltr => { left := strut.inlineStart, right := strut.inlineEnd, top := strut.blockStart, bottom := strut.blockEnd }
    | .rtl => { right := strut.inlineStart, left := strut.inlineEnd, top := strut.blockStart, bottom := strut.blockEnd }
  | .verticalRl =>
    match dir with
    | .ltr => { top := strut.inlineStart, bottom := strut.inlineEnd, right := strut.blockStart, left := strut.blockEnd }
    | .rtl => { bottom := strut.inlineStart, top := strut.inlineEnd, right := strut.blockStart, left := strut.blockEnd }
  | .verticalLr =>
    match dir with
    | .ltr => { top := strut.inlineStart, bottom := strut.inlineEnd, left := strut.blockStart, right := strut.blockEnd }
    | .rtl => { bottom := strut.inlineStart, top := strut.inlineEnd, left := strut.blockStart, right := strut.blockEnd }
  | .sidewaysRl =>
    match dir with
    | .ltr => { top := strut.inlineStart, bottom := strut.inlineEnd, right := strut.blockStart, left := strut.blockEnd }
    | .rtl => { bottom := strut.inlineStart, top := strut.inlineEnd, right := strut.blockStart, left := strut.blockEnd }
  | .sidewaysLr =>
    match dir with
    | .ltr => { bottom := strut.inlineStart, top := strut.inlineEnd, left := strut.blockStart, right := strut.blockEnd }
    | .rtl => { top := strut.inlineStart, bottom := strut.inlineEnd, left := strut.blockStart, right := strut.blockEnd }

/-- Unite two physical box struts taking maximum along each edge (`PhysicalBoxStrut::Unite`). -/
def physicalStrutUnite (s1 s2 : PhysicalBoxStrut) : PhysicalBoxStrut :=
  { top := Nat.max s1.top s2.top
  , right := Nat.max s1.right s2.right
  , bottom := Nat.max s1.bottom s2.bottom
  , left := Nat.max s1.left s2.left }

/-! ## 5. WritingModeConverter Model (`geometry/writing_mode_converter.h`) -/

structure PhysicalSize where
  width : Nat := 0
  height : Nat := 0
  deriving DecidableEq, Repr, Inhabited

structure PhysicalOffset where
  left : Nat := 0
  top : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Convert LogicalOffset to PhysicalOffset (`WritingModeConverter::ToPhysical`). -/
def logicalToPhysicalOffset (wm : WritingMode) (dir : TextDirection) (outerSize innerSize : PhysicalSize) (offset : LogicalOffset) : PhysicalOffset :=
  match wm with
  | .horizontalTb =>
    match dir with
    | .ltr => { left := offset.inlineOffset, top := offset.blockOffset }
    | .rtl => { left := outerSize.width - innerSize.width - offset.inlineOffset, top := offset.blockOffset }
  | .verticalRl | .sidewaysRl =>
    match dir with
    | .ltr => { left := outerSize.width - innerSize.width - offset.blockOffset, top := offset.inlineOffset }
    | .rtl => { left := outerSize.width - innerSize.width - offset.blockOffset, top := outerSize.height - innerSize.height - offset.inlineOffset }
  | .verticalLr =>
    match dir with
    | .ltr => { left := offset.blockOffset, top := offset.inlineOffset }
    | .rtl => { left := offset.blockOffset, top := outerSize.height - innerSize.height - offset.inlineOffset }
  | .sidewaysLr =>
    match dir with
    | .ltr => { left := offset.blockOffset, top := outerSize.height - innerSize.height - offset.inlineOffset }
    | .rtl => { left := offset.blockOffset, top := offset.inlineOffset }

/-- Convert PhysicalOffset to LogicalOffset (`WritingModeConverter::ToLogical`). -/
def physicalToLogicalOffset (wm : WritingMode) (dir : TextDirection) (outerSize innerSize : PhysicalSize) (offset : PhysicalOffset) : LogicalOffset :=
  match wm with
  | .horizontalTb =>
    match dir with
    | .ltr => { inlineOffset := offset.left, blockOffset := offset.top }
    | .rtl => { inlineOffset := outerSize.width - innerSize.width - offset.left, blockOffset := offset.top }
  | .verticalRl | .sidewaysRl =>
    match dir with
    | .ltr => { inlineOffset := offset.top, blockOffset := outerSize.width - innerSize.width - offset.left }
    | .rtl => { inlineOffset := outerSize.height - innerSize.height - offset.top, blockOffset := outerSize.width - innerSize.width - offset.left }
  | .verticalLr =>
    match dir with
    | .ltr => { inlineOffset := offset.top, blockOffset := offset.left }
    | .rtl => { inlineOffset := outerSize.height - innerSize.height - offset.top, blockOffset := offset.left }
  | .sidewaysLr =>
    match dir with
    | .ltr => { inlineOffset := outerSize.height - innerSize.height - offset.top, blockOffset := offset.left }
    | .rtl => { inlineOffset := offset.top, blockOffset := offset.left }

/-! ## 6. Logical and Physical Rect Operations (`geometry/logical_rect.h`, `physical_rect.h`) -/

structure LogicalRect where
  offset : LogicalOffset := {}
  size : LogicalSize := {}
  deriving DecidableEq, Repr, Inhabited

def LogicalRect.addOffset (r : LogicalRect) (o : LogicalOffset) : LogicalRect :=
  { offset := { inlineOffset := r.offset.inlineOffset + o.inlineOffset
              , blockOffset := r.offset.blockOffset + o.blockOffset }
  , size := r.size }

def LogicalRect.unite (r1 r2 : LogicalRect) : LogicalRect :=
  if r1.size.inlineSize == 0 && r1.size.blockSize == 0 then r2
  else if r2.size.inlineSize == 0 && r2.size.blockSize == 0 then r1
  else
    let minInline := Nat.min r1.offset.inlineOffset r2.offset.inlineOffset
    let minBlock := Nat.min r1.offset.blockOffset r2.offset.blockOffset
    let maxInline := Nat.max (r1.offset.inlineOffset + r1.size.inlineSize) (r2.offset.inlineOffset + r2.size.inlineSize)
    let maxBlock := Nat.max (r1.offset.blockOffset + r1.size.blockSize) (r2.offset.blockOffset + r2.size.blockSize)
    { offset := { inlineOffset := minInline, blockOffset := minBlock }
    , size := { inlineSize := maxInline - minInline, blockSize := maxBlock - minBlock } }

def PhysicalRect.addOffset (r : PhysicalRect) (xOffset yOffset : Nat) : PhysicalRect :=
  { r with x := r.x + xOffset, y := r.y + yOffset }

def PhysicalRect.squaredDistanceTo (r : PhysicalRect) (px py : Nat) : Nat :=
  let dx := if px < r.x then r.x - px else if px > r.x + r.width then px - (r.x + r.width) else 0
  let dy := if py < r.y then r.y - py else if py > r.y + r.height then py - (r.y + r.height) else 0
  dx * dx + dy * dy

def PhysicalRect.intersectsInclusively (r1 r2 : PhysicalRect) : Bool :=
  r1.x ≤ r2.x + r2.width && r2.x ≤ r1.x + r1.width &&
  r1.y ≤ r2.y + r2.height && r2.y ≤ r1.y + r1.height

def PhysicalRect.inclusiveIntersect (r1 r2 : PhysicalRect) : PhysicalRect :=
  if !r1.intersectsInclusively r2 then {}
  else
    let left := Nat.max r1.x r2.x
    let top := Nat.max r1.y r2.y
    let right := Nat.min (r1.x + r1.width) (r2.x + r2.width)
    let bottom := Nat.min (r1.y + r1.height) (r2.y + r2.height)
    { x := left, y := top, width := right - left, height := bottom - top }

/-! ## 7. LayoutUnitDiffuser Model (`geometry/layout_unit_diffuser.h`) -/

/-- Structurally recursive helper for Bresenham diffusion over buckets. -/
def diffuseRemainderAux (dx dy : Nat) : Nat → Nat → Nat → List Bool
  | 0, _, _ => []
  | count + 1, x, y =>
    let x' := x + dx
    if x' ≥ y then
      true :: diffuseRemainderAux dx dy count x' (y + dy)
    else
      false :: diffuseRemainderAux dx dy count x' y

/-- Diffuses fractional remainder evenly across N buckets using Bresenham stepping (`LayoutUnitDiffuser`). -/
def diffuseRemainder (remainder : Nat) (buckets : Nat) : List Bool :=
  diffuseRemainderAux (remainder * 2) (buckets * 2) buckets 0 buckets

/-- General Law: Helper produces output of length equal to count. -/
theorem diffuseRemainderAux_length (dx dy count x y : Nat) :
    (diffuseRemainderAux dx dy count x y).length = count := by
  induction count generalizing x y with
  | zero => rfl
  | succ n ih =>
    dsimp [diffuseRemainderAux]
    split <;> simp [ih]

/-- General Law: Diffuser length equals bucket count. -/
theorem diffuseRemainder_length (rem buckets : Nat) :
    (diffuseRemainder rem buckets).length = buckets := by
  dsimp [diffuseRemainder]
  apply diffuseRemainderAux_length

/-! ## 8. Fixed-Point Pixel Snapping and Enclosing (`geometry/physical_rect.h`) -/

structure LayoutUnitRect where
  x : Int := 0
  y : Int := 0
  width : Int := 0
  height : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Check if a 64th-fractional LayoutUnit raw value is on an integer pixel boundary (`raw % 64 == 0`). -/
def isPixelBoundary (raw : Int) : Bool :=
  raw % 64 == 0

/-- Check if all edges of a LayoutUnitRect are on integer pixel boundaries (`PhysicalRect::EdgesOnPixelBoundaries`). -/
def edgesOnPixelBoundaries (r : LayoutUnitRect) : Bool :=
  isPixelBoundary r.x && isPixelBoundary r.y && isPixelBoundary r.width && isPixelBoundary r.height

/-- Compute floor in pixel units of a 64th-fractional LayoutUnit raw value (`value_ >> 6`). -/
def floorPixel (raw : Int) : Int :=
  raw >>> 6

/-- Compute ceil in pixel units of a 64th-fractional LayoutUnit raw value (`(value_ + 63) >> 6`). -/
def ceilPixel (raw : Int) : Int :=
  (raw + 63) >>> 6

/-- Compute enclosing integer pixel rectangle (`ToEnclosingRect`). -/
def toEnclosingRect (r : LayoutUnitRect) : LayoutUnitRect :=
  let left := floorPixel r.x
  let top := floorPixel r.y
  let right := ceilPixel (r.x + r.width)
  let bottom := ceilPixel (r.y + r.height)
  { x := left, y := top, width := right - left, height := bottom - top }

/-- Expand edges to integer pixel boundaries in LayoutUnit scale (`ExpandEdgesToPixelBoundaries`). -/
def expandEdgesToPixelBoundaries (r : LayoutUnitRect) : LayoutUnitRect :=
  toEnclosingRect r

/-- Max-bounded integer rectangle (`InfiniteIntRect`). -/
def infiniteIntRect : LayoutUnitRect :=
  { x := -10000000, y := -10000000, width := 20000000, height := 20000000 }

/-- Check if a rectangle encloses another rectangle. -/
def LayoutUnitRect.encloses (r1 r2 : LayoutUnitRect) : Bool :=
  r1.x ≤ r2.x && r1.y ≤ r2.y &&
  r1.x + r1.width ≥ r2.x + r2.width &&
  r1.y + r1.height ≥ r2.y + r2.height

/-- General Law: Zero LayoutUnit raw has floor 0 and ceil 0. -/
theorem pixel_zero :
    floorPixel 0 = 0 ∧ ceilPixel 0 = 0 := by
  dsimp [floorPixel, ceilPixel]
  decide

/-- General Law: Infinite integer rectangle encloses itself. -/
theorem infiniteIntRect_encloses_self :
    infiniteIntRect.encloses infiniteIntRect = true := by
  decide

end ChromiumLayout
