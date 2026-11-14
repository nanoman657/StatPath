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

/-! ## 5b. Static Position Model (`geometry/static_position.h`, CSS Writing Modes 3 §3 & §4.2, CSS Positioned Layout 3 §4) -/

inductive InlineEdge where
  | inlineStart
  | inlineCenter
  | inlineEnd
  deriving DecidableEq, Repr, Inhabited

inductive BlockEdge where
  | blockStart
  | blockCenter
  | blockEnd
  deriving DecidableEq, Repr, Inhabited

inductive LogicalAlignmentDirection where
  | block
  | inline
  deriving DecidableEq, Repr, Inhabited

structure LogicalStaticPosition where
  offset : LogicalOffset := { inlineOffset := 0, blockOffset := 0 }
  inlineEdge : InlineEdge := .inlineStart
  blockEdge : BlockEdge := .blockStart
  alignSelfDirection : LogicalAlignmentDirection := .block
  deriving DecidableEq, Repr, Inhabited

inductive HorizontalEdge where
  | left
  | horizontalCenter
  | right
  deriving DecidableEq, Repr, Inhabited

inductive VerticalEdge where
  | top
  | verticalCenter
  | bottom
  deriving DecidableEq, Repr, Inhabited

inductive PhysicalAlignmentDirection where
  | horizontal
  | vertical
  deriving DecidableEq, Repr, Inhabited

structure PhysicalStaticPosition where
  offset : PhysicalOffset := { left := 0, top := 0 }
  horizontalEdge : HorizontalEdge := .left
  verticalEdge : VerticalEdge := .top
  alignSelfDirection : PhysicalAlignmentDirection := .vertical
  deriving DecidableEq, Repr, Inhabited

/-- Convert LogicalStaticPosition to PhysicalStaticPosition (`LogicalStaticPosition::ConvertToPhysical`).
    CSS Writing Modes 3 §3 & §4.2, CSS Positioned Layout 3 §4. -/
def logicalToPhysicalStaticPosition (wm : WritingMode) (dir : TextDirection) (outerSize : PhysicalSize)
    (pos : LogicalStaticPosition) : PhysicalStaticPosition :=
  let pOffset := logicalToPhysicalOffset wm dir outerSize { width := 0, height := 0 } pos.offset
  let hEdge : HorizontalEdge :=
    match wm with
    | .horizontalTb =>
      if pos.inlineEdge == .inlineCenter then .horizontalCenter
      else if (pos.inlineEdge == .inlineStart) == (dir == .ltr) then .left
      else .right
    | .verticalRl | .sidewaysRl =>
      if pos.blockEdge == .blockCenter then .horizontalCenter
      else if pos.blockEdge == .blockEnd then .left
      else .right
    | .verticalLr =>
      if pos.blockEdge == .blockCenter then .horizontalCenter
      else if pos.blockEdge == .blockStart then .left
      else .right
    | .sidewaysLr =>
      if pos.blockEdge == .blockCenter then .horizontalCenter
      else if pos.blockEdge == .blockStart then .left
      else .right
  let vEdge : VerticalEdge :=
    match wm with
    | .horizontalTb =>
      if pos.blockEdge == .blockCenter then .verticalCenter
      else if pos.blockEdge == .blockStart then .top
      else .bottom
    | .verticalRl | .sidewaysRl =>
      if pos.inlineEdge == .inlineCenter then .verticalCenter
      else if (pos.inlineEdge == .inlineStart) == (dir == .ltr) then .top
      else .bottom
    | .verticalLr =>
      if pos.inlineEdge == .inlineCenter then .verticalCenter
      else if (pos.inlineEdge == .inlineStart) == (dir == .ltr) then .top
      else .bottom
    | .sidewaysLr =>
      if pos.inlineEdge == .inlineCenter then .verticalCenter
      else if (pos.inlineEdge == .inlineEnd) == (dir == .ltr) then .top
      else .bottom
  let pAlign : PhysicalAlignmentDirection :=
    match wm with
    | .horizontalTb =>
      if pos.alignSelfDirection == .inline then .horizontal else .vertical
    | .verticalRl | .sidewaysRl | .verticalLr | .sidewaysLr =>
      if pos.alignSelfDirection == .inline then .vertical else .horizontal
  { offset := pOffset, horizontalEdge := hEdge, verticalEdge := vEdge, alignSelfDirection := pAlign }

/-- Convert PhysicalStaticPosition to LogicalStaticPosition (`PhysicalStaticPosition::ConvertToLogical`).
    CSS Writing Modes 3 §3 & §4.2, CSS Positioned Layout 3 §4. -/
def physicalToLogicalStaticPosition (wm : WritingMode) (dir : TextDirection) (outerSize : PhysicalSize)
    (pos : PhysicalStaticPosition) : LogicalStaticPosition :=
  let lOffset := physicalToLogicalOffset wm dir outerSize { width := 0, height := 0 } pos.offset
  let iEdge : InlineEdge :=
    match wm with
    | .horizontalTb =>
      if pos.horizontalEdge == .horizontalCenter then .inlineCenter
      else if (pos.horizontalEdge == .left) == (dir == .ltr) then .inlineStart
      else .inlineEnd
    | .verticalRl | .sidewaysRl =>
      if pos.verticalEdge == .verticalCenter then .inlineCenter
      else if (pos.verticalEdge == .top) == (dir == .ltr) then .inlineStart
      else .inlineEnd
    | .verticalLr =>
      if pos.verticalEdge == .verticalCenter then .inlineCenter
      else if (pos.verticalEdge == .top) == (dir == .ltr) then .inlineStart
      else .inlineEnd
    | .sidewaysLr =>
      if pos.verticalEdge == .verticalCenter then .inlineCenter
      else if (pos.verticalEdge == .bottom) == (dir == .ltr) then .inlineStart
      else .inlineEnd
  let bEdge : BlockEdge :=
    match wm with
    | .horizontalTb =>
      if pos.verticalEdge == .verticalCenter then .blockCenter
      else if pos.verticalEdge == .top then .blockStart
      else .blockEnd
    | .verticalRl | .sidewaysRl =>
      if pos.horizontalEdge == .horizontalCenter then .blockCenter
      else if pos.horizontalEdge == .right then .blockStart
      else .blockEnd
    | .verticalLr =>
      if pos.horizontalEdge == .horizontalCenter then .blockCenter
      else if pos.horizontalEdge == .left then .blockStart
      else .blockEnd
    | .sidewaysLr =>
      if pos.horizontalEdge == .horizontalCenter then .blockCenter
      else if pos.horizontalEdge == .left then .blockStart
      else .blockEnd
  let lAlign : LogicalAlignmentDirection :=
    match wm with
    | .horizontalTb =>
      if pos.alignSelfDirection == .horizontal then .inline else .block
    | .verticalRl | .sidewaysRl | .verticalLr | .sidewaysLr =>
      if pos.alignSelfDirection == .horizontal then .block else .inline
  { offset := lOffset, inlineEdge := iEdge, blockEdge := bEdge, alignSelfDirection := lAlign }

/-- General Law: converting logical edges and alignment to physical and back preserves all edges and directions. -/
theorem logicalStaticPosition_edges_roundtrip (wm : WritingMode) (dir : TextDirection)
    (off : LogicalOffset) (ie : InlineEdge) (be : BlockEdge) (al : LogicalAlignmentDirection) :
    let pos : LogicalStaticPosition := { offset := off, inlineEdge := ie, blockEdge := be, alignSelfDirection := al }
    let phys := logicalToPhysicalStaticPosition wm dir { width := 100, height := 100 } pos
    let log := physicalToLogicalStaticPosition wm dir { width := 100, height := 100 } phys
    log.inlineEdge = ie ∧ log.blockEdge = be ∧ log.alignSelfDirection = al := by
  cases wm <;> cases dir <;> cases ie <;> cases be <;> cases al <;> exact ⟨rfl, rfl, rfl⟩

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

/-! ## 9. PhysicalLinesBoundingBox and Quads (`layout_text.h`, CSS Writing Modes 3 §3.1 & CSS 2.1 §10.8) -/

/-- CSS Writing Modes 3 §3.1 & CSS 2.1 §10.8:
    Compute physical lines bounding box of a text fragment across writing modes.
    `wm`: writing mode (.horizontalTb or .verticalRl)
    `lh`: line-height
    `fs`: font-size
    `pad`: container padding
    `containerBlockSize`: container size in block direction (width for vertical-rl, height for horizontal-tb)
    `lineIdx`: 0-indexed line index
    `lineInlineOffset`: inline offset within the line
    `charCount`: number of characters in the text run -/
def computePhysicalLinesBoundingBox (wm : WritingMode) (lh fs pad containerBlockSize : Nat)
    (lineIdx lineInlineOffset charCount : Nat) : LayoutUnitRect :=
  let hl : Int := Int.ofNat ((lh - fs) / 2)
  let padI : Int := Int.ofNat pad
  let fsI : Int := Int.ofNat fs
  let runLenI : Int := Int.ofNat (charCount * fs)
  let lineOffI : Int := Int.ofNat lineInlineOffset
  let lineIdxI : Int := Int.ofNat lineIdx
  let lhI : Int := Int.ofNat lh
  match wm with
  | .horizontalTb =>
    let x := padI + lineOffI
    let y := padI + lineIdxI * lhI + hl
    { x := x, y := y, width := runLenI, height := fsI }
  | .verticalRl =>
    let y := padI + lineOffI
    let containerBI : Int := Int.ofNat containerBlockSize
    let x := containerBI - padI - (lineIdxI + 1) * lhI + hl
    { x := x, y := y, width := fsI, height := runLenI }
  | _ =>
    { x := 0, y := 0, width := 0, height := 0 }

/-! ## 10. General Laws for Bounding Boxes -/

/-- CSS Writing Modes 3 §3.1 Law: Horizontal text bounding box height equals font size. -/
theorem physicalLinesBoundingBox_horizontal_height (lh fs pad cb idx off cc : Nat) :
    (computePhysicalLinesBoundingBox .horizontalTb lh fs pad cb idx off cc).height = Int.ofNat fs := rfl

/-- CSS Writing Modes 3 §3.1 Law: Horizontal text bounding box width equals character count * font size. -/
theorem physicalLinesBoundingBox_horizontal_width (lh fs pad cb idx off cc : Nat) :
    (computePhysicalLinesBoundingBox .horizontalTb lh fs pad cb idx off cc).width = Int.ofNat (cc * fs) := rfl

/-- CSS Writing Modes 3 §3.1 Law: Vertical text bounding box width equals font size. -/
theorem physicalLinesBoundingBox_vertical_width (lh fs pad cb idx off cc : Nat) :
    (computePhysicalLinesBoundingBox .verticalRl lh fs pad cb idx off cc).width = Int.ofNat fs := rfl

/-- CSS Writing Modes 3 §3.1 Law: Vertical text bounding box height equals character count * font size. -/
theorem physicalLinesBoundingBox_vertical_height (lh fs pad cb idx off cc : Nat) :
    (computePhysicalLinesBoundingBox .verticalRl lh fs pad cb idx off cc).height = Int.ofNat (cc * fs) := rfl

/-- Rectangle union for LayoutUnitRect (`PhysicalRect::Unite`). -/
def LayoutUnitRect.union (r1 r2 : LayoutUnitRect) : LayoutUnitRect :=
  if r1.width == 0 && r1.height == 0 then r2
  else if r2.width == 0 && r2.height == 0 then r1
  else
    let minX := min r1.x r2.x
    let minY := min r1.y r2.y
    let maxX := max (r1.x + r1.width) (r2.x + r2.width)
    let maxY := max (r1.y + r1.height) (r2.y + r2.height)
    { x := minX, y := minY, width := maxX - minX, height := maxY - minY }

/-! ## 11. Local Selection Visual Rect (CSS 2.1 §10.8 & CSS Writing Modes 3 §3.1) -/

/-- Build a selection slice from horizontal line selection parameters:
    `lineIdx`, `startGlyph`, `glyphCount`, `hasTrailingBreak` (+1 space), `negativeLeading`, `fontSize`, `lineHeight`. -/
def horizontalSelectionSlice (lineIdx : Int) (startGlyph glyphCount : Int) (hasTrailingBreak : Bool)
    (negativeLeading : Int) (fontSize lineHeight : Int) (startX : Int := 0) : LayoutUnitRect :=
  let inlineOffset := startX + startGlyph * fontSize
  let extra := if hasTrailingBreak then fontSize else 0
  let inlineSize := glyphCount * fontSize + extra
  { x := inlineOffset,
    y := lineIdx * lineHeight + negativeLeading,
    width := inlineSize,
    height := lineHeight }

/-- Build a selection slice from vertical line selection parameters:
    block axis is X (lineIdx * lineHeight), inline axis is Y (startGlyph * fontSize). -/
def verticalSelectionSlice (colIdx : Int) (startGlyph glyphCount : Int) (fontSize lineHeight : Int)
    (startY : Int := 0) : LayoutUnitRect :=
  let inlineOffset := startY + startGlyph * fontSize
  let inlineSize := glyphCount * fontSize
  { x := colIdx * lineHeight,
    y := inlineOffset,
    width := lineHeight,
    height := inlineSize }

/-- Compute the united selection visual rectangle from a list of selection slices. -/
def computeSelectionVisualRect (slices : List LayoutUnitRect) : LayoutUnitRect :=
  match slices with
  | [] => { x := 0, y := 0, width := 0, height := 0 }
  | r :: rs => rs.foldl LayoutUnitRect.union r

/-- CSS 2.1 §10.8 Law: Empty selection slices yield zero rect. -/
theorem computeSelectionVisualRect_nil :
    computeSelectionVisualRect [] = { x := 0, y := 0, width := 0, height := 0 } := rfl

/-- CSS 2.1 §10.8 Law: Single selection slice yields exactly that slice. -/
theorem computeSelectionVisualRect_singleton (r : LayoutUnitRect) :
    computeSelectionVisualRect [r] = r := rfl

/-! ## 12. Draggable Regions (-webkit-app-region, CSS 2.1 §9.4.2 & CSS Writing Modes 3 §3.1) -/

/-- Draggable region mode corresponding to `-webkit-app-region` (`drag`, `no-drag`, `none`). -/
inductive AppRegionMode where
  | drag
  | noDrag
  | none
  deriving DecidableEq, Repr, Inhabited

/-- Draggable region descriptor (`DraggableRegionValue`). -/
structure DraggableRegionValue where
  bounds : LayoutUnitRect
  draggable : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Compute draggable regions for an inline element from its line slices and app-region mode. -/
def computeDraggableRegions (mode : AppRegionMode) (slices : List LayoutUnitRect) : List DraggableRegionValue :=
  match mode with
  | .none => []
  | .drag =>
    match slices with
    | [] => []
    | r :: rs => [{ bounds := rs.foldl LayoutUnitRect.union r, draggable := true }]
  | .noDrag =>
    match slices with
    | [] => []
    | r :: rs => [{ bounds := rs.foldl LayoutUnitRect.union r, draggable := false }]

/-- CSS 2.1 §9.4.2 Law: Elements without app-region property produce no draggable regions. -/
theorem computeDraggableRegions_none (slices : List LayoutUnitRect) :
    computeDraggableRegions .none slices = [] := rfl

/-- CSS 2.1 §9.4.2 Law: Draggable regions for drag mode always have draggable = true. -/
theorem computeDraggableRegions_drag_is_draggable (r : LayoutUnitRect) (rs : List LayoutUnitRect) :
    ∀ region ∈ computeDraggableRegions .drag (r :: rs), region.draggable = true := by
  intro reg h
  dsimp [computeDraggableRegions] at h
  simp only [List.mem_singleton] at h
  subst h
  rfl

/-- CSS 2.1 §9.4.2 Law: Draggable regions for noDrag mode always have draggable = false. -/
theorem computeDraggableRegions_noDrag_not_draggable (r : LayoutUnitRect) (rs : List LayoutUnitRect) :
    ∀ region ∈ computeDraggableRegions .noDrag (r :: rs), region.draggable = false := by
  intro reg h
  dsimp [computeDraggableRegions] at h
  simp only [List.mem_singleton] at h
  subst h
  rfl

/-! ## 13. Inline Hit Testing (CSS 2.1 §9.4.2 & §9.3.1) -/

/-- An inline hit target item with local bounding rectangle and node identifier. -/
structure InlineHitItem where
  nodeId : Nat
  bounds : LayoutUnitRect
  isPositioned : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Check if a 2D point falls within a rectangle. -/
def rectContainsPoint (r : LayoutUnitRect) (x y : Int) : Bool :=
  x ≥ r.x && x < r.x + r.width && y ≥ r.y && y < r.y + r.height

/-- Hit test a sequence of inline items (top-to-bottom / reverse-order for paint order).
    `ignorePositioned`: if true, skips positioned items (normal flow phase). -/
def hitTestInlineItems (containerX containerY : Int) (items : List InlineHitItem)
    (ignorePositioned : Bool) (hitX hitY : Int) : Option Nat :=
  let localX := hitX - containerX
  let localY := hitY - containerY
  let candidates := if ignorePositioned then items.filter (·.isPositioned == false) else items
  match candidates.find? (fun item => rectContainsPoint item.bounds localX localY) with
  | some item => some item.nodeId
  | none => none

/-- Check if a hit test location rectangle intersects a line box (`HitTestCulledInline`). -/
def hitTestCulledInlineIntersects (lineBox : LayoutUnitRect) (hitRect : LayoutUnitRect) : Bool :=
  hitRect.x < lineBox.x + lineBox.width && hitRect.x + hitRect.width > lineBox.x &&
  hitRect.y < lineBox.y + lineBox.height && hitRect.y + hitRect.height > lineBox.y

/-- CSS 2.1 §9.4.2 Law: Empty candidate list yields none for hit testing. -/
theorem hitTestInlineItems_nil (cx cy : Int) (ign : Bool) (hx hy : Int) :
    hitTestInlineItems cx cy [] ign hx hy = none := by
  dsimp [hitTestInlineItems]
  cases ign <;> rfl

/-- CSS 2.1 §9.4.2 Law: Point outside rectangle bounds does not intersect. -/
theorem rectContainsPoint_outside (r : LayoutUnitRect) (x y : Int) (h : x < r.x) :
    rectContainsPoint r x y = false := by
  dsimp [rectContainsPoint]
  have : ¬(x ≥ r.x) := by omega
  simp [this]

end ChromiumLayout
