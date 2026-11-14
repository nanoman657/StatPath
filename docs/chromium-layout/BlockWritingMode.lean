/-
  BlockWritingMode.lean: physical <-> logical box-strut mapping, written from length_utils_test.cc
  (`TestBorders`, `TestPadding`). Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockWritingMode

/-- `writing-mode` (horizontal-tb, vertical-lr, vertical-rl); direction is ltr.
    CSS Writing Modes Level 3 §3.2 Block Flow Direction: the writing-mode property. -/
inductive WritingMode where
  | horizontalTb
  | verticalLr
  | verticalRl
  deriving DecidableEq, Repr

/-- Four physical edge values. -/
structure Phys where
  top : Nat
  right : Nat
  bottom : Nat
  left : Nat
  deriving DecidableEq, Repr

/-- Four logical edge values.
    CSS Writing Modes Level 3 §6.2 Flow-relative Directions. -/
structure Logical where
  inlineStart : Nat
  inlineEnd : Nat
  blockStart : Nat
  blockEnd : Nat
  deriving DecidableEq, Repr

/-- Physical to logical edges (`TestBorders`: vertical-lr gives block-start = left, inline-end =
    bottom, block-end = right, inline-start = top; `TestPadding`: vertical-rl gives block-start =
    right, block-end = left).
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings. -/
def toLogical : WritingMode → Phys → Logical
  | .horizontalTb, p => ⟨p.left, p.right, p.top, p.bottom⟩
  | .verticalLr, p => ⟨p.top, p.bottom, p.left, p.right⟩
  | .verticalRl, p => ⟨p.top, p.bottom, p.right, p.left⟩

/-- Logical to physical edges (inverse of `toLogical`).
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings. -/
def toPhysical : WritingMode → Logical → Phys
  | .horizontalTb, l => ⟨l.blockStart, l.inlineEnd, l.blockEnd, l.inlineStart⟩
  | .verticalLr, l => ⟨l.inlineStart, l.blockEnd, l.inlineEnd, l.blockStart⟩
  | .verticalRl, l => ⟨l.inlineStart, l.blockStart, l.inlineEnd, l.blockEnd⟩

/-- The two mappings are inverse for every writing mode (justifies reading `TestBorders` and
    `TestPadding` as one rule). -/
theorem toPhysical_toLogical (wm : WritingMode) (p : Phys) : toPhysical wm (toLogical wm p) = p := by
  cases wm <;> rfl

/-- Converse direction. -/
theorem toLogical_toPhysical (wm : WritingMode) (l : Logical) : toLogical wm (toPhysical wm l) = l := by
  cases wm <;> rfl

/-- Whether a writing mode is vertical.
    CSS Writing Modes Level 3 §3.2 Block Flow Direction. -/
def isVertical : WritingMode → Bool
  | .horizontalTb => false
  | .verticalLr | .verticalRl => true

/-- Whether a child flow is orthogonal to its containing block.
    CSS Writing Modes Level 3 §7.3 Orthogonal Flows. -/
def isOrthogonal (parent child : WritingMode) : Bool :=
  isVertical parent ≠ isVertical child

/-- Orthogonality is symmetric between two writing modes.
    CSS Writing Modes Level 3 §7.3 Orthogonal Flows. -/
theorem isOrthogonal_symm (wm1 wm2 : WritingMode) : isOrthogonal wm1 wm2 = isOrthogonal wm2 wm1 := by
  cases wm1 <;> cases wm2 <;> decide

/-- Flow block-size: height in horizontal writing modes, width in vertical writing modes.
    CSS Writing Modes Level 3 §6.1 Abstract Dimensions. -/
def flowBlockSize (wm : WritingMode) (w h : Nat) : Nat :=
  match wm with
  | .horizontalTb => h
  | .verticalLr | .verticalRl => w

/-- Flow inline-size: width in horizontal writing modes, height in vertical writing modes.
    CSS Writing Modes Level 3 §6.1 Abstract Dimensions. -/
def flowInlineSize (wm : WritingMode) (w h : Nat) : Nat :=
  match wm with
  | .horizontalTb => w
  | .verticalLr | .verticalRl => h

/-- Flow-relative margins in the container's writing mode.
    CSS Writing Modes Level 3 §7.4 Flow-Relative Mappings. -/
def flowMargins (containerWm : WritingMode) (p : Phys) : Logical :=
  match containerWm with
  | .horizontalTb => ⟨p.left, p.right, p.top, p.bottom⟩
  | .verticalLr => ⟨p.top, p.bottom, p.left, p.right⟩
  | .verticalRl => ⟨p.top, p.bottom, p.right, p.left⟩

/-- Physical offset from flow-relative block and inline offsets.
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings. -/
def flowToPhysicalOffset (containerWm : WritingMode) (containerWidth childBlockSize : Nat)
    (blockOffset inlineOffset : Nat) : Nat × Nat :=
  match containerWm with
  | .horizontalTb => (inlineOffset, blockOffset)
  | .verticalLr => (blockOffset, inlineOffset)
  | .verticalRl => (containerWidth - (blockOffset + childBlockSize), inlineOffset)

/-- An in-flow block item with its writing mode, dimensions, and physical margins.
    CSS Writing Modes Level 3 §7.1, §7.3. -/
structure BlockItem where
  id : Nat := 0
  wm : WritingMode := .horizontalTb
  width : Nat := 0
  height : Nat := 0
  margins : Phys := ⟨0, 0, 0, 0⟩
  deriving DecidableEq, Repr

/-- Placed item fragment with resolved physical position and size. -/
structure PlacedItem where
  id : Nat := 0
  x : Nat := 0
  y : Nat := 0
  width : Nat := 0
  height : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- General block layout across writing modes with margin collapsing.
    CSS Writing Modes Level 3 §7.1, §7.3, §7.4 and CSS 2.1 §8.3.1. -/
def layoutWritingModeBlock (containerWm : WritingMode) (containerWidth : Nat) (items : List BlockItem) :
    List PlacedItem :=
  let rec loop (items : List BlockItem) (curBlockPos : Nat) (prevMarginEnd : Nat) : List PlacedItem :=
    match items with
    | [] => []
    | item :: rest =>
      let fm := flowMargins containerWm item.margins
      let bSize := flowBlockSize containerWm item.width item.height
      let collapsedMargin := Nat.max prevMarginEnd fm.blockStart
      let itemBlockStart := curBlockPos + collapsedMargin
      let itemInlineStart := fm.inlineStart
      let (px, py) := flowToPhysicalOffset containerWm containerWidth bSize itemBlockStart itemInlineStart
      let placed : PlacedItem := { id := item.id, x := px, y := py, width := item.width, height := item.height }
      placed :: loop rest (itemBlockStart + bSize) fm.blockEnd
  loop items 0 0

/-- Law: In vertical-lr block flow, second item's physical x-offset is at least first item's x-offset plus first item's block-size.
    CSS Writing Modes Level 3 §7.1 Principles of Layout in Vertical Writing Modes. -/
theorem layout_two_items_vertical_lr (cw : Nat) (i1 i2 : BlockItem) :
    match layoutWritingModeBlock .verticalLr cw [i1, i2] with
    | [p1, p2] => p2.x ≥ p1.x + flowBlockSize .verticalLr i1.width i1.height
    | _ => False := by
  dsimp [layoutWritingModeBlock, layoutWritingModeBlock.loop, flowToPhysicalOffset]
  omega

/-- Law: In horizontal-tb block flow, second item's physical y-offset is at least first item's y-offset plus first item's block-size.
    CSS 2.1 §8.3.1 & CSS Writing Modes Level 3 §7.1. -/
theorem layout_two_items_horizontal_tb (cw : Nat) (i1 i2 : BlockItem) :
    match layoutWritingModeBlock .horizontalTb cw [i1, i2] with
    | [p1, p2] => p2.y ≥ p1.y + flowBlockSize .horizontalTb i1.width i1.height
    | _ => False := by
  dsimp [layoutWritingModeBlock, layoutWritingModeBlock.loop, flowToPhysicalOffset]
  omega

/-- Physical rect (x, y, w, h) of a box's content box from its border, padding, and logical sizes.
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings, CSS 2.1 §8.1. -/
def physicalContentBox (wm : WritingMode) (border padding : Phys) (inlineSize blockSize : Nat) : Nat × Nat × Nat × Nat :=
  let x := border.left + padding.left
  let y := border.top + padding.top
  let (w, h) := if isVertical wm then (blockSize, inlineSize) else (inlineSize, blockSize)
  (x, y, w, h)

/-- Law: In vertical writing modes, physical width is logical block size and physical height is logical inline size.
    CSS Writing Modes Level 3 §6.4. -/
theorem physicalContentBox_vertical (wm : WritingMode) (h : isVertical wm = true) (b p : Phys) (is bs : Nat) :
    (physicalContentBox wm b p is bs).2.2 = (bs, is) := by
  dsimp [physicalContentBox]
  rw [h]
  rfl

/-- Law: In horizontal writing modes, physical width is logical inline size and physical height is logical block size.
    CSS Writing Modes Level 3 §6.4. -/
theorem physicalContentBox_horizontal (wm : WritingMode) (h : isVertical wm = false) (b p : Phys) (is bs : Nat) :
    (physicalContentBox wm b p is bs).2.2 = (is, bs) := by
  dsimp [physicalContentBox]
  rw [h]
  rfl

/-- Logical rect (inlineOffset, blockOffset, inlineSize, blockSize) of a child box within its container.
    CSS Writing Modes Level 3 §6.2 Flow-relative Directions, §6.4 Abstract-to-Physical Mappings. -/
def logicalRectInContainer (containerWm : WritingMode) (margins : Phys) (width height : Nat) :
    Nat × Nat × Nat × Nat :=
  let inlineOffset := match containerWm with
    | .horizontalTb => margins.left
    | .verticalLr | .verticalRl => margins.top
  let blockOffset := match containerWm with
    | .horizontalTb => margins.top
    | .verticalLr => margins.left
    | .verticalRl => margins.right
  let inlineSize := flowInlineSize containerWm width height
  let blockSize := flowBlockSize containerWm width height
  (inlineOffset, blockOffset, inlineSize, blockSize)

/-- Law: In horizontal-tb container, logical inline-offset is margins.left and block-offset is margins.top.
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings. -/
theorem logical_rect_in_container_horizontal_tb (m : Phys) (w h : Nat) :
    (logicalRectInContainer .horizontalTb m w h).1 = m.left ∧
    (logicalRectInContainer .horizontalTb m w h).2.1 = m.top := by
  exact ⟨rfl, rfl⟩

/-- Law: In vertical-lr container, logical inline-offset is margins.top and block-offset is margins.left.
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings. -/
theorem logical_rect_in_container_vertical_lr (m : Phys) (w h : Nat) :
    (logicalRectInContainer .verticalLr m w h).1 = m.top ∧
    (logicalRectInContainer .verticalLr m w h).2.1 = m.left := by
  exact ⟨rfl, rfl⟩

/-- Law: In vertical-rl container, logical inline-offset is margins.top and block-offset is margins.right.
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings. -/
theorem logical_rect_in_container_vertical_rl (m : Phys) (w h : Nat) :
    (logicalRectInContainer .verticalRl m w h).1 = m.top ∧
    (logicalRectInContainer .verticalRl m w h).2.1 = m.right := by
  exact ⟨rfl, rfl⟩

/-! ## Vertical Caret Rect Geometry (CSS Writing Modes Level 3 §6.4, §3.1) -/

/-- Text caret shape (`CaretShape::kBar`, `kBlock`, `kUnderscore`).
    CSS Writing Modes Level 3 §3.1. -/
inductive CaretShape where
  | bar
  | block
  | underscore
  deriving DecidableEq, Repr

/-- Caret dimensions (width, height) for vertical writing modes.
    CSS Writing Modes Level 3 §3.1, §6.4. -/
def caretDimensions (shape : CaretShape) (fontHeight fontWidth caretWidth : Nat) : Nat × Nat :=
  match shape with
  | .bar => (fontHeight, caretWidth)
  | .block => (fontHeight, fontWidth)
  | .underscore => (caretWidth, fontWidth)

/-- 2D Physical caret rect `(x, y, w, h)` for an empty element in vertical writing modes.
    CSS Writing Modes Level 3 §6.4 Abstract-to-Physical Mappings, §3.1. -/
def localCaretRectVertical (wm : WritingMode) (isInline : Bool) (boxWidth : Nat)
    (padding : Phys) (fontHeight fontWidth caretWidth : Nat) (shape : CaretShape) :
    Int × Int × Nat × Nat :=
  let (w, h) := caretDimensions shape fontHeight fontWidth caretWidth
  let y : Int := if isInline then (padding.top : Int) - (caretWidth : Int) else (padding.top : Int)
  let x : Int :=
    if isInline then
      match wm with
      | .verticalRl => if shape == .underscore then - (caretWidth : Int) else 0
      | .verticalLr => if shape == .underscore then (fontHeight : Int) * 2 else (fontHeight : Int)
      | .horizontalTb => 0
    else
      match wm with
      | .verticalRl =>
        let base := (boxWidth : Int) - (padding.right : Int) - (fontHeight : Int)
        if shape == .underscore then base - (caretWidth : Int) else base
      | .verticalLr =>
        if shape == .underscore then (padding.left : Int) + (fontHeight : Int) else (padding.left : Int)
      | .horizontalTb => (padding.left : Int)
  (x, y, w, h)

/-! ## Caret Rect Laws (CSS Writing Modes Level 3 §6.4, §3.1) -/

/-- Law: Caret bar dimensions in vertical writing mode are font-height by caret-width.
    CSS Writing Modes Level 3 §3.1. -/
theorem caret_dimensions_bar (fh fw cw : Nat) :
    caretDimensions .bar fh fw cw = (fh, cw) := rfl

/-- Law: Caret block dimensions in vertical writing mode are font-height by font-width.
    CSS Writing Modes Level 3 §3.1. -/
theorem caret_dimensions_block (fh fw cw : Nat) :
    caretDimensions .block fh fw cw = (fh, fw) := rfl

/-- Law: Caret underscore dimensions in vertical writing mode are caret-width by font-width.
    CSS Writing Modes Level 3 §3.1. -/
theorem caret_dimensions_underscore (fh fw cw : Nat) :
    caretDimensions .underscore fh fw cw = (cw, fw) := rfl

/-- Law: In vertical-lr block, caret bar X position is the left padding edge.
    CSS Writing Modes Level 3 §6.4. -/
theorem vertical_lr_bar_x (w : Nat) (p : Phys) (fh fw cw : Nat) :
    (localCaretRectVertical .verticalLr false w p fh fw cw .bar).1 = p.left := rfl

/-- Law: In vertical-rl block, caret block X position is box-width minus right padding minus font-height.
    CSS Writing Modes Level 3 §6.4. -/
theorem vertical_rl_block_x (w : Nat) (p : Phys) (fh fw cw : Nat) :
    (localCaretRectVertical .verticalRl false w p fh fw cw .block).1 = (w : Int) - (p.right : Int) - (fh : Int) := rfl

/-- Law: Block element caret Y position is always top padding.
    CSS Writing Modes Level 3 §6.4. -/
theorem vertical_block_caret_y (wm : WritingMode) (w : Nat) (p : Phys) (fh fw cw : Nat) (s : CaretShape) :
    (localCaretRectVertical wm false w p fh fw cw s).2.1 = p.top := rfl

end BlockWritingMode
end ChromiumLayout
