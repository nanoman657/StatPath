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

end BlockWritingMode
end ChromiumLayout
