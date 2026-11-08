/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineGeometry
import InlineShaping

/-!
# CSS 2.1 §9.4.2 & §10.8: Inline Formatting Context and Line Box Layout

Formalizes:
- CSS 2.1 §9.4.2: Inline formatting contexts, horizontal line box distribution, and line breaking.
- CSS 2.1 §10.8: Line height calculations and vertical alignment (`line-height`, `vertical-align`: `baseline`, `top`, `bottom`, `middle`).
- CSS 2.1 §10.8.1: Leading, half-leading, and strut metrics.
- CSS Writing Modes 3 §4: Inline-axis and block-axis progression across writing modes.

Owns:
- `VerticalAlign`
- `LineBoxLayoutResult`
- `layoutReplacedLineBox`
- `isLineBoxEmpty`
- `InlineWritingMode`, `InlineDirection`, `LineFragment`
- `computeLinePhysicalRects`
- `physicalLinesBoundingBox`
-/

namespace ChromiumLayout

/-! ## 1. Vertical Alignment and Replaced Element Layout (CSS 2.1 §10.8) -/

/-- CSS 2.1 §10.8: Values for the 'vertical-align' property. -/
inductive VerticalAlign where
  | baseline
  | top
  | bottom
  | middle
  deriving DecidableEq, Repr

/-- CSS 2.1 §10.8: Line box geometry result after vertical alignment. -/
structure LineBoxLayoutResult where
  lineHeight : Nat := 0
  itemTopOffset : Nat := 0
  isEmptyLineBox : Bool := false
  deriving DecidableEq, Repr

/-- CSS 2.1 §10.8: Vertical alignment and line box height calculation for replaced elements.
    "In case they are aligned 'top' or 'bottom', they must be aligned so as to minimize the line box height."
    For 'bottom', aligns item's bottom edge with line box bottom; for 'top', aligns item's top edge with line box top. -/
def layoutReplacedLineBox (strutHeight : Nat) (itemHeight : Nat) (align : VerticalAlign) : LineBoxLayoutResult :=
  match align with
  | .bottom =>
    let h := Nat.max strutHeight itemHeight
    let topOff := h - itemHeight
    { lineHeight := h, itemTopOffset := topOff, isEmptyLineBox := false }
  | .top =>
    let h := Nat.max strutHeight itemHeight
    { lineHeight := h, itemTopOffset := 0, isEmptyLineBox := false }
  | .baseline =>
    { lineHeight := Nat.max strutHeight itemHeight, itemTopOffset := 0, isEmptyLineBox := false }
  | .middle =>
    { lineHeight := Nat.max strutHeight itemHeight, itemTopOffset := 0, isEmptyLineBox := false }

/-- CSS 2.1 §10.8: Empty line box predicate.
    "Empty inline elements generate empty inline boxes, but these boxes still have margins, padding,
    borders and a line height..."
    A line box containing only empty tags is flagged as empty. -/
def isLineBoxEmpty (tokens : List InlineCollectionToken) : Bool :=
  tokens.all fun t =>
    match t with
    | .text s => s.isEmpty
    | .openTag _ => true
    | .closeTag => true
    | .atomicInline _ => false
    | .br => false

/-! ## 2. Physical Line Bounding Box (CSS 2.1 §9.4.2 & CSS Writing Modes 3 §4) -/

/-- Writing modes influencing block and inline progression (`writing-mode`). -/
inductive InlineWritingMode where
  | horizontalTb
  | verticalRl
  deriving DecidableEq, Repr

/-- Inline direction (`direction`). -/
inductive InlineDirection where
  | ltr
  | rtl
  deriving DecidableEq, Repr

/-- Dimensions of an individual line fragment in a line box. -/
structure LineFragment where
  width : Nat := 0
  height : Nat := 0
  deriving DecidableEq, Repr

/-- CSS 2.1 §9.4.2 & CSS Writing Modes 3 §4: Compute physical rectangles for line fragments in a block container.
    In horizontal-tb: lines stack top-to-bottom. In RTL, each line aligns to the right edge (`containerWidth - lineWidth`).
    In vertical-rl: lines stack right-to-left along X, advancing top-to-bottom along Y. -/
def computeLinePhysicalRects (containerWidth _containerHeight : Nat)
    (mode : InlineWritingMode) (dir : InlineDirection) (lines : List LineFragment) : List PhysicalRect :=
  match mode with
  | .horizontalTb =>
    let rec loopH (curY : Nat) : List LineFragment → List PhysicalRect
      | [] => []
      | l :: rest =>
        let x := match dir with
          | .ltr => 0
          | .rtl => if l.width ≤ containerWidth then containerWidth - l.width else 0
        let r : PhysicalRect := { x := x, y := curY, width := l.width, height := l.height }
        r :: loopH (curY + l.height) rest
    loopH 0 lines
  | .verticalRl =>
    let totalBlock := lines.foldl (fun acc l => acc + l.width) 0
    let startX := if totalBlock ≤ containerWidth then containerWidth - totalBlock else 0
    let rec loopV (curX : Nat) : List LineFragment → List PhysicalRect
      | [] => []
      | l :: rest =>
        let r : PhysicalRect := { x := curX, y := 0, width := l.width, height := l.height }
        r :: loopV (curX + l.width) rest
    loopV startX lines

/-- CSS 2.1 §9.4.2: PhysicalLinesBoundingBox: union of all physical line fragment rectangles (`LayoutInline::PhysicalLinesBoundingBox`). -/
def physicalLinesBoundingBox (containerWidth containerHeight : Nat)
    (mode : InlineWritingMode) (dir : InlineDirection) (lines : List LineFragment) : PhysicalRect :=
  let rects := computeLinePhysicalRects containerWidth containerHeight mode dir lines
  rects.foldl (fun acc r => acc.union r) {}

/-! ## 3. General Laws (CSS 2.1 §9.4.2 & §10.8) -/

/-- CSS 2.1 §10.8 Law: for any replaced element taller than the strut, bottom-alignment gives line height
    equal to item height and top offset 0. Proved for all strut and item heights satisfying `strutHeight ≤ itemHeight`. -/
theorem lineBox_verticalAlignBottom_height (strutHeight itemHeight : Nat) (h : strutHeight ≤ itemHeight) :
    (layoutReplacedLineBox strutHeight itemHeight .bottom).lineHeight = itemHeight ∧
    (layoutReplacedLineBox strutHeight itemHeight .bottom).itemTopOffset = 0 := by
  dsimp [layoutReplacedLineBox]
  have hmax : Nat.max strutHeight itemHeight = itemHeight := Nat.max_eq_right h
  rw [hmax]
  have hsub : itemHeight - itemHeight = 0 := Nat.sub_self itemHeight
  rw [hsub]
  exact ⟨rfl, rfl⟩

/-- CSS 2.1 §10.8 Law: an empty span produces an empty line box. Proved for all tag names. -/
theorem emptySpan_isEmptyLineBox (tag : String) :
    isLineBoxEmpty [.openTag tag, .closeTag] = true := by
  rfl

/-- CSS 2.1 §10.8 Law: any line box containing non-empty text is not empty. Proved for all non-empty strings. -/
theorem text_nonEmpty_notEmptyLineBox (s : String) (h : s.isEmpty = false) :
    isLineBoxEmpty [.text s] = false := by
  dsimp [isLineBoxEmpty]
  rw [h]
  rfl

end ChromiumLayout
