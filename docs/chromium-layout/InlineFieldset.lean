import InlineGeometry

namespace ChromiumLayout

/-! ## HTML Fieldset and Legend Layout Algorithm
    Specifications:
    - HTML 5.2 §4.10.16 The fieldset element
    - CSS 2.1 §10 Visual formatting model details
    - CSS Writing Modes 3 §4.2 Inline-level Alignment
    Blink reference:
    - `third_party/blink/renderer/core/layout/forms/fieldset_layout_algorithm.cc`

    Key principles:
    1. The rendered legend is placed over the block-start border of the fieldset.
       If the block-start border is thicker than the legend's block size, the legend
       is centered within the border; otherwise it aligns with the border-start edge.
    2. Fieldset padding is delegated to an anonymous content box inside the fieldset.
    3. The anonymous content box starts after the legend and block-start border.
    4. The fieldset block size encompasses the legend intrinsic block size, the content
       box block size, and the block-end border.
-/

/-- Margins in physical coordinates. -/
structure PhysicalMargins where
  top : Nat := 0
  right : Nat := 0
  bottom : Nat := 0
  left : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Input for a child box of a fieldset or legend. -/
structure ChildBoxInput where
  size : PhysicalSize
  offset : Option PhysicalOffset := none
  isAbspos : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Input for the fieldset legend. -/
structure LegendInput where
  size : PhysicalSize
  margins : PhysicalMargins := {}
  writingMode : WritingMode := WritingMode.horizontalTb
  direction : TextDirection := TextDirection.ltr
  children : List ChildBoxInput := []
  deriving DecidableEq, Repr, Inhabited

/-- Input parameters for fieldset layout (HTML 5.2 §4.10.16). -/
structure FieldsetInput where
  writingMode : WritingMode := WritingMode.horizontalTb
  direction : TextDirection := TextDirection.ltr
  borderTop : Nat := 0
  borderRight : Nat := 0
  borderBottom : Nat := 0
  borderLeft : Nat := 0
  paddingTop : Nat := 0
  paddingRight : Nat := 0
  paddingBottom : Nat := 0
  paddingLeft : Nat := 0
  specifiedWidth : Option Nat := none
  specifiedHeight : Option Nat := none
  maxHeight : Option Nat := none
  legend : Option LegendInput := none
  children : List ChildBoxInput := []
  deriving DecidableEq, Repr, Inhabited

/-- Result of laying out a fieldset and its anonymous content box. -/
structure FieldsetLayoutResult where
  fieldsetSize : PhysicalSize
  legendOffset : Option PhysicalOffset := none
  legendSize : Option PhysicalSize := none
  legendChildren : List (PhysicalOffset × PhysicalSize) := []
  contentOffset : PhysicalOffset
  contentSize : PhysicalSize
  childOffsets : List PhysicalOffset := []
  childSizes : List PhysicalSize := []
  deriving DecidableEq, Repr, Inhabited

/-- Layout algorithm for fieldset and legend according to HTML 5.2 §4.10.16 & CSS 2.1 §10. -/
def layoutFieldset (input : FieldsetInput) : FieldsetLayoutResult :=
  let isHoriz := match input.writingMode with
    | WritingMode.horizontalTb => true
    | _ => false

  let borderBlockStart := match input.writingMode with
    | WritingMode.horizontalTb => input.borderTop
    | WritingMode.verticalLr => input.borderLeft
    | WritingMode.verticalRl => input.borderRight
    | _ => input.borderTop

  let borderBlockEnd := match input.writingMode with
    | WritingMode.horizontalTb => input.borderBottom
    | WritingMode.verticalLr => input.borderRight
    | WritingMode.verticalRl => input.borderLeft
    | _ => input.borderBottom

  let borderInlineStart := match input.writingMode with
    | WritingMode.horizontalTb =>
      match input.direction with
      | TextDirection.ltr => input.borderLeft
      | TextDirection.rtl => input.borderRight
    | WritingMode.verticalLr | WritingMode.verticalRl => input.borderTop
    | _ => input.borderLeft

  let borderInlineEnd := match input.writingMode with
    | WritingMode.horizontalTb =>
      match input.direction with
      | TextDirection.ltr => input.borderRight
      | TextDirection.rtl => input.borderLeft
    | WritingMode.verticalLr | WritingMode.verticalRl => input.borderBottom
    | _ => input.borderRight

  let padBlockStart := match input.writingMode with
    | WritingMode.horizontalTb => input.paddingTop
    | WritingMode.verticalLr => input.paddingLeft
    | WritingMode.verticalRl => input.paddingRight
    | _ => input.paddingTop

  let padBlockEnd := match input.writingMode with
    | WritingMode.horizontalTb => input.paddingBottom
    | WritingMode.verticalLr => input.paddingRight
    | WritingMode.verticalRl => input.paddingLeft
    | _ => input.paddingBottom

  let padInlineStart := match input.writingMode with
    | WritingMode.horizontalTb =>
      match input.direction with
      | TextDirection.ltr => input.paddingLeft
      | TextDirection.rtl => input.paddingRight
    | WritingMode.verticalLr | WritingMode.verticalRl => input.paddingTop
    | _ => input.paddingLeft

  let padInlineEnd := match input.writingMode with
    | WritingMode.horizontalTb =>
      match input.direction with
      | TextDirection.ltr => input.paddingRight
      | TextDirection.rtl => input.paddingLeft
    | WritingMode.verticalLr | WritingMode.verticalRl => input.paddingBottom
    | _ => input.paddingRight

  -- Specified dimensions
  let specifiedInline := if isHoriz then input.specifiedWidth else input.specifiedHeight
  let specifiedBlock := if isHoriz then input.specifiedHeight else input.specifiedWidth
  let maxBlock := if isHoriz then input.maxHeight else none

  -- Child intrinsic dimensions
  let childInnerInline := match input.children with
    | [] => 0
    | c :: _ => if isHoriz then c.size.width else c.size.height

  let childInnerBlock := match input.children with
    | [] => 0
    | c :: _ => if isHoriz then c.size.height else c.size.width

  -- Content box inline size
  let contentInnerInline := match specifiedInline with
    | some w => w
    | none => childInnerInline
  let contentInlineSize := contentInnerInline + padInlineStart + padInlineEnd

  -- Legend dimensions and placement
  let (optLegOffset, optLegSize, legChildren, intrinsicBlockSize, legBlockSizeVal) :
      Option PhysicalOffset × Option PhysicalSize × List (PhysicalOffset × PhysicalSize) × Nat × Nat :=
    match input.legend with
    | none => (none, none, [], borderBlockStart, 0)
    | some leg =>
      let legBlockSize := if isHoriz then leg.size.height else leg.size.width
      let legMarginBlockEnd := match input.writingMode with
        | WritingMode.horizontalTb => leg.margins.bottom
        | WritingMode.verticalLr => leg.margins.right
        | WritingMode.verticalRl => leg.margins.left
        | _ => leg.margins.bottom
      let legMarginInlineStart := match input.writingMode with
        | WritingMode.horizontalTb =>
          match input.direction with
          | TextDirection.ltr => leg.margins.left
          | TextDirection.rtl => leg.margins.right
        | WritingMode.verticalLr | WritingMode.verticalRl => leg.margins.top
        | _ => leg.margins.left

      let legBlockOffset := if borderBlockStart > legBlockSize then (borderBlockStart - legBlockSize) / 2 else 0
      let legMarginEndOffset := legBlockOffset + legBlockSize + legMarginBlockEnd
      let intr := Nat.max borderBlockStart legMarginEndOffset
      let legInlineOffset := borderInlineStart + padInlineStart + legMarginInlineStart

      let legPhysOffset : PhysicalOffset :=
        match input.writingMode with
        | WritingMode.horizontalTb => { left := legInlineOffset, top := legBlockOffset }
        | WritingMode.verticalLr => { left := legBlockOffset, top := legInlineOffset }
        | WritingMode.verticalRl => { left := 0, top := legInlineOffset }
        | _ => { left := legInlineOffset, top := legBlockOffset }

      let legKids := leg.children.map (fun (c : ChildBoxInput) =>
        (match c.offset with | some o => o | none => ({ left := 0, top := 0 } : PhysicalOffset), c.size))

      (some legPhysOffset, some leg.size, legKids, intr, legBlockSize)

  -- Content box block size
  let contentInnerBlock := match maxBlock with
    | some 0 => 0
    | _ => match specifiedBlock with
      | some sb => if sb + borderBlockStart > intrinsicBlockSize then sb + borderBlockStart - intrinsicBlockSize else 0
      | none => childInnerBlock

  let contentBlockSize := contentInnerBlock + padBlockStart + padBlockEnd

  let totalInlineSize := contentInlineSize + borderInlineStart + borderInlineEnd
  let totalBlockSize := intrinsicBlockSize + contentBlockSize + borderBlockEnd

  let contentPhysSize : PhysicalSize :=
    if isHoriz then { width := contentInlineSize, height := contentBlockSize }
    else { width := contentBlockSize, height := contentInlineSize }

  let contentPhysOffset : PhysicalOffset :=
    match input.writingMode with
    | WritingMode.horizontalTb => { left := borderInlineStart, top := intrinsicBlockSize }
    | WritingMode.verticalLr => { left := intrinsicBlockSize, top := borderInlineStart }
    | WritingMode.verticalRl => { left := borderBlockEnd, top := borderInlineStart }
    | _ => { left := borderInlineStart, top := intrinsicBlockSize }

  let childPhysOffset (c : ChildBoxInput) : PhysicalOffset :=
    if c.isAbspos then ({ left := 0, top := 0 } : PhysicalOffset)
    else ({ left := padInlineStart, top := padBlockStart } : PhysicalOffset)

  let childPhysSize (c : ChildBoxInput) : PhysicalSize :=
    if c.isAbspos then contentPhysSize
    else if specifiedBlock.isSome && c.size.height == 0 then
      if isHoriz then { width := c.size.width, height := contentInnerBlock }
      else { width := contentInnerBlock, height := c.size.height }
    else c.size

  let childOffsets := input.children.map childPhysOffset
  let childSizes := input.children.map childPhysSize

  let totalPhysSize : PhysicalSize :=
    if isHoriz then { width := totalInlineSize, height := totalBlockSize }
    else { width := totalBlockSize, height := totalInlineSize }

  let finalLegOffset : Option PhysicalOffset := match optLegOffset with
    | none => none
    | some lo =>
      match input.writingMode with
      | WritingMode.verticalRl =>
        some ({ left := totalPhysSize.width - legBlockSizeVal, top := lo.top } : PhysicalOffset)
      | _ => some lo

  { fieldsetSize := totalPhysSize
  , legendOffset := finalLegOffset
  , legendSize := optLegSize
  , legendChildren := legChildren
  , contentOffset := contentPhysOffset
  , contentSize := contentPhysSize
  , childOffsets := childOffsets
  , childSizes := childSizes }

/-- General Law: An empty horizontal fieldset has block size equal to border-top + padding-top + padding-bottom + border-bottom (HTML 5.2 §4.10.16). -/
theorem fieldset_empty_block_size (bt bb pt pb w : Nat) :
    let inp : FieldsetInput := { borderTop := bt, borderBottom := bb, paddingTop := pt, paddingBottom := pb, specifiedWidth := some w }
    (layoutFieldset inp).fieldsetSize.height = bt + pt + pb + bb := by
  dsimp [layoutFieldset]
  omega

/-- General Law: When border-start > legend height, the centered legend offset plus height is within the border (HTML 5.2 §4.10.16). -/
theorem legend_centered_within_border (b h : Nat) (h_gt : b > h) :
    (b - h) / 2 + h ≤ b := by
  omega

/-- General Law: Legend centering offset is never greater than border-start (HTML 5.2 §4.10.16). -/
theorem legend_centering_offset_le (b h : Nat) :
    (if b > h then (b - h) / 2 else 0) ≤ b := by
  split <;> omega

/-- Min-max sizes for a layout box (CSS Sizing 3 §5). -/
structure MinMaxSizes where
  minSize : Nat
  maxSize : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Input parameters for computing fieldset min/max content sizes (HTML 5.2 §4.10.16, CSS Sizing 3 §5). -/
structure FieldsetMinMaxInput where
  borderPadding : Nat
  legendBorderPaddingMargin : Nat := 0
  legendFloats : List Nat := []
  hasLegend : Bool := false
  contentFloats : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- Compute min/max content sizes for a fieldset and legend according to HTML 5.2 §4.10.16 & CSS Sizing 3 §5. -/
def computeFieldsetMinMaxSizes (inp : FieldsetMinMaxInput) : MinMaxSizes :=
  let contentMin := if inp.contentFloats.isEmpty then 0 else inp.contentFloats.foldl Nat.max 0
  let contentMax := inp.contentFloats.foldl (· + ·) 0
  let contentTotalMin := inp.borderPadding + contentMin
  let contentTotalMax := inp.borderPadding + contentMax
  if inp.hasLegend then
    let legMin := if inp.legendFloats.isEmpty then 0 else inp.legendFloats.foldl Nat.max 0
    let legMax := inp.legendFloats.foldl (· + ·) 0
    let legTotalMin := inp.borderPadding + inp.legendBorderPaddingMargin + legMin
    let legTotalMax := inp.borderPadding + inp.legendBorderPaddingMargin + legMax
    { minSize := Nat.max legTotalMin contentTotalMin, maxSize := Nat.max legTotalMax contentTotalMax }
  else
    { minSize := contentTotalMin, maxSize := contentTotalMax }

/-- General Law: An empty fieldset with no legend has minSize = maxSize = borderPadding (CSS Sizing 3 §5). -/
theorem fieldset_empty_min_max_eq (bp : Nat) :
    let inp : FieldsetMinMaxInput := { borderPadding := bp, hasLegend := false, contentFloats := [] }
    computeFieldsetMinMaxSizes inp = { minSize := bp, maxSize := bp } :=
  rfl

/-- Fragmentation break avoidance specification (CSS Fragmentation 3 §3). -/
inductive BreakAvoidance where
  | auto
  | avoid
  deriving DecidableEq, Repr, Inhabited

/-- Resulting box fragment of a fieldset across fragmentainers (CSS Fragmentation 3 §2.1, HTML 5.2 §4.10.16). -/
structure FieldsetFragment where
  size : PhysicalSize
  hasBreakToken : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Determine whether a fieldset fragment generates a break token (CSS Fragmentation 3 §2.1). -/
def fieldsetFragmentHasBreakToken (remainingHeight : Nat) (availableSpace : Nat) : Bool :=
  if availableSpace = 0 then remainingHeight > 0
  else remainingHeight > availableSpace

/-- Compute fragmentation step for a fieldset given available fragmentainer space and remaining content (CSS Fragmentation 3 §2.1, HTML 5.2 §4.10.16). -/
def layoutFieldsetFragment (totalWidth : Nat) (remainingHeight : Nat) (availableSpace : Nat) : FieldsetFragment :=
  let h := if availableSpace = 0 then 0 else Nat.min remainingHeight availableSpace
  { size := { width := totalWidth, height := h }
  , hasBreakToken := fieldsetFragmentHasBreakToken remainingHeight availableSpace }

/-- Step layout for a fieldset with a monolithic child (e.g. legend) or break-inside: avoid (CSS Fragmentation 3 §4.1).
    If monolithic child height exceeds availableSpace, child cannot break inside and consumes its full height in fragment 1. -/
def layoutFieldsetMonolithicFragment (totalWidth : Nat) (childHeight : Nat) (remainingContent : Nat) (availableSpace : Nat) : FieldsetFragment :=
  if childHeight > availableSpace then
    { size := { width := totalWidth, height := childHeight }, hasBreakToken := remainingContent > 0 }
  else
    layoutFieldsetFragment totalWidth (childHeight + remainingContent) availableSpace

/-- General Law: Fragment width matches total specified width for all inputs (CSS Fragmentation 3 §2.1). -/
theorem fieldset_fragment_size_width (w h s : Nat) :
    (layoutFieldsetFragment w h s).size.width = w := by
  rfl

/-- General Law: Fragment height is 0 when available space is 0 (CSS Fragmentation 3 §2.1). -/
theorem fieldset_fragment_zero_space (w h : Nat) :
    (layoutFieldsetFragment w h 0).size.height = 0 := by
  rfl

/-- General Law: When remaining height fits in available space, no break token is generated (CSS Fragmentation 3 §2.1). -/
theorem fieldset_fragment_no_break_when_fits (w h s : Nat) (h_pos : s > 0) (h_fits : h ≤ s) :
    (layoutFieldsetFragment w h s).hasBreakToken = false := by
  dsimp [layoutFieldsetFragment, fieldsetFragmentHasBreakToken]
  split
  · rename_i hs; omega
  · exact decide_eq_false (by omega)

/-- General Law: When remaining height strictly exceeds available space, a break token is generated (CSS Fragmentation 3 §2.1). -/
theorem fieldset_fragment_breaks_when_exceeds (w h s : Nat) (h_pos : s > 0) (h_gt : h > s) :
    (layoutFieldsetFragment w h s).hasBreakToken = true := by
  dsimp [layoutFieldsetFragment, fieldsetFragmentHasBreakToken]
  split
  · rename_i hs; omega
  · exact decide_eq_true (by omega)

/-! ## HTML 5.2 §4.10.16 & CSS 2.1 §9.2.1.1: Fieldset Child Organization -/

/-- HTML 5.2 §4.10.16: Elements participating in fieldset child layout. -/
inductive FieldsetChild where
  | legend (content : String)
  | content (tag : String) (text : String)
  | whitespace
  deriving DecidableEq, Repr, Inhabited

/-- HTML 5.2 §4.10.16: Fieldset partitioning into rendered legend and content box. -/
structure FieldsetChildPartition where
  renderedLegend : Option String
  contentChildren : List (String × String)
  deriving DecidableEq, Repr, Inhabited

/-- HTML 5.2 §4.10.16: Partition raw DOM children of a fieldset into
    the rendered legend (first legend element) and the contents of the anonymous content box.
    Collapsible whitespace is pruned. -/
def partitionFieldsetChildren (children : List FieldsetChild) : FieldsetChildPartition :=
  let rec loop (items : List FieldsetChild) (leg : Option String) (acc : List (String × String)) : FieldsetChildPartition :=
    match items with
    | [] => { renderedLegend := leg, contentChildren := acc.reverse }
    | .whitespace :: rest => loop rest leg acc
    | .legend s :: rest =>
      match leg with
      | none => loop rest (some s) acc
      | some _ => loop rest leg (("legend", s) :: acc)
    | .content tag text :: rest => loop rest leg ((tag, text) :: acc)
  loop children none []

/-- HTML 5.2 §4.10.16 Law: Empty children list partitions into none legend and empty contents. -/
theorem partitionFieldsetChildren_empty :
    partitionFieldsetChildren [] = { renderedLegend := none, contentChildren := [] } := rfl

/-- HTML 5.2 §4.10.16 Law: Intervening whitespace does not alter the partition of legend and content. -/
theorem partitionFieldsetChildren_whitespace_after_content (tag text s : String) :
    partitionFieldsetChildren [.content tag text, .whitespace, .legend s] =
    partitionFieldsetChildren [.content tag text, .legend s] := rfl

/-- HTML 5.2 §4.10.16 Law: Intervening whitespace does not alter the partition with multiple contents. -/
theorem partitionFieldsetChildren_whitespace_nested (tag text s : String) :
    partitionFieldsetChildren [.content tag text, .whitespace, .whitespace, .legend s] =
    partitionFieldsetChildren [.content tag text, .legend s] := rfl

end ChromiumLayout
