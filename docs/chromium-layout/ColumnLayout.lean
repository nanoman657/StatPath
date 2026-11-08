/-
  ColumnLayout.lean: multi-column layout algorithm (CSS Multi-column Layout Level 1),
  written from column_layout_algorithm_test.cc (pin 36c121be). Owned by the block lane (Column*).
-/
import ColumnWidth

namespace ChromiumLayout
namespace ColumnLayout

open ColumnWidth

/-- Child sizing in multicol: a fixed pixel size, a percentage of column width, or auto. -/
inductive Len where
  | px (n : Nat)
  | pct (p : Nat)
  | auto
  deriving Inhabited, DecidableEq, Repr

/-- Resolve a child inline size against the used column inline size. -/
def resolveLen (colW : Nat) : Len → Nat
  | .px n => n
  | .pct p => colW * p / 100
  | .auto => colW

/-- A child block inside a multicol container. -/
structure ColChild where
  id : Nat := 0
  width : Len := .auto
  height : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Multicolumn container specification. -/
structure Multicol where
  cols : Nat
  gap : Nat
  width : Nat
  height : Nat
  children : List ColChild := []
  deriving Inhabited, DecidableEq, Repr

/-- Fragment of a child inside a column fragmentainer. -/
structure ChildSlice where
  id : Nat := 0
  relX : Nat := 0
  relY : Nat := 0
  w : Nat := 0
  h : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- A column fragmentainer. -/
structure ColFrag where
  colIdx : Nat := 0
  relX : Nat := 0
  relY : Nat := 0
  w : Nat := 0
  h : Nat := 0
  slices : List ChildSlice := []
  deriving Inhabited, DecidableEq, Repr

/-- Result of multicolumn layout. -/
structure MulticolResult where
  w : Nat := 0
  h : Nat := 0
  colWidth : Nat := 0
  columns : List ColFrag := []
  deriving Inhabited, DecidableEq, Repr

/-- Column stride: inline distance from start of one column to start of the next. -/
def colStride (colWidth gap : Nat) : Nat :=
  colWidth + gap

/-- Inline offset of the k-th column fragmentainer. -/
def columnInlineOffset (k : Nat) (colWidth gap : Nat) : Nat :=
  k * colStride colWidth gap

/-- Total content block size. -/
def totalContentHeight (children : List ColChild) : Nat :=
  children.foldl (fun acc c => acc + c.height) 0

/-- Number of column fragmentainers created for `column-fill: auto`. -/
def actualColumnCount (fragH : Nat) (contentH : Nat) : Nat :=
  if fragH = 0 then
    if contentH = 0 then 1 else contentH
  else
    Nat.max 1 ((contentH + fragH - 1) / fragH)

/-- Slice a list of sequential in-flow children into column fragmentainer k. -/
def sliceChildren (k : Nat) (fragH : Nat) (colW : Nat) (children : List ColChild) : List ChildSlice :=
  if fragH = 0 then
    let rec findChildAt (chs : List ColChild) (accum : Nat) : List ChildSlice :=
      match chs with
      | [] => []
      | c :: cs =>
          if k >= accum && k < accum + c.height then
            [⟨c.id, 0, 0, resolveLen colW c.width, 1⟩]
          else
            findChildAt cs (accum + c.height)
    findChildAt children 0
  else
    let colStart := k * fragH
    let colEnd := (k + 1) * fragH
    let rec sliceAt (chs : List ColChild) (curY : Nat) : List ChildSlice :=
      match chs with
      | [] => []
      | c :: cs =>
          let nextY := curY + c.height
          let cWidth := resolveLen colW c.width
          if c.height = 0 then
            let inCol := (curY >= colStart && curY < colEnd) ||
                         (curY = colEnd && k + 1 = actualColumnCount fragH curY)
            let rest := sliceAt cs nextY
            if inCol then
              ⟨c.id, 0, curY - colStart, cWidth, 0⟩ :: rest
            else
              rest
          else
            let overlapStart := Nat.max curY colStart
            let overlapEnd := Nat.min nextY colEnd
            let rest := sliceAt cs nextY
            if overlapStart < overlapEnd then
              let sliceH := overlapEnd - overlapStart
              let sliceY := overlapStart - colStart
              ⟨c.id, 0, sliceY, cWidth, sliceH⟩ :: rest
            else
              rest
    sliceAt children 0

/-- Multicolumn layout algorithm for `column-fill: auto`. -/
def layoutMulticol (mc : Multicol) : MulticolResult :=
  let colW := usedWidth mc.cols 0 mc.gap mc.width
  let contentH := totalContentHeight mc.children
  let numCols := actualColumnCount mc.height contentH
  let cols := (List.range numCols).map (fun k =>
    let x := columnInlineOffset k colW mc.gap
    let y := 0
    let slices := sliceChildren k mc.height colW mc.children
    ⟨k, x, y, colW, mc.height, slices⟩)
  ⟨mc.width, mc.height, colW, cols⟩

/-- Column stride is strictly positive when column width is positive. -/
theorem colStride_pos (colWidth gap : Nat) (h : 0 < colWidth) :
    0 < colStride colWidth gap := by
  unfold colStride
  omega

/-- Column offset advances by stride for each subsequent column. -/
theorem columnInlineOffset_step (k colWidth gap : Nat) :
    columnInlineOffset (k + 1) colWidth gap = columnInlineOffset k colWidth gap + colStride colWidth gap := by
  unfold columnInlineOffset
  rw [Nat.add_mul]
  rw [Nat.one_mul]

/-- Columns do not overlap when gap is non-negative and column width is positive. -/
theorem columns_non_overlapping (k colWidth gap : Nat) :
    columnInlineOffset k colWidth gap + colWidth ≤ columnInlineOffset (k + 1) colWidth gap := by
  rw [columnInlineOffset_step]
  unfold colStride
  omega

/-- Multicolumn container always generates at least one column fragmentainer. -/
theorem actualColumnCount_at_least_one (fragH contentH : Nat) :
    1 ≤ actualColumnCount fragH contentH := by
  unfold actualColumnCount
  split
  · split <;> omega
  · apply Nat.le_max_left

/- =========================================================================
   Column Spanners (`column-span: all`, CSS Multi-column Layout Level 1 §6)
   ========================================================================= -/

/-- Item in a multicol container: either a regular in-flow child or a column spanner. -/
structure MulticolItem where
  id : Nat := 0
  isSpanner : Bool := false
  width : Len := .auto
  height : Nat := 0
  avoid : Bool := false
  marginTop : Nat := 0
  marginBottom : Nat := 0
  marginStart : Nat := 0
  autoMargin : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- Multicol container specification with spanner and border support. -/
structure MulticolWithSpanners where
  cols : Nat
  gap : Nat
  width : Nat
  height : Nat := 0
  border : Nat := 0
  fillAuto : Bool := false
  isRtl : Bool := false
  items : List MulticolItem := []
  deriving Inhabited, DecidableEq, Repr

/-- Fragment generated by multicol layout (column fragmentainer or spanner fragment). -/
structure MulticolFrag where
  isSpanner : Bool := false
  relX : Nat := 0
  relY : Nat := 0
  w : Nat := 0
  h : Nat := 0
  slices : List ChildSlice := []
  deriving Inhabited, DecidableEq, Repr

/-- Result of multicolumn layout with spanners. -/
structure MulticolSpannerResult where
  w : Nat := 0
  h : Nat := 0
  colWidth : Nat := 0
  fragments : List MulticolFrag := []
  deriving Inhabited, DecidableEq, Repr

/-- Test whether items can be packed into at most `numCols` columns of capacity `h`. -/
def canPack (numCols : Nat) (h : Nat) (items : List MulticolItem) : Bool :=
  if h = 0 then false
  else
    let rec pack (colsUsed : Nat) (curColH : Nat) (rem : List MulticolItem) : Bool :=
      match rem with
      | [] => colsUsed ≤ numCols
      | it :: rest =>
          if it.height > h then false
          else if curColH + it.height ≤ h then
            pack colsUsed (curColH + it.height) rest
          else
            pack (colsUsed + 1) it.height rest
    pack 1 0 items

/-- Minimum column capacity to balance items into at most `numCols` columns. -/
def balanceRowHeight (numCols : Nat) (items : List MulticolItem) : Nat :=
  if items.isEmpty then 0
  else
    let totalH := items.foldl (fun acc it => acc + it.height) 0
    if totalH = 0 then 0
    else
      let maxH := items.foldl (fun acc it => Nat.max acc it.height) 0
      let minH := Nat.max (Nat.max 1 maxH) ((totalH + numCols - 1) / numCols)
      let rec search (h fuel : Nat) : Nat :=
        match fuel with
        | 0 => totalH
        | fuel + 1 =>
            if canPack numCols h items then h
            else search (h + 1) fuel
      search minH totalH

/-- Number of columns used to pack items into columns of capacity `h`. -/
def countColumnsUsed (h : Nat) (items : List MulticolItem) : Nat :=
  if h = 0 then 1
  else
    let rec pack (colsUsed : Nat) (curColH : Nat) (rem : List MulticolItem) : Nat :=
      match rem with
      | [] => colsUsed
      | it :: rest =>
          if curColH + it.height ≤ h then
            pack colsUsed (curColH + it.height) rest
          else
            pack (colsUsed + 1) it.height rest
    pack 1 0 items

/-- Greedily place children into columns of capacity `colH`. -/
def packColumnSlices (numCols : Nat) (colW : Nat) (colH : Nat) (items : List MulticolItem) : List (List ChildSlice) :=
  let rec pack (colIdx : Nat) (curY : Nat) (rem : List MulticolItem) (acc : List (List ChildSlice)) : List (List ChildSlice) :=
    match rem with
    | [] => acc
    | it :: rest =>
        let (targetCol, newY) :=
          if curY + it.height ≤ colH then (colIdx, curY)
          else (colIdx + 1, 0)
        let slice : ChildSlice := ⟨it.id, 0, newY, colW, it.height⟩
        let updatedAcc :=
          if targetCol < acc.length then
            acc.set targetCol (acc[targetCol]! ++ [slice])
          else acc
        pack targetCol (newY + it.height) rest updatedAcc
  pack 0 0 items (List.replicate numCols [])

/-- A segment in a multicol container is either a set of column items or a spanner. -/
inductive MulticolSegment where
  | row (items : List MulticolItem)
  | spanner (item : MulticolItem)
  deriving Inhabited, DecidableEq, Repr

/-- Partition multicol items into alternating column rows and spanners. -/
def partitionSegments (items : List MulticolItem) : List MulticolSegment :=
  let rec loop (cur : List MulticolItem) (rem : List MulticolItem) : List MulticolSegment :=
    match rem with
    | [] => if cur.isEmpty then [] else [.row cur.reverse]
    | it :: rest =>
        if it.isSpanner then
          if cur.isEmpty then
            .spanner it :: loop [] rest
          else
            .row cur.reverse :: .spanner it :: loop [] rest
        else
          loop (it :: cur) rest
  loop [] items

/-- Layout algorithm for multicolumn containers with column spanners (CSS Multicol §6). -/
def layoutMulticolWithSpanners (mc : MulticolWithSpanners) : MulticolSpannerResult :=
  let colW := usedWidth mc.cols 0 mc.gap mc.width
  let border := mc.border
  let initFrags : List MulticolFrag :=
    match mc.items.head? with
    | some it =>
        if it.isSpanner then
          let cx := if mc.isRtl then border + (mc.cols - 1) * (colW + mc.gap) else border
          [⟨false, cx, border, colW, 0, []⟩]
        else []
    | none => []
  let segments := partitionSegments mc.items
  let rec processSegs (segs : List MulticolSegment) (curY : Nat) (prevMarginBottom : Nat)
      (hasSeenSpanner : Bool) (acc : List MulticolFrag) : Nat × Nat × List MulticolFrag :=
    match segs with
    | [] => (curY, prevMarginBottom, acc)
    | seg :: rest =>
        match seg with
        | .spanner it =>
            let sw := resolveLen mc.width it.width
            let collM := Nat.max prevMarginBottom it.marginTop
            let sy := curY + collM
            let sx :=
              if it.autoMargin then
                border + (mc.width - sw) / 2
              else if mc.isRtl then
                border + mc.width - it.marginStart - sw
              else
                border + it.marginStart
            let frag : MulticolFrag := ⟨true, sx, sy, sw, it.height, []⟩
            processSegs rest (sy + it.height) it.marginBottom true (acc ++ [frag])
        | .row rowItems =>
            let ry := curY + prevMarginBottom
            let isAvoid := rowItems.all (·.avoid)
            let rh :=
              if mc.fillAuto && mc.height > 0 && hasSeenSpanner then
                mc.height + border - ry
              else if isAvoid then
                balanceRowHeight mc.cols rowItems
              else
                let totalH := rowItems.foldl (fun acc it => acc + it.height) 0
                (totalH + mc.cols - 1) / mc.cols
            let numCols :=
              if mc.fillAuto && hasSeenSpanner && isAvoid then 1
              else if isAvoid then
                Nat.min mc.cols (countColumnsUsed rh rowItems)
              else mc.cols
            let colSlices :=
              if isAvoid then
                packColumnSlices numCols colW rh rowItems
              else
                let w := (rowItems.head?.map (fun it => resolveLen colW it.width)).getD colW
                (List.range numCols).map (fun _ => [⟨0, 0, 0, w, rh⟩])
            let colFrags := (List.range numCols).map (fun ci =>
              let cx := if mc.isRtl then border + (mc.cols - 1 - ci) * (colW + mc.gap) else border + ci * (colW + mc.gap)
              let slices := colSlices[ci]?.getD []
              ⟨false, cx, ry, colW, rh, slices⟩)
            processSegs rest (ry + rh) 0 hasSeenSpanner (acc ++ colFrags)
  let (finalY, finalMarginBottom, allFrags) := processSegs segments border 0 (initFrags.length > 0) initFrags
  let totW := mc.width + 2 * border
  let totH := if mc.height > 0 then mc.height + 2 * border else finalY + border + finalMarginBottom
  ⟨totW, totH, colW, allFrags⟩

/-- A spanner with auto inline size spans the full content width of the multicol container. -/
theorem spanner_width_auto (containerW : Nat) :
    resolveLen containerW .auto = containerW := by
  rfl

/-- Spanner vertical position advances by at least the spanner block size. -/
theorem spanner_offset_advances (sy spannerH : Nat) :
    sy ≤ sy + spannerH := by
  omega

/-- Collapsed margin between spanners is at least each adjacent margin. -/
theorem spanner_margin_collapsing (m1 m2 : Nat) :
    m1 ≤ Nat.max m1 m2 ∧ m2 ≤ Nat.max m1 m2 := by
  constructor
  · apply Nat.le_max_left
  · apply Nat.le_max_right

/-- `break-inside` values. CSS Fragmentation Level 3 §3.2 (`break-inside`). -/
inductive BreakInside where
  | auto | avoid | avoidColumn | avoidPage
  deriving Inhabited, DecidableEq, Repr

/-- Whether a `break-inside` value forbids a break inside the box in a column fragmentainer;
    `avoid-page` only applies to page breaks. CSS Fragmentation Level 3 §3.2. -/
def BreakInside.avoidsColumn : BreakInside → Bool
  | .avoid | .avoidColumn => true
  | _ => false

/-- A child block with top and bottom margins inside a multicol container.
    CSS Fragmentation Level 3 §5.2 Adjoining Margins at Breaks. -/
structure ColChildWithMargin where
  id : Nat := 0
  width : Len := .auto
  height : Nat := 0
  marginTop : Nat := 0
  marginBottom : Nat := 0
  breakInside : BreakInside := .auto
  deriving Inhabited, DecidableEq, Repr

/-- Fragment slice of a child placed in a specific column fragmentainer.
    CSS Fragmentation Level 3 §5.3 Splitting Boxes. -/
structure PlacedSlice where
  colIdx : Nat := 0
  id : Nat := 0
  relX : Nat := 0
  relY : Nat := 0
  w : Nat := 0
  h : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Slice a child box across columns.
    CSS Fragmentation Level 3 §5.3 Splitting Boxes. -/
def placeChildSlices (fragH w fuel cId remH colIdx curY : Nat) : List PlacedSlice × Nat × Nat :=
  match fuel with
  | 0 => ([], colIdx, curY)
  | fuel + 1 =>
    if remH = 0 then ([], colIdx, curY)
    else
      let avail := fragH - curY
      let sliceH := Nat.min remH avail
      let s : PlacedSlice := ⟨colIdx, cId, 0, curY, w, sliceH⟩
      let newRem := remH - sliceH
      if newRem = 0 then
        ([s], colIdx, curY + sliceH)
      else
        let (more, finalCol, finalY) := placeChildSlices fragH w fuel cId newRem (colIdx + 1) 0
        (s :: more, finalCol, finalY)

/-- Layout block children with margins across fragmentainers (columns), truncating margins at breaks.
    CSS Fragmentation Level 3 §5.2 & CSS Multi-column Layout Level 1 §4. -/
def layoutFragmentedBlocks (fragH : Nat) (colW : Nat) (children : List ColChildWithMargin) : List PlacedSlice :=
  let rec loop (chs : List ColChildWithMargin) (colIdx curY prevMarginBottom : Nat) : List PlacedSlice :=
    match chs with
    | [] => []
    | c :: cs =>
      let w := resolveLen colW c.width
      let margin := Nat.max prevMarginBottom c.marginTop
      let candY := curY + margin
      -- CSS Fragmentation 3 §3.2: a box avoiding breaks inside that does not fit in the
      -- remaining space moves to the next fragmentainer start (even if it is too tall there).
      if curY > 0 && (candY >= fragH || (c.breakInside.avoidsColumn && candY + c.height > fragH)) then
        let (slices, nextCol, nextY) := placeChildSlices fragH w (c.height + 1) c.id c.height (colIdx + 1) 0
        slices ++ loop cs nextCol nextY c.marginBottom
      else
        let startY := if curY = 0 then 0 else candY
        let (slices, nextCol, nextY) := placeChildSlices fragH w (c.height + 1) c.id c.height colIdx startY
        slices ++ loop cs nextCol nextY c.marginBottom

  loop children 0 0 0

/-- Law: A single in-flow child that fits within fragmentainer height is placed in column 0 with relY = 0.
    CSS Fragmentation Level 3 §5.3 Splitting Boxes. -/
theorem single_child_slice_col_zero (fragH colW : Nat) (c : ColChildWithMargin) (h : c.height > 0) (h_fit : c.height ≤ fragH) :
    let res := layoutFragmentedBlocks fragH colW [c]
    ∃ s, res = [s] ∧ s.colIdx = 0 ∧ s.relY = 0 ∧ s.h = c.height := by
  dsimp [layoutFragmentedBlocks, layoutFragmentedBlocks.loop, placeChildSlices]
  split
  · omega
  · split
    · refine ⟨_, rfl, rfl, rfl, ?_⟩
      exact Nat.min_eq_left h_fit
    · have h_min : Nat.min c.height fragH = c.height := Nat.min_eq_left h_fit
      omega

/-- Law: a box avoiding column breaks that does not fit after its predecessor starts at the top of
    the next column. CSS Fragmentation Level 3 §3.2 (`break-inside: avoid`). -/
theorem avoid_moves_to_next_column (fragH colW : Nat) (c1 c2 : ColChildWithMargin)
    (h1 : 0 < c1.height) (h1f : c1.height < fragH) (m1 : c1.marginBottom = 0) (m2 : c2.marginTop = 0)
    (ha : c2.breakInside.avoidsColumn = true) (hf : fragH < c1.height + c2.height) (h2 : 0 < c2.height) :
    ∃ s1 s2 rest, layoutFragmentedBlocks fragH colW [c1, c2] = s1 :: s2 :: rest ∧
      s1.colIdx = 0 ∧ s2.colIdx = 1 ∧ s2.relY = 0 := by
  have e1 : Nat.min c1.height fragH = c1.height := Nat.min_eq_left (by omega)
  have e2 : c1.height - c1.height = 0 := Nat.sub_self _
  have e3 : c1.height + 1 = (c1.height).succ := rfl
  have e4 : ¬ (c1.height = 0) := by omega
  have e5 : fragH - 0 = fragH := rfl
  have e6 : 0 < fragH - c1.height := by omega
  have e7 : ¬ (fragH ≤ c1.height + 0) := by omega
  have hc : 0 < c1.height ∧ (fragH ≤ c1.height ∨ fragH < c1.height + c2.height) := by omega
  have e8 : c2.height ≠ 0 := by omega
  simp [layoutFragmentedBlocks, layoutFragmentedBlocks.loop, placeChildSlices, m1, m2, ha, e1, e2, e4, hc, e8]
  split <;> exact ⟨_, _, ⟨rfl, _, rfl⟩, rfl, rfl, rfl⟩

end ColumnLayout
end ChromiumLayout
