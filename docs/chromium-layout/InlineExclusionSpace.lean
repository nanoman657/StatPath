/-!
# Chromium Inline Exclusion Space Model

Formalization of Chromium's exclusion space and layout opportunity derivation
based on:
- **CSS 2.1 §9.5**: Visual formatting model - Floats (`float`, `clear`, float placement rules)
- **CSS Inline 3 §3**: Initial Letters (`initial-letter`, drop/raise clearance)
- **CSS Exclusions 1 §3**: Exclusion Areas and Opportunities
- **CSS Writing Modes 3 §4**: Inline-level Alignment and Text Direction

Corresponds to Blink's:
- `third_party/blink/renderer/core/layout/exclusions/exclusion_space.h`
- `third_party/blink/renderer/core/layout/exclusions/exclusion_space.cc`
- `third_party/blink/renderer/core/layout/exclusions/exclusion_area.h`
- `third_party/blink/renderer/core/layout/exclusions/layout_opportunity.h`
- `third_party/blink/renderer/core/layout/exclusions/layout_opportunity.cc`
-/

namespace Chromium.Layout

/-! ## 1. Core Constants & Enumerations -/

/-- CSS 2.1 §9.5 & Blink `LayoutUnit::Max()` raw representation (`2^30 - 1`). -/
def layoutUnitMax : Int := 1073741823

/-- CSS 2.1 §9.5 & Blink `LayoutUnit::Min()` raw representation (`-2^30`). -/
def layoutUnitMin : Int := -1073741824

/-- CSS 2.1 §9.5.1: Float placement direction (`EFloat`). -/
inductive EFloat where
  | kNone
  | kLeft
  | kRight
deriving DecidableEq, Repr

/-- CSS 2.1 §9.5.2: Float clearance mode (`EClear`). -/
inductive EClear where
  | kNone
  | kLeft
  | kRight
  | kBoth
deriving DecidableEq, Repr

/-- CSS Writing Modes 3 §4: Text Direction (`TextDirection`). -/
inductive TextDirection where
  | kLtr
  | kRtl
deriving DecidableEq, Repr

/-! ## 2. Geometric Coordinates & Rectangles -/

/-- Block Formatting Context coordinate point (`BfcOffset`). -/
structure BfcOffset where
  line_offset : Int
  block_offset : Int
deriving DecidableEq, Repr

/-- Block Formatting Context rectangle (`BfcRect`). -/
structure BfcRect where
  start_offset : BfcOffset
  end_offset : BfcOffset
deriving DecidableEq, Repr

def BfcRect.lineStartOffset (r : BfcRect) : Int := r.start_offset.line_offset
def BfcRect.lineEndOffset (r : BfcRect) : Int := r.end_offset.line_offset
def BfcRect.blockStartOffset (r : BfcRect) : Int := r.start_offset.block_offset
def BfcRect.blockEndOffset (r : BfcRect) : Int := r.end_offset.block_offset
def BfcRect.inlineSize (r : BfcRect) : Int := r.end_offset.line_offset - r.start_offset.line_offset
def BfcRect.blockSize (r : BfcRect) : Int := r.end_offset.block_offset - r.start_offset.block_offset

/-- Single layout opportunity rectangle (`LayoutOpportunity`). -/
structure LayoutOpportunity where
  rect : BfcRect
deriving DecidableEq, Repr

/-- Line layout opportunity (`LineLayoutOpportunity`). -/
structure LineLayoutOpportunity where
  line_left_offset : Int
  line_right_offset : Int
deriving DecidableEq, Repr

/-- Minimal ConstraintSpace representation for line layout opportunity computation. -/
structure ConstraintSpace where
  direction : TextDirection
  bfc_offset : BfcOffset
  available_inline_size : Int
  available_block_size : Int
deriving DecidableEq, Repr

/-- CSS 2.1 §9.5 & Blink `LayoutOpportunity::ComputeLineLayoutOpportunity`:
    Derives line-left and line-right offsets from a layout opportunity, clamping
    the non-dominant side against available inline size in constraint space. -/
def LayoutOpportunity.computeLineLayoutOpportunity
    (opp : LayoutOpportunity)
    (space : ConstraintSpace)
    (_line_block_size : Int := 0)
    (_block_delta : Int := 0) : LineLayoutOpportunity :=
  let line_left := opp.rect.lineStartOffset
  let line_right := opp.rect.lineEndOffset
  match space.direction with
  | TextDirection.kLtr =>
    let avail_right := space.bfc_offset.line_offset + space.available_inline_size
    let clamped_right := max (min line_right avail_right) line_left
    { line_left_offset := line_left, line_right_offset := clamped_right }
  | TextDirection.kRtl =>
    let avail_left := space.bfc_offset.line_offset
    let clamped_left := min (max line_left avail_left) line_right
    { line_left_offset := clamped_left, line_right_offset := line_right }

/-! ## 3. Exclusion Areas & Shelf Structures -/

/-- Single exclusion area (`ExclusionArea`). -/
structure ExclusionArea where
  rect : BfcRect
  type : EFloat
  isInitialLetter : Bool := false
deriving DecidableEq, Repr

def ExclusionArea.create (rect : BfcRect) (type : EFloat := EFloat.kLeft) : ExclusionArea :=
  { rect := rect, type := type, isInitialLetter := false }

def ExclusionArea.createForInitialLetterBox (rect : BfcRect) (type : EFloat := EFloat.kLeft) : ExclusionArea :=
  { rect := rect, type := type, isInitialLetter := true }

/-- Float vertical span edge against a shelf (`ShelfEdge`). -/
structure ShelfEdge where
  block_start : Int
  block_end : Int
deriving DecidableEq, Repr

/-- Internal horizontal shelf representing the bottom of one or more floats (`Shelf`). -/
structure Shelf where
  block_offset : Int
  line_left : Int
  line_right : Int
  line_left_edges : List ShelfEdge
  line_right_edges : List ShelfEdge
deriving DecidableEq, Repr

/-- Closed-off layout opportunity area above an added float (`ClosedArea`). -/
structure ClosedArea where
  opportunity : LayoutOpportunity
  line_left_edges : List ShelfEdge
  line_right_edges : List ShelfEdge
deriving DecidableEq, Repr

/-- Check if an edge vector contains a solid float edge spanning the block range. -/
def hasSolidEdges (edges : List ShelfEdge) (block_start block_end : Int) : Bool :=
  if edges.isEmpty then true
  else edges.any (fun e => e.block_end > block_start && e.block_start < block_end)

/-- Retain solid edges that extend past the specified block offset limit. -/
def collectSolidEdges (edges : List ShelfEdge) (block_offset : Int) : List ShelfEdge :=
  edges.filter (fun e => e.block_end > block_offset)

/-- Check if an opportunity intersects the query area. -/
def intersectsOpp (opp : LayoutOpportunity) (offset : BfcOffset) (inline_size : Int) : Bool :=
  opp.rect.lineEndOffset >= offset.line_offset &&
  opp.rect.lineStartOffset <= offset.line_offset + inline_size &&
  opp.rect.blockEndOffset > offset.block_offset

/-- Slice a closed area opportunity by query offset and available inline size. -/
def createLayoutOpportunityFromArea (opp : LayoutOpportunity) (offset : BfcOffset) (inline_size : Int) : LayoutOpportunity :=
  let start_line := max opp.rect.lineStartOffset offset.line_offset
  let start_block := max opp.rect.blockStartOffset offset.block_offset
  let end_line := min opp.rect.lineEndOffset (offset.line_offset + inline_size)
  let end_block := opp.rect.blockEndOffset
  { rect := { start_offset := { line_offset := start_line, block_offset := start_block },
              end_offset := { line_offset := end_line, block_offset := end_block } } }

/-- Derive an opportunity from a shelf, clamping negative inline size to dominant edge. -/
def createLayoutOpportunityFromShelf (shelf : Shelf) (offset : BfcOffset) (inline_size : Int) (direction : TextDirection) : LayoutOpportunity :=
  let left0 := max shelf.line_left offset.line_offset
  let right0 := min shelf.line_right (offset.line_offset + inline_size)
  let (left, right) :=
    match direction with
    | TextDirection.kLtr => (left0, max right0 left0)
    | TextDirection.kRtl => (min left0 right0, right0)
  let start_block := max shelf.block_offset offset.block_offset
  { rect := { start_offset := { line_offset := left, block_offset := start_block },
              end_offset := { line_offset := right, block_offset := layoutUnitMax } } }

/-! ## 4. Derived Geometry & Opportunity Iteration -/

/-- Derived geometric state maintaining sorted shelves and completed closed-off areas. -/
structure DerivedGeometry where
  shelves : List Shelf
  areas : List ClosedArea
deriving DecidableEq, Repr

def DerivedGeometry.init : DerivedGeometry :=
  { shelves := [{ block_offset := layoutUnitMin,
                  line_left := layoutUnitMin,
                  line_right := layoutUnitMax,
                  line_left_edges := [],
                  line_right_edges := [] }],
    areas := [] }

def insertClosedArea (area : ClosedArea) (areas : List ClosedArea) : List ClosedArea :=
  let rec insertLoop (acc : List ClosedArea) : List ClosedArea → List ClosedArea
    | [] => (area :: acc).reverse
    | a :: as =>
      if area.opportunity.rect.blockStartOffset < a.opportunity.rect.blockStartOffset then
        acc.reverse ++ (area :: a :: as)
      else
        insertLoop (a :: acc) as
  insertLoop [] areas

/-- CSS 2.1 §9.5 & Blink `DerivedGeometry::Add`:
    Updates horizontal shelves and creates closed layout opportunities when an exclusion is placed. -/
def DerivedGeometry.addExclusion (geom : DerivedGeometry) (exclusion : ExclusionArea) : DerivedGeometry :=
  if exclusion.rect.lineEndOffset <= exclusion.rect.lineStartOffset then geom
  else
    let excl_end := exclusion.rect.blockEndOffset
    let rec processShelves (fuel : Nat) (idx : Nat) (shelves : List Shelf) (areas : List ClosedArea) : (List Shelf × List ClosedArea) :=
      match fuel with
      | 0 => (shelves, areas)
      | fuel' + 1 =>
        if h : idx < shelves.length then
          let shelf := shelves.get ⟨idx, h⟩
          let next_block_opt : Option Int :=
            if h2 : idx + 1 < shelves.length then some (shelves.get ⟨idx + 1, h2⟩).block_offset else none
          let is_between :=
            excl_end >= shelf.block_offset &&
            match next_block_opt with
            | none => true
            | some next_b => excl_end < next_b
          let shelf_copy := shelf

          let is_below := exclusion.rect.blockStartOffset > shelf.block_offset
          let new_areas :=
            if is_below then
              let has_solid :=
                hasSolidEdges shelf.line_left_edges shelf.block_offset exclusion.rect.blockStartOffset &&
                hasSolidEdges shelf.line_right_edges shelf.block_offset exclusion.rect.blockStartOffset
              let is_overlapping :=
                match exclusion.type with
                | EFloat.kLeft =>
                  exclusion.rect.lineStartOffset <= shelf.line_right &&
                  exclusion.rect.lineEndOffset > shelf.line_left
                | _ =>
                  exclusion.rect.lineStartOffset < shelf.line_right &&
                  exclusion.rect.lineEndOffset >= shelf.line_left
              if has_solid && is_overlapping then
                let opp : LayoutOpportunity :=
                  { rect := { start_offset := { line_offset := shelf.line_left, block_offset := shelf.block_offset },
                              end_offset := { line_offset := shelf.line_right, block_offset := exclusion.rect.blockStartOffset } } }
                insertClosedArea { opportunity := opp, line_left_edges := shelf.line_left_edges, line_right_edges := shelf.line_right_edges } areas
              else areas
            else areas

          let is_intersecting := !is_below && excl_end > shelf.block_offset
          let (updated_shelf, should_modify) : (Shelf × Bool) :=
            if is_below || is_intersecting then
              if exclusion.type == EFloat.kLeft then
                if exclusion.rect.lineEndOffset >= shelf.line_left then
                  let edges := if exclusion.rect.lineEndOffset > shelf.line_left then [] else shelf.line_left_edges
                  let s := { shelf with line_left := exclusion.rect.lineEndOffset,
                                        line_left_edges := edges ++ [{ block_start := exclusion.rect.blockStartOffset, block_end := exclusion.rect.blockEndOffset }] }
                  (s, true)
                else (shelf, true)
              else
                if exclusion.rect.lineStartOffset <= shelf.line_right then
                  let edges := if exclusion.rect.lineStartOffset < shelf.line_right then [] else shelf.line_right_edges
                  let s := { shelf with line_right := exclusion.rect.lineStartOffset,
                                        line_right_edges := edges ++ [{ block_start := exclusion.rect.blockStartOffset, block_end := exclusion.rect.blockEndOffset }] }
                  (s, true)
                else (shelf, true)
            else (shelf, false)

          let is_closed_off := updated_shelf.line_left > updated_shelf.line_right
          let is_same_as_previous :=
            if h_prev : idx > 0 ∧ idx - 1 < shelves.length then
              let prev := shelves.get ⟨idx - 1, h_prev.2⟩
              updated_shelf.line_left == prev.line_left && updated_shelf.line_right == prev.line_right
            else false

          let (shelves_after_modify, next_idx) :=
            if should_modify && (is_closed_off || is_same_as_previous) then
              (shelves.eraseIdx idx, idx)
            else
              (shelves.set idx updated_shelf, idx + 1)

          if is_between then
            if excl_end != shelf_copy.block_offset then
              let left_edges := collectSolidEdges shelf_copy.line_left_edges excl_end
              let right_edges := collectSolidEdges shelf_copy.line_right_edges excl_end
              let new_left := if left_edges.isEmpty then layoutUnitMin else shelf_copy.line_left
              let new_right := if right_edges.isEmpty then layoutUnitMax else shelf_copy.line_right
              let new_shelf : Shelf :=
                { block_offset := excl_end,
                  line_left := new_left,
                  line_right := new_right,
                  line_left_edges := left_edges,
                  line_right_edges := right_edges }
              let insert_pos := if should_modify && (is_closed_off || is_same_as_previous) then idx else idx + 1
              (shelves_after_modify.insertIdx insert_pos new_shelf, new_areas)
            else
              (shelves_after_modify, new_areas)
          else
            processShelves fuel' next_idx shelves_after_modify new_areas
        else (shelves, areas)
    let (final_shelves, final_areas) := processShelves (geom.shelves.length * 2 + 2) 0 geom.shelves geom.areas
    { shelves := final_shelves, areas := final_areas }

def DerivedGeometry.allLayoutOpportunities
    (geom : DerivedGeometry)
    (offset : BfcOffset)
    (inline_size : Int)
    (direction : TextDirection) : List LayoutOpportunity :=
  let rec loop (fuel : Nat) (shelves : List Shelf) (areas : List ClosedArea) (acc : List LayoutOpportunity) : List LayoutOpportunity :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      match shelves, areas with
      | [], _ => acc.reverse
      | shelf :: rest_shelves, [] =>
        let has_solid :=
          hasSolidEdges shelf.line_left_edges offset.block_offset layoutUnitMax &&
          hasSolidEdges shelf.line_right_edges offset.block_offset layoutUnitMax
        let new_acc :=
          if has_solid then
            createLayoutOpportunityFromShelf shelf offset inline_size direction :: acc
          else acc
        loop fuel' rest_shelves [] new_acc
      | shelf :: rest_shelves, area :: rest_areas =>
        if !intersectsOpp area.opportunity offset inline_size then
          loop fuel' (shelf :: rest_shelves) rest_areas acc
        else
          let start_b := max area.opportunity.rect.blockStartOffset offset.block_offset
          let shelf_b := max shelf.block_offset offset.block_offset
          if start_b <= shelf_b then
            let end_b := area.opportunity.rect.blockEndOffset
            let has_solid :=
              hasSolidEdges area.line_left_edges start_b end_b &&
              hasSolidEdges area.line_right_edges start_b end_b
            let new_acc :=
              if has_solid then
                createLayoutOpportunityFromArea area.opportunity offset inline_size :: acc
              else acc
            loop fuel' (shelf :: rest_shelves) rest_areas new_acc
          else
            let has_solid :=
              hasSolidEdges shelf.line_left_edges offset.block_offset layoutUnitMax &&
              hasSolidEdges shelf.line_right_edges offset.block_offset layoutUnitMax
            let new_acc :=
              if has_solid then
                createLayoutOpportunityFromShelf shelf offset inline_size direction :: acc
              else acc
            loop fuel' rest_shelves (area :: rest_areas) new_acc
  loop (geom.shelves.length + geom.areas.length + 1) geom.shelves geom.areas []

/-! ## 5. Exclusion Space Model & Clearance Calculations -/

/-- Main exclusion space tracking placed float exclusions and clearance lines (`ExclusionSpace`). -/
structure ExclusionSpace where
  exclusions : List ExclusionArea := []
  left_clear_offset : Int := layoutUnitMin
  right_clear_offset : Int := layoutUnitMin
  initial_letter_left_clear_offset : Int := layoutUnitMin
  initial_letter_right_clear_offset : Int := layoutUnitMin
deriving DecidableEq, Repr

/-- Add an exclusion area to the space, updating clearance offsets and exclusion lists. -/
def ExclusionSpace.add (space : ExclusionSpace) (exclusion : ExclusionArea) : ExclusionSpace :=
  let clear_offset := exclusion.rect.blockEndOffset
  if exclusion.isInitialLetter then
    let new_left_clear :=
      if exclusion.type == EFloat.kLeft then max space.initial_letter_left_clear_offset clear_offset
      else space.initial_letter_left_clear_offset
    let new_right_clear :=
      if exclusion.type == EFloat.kRight then max space.initial_letter_right_clear_offset clear_offset
      else space.initial_letter_right_clear_offset
    let rec insertByBlockStart (excl : ExclusionArea) : List ExclusionArea → List ExclusionArea
      | [] => [excl]
      | e :: es =>
        if excl.rect.blockStartOffset < e.rect.blockStartOffset then excl :: e :: es
        else e :: insertByBlockStart excl es
    { space with
      exclusions := insertByBlockStart exclusion space.exclusions,
      initial_letter_left_clear_offset := new_left_clear,
      initial_letter_right_clear_offset := new_right_clear }
  else
    let new_left_clear :=
      if exclusion.type == EFloat.kLeft then max space.left_clear_offset clear_offset
      else space.left_clear_offset
    let new_right_clear :=
      if exclusion.type == EFloat.kRight then max space.right_clear_offset clear_offset
      else space.right_clear_offset
    { space with
      exclusions := space.exclusions ++ [exclusion],
      left_clear_offset := new_left_clear,
      right_clear_offset := new_right_clear }

/-- CSS 2.1 §9.5.2: Float clearance block offset (`ClearanceOffset`). -/
def ExclusionSpace.clearanceOffset (space : ExclusionSpace) (clear_type : EClear) : Int :=
  match clear_type with
  | EClear.kNone => layoutUnitMin
  | EClear.kLeft => space.left_clear_offset
  | EClear.kRight => space.right_clear_offset
  | EClear.kBoth => max space.left_clear_offset space.right_clear_offset

/-- CSS Inline 3 §3: Initial letter clearance block offset (`InitialLetterClearanceOffset`). -/
def ExclusionSpace.initialLetterClearanceOffset (space : ExclusionSpace) (clear_type : EClear) : Int :=
  match clear_type with
  | EClear.kNone => layoutUnitMin
  | EClear.kLeft => space.initial_letter_left_clear_offset
  | EClear.kRight => space.initial_letter_right_clear_offset
  | EClear.kBoth => max space.initial_letter_left_clear_offset space.initial_letter_right_clear_offset

/-- Helper returning { kBoth, kLeft, kRight } clearance vector matching test expectations. -/
def ExclusionSpace.initialLetterClearanceOffsets (space : ExclusionSpace) : List Int :=
  [space.initialLetterClearanceOffset EClear.kBoth,
   space.initialLetterClearanceOffset EClear.kLeft,
   space.initialLetterClearanceOffset EClear.kRight]

/-- Builds derived geometry from the sorted list of exclusions. -/
def ExclusionSpace.derivedGeometry (space : ExclusionSpace) : DerivedGeometry :=
  space.exclusions.foldl DerivedGeometry.addExclusion DerivedGeometry.init

/-- CSS Exclusions 1 §3: Returns all layout opportunities available at the given query position. -/
def ExclusionSpace.allLayoutOpportunities
    (space : ExclusionSpace)
    (offset : BfcOffset)
    (available_inline_size : Int)
    (direction : TextDirection := TextDirection.kLtr) : List LayoutOpportunity :=
  let max_clear :=
    max (max space.left_clear_offset space.right_clear_offset)
        (max space.initial_letter_left_clear_offset space.initial_letter_right_clear_offset)
  if offset.block_offset >= max_clear then
    let end_line := offset.line_offset + max 0 available_inline_size
    [{ rect := { start_offset := offset,
                 end_offset := { line_offset := end_line, block_offset := layoutUnitMax } } }]
  else
    space.derivedGeometry.allLayoutOpportunities offset available_inline_size direction

/-- Finds the first layout opportunity fitting `minimal_inline_size`. -/
def ExclusionSpace.findLayoutOpportunity
    (space : ExclusionSpace)
    (offset : BfcOffset)
    (available_inline_size : Int)
    (direction : TextDirection := TextDirection.kLtr)
    (minimal_inline_size : Int := 0) : LayoutOpportunity :=
  let opps := space.allLayoutOpportunities offset available_inline_size direction
  match opps.find? (fun opp => opp.rect.inlineSize >= minimal_inline_size ||
                               (opp.rect.inlineSize == available_inline_size && opp.rect.lineStartOffset == offset.line_offset)) with
  | some opp => opp
  | none =>
    let end_line := offset.line_offset + max 0 available_inline_size
    { rect := { start_offset := offset,
                end_offset := { line_offset := end_line, block_offset := layoutUnitMax } } }

/-- Merges exclusions from cached layout results shifted by offset_delta (`MergeExclusionSpaces`). -/
def ExclusionSpace.mergeExclusionSpaces
    (old_output old_input new_input : ExclusionSpace)
    (offset_delta : BfcOffset) : ExclusionSpace :=
  let added_exclusions := old_output.exclusions.drop old_input.exclusions.length
  let shifted_exclusions := added_exclusions.map (fun e =>
    let r := e.rect
    let new_start : BfcOffset := { line_offset := r.start_offset.line_offset + offset_delta.line_offset,
                                   block_offset := r.start_offset.block_offset + offset_delta.block_offset }
    let new_end : BfcOffset := { line_offset := r.end_offset.line_offset + offset_delta.line_offset,
                                 block_offset := r.end_offset.block_offset + offset_delta.block_offset }
    { e with rect := { start_offset := new_start, end_offset := new_end } })
  shifted_exclusions.foldl ExclusionSpace.add new_input

/-! ## 6. General Theorems & Invariants -/

/-- General Law: Clearance of EClear.kNone is always layoutUnitMin. -/
theorem clearanceOffset_kNone (space : ExclusionSpace) :
    space.clearanceOffset EClear.kNone = layoutUnitMin := by
  rfl

/-- General Law: Initial letter clearance of EClear.kNone is always layoutUnitMin. -/
theorem initialLetterClearanceOffset_kNone (space : ExclusionSpace) :
    space.initialLetterClearanceOffset EClear.kNone = layoutUnitMin := by
  rfl

/-- General Law: Initial letter clearance for EClear.kBoth equals the maximum of kLeft and kRight. -/
theorem initialLetterClearanceOffset_both (space : ExclusionSpace) :
    space.initialLetterClearanceOffset EClear.kBoth =
    max (space.initialLetterClearanceOffset EClear.kLeft)
        (space.initialLetterClearanceOffset EClear.kRight) := by
  rfl

/-- General Law: Merging exclusion spaces when the cached pass produced no new exclusions
    preserves new_input identically. -/
theorem mergeExclusionSpaces_empty_old_output
    (old_input new_input : ExclusionSpace) (delta : BfcOffset) :
    ExclusionSpace.mergeExclusionSpaces old_input old_input new_input delta = new_input := by
  dsimp [ExclusionSpace.mergeExclusionSpaces]
  rw [List.drop_length]
  rfl

end Chromium.Layout
