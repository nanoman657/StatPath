/-
  TableLayout.lean: CSS Table Layout Level 3 algorithms,
  written from layout_table_test.cc, layout_table_section_test.cc, and table_layout_utils_test.cc.
  Owned by the block lane (Table*).
-/

namespace ChromiumLayout
namespace TableLayout

/-- HTML/CSS table section type (`<thead>`, `<tbody>`, `<tfoot>`). -/
inductive TableSectionType where
  | thead
  | tbody
  | tfoot
  deriving Inhabited, DecidableEq, Repr

/-- Specification of a table section. -/
structure TableSectionSpec where
  id : Nat := 0
  secType : TableSectionType
  rowCount : Nat := 0
  blockSize : Nat := 0
  percent : Option Nat := none
  deriving Inhabited, DecidableEq, Repr

/-- Order table sections in physical fragment order: thead first, tbody middle, tfoot last.
    Empty sections (rowCount = 0) generate no fragments and are omitted. -/
def orderTableSections (sections : List TableSectionSpec) : List TableSectionSpec :=
  let nonEmpty := sections.filter (fun s => s.rowCount > 0)
  let heads := nonEmpty.filter (fun s => s.secType == .thead)
  let bodies := nonEmpty.filter (fun s => s.secType == .tbody)
  let foots := nonEmpty.filter (fun s => s.secType == .tfoot)
  heads ++ bodies ++ foots

/-- Distribute rowspan cell extra height to covered rows (proportional or to non-empty rows). -/
def distributeRowspan (rowHeights : List Nat) (neededHeight : Nat) : List Nat :=
  let totalH := rowHeights.foldl (·+·) 0
  if totalH >= neededHeight then rowHeights
  else
    let nonZero := rowHeights.filter (· > 0)
    if nonZero.isEmpty then
      match rowHeights.reverse with
      | [] => []
      | _ :: rest => (neededHeight :: rest).reverse
    else if nonZero.length = 1 then
      rowHeights.map (fun h => if h > 0 then neededHeight else 0)
    else
      rowHeights.map (fun h => neededHeight * h / totalH)

/-- Distribute colspan min inline size across covered columns proportionally to max sizes. -/
def distributeColspanAuto (colMaxSizes : List Nat) (neededSize : Nat) : List Nat :=
  let totalMax := colMaxSizes.foldl (·+·) 0
  if totalMax = 0 then
    let n := colMaxSizes.length
    if n = 0 then []
    else List.replicate n (neededSize / n)
  else
    colMaxSizes.map (fun m => neededSize * m / totalMax)

/-- Distribute colspan percentage across covered non-percent columns. -/
def distributeColspanPercent (colMaxSizes : List Nat) (existingPercents : List (Option Nat)) (neededPercent : Nat) : List Nat :=
  let assignedPercent := (existingPercents.filterMap id).foldl (·+·) 0
  let remPercent := if neededPercent > assignedPercent then neededPercent - assignedPercent else 0
  let nonPercentMax := (colMaxSizes.zip existingPercents).filterMap (fun (m, p) => if p.isNone then some m else none)
  let totalNonPercentMax := nonPercentMax.foldl (·+·) 0
  if totalNonPercentMax = 0 then
    let n := nonPercentMax.length
    if n = 0 then [] else List.replicate n (remPercent / n)
  else
    nonPercentMax.map (fun m => remPercent * m / totalNonPercentMax)

/-- Distribute section fixed block size to rows with percentage support. -/
def distributeSectionBlockSizeToRows (rowHeights : List Nat) (rowPercents : List (Option Nat)) (totalSize : Nat) : List Nat :=
  let percentRows := rowPercents.map (fun p => p.map (fun pct => totalSize * pct / 100))
  let assignedPercent := (percentRows.filterMap id).foldl (·+·) 0
  let remSize := if totalSize > assignedPercent then totalSize - assignedPercent else 0
  let nonPercentCount := (rowPercents.filter (·.isNone)).length
  let perRow := if nonPercentCount > 0 then remSize / nonPercentCount else 0
  (percentRows.zip rowHeights).map (fun (pOpt, _) =>
    match pOpt with
    | some p => p
    | none => perRow)

/-- Distribute table block size to sections with percentage support. -/
def distributeTableBlockSizeToSections (sections : List (Nat × Option Nat)) (tableSize : Nat) : List Nat :=
  let percentSecs := sections.map (fun (_, pOpt) => pOpt.map (fun pct => tableSize * pct / 100))
  let assignedPercent := (percentSecs.filterMap id).foldl (·+·) 0
  let remSize := if tableSize > assignedPercent then tableSize - assignedPercent else 0
  let nonPercentCount := (sections.filter (fun (_, p) => p.isNone)).length
  let perSec := if nonPercentCount > 0 then remSize / nonPercentCount else 0
  (percentSecs.zip sections).map (fun (pOpt, (h, _)) =>
    match pOpt with
    | some p => p
    | none => if perSec > 0 then perSec else h)

/-- Maximum table width in Blink (`TableLayoutAlgorithm::kMaxTableWidth`). -/
def kMaxTableWidth : Nat := 1000000

/-- Clamp table width to maximum allowed width. -/
def clampTableWidth (w : Nat) : Nat :=
  Nat.min w kMaxTableWidth

/-- In collapsed border model, table padding is ignored (CSS 2.1 §17.6.2). -/
def tablePadding (borderCollapse : Bool) (specifiedPadding : Nat) : Nat :=
  if borderCollapse then 0 else specifiedPadding

/-- Table width is always clamped to at most kMaxTableWidth. -/
theorem clampTableWidth_le (w : Nat) :
    clampTableWidth w ≤ kMaxTableWidth := by
  unfold clampTableWidth
  apply Nat.min_le_right

/-- Padding in collapsed border model is always 0. -/
theorem collapsed_border_padding_zero (p : Nat) :
    tablePadding true p = 0 := by
  rfl

/-- A border specification for table elements in collapsed borders model. CSS 2.1 §17.6.2. -/
structure TableBorder where
  width : Nat := 0
  isHidden : Bool := false
  deriving Inhabited, DecidableEq, Repr

/-- Resolve conflict between borders on a shared edge. CSS 2.1 §17.6.2.1.
    A border with 'hidden' takes precedence over all other borders and collapses to 0.
    Otherwise, the widest border wins. -/
def resolveBorderConflict (borders : List TableBorder) : Nat :=
  if borders.any (·.isHidden) then 0
  else borders.foldl (fun acc b => Nat.max acc b.width) 0

/-- Outset of a collapsed border in LayoutUnit quanta (1/64th px), which is (resolved width / 2) * 64 = resolved width * 32.
    CSS 2.1 §17.6.2. -/
def collapsedBorderOutsetLU (borders : List TableBorder) : Nat :=
  resolveBorderConflict borders * 32

/-- Synchronize assignable table inline size and columns. CSS Table 3 §3, CSS 2.1 §17.5.2.
    When assignable table inline size equals the sum of column maximum sizes, each column
    size is exactly its maximum size (no redistribution). -/
def synchronizeColumns (assignableTableSize : Nat) (colMaxSizes : List Nat) : List Nat :=
  let totalMax := colMaxSizes.foldl (·+·) 0
  if assignableTableSize == totalMax then
    colMaxSizes
  else
    distributeColspanAuto colMaxSizes assignableTableSize

/-- Column constraints for computing table grid min/max inline sizes. CSS Table 3 §3. -/
structure TableColConstraint where
  minSize : Nat := 0
  maxSize : Nat := 0
  pct : Option Nat := none
  deriving Inhabited, DecidableEq, Repr

/-- Compute grid inline min/max sizes. CSS 2.1 §17.5.2.1, CSS Table 3 §3. -/
def computeGridInlineMinMax (cols : List TableColConstraint) (isLayoutPass : Bool) : Nat × Nat :=
  let minSize := cols.foldl (fun acc c => acc + c.minSize) 0
  let rawMaxSize := cols.foldl (fun acc c => acc + c.maxSize) 0
  if !isLayoutPass then
    (minSize, rawMaxSize)
  else
    let totalPct := cols.foldl (fun acc c => acc + match c.pct with | some p => p | none => 0) 0
    let nonPctMax := cols.foldl (fun acc c => acc + match c.pct with | some _ => 0 | none => c.maxSize) 0
    let maxFromNonPct :=
      if totalPct > 0 && totalPct < 100 then
        nonPctMax + (totalPct * nonPctMax / (100 - totalPct))
      else rawMaxSize
    let maxFromPcts := cols.foldl (fun acc c =>
      match c.pct with
      | some p => if p > 0 then Nat.max acc (c.maxSize * 100 / p) else acc
      | none => acc) 0
    let maxSize := Nat.max rawMaxSize (Nat.max maxFromNonPct maxFromPcts)
    (minSize, maxSize)

/-- Law: Any border set containing a hidden border resolves to 0 width.
    CSS 2.1 §17.6.2.1. -/
theorem resolve_hidden_zero (borders : List TableBorder) (h : borders.any (·.isHidden) = true) :
    resolveBorderConflict borders = 0 := by
  dsimp [resolveBorderConflict]
  rw [h]
  rfl

/-- Law: When assignable size equals total max size, columns equal their max sizes without redistribution.
    CSS 2.1 §17.5.2. -/
theorem sync_exact_max (colMaxSizes : List Nat) :
    synchronizeColumns (colMaxSizes.foldl (·+·) 0) colMaxSizes = colMaxSizes := by
  dsimp [synchronizeColumns]
  simp

/-- Law: Table grid minimum inline size is always the sum of column minimum sizes.
    CSS 2.1 §17.5.2.1, CSS Table 3 §3. -/
theorem grid_min_sum (cols : List TableColConstraint) (pass : Bool) :
    (computeGridInlineMinMax cols pass).1 = cols.foldl (fun acc c => acc + c.minSize) 0 := by
  dsimp [computeGridInlineMinMax]
  split <;> rfl

end TableLayout
end ChromiumLayout
