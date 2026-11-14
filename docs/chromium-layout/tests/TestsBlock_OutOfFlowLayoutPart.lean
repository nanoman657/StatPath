import BlockAbsolute
import ColumnLayout

namespace TestsBlock

open ChromiumLayout.BlockAbsolute
open ChromiumLayout.ColumnLayout

-- out_of_flow_layout_part_test.cc:46: FixedInsideAbs
-- #abs is at top:49, left:0. #pad has height:50.
-- fixed1 has no explicit top/left; static position top is #abs.top + #pad.height = 99.
-- fixed2 has top:9, left:7.
def fixedInsideAbs_fixed1 : OofDescendant :=
  { posType := .fixed, top := .auto, width := .px 50, staticTop := 50 }

def fixedInsideAbs_fixed2 : OofDescendant :=
  { posType := .fixed, top := .px 9, left := .px 7 }

theorem FixedInsideAbs_offsets :
    -- fixed1 top is static: #abs.top (49) + #pad.height (50) = 99
    (resolveOofOffset 49 0 fixedInsideAbs_fixed1).2 = 99 ∧
    -- fixed2 top is positioned: #fixed2.top = 9, left = 7
    (resolveOofOffset 49 0 fixedInsideAbs_fixed2).2 = 9 ∧
    (resolveOofOffset 49 0 fixedInsideAbs_fixed2).1 = 7 := by
  decide

-- out_of_flow_layout_part_test.cc:103: OutOfFlowLayoutPartTest.PositionedInMulticol
-- Out-of-flow positioned nodes inside a multi-column with relative containing blocks.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2.
theorem PositionedInMulticol_vectors :
    let colWidth := (1000 - 16) / 2
    let col0Offset := 0
    let col1Offset := colWidth + 16
    let child1Slice0Height := 40
    let child1Slice1Height := 10
    let relBlockOffsetInCol1 := child1Slice1Height
    let abs1Top := resolveMulticolOofOffset relBlockOffsetInCol1 10
    let abs2Top := resolveMulticolOofOffset relBlockOffsetInCol1 20
    colWidth = 492 ∧
    col0Offset = 0 ∧
    col1Offset = 508 ∧
    child1Slice0Height = 40 ∧
    child1Slice1Height = 10 ∧
    relBlockOffsetInCol1 = 10 ∧
    abs1Top = 20 ∧
    abs2Top = 30 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:149: OutOfFlowLayoutPartTest.SimplePositionedFragmentation
-- Positioned nodes fragment across columns when exceeding available fragmentainer height.
-- CSS Multi-column Layout Level 1 §2, CSS Fragmentation Level 3 §2, §4.
theorem SimplePositionedFragmentation_vectors :
    let fragH := 40
    let col0Offset := columnInlineOffset 0 492 16
    let col1Offset := columnInlineOffset 1 492 16
    let col2Offset := columnInlineOffset 2 492 16
    let inflowSlice0H := 40
    let inflowSlice1H := 10
    let relBlockOffsetInCol1 := inflowSlice1H
    let absBoxH := 50 + 2 * 5 + 2 * 2
    let absW := 5 + 2 * 5 + 2 * 2
    let absStartY := resolveMulticolOofOffset relBlockOffsetInCol1 0 + 5
    let slices := fragmentOofWithContent 1 absStartY absBoxH absBoxH fragH
    let totalCols := multicolTotalColumns 2 slices
    col0Offset = 0 ∧
    col1Offset = 508 ∧
    col2Offset = 1016 ∧
    inflowSlice0H = 40 ∧
    inflowSlice1H = 10 ∧
    absBoxH = 64 ∧
    absW = 19 ∧
    absStartY = 15 ∧
    slices = [⟨1, 15, 25, 25⟩, ⟨2, 0, 39, 39⟩] ∧
    totalCols = 3 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:191: OutOfFlowLayoutPartTest.PositionedFragmentationWithOverflow
-- Positioned node with overflowing child fragments across columns, producing a zero-height
-- parent continuation fragment to host the child's continuation slice.
-- CSS Multi-column Layout Level 1 §2, CSS Fragmentation Level 3 §2, §4.
theorem PositionedFragmentationWithOverflow_vectors :
    let fragH := 40
    let col0Offset := columnInlineOffset 0 492 16
    let col1Offset := columnInlineOffset 1 492 16
    let col2Offset := columnInlineOffset 2 492 16
    let absBoxH := 10
    let childH := 50
    let absStartY := resolveMulticolOofOffset 0 10
    let slices := fragmentOofWithContent 0 absStartY absBoxH childH fragH
    col0Offset = 0 ∧
    col1Offset = 508 ∧
    col2Offset = 1016 ∧
    absStartY = 10 ∧
    slices = [⟨0, 10, 10, 30⟩, ⟨1, 0, 0, 20⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:238: OutOfFlowLayoutPartTest.PositionedFragmentationWithNewColumns
-- Positioned node fragments beyond the initial column count, creating new columns as needed.
-- CSS Multi-column Layout Level 1 §2, CSS Fragmentation Level 3 §2.
theorem PositionedFragmentationWithNewColumns_vectors :
    let fragH := 40
    let absBoxH := 120
    let absStartY := resolveMulticolOofOffset 0 0
    let slices := fragmentOofWithContent 0 absStartY absBoxH absBoxH fragH
    let totalCols := multicolTotalColumns 2 slices
    slices = [⟨0, 0, 40, 40⟩, ⟨1, 0, 40, 40⟩, ⟨2, 0, 40, 40⟩] ∧
    totalCols = 3 := by
  exact ⟨rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:320: OutOfFlowLayoutPartTest.BreakInsideAvoid
-- An absolute positioned element with break-inside: avoid is not pushed to the next
-- column; it fragments across columns. CSS Fragmentation Level 3 §3.2.
theorem BreakInsideAvoid_vectors :
    let desc : OofDescendant := { posType := .absolute, width := .px 40, height := .px 40, breakInside := .avoid }
    let slices := fragmentOof 40 492 desc false false 0 0 10 40 40
    slices = [⟨0, 0, 10, 40, 30, []⟩, ⟨1, 0, 0, 40, 10, []⟩] := by
  decide

-- out_of_flow_layout_part_test.cc:359: OutOfFlowLayoutPartTest.BreakBeforeColumn
theorem BreakBeforeColumn_vectors :
    let desc : OofDescendant := { posType := .absolute, width := .px 40, height := .px 30 }
    let slices := fragmentOof 40 492 desc true false 0 0 30 40 30
    slices = [⟨0, 0, 30, 40, 10, []⟩, ⟨1, 0, 0, 40, 20, []⟩] := by
  decide

-- out_of_flow_layout_part_test.cc:398: OutOfFlowLayoutPartTest.BreakAfterColumn
theorem BreakAfterColumn_vectors :
    let desc : OofDescendant := { posType := .absolute, width := .px 40, height := .px 30 }
    let slices := fragmentOof 40 492 desc false true 0 0 30 40 30
    slices = [⟨0, 0, 30, 40, 10, []⟩, ⟨1, 0, 0, 40, 20, []⟩] := by
  decide

-- out_of_flow_layout_part_test.cc:437: OutOfFlowLayoutPartTest.ChildBreakInsideAvoid
-- In-flow children inside an absolute container honor break-inside: avoid and push to the next column.
-- CSS Fragmentation Level 3 §3.2.
theorem ChildBreakInsideAvoid_vectors :
    let desc : OofDescendant := {
      posType := .absolute, width := .px 40, height := .px 150,
      children := [⟨15, 50, .auto, false, false⟩, ⟨20, 100, .avoid, false, false⟩]
    }
    let slices := fragmentOof 100 492 desc false false 0 0 0 40 150
    slices = [
      ⟨0, 0, 0, 40, 100, [⟨0, 0, 0, 15, 50⟩]⟩,
      ⟨1, 0, 0, 40, 50, [⟨1, 0, 0, 20, 100⟩]⟩
    ] := by
  decide

-- out_of_flow_layout_part_test.cc:479: OutOfFlowLayoutPartTest.ChildBreakBeforeAvoid
-- In-flow children inside an absolute container honor break-before: avoid by pushing the previous child.
-- CSS Fragmentation Level 3 §3.2.
theorem ChildBreakBeforeAvoid_vectors :
    let desc : OofDescendant := {
      posType := .absolute, width := .px 40, height := .px 150,
      children := [⟨15, 50, .auto, false, false⟩, ⟨20, 50, .auto, false, false⟩, ⟨10, 20, .auto, true, false⟩]
    }
    let slices := fragmentOof 100 492 desc false false 0 0 0 40 150
    slices = [
      ⟨0, 0, 0, 40, 100, [⟨0, 0, 0, 15, 50⟩]⟩,
      ⟨1, 0, 0, 40, 50, [⟨1, 0, 0, 20, 50⟩, ⟨1, 0, 50, 10, 20⟩]⟩
    ] := by
  decide

-- out_of_flow_layout_part_test.cc:523: OutOfFlowLayoutPartTest.ChildBreakAfterAvoid
-- In-flow children inside an absolute container honor break-after: avoid by pushing with the next child.
-- CSS Fragmentation Level 3 §3.2.
theorem ChildBreakAfterAvoid_vectors :
    let desc : OofDescendant := {
      posType := .absolute, width := .px 40, height := .px 150,
      children := [⟨15, 50, .auto, false, false⟩, ⟨20, 50, .auto, false, true⟩, ⟨10, 20, .auto, false, false⟩]
    }
    let slices := fragmentOof 100 492 desc false false 0 0 0 40 150
    slices = [
      ⟨0, 0, 0, 40, 100, [⟨0, 0, 0, 15, 50⟩]⟩,
      ⟨1, 0, 0, 40, 50, [⟨1, 0, 0, 20, 50⟩, ⟨1, 0, 50, 10, 20⟩]⟩
    ] := by
  decide

-- out_of_flow_layout_part_test.cc:568: OutOfFlowLayoutPartTest.PositionedFragmentationWithNegativeTopPropertyAndNewEmptyColumn
-- A positioned element with negative top property moves to the previous fragmentainer and fragments across columns.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2, CSS Fragmentation Level 3 §2.
theorem PositionedFragmentationWithNegativeTopPropertyAndNewEmptyColumn_vectors :
    let fragH := 40
    let (startCol, startOffsetY) := resolveMulticolOofStart 1 20 (-40) fragH
    let slices := fragmentOofWithContent startCol startOffsetY 80 80 fragH
    let totalCols := multicolTotalColumns 2 slices
    startCol = 0 ∧
    startOffsetY = 20 ∧
    slices = [⟨0, 20, 20, 20⟩, ⟨1, 0, 40, 40⟩, ⟨2, 0, 20, 20⟩] ∧
    totalCols = 3 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:649: OutOfFlowLayoutPartTest.PositionedFragmentationInFlowWithAddedColumns
-- A positioned element in static position fragments across columns and expands multi-column column count.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2, CSS Fragmentation Level 3 §2.
theorem PositionedFragmentationInFlowWithAddedColumns_vectors :
    let fragH := 40
    let (startCol, startOffsetY) := resolveMulticolOofStart 1 20 0 fragH
    let slices := fragmentOofWithContent startCol startOffsetY 80 80 fragH
    let totalCols := multicolTotalColumns 2 slices
    startCol = 1 ∧
    startOffsetY = 20 ∧
    slices = [⟨1, 20, 20, 20⟩, ⟨2, 0, 40, 40⟩, ⟨3, 0, 20, 20⟩] ∧
    totalCols = 4 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:1175: OutOfFlowLayoutPartTest.AbsposFragmentationPctResolution
-- Out-of-flow positioned element with percentage block size resolved in fragmentainer before spanner.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2, CSS Fragmentation Level 3 §2.
theorem AbsposFragmentationPctResolution_vectors :
    let fragH := 30
    let (startCol, startOffsetY) := resolveMulticolOofStart 0 0 30 fragH
    let slices := fragmentOofWithContent startCol startOffsetY 30 30 fragH
    let totalCols := multicolTotalColumns 2 slices
    startCol = 1 ∧
    startOffsetY = 0 ∧
    slices = [⟨1, 0, 30, 30⟩] ∧
    totalCols = 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:1278: OutOfFlowLayoutPartTest.SimpleAbsposNestedFragmentation
-- Out-of-flow positioned element fragments inside a nested multi-column container.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2, CSS Fragmentation Level 3 §2.
theorem SimpleAbsposNestedFragmentation_vectors :
    let fragH := 60
    let (startCol, startOffsetY) := resolveMulticolOofStart 0 0 0 fragH
    let slices := fragmentOofWithContent startCol startOffsetY 80 80 fragH
    let totalCols := multicolTotalColumns 2 slices
    startCol = 0 ∧
    startOffsetY = 0 ∧
    slices = [⟨0, 0, 60, 60⟩, ⟨1, 0, 20, 20⟩] ∧
    totalCols = 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- out_of_flow_layout_part_test.cc:1549: OutOfFlowLayoutPartTest.PositionedObjectsInMulticol
-- Out-of-flow positioned descendants in multicolumn are attached to column fragmentainers,
-- not directly to the multicol fragmentation context root.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2.
theorem PositionedObjectsInMulticol_vectors :
    let abs1 : FragNode := FragNode.mk .normalChild (some 101) true []
    let abs2 : FragNode := FragNode.mk .normalChild (some 102) true []
    let innerMulticol := makeMulticolFrag (some 2) 2 [abs2]
    let outerMulticol := makeMulticolFrag (some 1) 2 [abs1, innerMulticol]
    isFragContextRoot outerMulticol = true ∧
    hasOutOfFlowChild outerMulticol = false ∧
    isFragContextRoot innerMulticol = true ∧
    hasOutOfFlowChild innerMulticol = false ∧
    outerMulticol.children.length = 2 ∧
    (match outerMulticol.children with
     | col0 :: _ =>
         isColumnBox col0 = true ∧
         hasOutOfFlowChild col0 = true
     | _ => false) ∧
    (match innerMulticol.children with
     | col0 :: _ =>
         isColumnBox col0 = true ∧
         hasOutOfFlowChild col0 = true
     | _ => false) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- out_of_flow_layout_part_test.cc:1572: OutOfFlowLayoutPartTest.PositionedObjectsInMulticolWithInline
-- Out-of-flow positioned objects inside an inline (span) within multicolumn are attached
-- to the column fragmentainer, not directly to the multicol fragmentation context root.
-- CSS Multi-column Layout Level 1 §2, CSS Positioned Layout Level 3 §2.
theorem PositionedObjectsInMulticolWithInline_vectors :
    let abs1 : FragNode := FragNode.mk .normalChild (some 101) true []
    let abs2 : FragNode := FragNode.mk .normalChild (some 102) true []
    let multicol := makeMulticolFrag (some 1) 2 [abs1, abs2]
    isFragContextRoot multicol = true ∧
    hasOutOfFlowChild multicol = false ∧
    multicol.children.length = 2 ∧
    (match multicol.children with
     | col0 :: _ =>
         isColumnBox col0 = true ∧
         hasOutOfFlowChild col0 = true
     | _ => false) := by
  exact ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩⟩

end TestsBlock
