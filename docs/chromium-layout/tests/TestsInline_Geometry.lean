/-
  docs/chromium-layout/tests/TestsInline_Geometry.lean

  Formalized layout geometry tests
  (`third_party/blink/renderer/core/layout/geometry/`).

  Covers:
  - ToPhysicalAxes (`geometry/axis_test.cc:213`)
  - ToLogicalAxes (`geometry/axis_test.cc:239`)
  - LogicalBoxSidesToLineLogical (`geometry/box_sides_test.cc:14`)
  - PhysicalBoxSidesToLogical (`geometry/box_sides_test.cc:33`)
  - BoxEdge operations (`geometry/box_edge_test.cc:10-46`)
  - ConvertPhysicalStrutToLogical (`geometry/box_strut_test.cc:17`)
  - ConvertLogicalStrutToPhysical (`geometry/box_strut_test.cc:52`)
  - BoxStrut Unite (`geometry/box_strut_test.cc:114`)
  - ConvertLogicalOffsetToPhysicalOffset (`geometry/writing_mode_converter_test.cc:15`)
  - ConvertPhysicalOffsetToLogicalOffset (`geometry/writing_mode_converter_test.cc:73`)
  - LogicalRect operations (`geometry/logical_rect_test.cc:15-56`)
  - PhysicalRect operations (`geometry/physical_rect_test.cc:17-146`)
  - LayoutUnitDiffuser (`geometry/layout_unit_diffuser_test.cc:35-64`)
-/
import LayoutTypes
import InlineFragmentItem
import InlineGeometry

namespace ChromiumLayout

/-! ## 1. Axes Tests (`geometry/axis_test.cc`) -/

/-- Test `AxisTest, ToPhysicalAxes` (`geometry/axis_test.cc:213`). -/
theorem axis_toPhysicalAxes :
    (toPhysicalAxes .none .horizontalTb = .none) ∧
    (toPhysicalAxes .none .verticalRl = .none) ∧
    (toPhysicalAxes .both .horizontalTb = .both) ∧
    (toPhysicalAxes .both .verticalRl = .both) ∧
    (toPhysicalAxes .inline .horizontalTb = .horizontal) ∧
    (toPhysicalAxes .inline .verticalRl = .vertical) ∧
    (toPhysicalAxes .block .horizontalTb = .vertical) ∧
    (toPhysicalAxes .block .verticalRl = .horizontal) := by
  decide

/-- Test `AxisTest, ToLogicalAxes` (`geometry/axis_test.cc:239`). -/
theorem axis_toLogicalAxes :
    (toLogicalAxes .none .horizontalTb = .none) ∧
    (toLogicalAxes .none .verticalRl = .none) ∧
    (toLogicalAxes .both .horizontalTb = .both) ∧
    (toLogicalAxes .both .verticalRl = .both) ∧
    (toLogicalAxes .horizontal .horizontalTb = .inline) ∧
    (toLogicalAxes .horizontal .verticalRl = .block) ∧
    (toLogicalAxes .vertical .horizontalTb = .block) ∧
    (toLogicalAxes .vertical .verticalRl = .inline) := by
  decide

/-! ## 2. Box Sides Tests (`geometry/box_sides_test.cc`) -/

/-- Test `GeometryUnitsTest, LogicalBoxSidesToLineLogical` (`geometry/box_sides_test.cc:14`). -/
theorem boxSides_logicalToLineLogical :
    let sides : LogicalBoxSides := { inlineStart := false, inlineEnd := true, blockStart := false, blockEnd := true }
    let rtl := logicalBoxSidesToLineLogical sides .rtl
    let ltr := logicalBoxSidesToLineLogical sides .ltr
    (rtl.blockStart = false) ∧
    (rtl.blockEnd = true) ∧
    (rtl.lineLeft = true) ∧
    (rtl.lineRight = false) ∧
    (ltr.blockStart = false) ∧
    (ltr.blockEnd = true) ∧
    (ltr.lineLeft = false) ∧
    (ltr.lineRight = true) := by
  decide

/-- Test `GeometryUnitsTest, PhysicalBoxSidesToLogical` (`geometry/box_sides_test.cc:33`). -/
theorem boxSides_physicalToLogical :
    let sides : PhysicalBoxSides := { top := true, right := true, bottom := false, left := false }
    let vRlRtl := physicalBoxSidesToLogical sides .verticalRl .rtl
    let vRlLtr := physicalBoxSidesToLogical sides .verticalRl .ltr
    let vLrRtl := physicalBoxSidesToLogical sides .verticalLr .rtl
    let vLrLtr := physicalBoxSidesToLogical sides .verticalLr .ltr
    let hTbRtl := physicalBoxSidesToLogical sides .horizontalTb .rtl
    let hTbLtr := physicalBoxSidesToLogical sides .horizontalTb .ltr
    (vRlRtl = { inlineStart := false, inlineEnd := true, blockStart := true, blockEnd := false }) ∧
    (vRlLtr = { inlineStart := true, inlineEnd := false, blockStart := true, blockEnd := false }) ∧
    (vLrRtl = { inlineStart := false, inlineEnd := true, blockStart := false, blockEnd := true }) ∧
    (vLrLtr = { inlineStart := true, inlineEnd := false, blockStart := false, blockEnd := true }) ∧
    (hTbRtl = { inlineStart := true, inlineEnd := false, blockStart := true, blockEnd := false }) ∧
    (hTbLtr = { inlineStart := false, inlineEnd := true, blockStart := true, blockEnd := false }) := by
  decide

/-! ## 3. Box Edge Tests (`geometry/box_edge_test.cc`) -/

/-- Test `BoxEdgeTest, Construction, End, IsEmpty, Move, MathOperators` (`geometry/box_edge_test.cc:10-46`). -/
theorem boxEdge_properties :
    let e : BoxEdge := { offset := 10, size := 40 }
    (e.endOffset = 50) ∧
    (BoxEdge.isEmpty { offset := 10, size := 0 } = true) ∧
    (BoxEdge.isEmpty { offset := 50, size := -40 } = true) ∧
    (BoxEdge.isEmpty e = false) ∧
    (e.move 10 = { offset := 20, size := 40 }) ∧
    ((e.move 10).move (-15) = { offset := 5, size := 40 }) := by
  decide

/-! ## 4. Box Strut Tests (`geometry/box_strut_test.cc`) -/

/-- Test `GeometryUnitsTest, ConvertPhysicalStrutToLogical` (`geometry/box_strut_test.cc:17`). -/
theorem boxStrut_convertPhysicalToLogical :
    let p : PhysicalBoxStrut := { top := 15, right := 10, bottom := 20, left := 5 }
    let hLtr := physicalStrutToLogical p .horizontalTb .ltr
    let hRtl := physicalStrutToLogical p .horizontalTb .rtl
    let vLrLtr := physicalStrutToLogical p .verticalLr .ltr
    let vLrRtl := physicalStrutToLogical p .verticalLr .rtl
    let vRlLtr := physicalStrutToLogical p .verticalRl .ltr
    let vRlRtl := physicalStrutToLogical p .verticalRl .rtl
    (hLtr.inlineStart = 5 ∧ hLtr.blockStart = 15) ∧
    (hRtl.inlineStart = 10 ∧ hRtl.blockStart = 15) ∧
    (vLrLtr.inlineStart = 15 ∧ vLrLtr.blockStart = 5) ∧
    (vLrRtl.inlineStart = 20 ∧ vLrRtl.blockStart = 5) ∧
    (vRlLtr.inlineStart = 15 ∧ vRlLtr.blockStart = 10) ∧
    (vRlRtl.inlineStart = 20 ∧ vRlRtl.blockStart = 10) := by
  decide

/-- Test `GeometryUnitsTest, ConvertLogicalStrutToPhysical` roundtrip (`geometry/box_strut_test.cc:52`). -/
theorem boxStrut_convertLogicalToPhysical :
    let l : BoxStrut := { inlineStart := 5, inlineEnd := 10, blockStart := 15, blockEnd := 20 }
    (physicalStrutToLogical (logicalStrutToPhysical l .horizontalTb .ltr) .horizontalTb .ltr = l) ∧
    (physicalStrutToLogical (logicalStrutToPhysical l .horizontalTb .rtl) .horizontalTb .rtl = l) ∧
    (physicalStrutToLogical (logicalStrutToPhysical l .verticalLr .ltr) .verticalLr .ltr = l) ∧
    (physicalStrutToLogical (logicalStrutToPhysical l .verticalLr .rtl) .verticalLr .rtl = l) ∧
    (physicalStrutToLogical (logicalStrutToPhysical l .verticalRl .ltr) .verticalRl .ltr = l) ∧
    (physicalStrutToLogical (logicalStrutToPhysical l .verticalRl .rtl) .verticalRl .rtl = l) := by
  decide

/-- Test `PhysicalBoxStrutTest, Unite` (`geometry/box_strut_test.cc:114`). -/
theorem boxStrut_unite :
    let s1 : PhysicalBoxStrut := { top := 10, right := 10, bottom := 10, left := 10 }
    let s2 : PhysicalBoxStrut := { top := 10, right := 11, bottom := 0, left := 50 }
    let u := physicalStrutUnite s1 s2
    (u.top = 10) ∧ (u.right = 11) ∧ (u.bottom = 10) ∧ (u.left = 50) := by
  decide

/-! ## 5. WritingModeConverter Tests (`geometry/writing_mode_converter_test.cc`) -/

/-- Test `WritingModeConverterTest, ConvertLogicalOffsetToPhysicalOffset` (`geometry/writing_mode_converter_test.cc:15`). -/
theorem writingModeConverter_toPhysical :
    let logical : LogicalOffset := { inlineOffset := 20, blockOffset := 30 }
    let outer : PhysicalSize := { width := 300, height := 400 }
    let inner : PhysicalSize := { width := 5, height := 65 }
    (logicalToPhysicalOffset .horizontalTb .ltr outer inner logical = { left := 20, top := 30 }) ∧
    (logicalToPhysicalOffset .horizontalTb .rtl outer inner logical = { left := 275, top := 30 }) ∧
    (logicalToPhysicalOffset .verticalRl .ltr outer inner logical = { left := 265, top := 20 }) ∧
    (logicalToPhysicalOffset .verticalRl .rtl outer inner logical = { left := 265, top := 315 }) ∧
    (logicalToPhysicalOffset .verticalLr .ltr outer inner logical = { left := 30, top := 20 }) ∧
    (logicalToPhysicalOffset .verticalLr .rtl outer inner logical = { left := 30, top := 315 }) := by
  decide

/-- Test `WritingModeConverterTest, ConvertPhysicalOffsetToLogicalOffset` (`geometry/writing_mode_converter_test.cc:73`). -/
theorem writingModeConverter_toLogical :
    let outer : PhysicalSize := { width := 300, height := 400 }
    let inner : PhysicalSize := { width := 5, height := 65 }
    (physicalToLogicalOffset .horizontalTb .ltr outer inner { left := 20, top := 30 } = { inlineOffset := 20, blockOffset := 30 }) ∧
    (physicalToLogicalOffset .horizontalTb .rtl outer inner { left := 275, top := 30 } = { inlineOffset := 20, blockOffset := 30 }) ∧
    (physicalToLogicalOffset .verticalRl .ltr outer inner { left := 265, top := 20 } = { inlineOffset := 20, blockOffset := 30 }) ∧
    (physicalToLogicalOffset .verticalRl .rtl outer inner { left := 265, top := 315 } = { inlineOffset := 20, blockOffset := 30 }) ∧
    (physicalToLogicalOffset .verticalLr .ltr outer inner { left := 30, top := 20 } = { inlineOffset := 20, blockOffset := 30 }) ∧
    (physicalToLogicalOffset .verticalLr .rtl outer inner { left := 30, top := 315 } = { inlineOffset := 20, blockOffset := 30 }) := by
  decide

/-! ## 6. Rect Operations Tests (`geometry/logical_rect_test.cc`, `physical_rect_test.cc`) -/

/-- Test `LogicalRectTest, AddOffset and Unite` (`geometry/logical_rect_test.cc:15,56`). -/
theorem logicalRect_addOffsetAndUnite :
    let r1 : LogicalRect := { offset := { inlineOffset := 1, blockOffset := 2 }, size := { inlineSize := 3, blockSize := 4 } }
    let o : LogicalOffset := { inlineOffset := 5, blockOffset := 6 }
    let u1 := LogicalRect.unite {} { offset := { inlineOffset := 1, blockOffset := 2 }, size := { inlineSize := 3, blockSize := 4 } }
    let u2 := LogicalRect.unite
      { offset := { inlineOffset := 100, blockOffset := 50 }, size := { inlineSize := 300, blockSize := 200 } }
      { offset := { inlineOffset := 200, blockOffset := 50 }, size := { inlineSize := 200, blockSize := 200 } }
    (r1.addOffset o = { offset := { inlineOffset := 6, blockOffset := 8 }, size := { inlineSize := 3, blockSize := 4 } }) ∧
    (u1 = { offset := { inlineOffset := 1, blockOffset := 2 }, size := { inlineSize := 3, blockSize := 4 } }) ∧
    (u2 = { offset := { inlineOffset := 100, blockOffset := 50 }, size := { inlineSize := 300, blockSize := 200 } }) := by
  decide

/-- Test `PhysicalRectTest, Operations` (`geometry/physical_rect_test.cc:17-146`). -/
theorem physicalRect_operations :
    let r : PhysicalRect := { x := 1, y := 2, width := 3, height := 4 }
    let r2 : PhysicalRect := { x := 2, y := 3, width := 5, height := 6 }
    (r.addOffset 5 6 = { x := 6, y := 8, width := 3, height := 4 }) ∧
    (r.squaredDistanceTo 1 2 = 0) ∧
    (r.squaredDistanceTo 10 2 = 36) ∧
    (r.intersectsInclusively r2 = true) ∧
    (r.inclusiveIntersect r2 = { x := 2, y := 3, width := 2, height := 3 }) := by
  decide

/-! ## 7. LayoutUnitDiffuser Tests (`geometry/layout_unit_diffuser_test.cc`) -/

/-- Test `LayoutUnitDiffuserTest, FourBuckets and SevenBuckets` (`geometry/layout_unit_diffuser_test.cc:35,64`). -/
theorem layoutUnitDiffuser_buckets :
    (diffuseRemainder 1 4 = [false, true, false, false]) ∧
    (diffuseRemainder 2 4 = [true, false, true, false]) ∧
    (diffuseRemainder 3 4 = [true, true, false, true]) ∧
    (diffuseRemainder 1 7 = [false, false, false, true, false, false, false]) ∧
    (diffuseRemainder 2 7 = [false, true, false, false, false, true, false]) ∧
    (diffuseRemainder 3 7 = [false, true, false, true, false, true, false]) ∧
    (diffuseRemainder 4 7 = [true, false, true, false, true, false, true]) ∧
    (diffuseRemainder 5 7 = [true, false, true, true, true, false, true]) ∧
    (diffuseRemainder 6 7 = [true, true, true, false, true, true, true]) := by
  decide

end ChromiumLayout
