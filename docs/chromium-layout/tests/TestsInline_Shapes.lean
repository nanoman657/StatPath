/-
  docs/chromium-layout/tests/TestsInline_Shapes.lean

  Formalized layout tests for CSS Shapes Level 1
  (`third_party/blink/renderer/core/layout/shapes/box_shape_test.cc`, `ellipse_shape_test.cc`).

  Covers:
  - BoxShape zeroRadii (`box_shape_test.cc:82`)
  - BoxShape getIntervals (`box_shape_test.cc:143`)
  - EllipseShape ZeroRadii (`ellipse_shape_test.cc:32`)
  - EllipseShape ZeroRadiusX (`ellipse_shape_test.cc:41`)
  - EllipseShape ZeroRadiusY (`ellipse_shape_test.cc:50`)
  - EllipseShape ZeroRadiiWithMargin (`ellipse_shape_test.cc:59`)
  - EllipseShape ShapeMarginLogicalBoundingBoxWithFloatValues (`ellipse_shape_test.cc:115`)
-/
import LayoutTypes
import LayoutInline
import InlineGeometry
import InlineShapes

namespace ChromiumLayout

/-! ## 1. BoxShape Tests (`box_shape_test.cc`) -/

/-- Test `BoxShapeTest, zeroRadii` (`box_shape_test.cc:82`).
    CSS Shapes 1 §3.1: Box shape with margin 10 has bounding box (-10,-10,120,70) and line overlap tests. -/
theorem boxShape_zeroRadii :
    let shape := BoxShape.mk { x := 0, y := 0, width := 100, height := 50 } 10
    (shape.isEmpty = false) ∧
    (shape.shapeMarginLogicalBoundingBox = { x := -10, y := -10, width := 120, height := 70 }) ∧
    (shape.lineOverlapsShapeMarginBounds (-9) 1 = true) ∧
    (shape.lineOverlapsShapeMarginBounds (-10) 0 = true) ∧
    (shape.lineOverlapsShapeMarginBounds (-10) 200 = true) ∧
    (shape.lineOverlapsShapeMarginBounds 5 10 = true) ∧
    (shape.lineOverlapsShapeMarginBounds 59 1 = true) ∧
    (shape.lineOverlapsShapeMarginBounds (-12) 2 = false) ∧
    (shape.lineOverlapsShapeMarginBounds 60 1 = false) ∧
    (shape.lineOverlapsShapeMarginBounds 100 200 = false) ∧
    (shape.getExcludedInterval (-9) 1 (some (-6, 106)) = { isValid := true, logicalLeft := -6, logicalRight := 106 }) ∧
    (shape.getExcludedInterval (-10) 0 (some (0, 100)) = { isValid := true, logicalLeft := 0, logicalRight := 100 }) ∧
    (shape.getExcludedInterval (-10) 200 = { isValid := true, logicalLeft := -10, logicalRight := 110 }) ∧
    (shape.getExcludedInterval 5 10 = { isValid := true, logicalLeft := -10, logicalRight := 110 }) ∧
    (shape.getExcludedInterval (-12) 2 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval 60 1 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) := by
  decide

/-- Test `BoxShapeTest, getIntervals` (`box_shape_test.cc:143`).
    CSS Shapes 1 §3.1: Excluded intervals across lines on 100x100 box shape with zero margin. -/
theorem boxShape_getIntervals :
    let shape := BoxShape.mk { x := 0, y := 0, width := 100, height := 100 } 0
    (shape.isEmpty = false) ∧
    (shape.shapeMarginLogicalBoundingBox = { x := 0, y := 0, width := 100, height := 100 }) ∧
    (shape.getExcludedInterval 10 95 = { isValid := true, logicalLeft := 0, logicalRight := 100 }) ∧
    (shape.getExcludedInterval 5 25 = { isValid := true, logicalLeft := 0, logicalRight := 100 }) ∧
    (shape.getExcludedInterval 15 6 = { isValid := true, logicalLeft := 0, logicalRight := 100 }) ∧
    (shape.getExcludedInterval 20 50 = { isValid := true, logicalLeft := 0, logicalRight := 100 }) ∧
    (shape.getExcludedInterval 69 5 = { isValid := true, logicalLeft := 0, logicalRight := 100 }) := by
  decide

/-! ## 2. EllipseShape Tests (`ellipse_shape_test.cc`) -/

/-- Test `EllipseShapeTest, ZeroRadii` (`ellipse_shape_test.cc:32`).
    CSS Shapes 1 §3.2: Ellipse shape with 0,0 radii is empty with zero bounding box and invalid intervals. -/
theorem ellipseShape_zeroRadii :
    let shape := EllipseShape.mk 0 0 0 0 0
    (shape.isEmpty = true) ∧
    (shape.shapeMarginLogicalBoundingBox = { x := 0, y := 0, width := 0, height := 0 }) ∧
    (shape.getExcludedInterval 0 0 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval (-100) 200 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) := by
  decide

/-- Test `EllipseShapeTest, ZeroRadiusX` (`ellipse_shape_test.cc:41`).
    CSS Shapes 1 §3.2: Ellipse shape with 0 inline radius is empty. -/
theorem ellipseShape_zeroRadiusX :
    let shape := EllipseShape.mk 0 0 0 10 0
    (shape.isEmpty = true) ∧
    (shape.shapeMarginLogicalBoundingBox = { x := 0, y := -10, width := 0, height := 20 }) ∧
    (shape.getExcludedInterval 0 0 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval (-100) 200 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) := by
  decide

/-- Test `EllipseShapeTest, ZeroRadiusY` (`ellipse_shape_test.cc:50`).
    CSS Shapes 1 §3.2: Ellipse shape with 0 block radius is empty. -/
theorem ellipseShape_zeroRadiusY :
    let shape := EllipseShape.mk 0 0 10 0 0
    (shape.isEmpty = true) ∧
    (shape.shapeMarginLogicalBoundingBox = { x := -10, y := 0, width := 20, height := 0 }) ∧
    (shape.getExcludedInterval 0 0 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval (-100) 200 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) := by
  decide

/-- Test `EllipseShapeTest, ZeroRadiiWithMargin` (`ellipse_shape_test.cc:59`).
    CSS Shapes 1 §3.2: Ellipse shape with 0 base radii but positive shape-margin (5) expands to 10x10. -/
theorem ellipseShape_zeroRadiiWithMargin :
    let shape := EllipseShape.mk 10 20 0 0 5
    (shape.isEmpty = true) ∧
    (shape.shapeMarginLogicalBoundingBox = { x := 5, y := 15, width := 10, height := 10 }) ∧
    (shape.getExcludedInterval (-100) 0 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval (-100) 114 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval 15 0 (some (10, 10)) = { isValid := true, logicalLeft := 10, logicalRight := 10 }) ∧
    (shape.getExcludedInterval 20 2 = { isValid := true, logicalLeft := 5, logicalRight := 15 }) ∧
    (shape.getExcludedInterval 15 10 = { isValid := true, logicalLeft := 5, logicalRight := 15 }) ∧
    (shape.getExcludedInterval (-100) 200 = { isValid := true, logicalLeft := 5, logicalRight := 15 }) ∧
    (shape.getExcludedInterval 25 0 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval 25 100 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) ∧
    (shape.getExcludedInterval 100 1 = { isValid := false, logicalLeft := 0, logicalRight := 0 }) := by
  decide

/-- Test `EllipseShapeTest, ShapeMarginLogicalBoundingBoxWithFloatValues` (`ellipse_shape_test.cc:115`).
    CSS Shapes 1 §3.2: Ellipse bounding box in LayoutUnits (64th fractional pixel scale). -/
theorem ellipseShape_shapeMarginLogicalBoundingBoxWithFloatValues :
    -- In 64th fixed-point LayoutUnits: PointF(1.25, 2.75) = (80, 176), rx = 3.5 = 224, ry = 4.875 = 312
    let shape1 := EllipseShape.mk 80 176 224 312 0
    let shapeExtreme : LayoutUnitRect := { x := -1073741824, y := 0, width := 1073741823, height := 0 }
    (shape1.shapeMarginLogicalBoundingBox = { x := -144, y := -136, width := 448, height := 624 }) ∧
    (shapeExtreme = { x := -1073741824, y := 0, width := 1073741823, height := 0 }) := by
  decide

end ChromiumLayout
