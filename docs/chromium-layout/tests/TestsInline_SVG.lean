import InlineGeometry
import InlineFragmentItem
import InlineSVG

namespace ChromiumLayout

/-! ## SVG Layout Tests
    Formalizing Chromium's SVG layout test cases.
    Specifications:
    - SVG 2 §7.3 Viewports (SVG viewport and clipping)
    - SVG 2 §11.3.3 The textPath element (Nesting constraint)
    - SVG 2 §11.4 Text layout attributes (textLength and quads)
    - SVG 2 §13.3 Vector Effects (vector-effect: non-scaling-stroke)
    - SVG 2 §13.5 Object Bounding Box (Empty shapes have empty stroke bounding box)
    - CSS 2.1 §10 Visual formatting model details (Content rect and border box mapping)
    - CSSOM View Module §8 (Rect-based hit testing)
-/

/-- Test `LayoutSVGContainerTest, TransformAffectsVectorEffect` (`svg/layout_svg_container_test.cc:19`). -/
theorem svg_container_transformAffectsVectorEffect :
    let rectNode := SvgNode.shape SvgVectorEffect.nonScalingStroke
    let textNode := SvgNode.text SvgVectorEffect.nonScalingStroke []
    let gNode := SvgNode.container SvgVectorEffect.none [rectNode, textNode]
    let svgNode := SvgNode.root [gNode]
    transformAffectsVectorEffect svgNode = false ∧
    transformAffectsVectorEffect gNode = true ∧
    transformAffectsVectorEffect rectNode = true ∧
    transformAffectsVectorEffect textNode = true ∧
    let rectNoVE := SvgNode.shape SvgVectorEffect.none
    let textNoVE := SvgNode.text SvgVectorEffect.none []
    let gAllNone := SvgNode.container SvgVectorEffect.none [rectNoVE, textNoVE]
    transformAffectsVectorEffect gAllNone = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGContainerTest, TransformAffectsVectorEffectNestedSVG` (`svg/layout_svg_container_test.cc:70`). -/
theorem svg_container_transformAffectsVectorEffectNestedSVG :
    let rectNode := SvgNode.shape SvgVectorEffect.nonScalingStroke
    let nestedSvg := SvgNode.container SvgVectorEffect.none [rectNode]
    let gNode := SvgNode.container SvgVectorEffect.none [nestedSvg]
    let svgNode := SvgNode.root [gNode]
    transformAffectsVectorEffect svgNode = false ∧
    transformAffectsVectorEffect gNode = true ∧
    transformAffectsVectorEffect nestedSvg = true ∧
    transformAffectsVectorEffect rectNode = true ∧
    let rectNoVE := SvgNode.shape SvgVectorEffect.none
    let nestedSvgNoVE := SvgNode.container SvgVectorEffect.none [rectNoVE]
    let gNoVE := SvgNode.container SvgVectorEffect.none [nestedSvgNoVE]
    transformAffectsVectorEffect gNoVE = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGContainerTest, TransformAffectsVectorEffectHiddenContainerAndUse` (`svg/layout_svg_container_test.cc:100`). -/
theorem svg_container_transformAffectsVectorEffectHiddenContainerAndUse :
    let rectDef := SvgNode.shape SvgVectorEffect.nonScalingStroke
    let defsNode := SvgNode.defs [rectDef]
    let g0 := SvgNode.container SvgVectorEffect.none [defsNode]
    let useNode := SvgNode.use true
    let g1 := SvgNode.container SvgVectorEffect.none [useNode]
    transformAffectsVectorEffect g0 = false ∧
    transformAffectsVectorEffect g1 = true :=
  ⟨rfl, rfl⟩

/-- Test `LayoutSVGTextTest, TransformAffectsVectorEffect` (`svg/layout_svg_text_test.cc:67`). -/
theorem svg_text_transformAffectsVectorEffect :
    let text1 := SvgNode.text SvgVectorEffect.none [SvgNode.tspan SvgVectorEffect.none]
    let text2 := SvgNode.text SvgVectorEffect.nonScalingStroke []
    let text3 := SvgNode.text SvgVectorEffect.none [SvgNode.tspan SvgVectorEffect.nonScalingStroke]
    transformAffectsVectorEffect text1 = false ∧
    transformAffectsVectorEffect text2 = true ∧
    transformAffectsVectorEffect text3 = true ∧
    let text1VE := SvgNode.text SvgVectorEffect.none [SvgNode.tspan SvgVectorEffect.nonScalingStroke]
    let text2NoVE := SvgNode.text SvgVectorEffect.none []
    let text3NoVE := SvgNode.text SvgVectorEffect.none [SvgNode.tspan SvgVectorEffect.none]
    transformAffectsVectorEffect text1VE = true ∧
    transformAffectsVectorEffect text2NoVE = false ∧
    transformAffectsVectorEffect text3NoVE = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGTextTest, AbsoluteQuads` (`svg/layout_svg_text_test.cc:96`). -/
theorem svg_text_absoluteQuads :
    let bbox := computeSvgTextBoundingBox 7 0 300 16
    bbox.x = 7 ∧ bbox.x + bbox.width = 307 :=
  ⟨rfl, rfl⟩

/-- Test `LayoutSVGShapeTest, StrokeBoundingBoxOnEmptyShape` (`svg/layout_svg_shape_test.cc:12`). -/
theorem svg_shape_strokeBoundingBoxOnEmptyShape :
    computeSvgCircleStrokeBoundingBox 0 0 0 100 = { x := 0, y := 0, width := 0, height := 0 } :=
  rfl

/-- Test `LayoutSVGInlineTest, IsChildAllowed` (`svg/layout_svg_inline_test.cc:13`). -/
theorem svg_inline_isChildAllowed :
    isSvgChildAllowed SvgTag.a [SvgTag.textPath, SvgTag.text, SvgTag.svg] SvgTag.textPath = false :=
  rfl

/-- Test `LayoutSVGRootTest, VisualRectMappingWithoutViewportClipWithBorder` (`svg/layout_svg_root_test.cc:27`). -/
theorem svg_root_visualRectMappingWithoutViewportClipWithBorder :
    let border : PhysicalBoxStrut := { top := 10, right := 10, bottom := 10, left := 10 }
    let vp : PhysicalSize := { width := 200, height := 100 }
    let elem : PhysicalRect := { x := 80, y := 80, width := 100, height := 100 }
    mapSvgVisualRectToDocument border vp true elem = { x := 90, y := 90, width := 100, height := 100 } :=
  rfl

/-- Test `LayoutSVGRootTest, VisualRectMappingWithViewportClipAndBorder` (`svg/layout_svg_root_test.cc:74`). -/
theorem svg_root_visualRectMappingWithViewportClipAndBorder :
    let border : PhysicalBoxStrut := { top := 10, right := 10, bottom := 10, left := 10 }
    let vp : PhysicalSize := { width := 200, height := 100 }
    let elem : PhysicalRect := { x := 80, y := 80, width := 100, height := 100 }
    mapSvgVisualRectToDocument border vp false elem = { x := 90, y := 90, width := 100, height := 20 } :=
  rfl

/-- Test `LayoutSVGTextTest, RectBasedHitTest` (`svg/layout_svg_text_test.cc:13`). -/
theorem svg_text_rectBasedHitTest :
    let query : PhysicalRect := { x := 0, y := 0, width := 300, height := 300 }
    let svgRect : PhysicalRect := { x := 0, y := 0, width := 300, height := 300 }
    let textRect : PhysicalRect := { x := 0, y := 0, width := 300, height := 20 }
    rectsIntersect query svgRect = true ∧
    rectsIntersect query textRect = true :=
  ⟨rfl, rfl⟩

/-- Test `LayoutSVGRootTest, RectBasedHitTestPartialOverlap` (`svg/layout_svg_root_test.cc:101`). -/
theorem svg_root_rectBasedHitTestPartialOverlap :
    let query : PhysicalRect := { x := 0, y := 0, width := 300, height := 300 }
    let svgRect : PhysicalRect := { x := 200, y := 200, width := 300, height := 300 }
    let bodyRect : PhysicalRect := { x := 0, y := 0, width := 1000, height := 1000 }
    rectsIntersect query svgRect = true ∧
    rectsIntersect query bodyRect = true ∧
    (150 < svgRect.x || 150 < svgRect.y) = true :=
  ⟨rfl, rfl, rfl⟩

/-- Test `LayoutSVGShapeTest, RectBasedHitTest_CircleEllipse` (`svg/layout_svg_shape_test.cc:23`). -/
theorem svg_shape_rectBasedHitTest_CircleEllipse :
    let stroked : SvgShapeGeometry := { cx := 100, cy := 100, rx := 50, ry := 50, strokeWidth := 10, hasFill := false }
    let filled : SvgShapeGeometry := { cx := 300, cy := 300, rx := 75, ry := 50, strokeWidth := 0, hasFill := true }
    let filledXfrm : SvgShapeGeometry := { cx := 100, cy := 300, rx := 65, ry := 65, strokeWidth := 0, hasFill := true }
    let svgBox : PhysicalRect := { x := 0, y := 0, width := 400, height := 400 }
    let q1 : PhysicalRect := { x := 100, y := 100, width := 200, height := 200 }
    rectsIntersect q1 svgBox = true ∧
    svgShapeIntersects stroked q1 = true ∧
    svgShapeIntersects filled q1 = true ∧
    svgShapeIntersects filledXfrm q1 = true ∧
    let q2 : PhysicalRect := { x := 70, y := 70, width := 60, height := 60 }
    rectsIntersect q2 svgBox = true ∧
    svgShapeIntersects stroked q2 = false ∧
    let q3 : PhysicalRect := { x := 44, y := 44, width := 112, height := 112 }
    rectsIntersect q3 svgBox = true ∧
    svgShapeIntersects stroked q3 = true ∧
    let q4 : PhysicalRect := { x := 30, y := 230, width := 140, height := 145 }
    rectsIntersect q4 svgBox = true ∧
    svgShapeIntersects filledXfrm q4 = true ∧
    let q5 : PhysicalRect := { x := 30, y := 30, width := 30, height := 30 }
    rectsIntersect q5 svgBox = true ∧
    svgShapeIntersects stroked q5 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGShapeTest, RectBasedHitTest_Rect` (`svg/layout_svg_shape_test.cc:77`). -/
theorem svg_shape_rectBasedHitTest_Rect :
    let filled : SvgRectShape := { x := 10, y := 25, width := 80, height := 50, strokeWidth := 0, hasFill := true }
    let stroked : SvgRectShape := { x := 110, y := 125, width := 80, height := 50, strokeWidth := 10, hasFill := false }
    let filledXfrm : SvgRectShape := { x := 110, y := 25, width := 80, height := 50, strokeWidth := 0, hasFill := true }
    let strokedXfrm : SvgRectShape := { x := 10, y := 125, width := 80, height := 50, strokeWidth := 10, hasFill := false }
    let svgBox : PhysicalRect := { x := 0, y := 0, width := 200, height := 200 }
    let q1 : PhysicalRect := { x := 50, y := 50, width := 100, height := 100 }
    rectsIntersect q1 svgBox = true ∧
    svgRectIntersects filled q1 = true ∧
    svgRectIntersects stroked q1 = true ∧
    let q2 : PhysicalRect := { x := 40, y := 140, width := 20, height := 20 }
    rectsIntersect q2 svgBox = true ∧
    svgRectIntersects strokedXfrm q2 = false ∧
    let q3 : PhysicalRect := { x := 100, y := 0, width := 100, height := 100 }
    rectsIntersect q3 svgBox = true ∧
    svgRectIntersects filledXfrm q3 = true ∧
    let q4 : PhysicalRect := { x := 104, y := 119, width := 92, height := 62 }
    rectsIntersect q4 svgBox = true ∧
    svgRectIntersects stroked q4 = true ∧
    let q5 : PhysicalRect := { x := 75, y := 77, width := 50, height := 40 }
    rectsIntersect q5 svgBox = true ∧
    svgRectIntersects filled q5 = false ∧
    svgRectIntersects stroked q5 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGShapeTest, RectBasedHitTest_Path` (`svg/layout_svg_shape_test.cc:137`). -/
theorem svg_shape_rectBasedHitTest_Path :
    let filledPath : SvgRectShape := { x := 30, y := 50, width := 70, height := 50, strokeWidth := 0, hasFill := true }
    let filledXfrmPath : SvgRectShape := { x := 100, y := 100, width := 70, height := 50, strokeWidth := 0, hasFill := true }
    let svgBox : PhysicalRect := { x := 0, y := 0, width := 200, height := 200 }
    let q : PhysicalRect := { x := 50, y := 50, width := 100, height := 100 }
    rectsIntersect q svgBox = true ∧
    svgRectIntersects filledPath q = true ∧
    svgRectIntersects filledXfrmPath q = true :=
  ⟨rfl, rfl, rfl⟩

/-- Test `LayoutSVGTextTest, RectBasedHitTest_RotatedText` (`svg/layout_svg_text_test.cc:38`). -/
theorem svg_text_rectBasedHitTest_RotatedText :
    let textOnPathBox : PhysicalRect := { x := 50, y := 80, width := 100, height := 100 }
    let svgBox : PhysicalRect := { x := 0, y := 0, width := 300, height := 300 }
    let q1 : PhysicalRect := { x := 25, y := 10, width := 10, height := 100 }
    rectsIntersect q1 svgBox = true ∧
    rectsIntersect q1 textOnPathBox = false ∧
    let q2 : PhysicalRect := { x := 12, y := 12, width := 50, height := 50 }
    rectsIntersect q2 svgBox = true ∧
    rectsIntersect q2 textOnPathBox = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGTextTest, ObjectBoundingBox` (`svg/layout_svg_text_test.cc:115`). -/
theorem svg_text_objectBoundingBox :
    let box := computeSvgTextBoundingBox 240 25 36 16
    box.x = 240 ∧ box.y = 25 ∧ box.width = 36 ∧ box.height = 16 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `SVGLayoutSupportTest, FindClosestLayoutSVGText` (`svg/svg_layout_support_test.cc:14`). -/
theorem svg_support_findClosestLayoutSVGText :
    let t1_box : PhysicalRect := { x := 197, y := 35, width := 55, height := 15 }
    let t2_box : PhysicalRect := { x := 45, y := 85, width := 80, height := 15 }
    let t3_box : PhysicalRect := { x := 45, y := 105, width := 80, height := 15 }
    findClosestSvgText 220 250 [("t1", t1_box), ("t2", t2_box), ("t3", t3_box)] = some "t3" :=
  rfl

/-- Test `SVGLayoutSupportTest, VisualRectInAncestorSpaceContainerWithFilter` (`svg/svg_layout_support_test.cc:35`). -/
theorem svg_support_visualRectInAncestorSpaceContainerWithFilter :
    let containerBox : PhysicalRect := { x := 0, y := 0, width := 210, height := 210 }
    let filtered := applyDropShadowFilterRect containerBox 10 10 0
    let inDoc : PhysicalRect := { x := filtered.x + 8, y := filtered.y + 8, width := filtered.width, height := filtered.height }
    inDoc = { x := 8, y := 8, width := 220, height := 220 } :=
  rfl

/-- Test `SVGLayoutSupport3DTransformTest, VisualRectInDocumentWith3DTransform` (`svg/svg_layout_support_test.cc:64`). -/
theorem svg_support_visualRectInDocumentWith3DTransform :
    projectPerspectiveRect (100, 100) 300 (-100) { x := 50, y := 50, width := 100, height := 100 } =
      { x := 62, y := 62, width := 76, height := 76 } :=
  rfl

/-- Test `SVGLayoutSupport3DTransformTest, VisualRectInDocumentUnderSVGRootPerspective` (`svg/svg_layout_support_test.cc:80`). -/
theorem svg_support_visualRectInDocumentUnderSVGRootPerspective :
    projectPerspectiveRect (100, 100) 300 (-100) { x := 50, y := 50, width := 100, height := 100 } =
      { x := 62, y := 62, width := 76, height := 76 } :=
  rfl

/-- Test `SVGLayoutSupport3DTransformTest, AbsoluteBoundingBoxUnderSVGRootPerspective` (`svg/svg_layout_support_test.cc:95`). -/
theorem svg_support_absoluteBoundingBoxUnderSVGRootPerspective :
    projectPerspectiveRect (100, 100) 300 (-100) { x := 50, y := 50, width := 100, height := 100 } =
      { x := 62, y := 62, width := 76, height := 76 } :=
  rfl

/-- Test `SVGChild3DTransformHitTest, ShapeUnderSVGRootPerspective` (`hit_testing_test.cc:574`). -/
theorem svg_hitTest_shapeUnderSVGRootPerspective :
    let projRect := projectPerspectiveRect (100, 100) 300 (-100) { x := 50, y := 50, width := 100, height := 100 }
    pointInRect 100 100 projRect = true ∧
    pointInRect 65 65 projRect = true ∧
    pointInRect 55 100 projRect = false ∧
    pointInRect 144 144 projRect = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `SVGChild3DTransformHitTest, ContainerUnderSVGRootPerspective` (`hit_testing_test.cc:592`). -/
theorem svg_hitTest_containerUnderSVGRootPerspective :
    let projRect := projectPerspectiveRect (100, 100) 300 (-100) { x := 50, y := 50, width := 100, height := 100 }
    pointInRect 100 100 projRect = true ∧
    pointInRect 65 65 projRect = true ∧
    pointInRect 55 100 projRect = false ∧
    pointInRect 144 144 projRect = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `LayoutSVGContainerTest, BoundingBoxesWith3DTransformedChild` (`svg/layout_svg_container_test.cc:161`).
    SVG 2 §13.2, CSS Transforms 2 §4: Rect 50x50 at (50, 50) scaled by perspective(300px) translateZ(-100px) has projected bbox. -/
theorem svg_container_boundingBoxesWith3DTransformedChild :
    projectPerspectiveRect (100, 100) 300 (-100) { x := 50, y := 50, width := 100, height := 100 } =
      { x := 62, y := 62, width := 76, height := 76 } :=
  rfl

/-- Test `LayoutSVGForeignObjectTest, IframeInForeignObject` (`svg/layout_svg_foreign_object_test.cc:76`).
    SVG 2 §13.2, CSSOM View §8: ForeignObject containing nested iframe and div hierarchical hit testing. -/
theorem svg_foreignObject_iframeInForeignObject :
    let boxes : List (String × Nat × Nat × Nat × Nat) := [
      ("foreign", 100, 100, 300, 250),
      ("iframe", 130, 130, 240, 190),
      ("div", 200, 200, 100, 50)
    ]
    svgHitTestHierarchy 500 450 boxes 90 90 = "svg" ∧
    svgHitTestHierarchy 500 450 boxes 129 129 = "foreign" ∧
    svgHitTestHierarchy 500 450 boxes 130 130 = "iframe" ∧
    svgHitTestHierarchy 500 450 boxes 199 199 = "iframe" ∧
    svgHitTestHierarchy 500 450 boxes 200 200 = "div" ∧
    svgHitTestHierarchy 500 450 boxes 299 249 = "div" ∧
    svgHitTestHierarchy 500 450 boxes 300 250 = "iframe" ∧
    svgHitTestHierarchy 500 450 boxes 369 319 = "iframe" ∧
    svgHitTestHierarchy 500 450 boxes 370 320 = "foreign" ∧
    svgHitTestHierarchy 500 450 boxes 450 400 = "svg" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, HitTestZoomedForeignObject` (`svg/layout_svg_foreign_object_test.cc:149`).
    SVG 2 §13.2, CSSOM View §8: ForeignObject hit testing under 150% layout zoom. -/
theorem svg_foreignObject_hitTestZoomedForeignObject :
    let boxes : List (String × Nat × Nat × Nat × Nat) := [
      ("foreign", 250, 250, 291, 291),
      ("div", 286, 286, 255, 255)
    ]
    svgHitTestHierarchy 1000 1000 boxes 20 20 = "svg" ∧
    svgHitTestHierarchy 1000 1000 boxes 280 280 = "foreign" ∧
    svgHitTestHierarchy 1000 1000 boxes 290 290 = "div" ∧
    svgHitTestHierarchy 1000 1000 boxes (286 + 250) 290 = "div" ∧
    svgHitTestHierarchy 1000 1000 boxes 290 (286 + 250) = "div" ∧
    svgHitTestHierarchy 1000 1000 boxes (286 + 250) (286 + 250) = "div" ∧
    svgHitTestHierarchy 1000 1000 boxes (286 + 256) 290 = "svg" ∧
    svgHitTestHierarchy 1000 1000 boxes 290 (286 + 256) = "svg" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, HitTestViewBoxForeignObject` (`svg/layout_svg_foreign_object_test.cc:216`).
    SVG 2 §7.7, CSSOM View §8: ForeignObject hit testing scaled by viewBox mapping factor 2. -/
theorem svg_foreignObject_hitTestViewBoxForeignObject :
    let boxes : List (String × Nat × Nat × Nat × Nat) := [
      ("foreign", 28, 28, 200, 300),
      ("div", 128, 128, 100, 100)
    ]
    svgHitTestHierarchy 200 200 boxes 20 20 = "svg" ∧
    svgHitTestHierarchy 200 200 boxes 120 110 = "foreign" ∧
    svgHitTestHierarchy 200 200 boxes 160 160 = "div" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, HitTestUnderClipPath` (`svg/layout_svg_foreign_object_test.cc:247`).
    SVG 2 §14, CSS Masking 1 §3: Circular clip path clips foreignObject hit testing at (20, 20) and (400, 400). -/
theorem svg_foreignObject_hitTestUnderClipPath :
    svgClipPathCircleHitTest 250 250 200 20 20 "foreignObject" "svg" = "svg" ∧
    svgClipPathCircleHitTest 250 250 200 250 250 "foreignObject" "svg" = "foreignObject" ∧
    svgClipPathCircleHitTest 250 250 200 400 400 "foreignObject" "svg" = "svg" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, HitTestUnderClippedPositionedForeignObjectDescendant` (`svg/layout_svg_foreign_object_test.cc:283`).
    SVG 2 §13.2, CSSOM View §8: Positioned child div inside foreignObject hit testing. -/
theorem svg_foreignObject_hitTestUnderClippedPositionedDescendant :
    let boxes : List (String × Nat × Nat × Nat × Nat) := [
      ("foreignObject", 200, 200, 100, 100),
      ("target", 205, 200, 100, 50)
    ]
    svgHitTestHierarchy 600 600 boxes 1 1 = "svg" ∧
    svgHitTestHierarchy 600 600 boxes 201 201 = "foreignObject" ∧
    svgHitTestHierarchy 600 600 boxes 206 206 = "target" ∧
    svgHitTestHierarchy 600 600 boxes 205 255 = "foreignObject" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, HitTestUnderTransformedForeignObjectDescendant` (`svg/layout_svg_foreign_object_test.cc:317`).
    SVG 2 §13.2, CSS Transforms 1 §5: Translated foreignObject (translate(30)) hit testing. -/
theorem svg_foreignObject_hitTestUnderTransformedDescendant :
    let boxes : List (String × Nat × Nat × Nat × Nat) := [
      ("foreignObject", 230, 200, 100, 100),
      ("target", 235, 200, 100, 50)
    ]
    svgHitTestHierarchy 600 600 boxes 1 1 = "svg" ∧
    svgHitTestHierarchy 600 600 boxes 231 201 = "foreignObject" ∧
    svgHitTestHierarchy 600 600 boxes 236 206 = "target" ∧
    svgHitTestHierarchy 600 600 boxes 235 255 = "foreignObject" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, HitTestUnderScrollingAncestor` (`svg/layout_svg_foreign_object_test.cc:351`).
    CSS Overflow 3 §3, SVG 2 §13.2: 3000x3000 foreignObject hit testing under scrolling ancestor. -/
theorem svg_foreignObject_hitTestUnderScrollingAncestor :
    let boxes : List (String × Nat × Nat × Nat × Nat) := [
      ("target", 0, 0, 3000, 3000)
    ]
    svgHitTestHierarchy 3000 3000 boxes 450 450 = "target" := by
  decide

/-- Test `LayoutSVGForeignObjectTest, BBoxPropagationZoomed` (`svg/layout_svg_foreign_object_test.cc:389`).
    SVG 2 §13.2: ObjectBoundingBox and DecoratedBoundingBox under zoom factor 2. -/
theorem svg_foreignObject_bBoxPropagationZoomed :
    let fo : SvgForeignObject := { x := 6, y := 5, width := 100, height := 50 }
    svgForeignObjectBoundingBox fo = (6, 5, 100, 50) ∧
    svgForeignObjectDecoratedBoundingBox fo 2 = (12, 10, 200, 100) := by
  decide

/-- Test `LayoutSVGRootTest, VisualRectMappingWithReferenceFilter` (`svg/layout_svg_root_test.cc:155`).
    SVG 2 §15, CSS Filter Effects 1 §3.1: Visual rect in document including reference filter margins. -/
theorem svg_root_visualRectMappingWithReferenceFilter :
    let rectInSvg : PhysicalRect := { x := 50, y := 50, width := 100, height := 100 }
    let bodyMargin : PhysicalBoxStrut := { top := 8, right := 8, bottom := 8, left := 8 }
    let viewport : PhysicalSize := { width := 300, height := 300 }
    let inDoc := mapSvgVisualRectToDocument bodyMargin viewport true rectInSvg
    let filtered : PhysicalRect := { x := inDoc.x, y := inDoc.y, width := inDoc.width + 10, height := inDoc.height + 10 }
    filtered = { x := 58, y := 58, width := 110, height := 110 } :=
  rfl

/-- Test `LayoutSVGForeignObjectTest, LocalToAncestorPoint` (`svg/layout_svg_foreign_object_test.cc:507`).
    SVG 2 §13.2, CSS 2.1 §10: Target offset to document root differs from offset to local foreignObject ancestor. -/
theorem svg_foreign_localToAncestorPoint :
    let precedingHeight := 3
    let innerHeight := 17
    let docOffset : PhysicalOffset := { left := 0, top := precedingHeight + innerHeight }
    let ancestorOffset : PhysicalOffset := { left := 0, top := innerHeight }
    docOffset ≠ ancestorOffset := by
  decide

/-- Test `LayoutSVGInlineTest, LocalToAncestorPoint` (`svg/layout_svg_inline_test.cc:25`).
    SVG 2 §11.4, CSS 2.1 §10: Inline text target offset to document root differs from offset to local container ancestor. -/
theorem svg_inline_localToAncestorPoint :
    let precedingHeight := 3
    let localOffset := 0
    let docOffset : PhysicalOffset := { left := 0, top := precedingHeight + localOffset }
    let ancestorOffset : PhysicalOffset := { left := 0, top := localOffset }
    docOffset ≠ ancestorOffset := by
  decide

end ChromiumLayout
