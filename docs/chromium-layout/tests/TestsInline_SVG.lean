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

end ChromiumLayout
