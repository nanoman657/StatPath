import InlineGeometry
import InlineFragmentItem
import InlineHitTesting

namespace ChromiumLayout

/-! ## Chromium Layout Inline Hit Testing Tests
    Formalized test cases from `third_party/blink/renderer/core/layout/hit_testing_test.cc`.
    Specifications:
    - CSSOM View Module §8 (Hit Testing, Rect-based hit testing, occlusion testing)
    - CSS 2.1 §9.9 & Appendix E (Layered presentation, stacking contexts, paint order)
    - CSS Transforms Module Level 2 §4 (3D Transforms, `preserve-3d`, flattening)
    - CSS Masking Module Level 1 §3 (Clipping paths and hit testing)
    - CSS Backgrounds and Borders Module Level 3 §7.1 (Border shapes hit testing)
    - CSS Filter Effects Module Level 1 §3.1 (Filter margins, visual overflow rect)
    - CSS Overflow Module Level 3 §3 (Scrolling, line boxes hit testing)
-/

/-- Test `HitTestingTest, OcclusionHitTest` (`hit_testing_test.cc:87`).
    CSSOM View §8, CSS 2.1 §9.9: When occluder shifts by -10px margin-top, it intersects target visual rect. -/
theorem hitTest_occlusion :
    let target : PhysicalRect := { x := 0, y := 0, width := 100, height := 100 }
    let occluder_initial : PhysicalRect := { x := 0, y := 100, width := 100, height := 100 }
    let occluder_shifted : PhysicalRect := { x := 0, y := 90, width := 100, height := 100 }
    occludes2D target occluder_initial = false ∧
    occludes2D target occluder_shifted = true := by
  decide

/-- Test `HitTestingTest, HitTestWithCallback` (`hit_testing_test.cc:136`).
    CSSOM View §8: Hit test traversal with callback stopper stops at requested node. -/
theorem hitTest_withCallback :
    let candidates : List String := ["occluder_3", "occluder_2", "occluder_1", "target"]
    let (resNoStop, stoppedNo) := hitTestWithStopper candidates ""
    let (resWithStop, stoppedYes) := hitTestWithStopper candidates "occluder_2"
    resNoStop = candidates ∧ stoppedNo = false ∧
    resWithStop = ["occluder_3", "occluder_2"] ∧ stoppedYes = true := by
  decide

/-- Test `HitTestingTest, OcclusionHitTestWithClipPath` (`hit_testing_test.cc:205`).
    CSS Masking 1 §3, CSSOM View §8: Circular clip path clips out overlap until margin-top exceeds circle boundary. -/
theorem hitTest_occlusionWithClipPath :
    let target : PhysicalRect := { x := 0, y := 0, width := 100, height := 100 }
    let occ1 : PhysicalRect := { x := 0, y := 100, width := 100, height := 100 }
    let occ2 : PhysicalRect := { x := 0, y := 96, width := 100, height := 100 }
    let occ3 : PhysicalRect := { x := 0, y := 94, width := 100, height := 100 }
    occludesWithClipCircle target occ1 50 50 45 = false ∧
    occludesWithClipCircle target occ2 50 50 45 = false ∧
    occludesWithClipCircle target occ3 50 50 45 = true := by
  decide

/-- Test `HitTestingTest, OcclusionHitTestWithBorderShapeStrokeMode` (`hit_testing_test.cc:253`).
    CSS Backgrounds and Borders 3 §7.1, CSSOM View §8: Border shape circle stroke mode early-out hit testing. -/
theorem hitTest_occlusionWithBorderShapeStrokeMode :
    let target : PhysicalRect := { x := 0, y := 0, width := 100, height := 100 }
    let occ1 : PhysicalRect := { x := 100, y := 100, width := 100, height := 100 }
    let occ2 : PhysicalRect := { x := 90, y := 100, width := 100, height := 100 }
    let occ3 : PhysicalRect := { x := 70, y := 100, width := 100, height := 100 }
    occludesWithBorderShapeCircle target occ1 50 50 60 = false ∧
    occludesWithBorderShapeCircle target occ2 50 50 60 = false ∧
    occludesWithBorderShapeCircle target occ3 50 50 60 = true := by
  decide

/-- Test `HitTestingTest, OcclusionHitTestWithBorderShapeFillMode` (`hit_testing_test.cc:319`).
    CSS Backgrounds and Borders 3 §7.1, CSSOM View §8: Concentric polygon outer shape hit testing early-out. -/
theorem hitTest_occlusionWithBorderShapeFillMode :
    let target : PhysicalRect := { x := 0, y := 0, width := 100, height := 100 }
    let occ1 : PhysicalRect := { x := 100, y := 100, width := 100, height := 100 }
    let occ2 : PhysicalRect := { x := 90, y := 100, width := 100, height := 100 }
    let occ3 : PhysicalRect := { x := 70, y := 100, width := 100, height := 100 }
    occludesWithBorderShapeDiamond target occ1 70 = false ∧
    occludesWithBorderShapeDiamond target occ2 70 = false ∧
    occludesWithBorderShapeDiamond target occ3 70 = true := by
  decide

/-- Test `HitTestingTest, ScrolledInline` (`hit_testing_test.cc:384`).
    CSS Overflow 3 §3, CSSOM View §8: Scrolled inline hit testing maps point (5, 5) with scrollTop 100 to line 3 start. -/
theorem hitTest_scrolledInline :
    let lineLengths : List Nat := [6, 6, 6, 6, 6, 6, 6, 6, 6]
    hitTestScrolledLine 100 5 50 lineLengths = 12 := by
  rfl

/-- Test `HitTestingTest, ReferenceFilter` (`hit_testing_test.cc:421`).
    CSS Filter Effects 1 §3.1: Visual overflow rect including reference filter expansion. -/
theorem hitTest_referenceFilter :
    let content : PhysicalRect := { x := 0, y := 0, width := 100, height := 100 }
    filterVisualOverflowRect content 10 = (-10, -10, 120, 120) := by
  rfl

/-- Test `HitTestingTest, OcclusionHitTestWith3DTransform` (`hit_testing_test.cc:457`).
    CSS Transforms 2 §4, CSSOM View §8: In preserve-3d, occluder with rotateY(30deg) extends into z > 0, occluding target; rotateY(10deg) stays behind target. -/
theorem hitTest_occlusionWith3DTransform :
    occludes3D TransformStyle.preserve3d false true (-10) 50 1 2 = true ∧
    occludes3D TransformStyle.preserve3d false true (-10) 50 17 100 = false := by
  decide

/-- Test `HitTestingTest, OcclusionHitTestWithFlattenedPreserve3DOccluder` (`hit_testing_test.cc:495`).
    CSS Transforms 2 §4, CSS 2.1 §9.9: Flat stacking context flattens 3D translations, so occluder paints on top in DOM order regardless of translateZ. -/
theorem hitTest_occlusionWithFlattenedPreserve3DOccluder :
    occludes3D TransformStyle.flat true true (-10) 50 0 1 = true ∧
    occludes3D TransformStyle.flat true true 10 50 0 1 = true := by
  decide

end ChromiumLayout
