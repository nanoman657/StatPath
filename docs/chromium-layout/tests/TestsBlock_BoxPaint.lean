import BlockBoxPaint

/-!
  Test vectors for `layout_box_test.cc` background/foreground paint queries,
  background paint location, contents visual overflow propagation, and hit-testing.
-/

namespace TestsBlock_BoxPaint

open BlockBoxPaint

-- layout_box_test.cc:45: BackgroundIsKnownToBeObscured
theorem backgroundIsKnownToBeObscured :
    backgroundKnownObscured 295 100 295 100 true true false = true := by decide

-- layout_box_test.cc:59: BackgroundNotObscuredWithCssClippedChild
theorem backgroundNotObscuredWithCssClippedChild :
    backgroundKnownObscured 200 200 0 0 false true true = false ∧
    backgroundKnownObscured 200 200 200 200 true true true = false := by decide

-- layout_box_test.cc:88: BackgroundNotObscuredWithCssClippedGrandChild
theorem backgroundNotObscuredWithCssClippedGrandChild :
    backgroundKnownObscured 200 200 0 0 false true true = false ∧
    backgroundKnownObscured 200 200 200 200 true true true = false := by decide

-- layout_box_test.cc:127: ForegroundIsKnownToBeOpaqueInRect
theorem foregroundIsKnownToBeOpaqueInRect :
    foregroundKnownOpaqueInRect 0 0 10 10 30 0 10 10 false true true = true ∧
    foregroundKnownOpaqueInRect 0 10 10 10 30 10 10 10 false false true = false ∧
    foregroundKnownOpaqueInRect 20 20 10 10 30 20 10 10 false true false = false ∧
    foregroundKnownOpaqueInRect 0 20 10 10 30 0 10 10 false true true = false ∧
    foregroundKnownOpaqueInRect 0 0 30 30 30 0 10 10 false true true = false ∧
    foregroundKnownOpaqueInRect 0 0 10 30 30 0 10 10 false true true = false := by decide

-- layout_box_test.cc:161: ForegroundIsKnownToBeOpaqueInRectVerticalRL
theorem foregroundIsKnownToBeOpaqueInRectVerticalRL :
    foregroundKnownOpaqueInRect 20 0 10 10 30 0 10 10 true true true = true ∧
    foregroundKnownOpaqueInRect 10 0 10 10 30 10 10 10 true false true = false ∧
    foregroundKnownOpaqueInRect 0 20 10 10 30 20 10 10 true true false = false ∧
    foregroundKnownOpaqueInRect 0 0 10 10 30 0 10 10 true true true = false ∧
    foregroundKnownOpaqueInRect 0 0 30 30 30 0 10 10 true true true = false ∧
    foregroundKnownOpaqueInRect 20 0 30 10 30 0 10 10 true true true = false := by decide

-- layout_box_test.cc:197: BackgroundRect
theorem backgroundRect :
    let check (a b : (Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat)) : Bool := a == b
    -- target1: image border-box, opaque color content-box, solid border
    check (physicalBackgroundRects 10 10 100 100 true true false false 0 true 2 true)
      ((20, 20, 100, 100), (10, 10, 120, 120)) ∧
    -- target1a: dashed border (not opaque)
    check (physicalBackgroundRects 10 10 100 100 true true false false 0 true 2 false)
      ((20, 20, 100, 100), (0, 0, 140, 140)) ∧
    -- target1b: image border-box only, solid border
    check (physicalBackgroundRects 10 10 100 100 false false false false 0 true 2 true)
      ((0, 0, 0, 0), (10, 10, 120, 120)) ∧
    -- target2: image content-box, opaque local color border-box
    check (physicalBackgroundRects 10 10 100 100 true true false true 2 true 0 true)
      ((10, 10, 120, 120), (10, 10, 120, 120)) ∧
    -- target2b: image content-box only
    check (physicalBackgroundRects 10 10 100 100 false false false false 0 true 0 true)
      ((0, 0, 0, 0), (20, 20, 100, 100)) ∧
    -- target3: image content-box, translucent color border-box
    check (physicalBackgroundRects 10 10 100 100 true false false false 2 true 0 true)
      ((0, 0, 0, 0), (10, 10, 120, 120)) ∧
    -- target4: image content-box, blend-mode color border-box
    check (physicalBackgroundRects 10 10 100 100 true true true false 2 true 0 true)
      ((0, 0, 0, 0), (10, 10, 120, 120)) ∧
    -- target5: none border-box, opaque color content-box
    check (physicalBackgroundRects 10 10 100 100 true true false false 0 false 2 true)
      ((20, 20, 100, 100), (20, 20, 100, 100)) ∧
    -- target6: opaque color content-box local
    check (physicalBackgroundRects 10 10 100 100 true true false true 0 false 0 true)
      ((20, 20, 100, 100), (10, 10, 120, 120)) ∧
    -- target7: opaque color text clip, solid border
    check (physicalBackgroundRects 10 10 100 100 true true false false 3 false 0 true)
      ((0, 0, 0, 0), (10, 10, 120, 120)) ∧
    -- target7a: opaque color text clip, dashed border
    check (physicalBackgroundRects 10 10 100 100 true true false false 3 false 0 false)
      ((0, 0, 0, 0), (0, 0, 140, 140)) ∧
    -- target8 / target9: transparent / none
    check (physicalBackgroundRects 10 10 100 100 false false false false 2 false 0 true)
      ((0, 0, 0, 0), (0, 0, 0, 0)) := by decide

-- layout_box_test.cc:356: LocationContainer
theorem locationContainer :
    -- body=1, div=2, b(inline)=3, img=4, table=5, tbody=6, row=7, cell=8
    resolveLocationContainer 1 1 false false = 1 ∧
    resolveLocationContainer 3 2 true false = 2 ∧
    resolveLocationContainer 1 1 false false = 1 ∧
    resolveLocationContainer 5 5 false false = 5 ∧
    resolveLocationContainer 6 6 false false = 6 ∧
    resolveLocationContainer 7 7 false false = 7 := by decide

-- layout_box_test.cc:435: LocationContainerOfSVG
theorem locationContainerOfSVG :
    -- svg_root=2 in body=1; foreignObject=3 has null LocationContainer (0) and
    -- physical rect (44, 77, 100, 80); child=4 in vertical-rl foreignObject has
    -- LocationContainer=3 and physical x = 100 - 33 = 67.
    resolveLocationContainer 1 1 false false = 1 ∧
    resolveLocationContainer 2 2 false true = 0 ∧
    resolveLocationContainer 3 3 false false = 3 ∧
    (100 - 33, (0 : Int)) = (67, 0) := by decide

-- layout_box_test.cc:670: ContentsVisualOverflowPropagation
theorem contentsVisualOverflowPropagation :
    let selfRect : Int × Int × Int × Int := (0, 0, 100, 100)
    let cContents : Int × Int × Int × Int := (-10, 20, 100, 100)
    let cVis := rectUnion selfRect cContents
    let dContents : Int × Int × Int × Int := (10, 20, 100, 100)
    let dVis := rectUnion selfRect dContents
    let bContents := rectUnion (offsetRect (-30) 40 cVis) (offsetRect (-130) 40 dVis)
    let bVis := rectUnion selfRect bContents
    let aContents := offsetRect 60 50 bVis
    let aVis := rectUnion selfRect aContents
    cVis = (-10, 0, 110, 120) ∧
    dVis = (0, 0, 110, 120) ∧
    bContents = (-130, 40, 200, 120) ∧
    bVis = (-130, 0, 230, 160) ∧
    aContents = (-70, 50, 230, 160) ∧
    aVis = (-70, 0, 230, 210) := by decide

-- layout_box_test.cc:717: HitTestOverflowClipMargin
theorem hitTestOverflowClipMargin :
    hitTestBoxWithClipAndResizer 0 0 200 200 50 300 100 0 230 50 true = 4 ∧
    hitTestBoxWithClipAndResizer 0 0 200 200 50 300 100 0 280 50 true = 2 ∧
    hitTestBoxWithClipAndResizer 0 0 200 200 50 300 100 0 100 150 true = 3 ∧
    hitTestBoxWithClipAndResizer 0 0 200 200 50 300 100 0 100 230 true = 1 := by decide

-- layout_box_test.cc:737: HitTestContainPaint
theorem hitTestContainPaint :
    hitTestBoxWithClipAndResizer 8 8 100 200 0 300 400 0 1 1 true = 1 ∧
    hitTestBoxWithClipAndResizer 8 8 100 200 0 300 400 0 10 10 true = 4 ∧
    hitTestBoxWithClipAndResizer 8 8 100 200 0 300 400 0 150 10 true = 2 ∧
    hitTestBoxWithClipAndResizer 8 8 100 200 0 300 400 0 10 250 true = 1 := by decide

-- layout_box_test.cc:816: DelayedInvalidation
theorem delayedInvalidation :
    imageChangedInvalidation true true false = (false, true, true) ∧
    imageChangedInvalidation true false false = (true, true, false) := by decide

-- layout_box_test.cc:849: DelayedInvalidationLayoutViewScrolled
theorem delayedInvalidationLayoutViewScrolled :
    imageChangedInvalidation true true true = (false, true, false) := by decide

-- layout_box_test.cc:891: MarkerContainerScrollableOverflowRect
theorem markerContainerScrollableOverflowRect :
    let lineHeight : Int := 100
    let fontSize : Int := 16
    let markerBottom := (lineHeight - fontSize) / 2 + fontSize
    markerBottom ≥ 50 := by decide

-- layout_box_test.cc:1664: HasReflection
theorem hasReflection :
    supportsLayerAndReflection false false = true ∧
    supportsLayerAndReflection true false = false ∧
    supportsLayerAndReflection false true = false := by decide

-- layout_box_test.cc:1709: SetNeedsOverflowRecalcLayoutBox
theorem setNeedsOverflowRecalcLayoutBox :
    overflowRecalcOnTransformChange false false = (false, false) ∧
    overflowRecalcOnTransformChange false true = (false, true) ∧
    overflowRecalcOnTransformChange true false = (false, true) := by decide

-- layout_box_test.cc:1732: SetNeedsOverflowRecalcFlexBox
theorem setNeedsOverflowRecalcFlexBox :
    overflowRecalcOnTransformChange false false = (false, false) ∧
    overflowRecalcOnTransformChange false true = (false, true) ∧
    overflowRecalcOnTransformChange true false = (false, true) := by decide

-- layout_box_test.cc:1775: HitTestResizerWithTextAreaChild
theorem hitTestResizerWithTextAreaChild :
    hitTestBoxWithClipAndResizer 0 0 100 100 0 100 100 15 99 99 true = 3 ∧
    hitTestBoxWithClipAndResizer 0 0 100 100 0 100 100 15 1 1 true = 4 := by decide

-- layout_box_test.cc:2245: AttachmentLocalContentBoxClipNonZeroPadding
theorem attachmentLocalContentBoxClipNonZeroPadding :
    backgroundPaintLocation false false true false 0 true false true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2259: NonLocalImage
theorem nonLocalImage :
    backgroundPaintLocation true false true false 2 false false true false false false false false false false = 2 := by decide

-- layout_box_test.cc:2274: LocalImageAndColor
theorem localImageAndColor :
    backgroundPaintLocation true true true false 2 false false true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2288: LocalImageAndNonLocalClipPaddingColor
theorem localImageAndNonLocalClipPaddingColor :
    backgroundPaintLocation true true false false 1 true false true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2306: LocalImageAndNonLocalClipContentColorNonZeroPadding
theorem localImageAndNonLocalClipContentColorNonZeroPadding :
    backgroundPaintLocation true true false false 0 true false true false false false false false false false = 2 := by decide

-- layout_box_test.cc:2323: BorderBoxClipColorNoBorder
theorem borderBoxClipColorNoBorder :
    backgroundPaintLocation false false false false 2 false false true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2335: BorderBoxClipColorSolidBorder
theorem borderBoxClipColorSolidBorder :
    backgroundPaintLocation false false false false 2 false true true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2349: BorderBoxClipColorSolidBorderWithBorderShape
theorem borderBoxClipColorSolidBorderWithBorderShape :
    backgroundPaintLocation false false false false 2 false true true false true false false false false false = 2 := by decide

-- layout_box_test.cc:2365: BorderBoxClipColorTranslucentBorder
theorem borderBoxClipColorTranslucentBorder :
    backgroundPaintLocation false false false false 2 false true false false false false false false false false = 3 := by decide

-- layout_box_test.cc:2381: BorderBoxClipColorDashedBorder
theorem borderBoxClipColorDashedBorder :
    backgroundPaintLocation false false false false 2 false true true true false false false false false false = 3 := by decide

-- layout_box_test.cc:2395: ContentClipColorZeroPadding
theorem contentClipColorZeroPadding :
    backgroundPaintLocation false false false false 0 false false true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2407: ContentClipColorNonZeroPadding
theorem contentClipColorNonZeroPadding :
    backgroundPaintLocation false false false false 0 true false true false false false false false false false = 2 := by decide

-- layout_box_test.cc:2420: CustomScrollbar
theorem customScrollbar :
    backgroundPaintLocation false false false false 2 false false true false false false false true false false = 3 := by decide

-- layout_box_test.cc:2438: TranslucentColorAndTranslucentBorder
theorem translucentColorAndTranslucentBorder :
    backgroundPaintLocation false false false true 2 false true false false false false false false false false = 2 := by decide

-- layout_box_test.cc:2471: InsetBoxShadow
theorem insetBoxShadow :
    backgroundPaintLocation false false false false 2 false false true false false true false false false false = 2 := by decide

-- layout_box_test.cc:2485: OutsetBoxShadow
theorem outsetBoxShadow :
    backgroundPaintLocation false false false false 2 false false true false false false false false false false = 1 := by decide

-- layout_box_test.cc:2496: BorderImage
theorem borderImage :
    backgroundPaintLocation false false false false 2 false true true false false false true false false false = 2 := by decide

-- layout_box_test.cc:2509: ElasticOverscrollEnabledForSubscroll
theorem elasticOverscrollEnabledForSubscroll :
    backgroundPaintLocation false false false false 2 false false true false false false false false false false = 1 ∧
    backgroundPaintLocation false false false false 2 false false true false false false false false true false = 3 ∧
    backgroundPaintLocation false false false true 2 false false true false false false false false true false = 2 ∧
    backgroundPaintLocation false false true false 2 false false true false false false false false true false = 1 := by decide

-- layout_box_test.cc:2560: ElasticOverscrollSupportedForLayoutView
theorem elasticOverscrollSupportedForLayoutView :
    backgroundPaintLocation false false false false 2 false false true false false false false false false false = 1 ∧
    backgroundPaintLocation false false false false 2 false false true false false false false false true false = 3 ∧
    backgroundPaintLocation false false false true 2 false false true false false false false false true false = 2 ∧
    backgroundPaintLocation false false false true 2 false false true false false false false false true true = 1 := by decide

end TestsBlock_BoxPaint
