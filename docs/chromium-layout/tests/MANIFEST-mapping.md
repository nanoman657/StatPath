# Mapping lane test manifest

Branch `chromium-layout-mapping`, pin `36c121be58126ddbb0686965897b8c8ff9b246fb`,
folder `third_party/blink/renderer/core/layout/`. The tests are the specification: rows record
what each test says coordinate mapping and visual-rect mapping must do. Each test is a `TEST_P` that
runs twice (with and without the geometry mapper); a row stands for both runs.

Rule (a)-(c) for `formalized`: (a) the test's HTML/CSS is written as a value of a model input type
(`BlockFlow.BF` box tree and `Mapping.*` node/hop types); (b) a general model function that mentions
no test computes the mapped point or rectangle; (c) the theorem compares it with the test's
`EXPECT_*` values as literals. Classes: `geometry`, `behaviour`, `internal`. Status: `formalized`,
`partly formalized`, `blocked` (reason given), `internal`.

Model modules: `Mapping*.lean`. Vectors: `tests/TestsMapping_<File>.lean`. Chromium/spec
disagreements: `SPEC-DIFF-mapping.md`.

| file:line | test | class | status | evidence / reason |
|---|---|---|---|---|
| map_coordinates_test.cc:127 | MapCoordinatesTest.SimpleText | geometry | formalized | `TestsMapping.SimpleText_vectors` |
| map_coordinates_test.cc:140 | MapCoordinatesTest.SimpleInline | geometry | formalized | `TestsMapping.SimpleInline_vectors` |
| map_coordinates_test.cc:153 | MapCoordinatesTest.SimpleBlock | geometry | formalized | `TestsMapping.SimpleBlock_vectors` |
| map_coordinates_test.cc:171 | MapCoordinatesTest.OverflowClip | geometry | partly formalized | `TestsMapping.OverflowClip_vectors` covers the scrolled and unscrolled values; the geometry-mapper run reading stale paint properties right after the scroll is not modelled |
| map_coordinates_test.cc:210 | MapCoordinatesTest.TextInRelPosInline | geometry | formalized | `TestsMapping.TextInRelPosInline_vectors` |
| map_coordinates_test.cc:225 | MapCoordinatesTest.RelposInline | geometry | formalized | `TestsMapping.RelposInline_vectors` |
| map_coordinates_test.cc:240 | MapCoordinatesTest.RelposInlineInRelposInline | geometry | formalized | `TestsMapping.RelposInlineInRelposInline_vectors` |
| map_coordinates_test.cc:274 | MapCoordinatesTest.RelPosBlock | geometry | formalized | `TestsMapping.RelPosBlock_vectors` |
| map_coordinates_test.cc:311 | MapCoordinatesTest.AbsPos | geometry | formalized | `TestsMapping.AbsPos_vectors` |
| map_coordinates_test.cc:348 | MapCoordinatesTest.AbsPosAuto | geometry | formalized | `TestsMapping.AbsPosAuto_vectors` |
| map_coordinates_test.cc:385 | MapCoordinatesTest.FixedPos | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| map_coordinates_test.cc:444 | MapCoordinatesTest.FixedPosAuto | geometry | formalized | `TestsMapping.FixedPosAuto_vectors` |
| map_coordinates_test.cc:504 | MapCoordinatesTest.FixedPosInFixedPos | geometry | formalized | `TestsMapping.FixedPosInFixedPos_vectors` |
| map_coordinates_test.cc:573 | MapCoordinatesTest.FixedPosInFixedPosScrollView | geometry | formalized | `TestsMapping.FixedPosInFixedPosScrollView_vectors` |
| map_coordinates_test.cc:610 | MapCoordinatesTest.FixedPosInAbsolutePosScrollView | geometry | formalized | `TestsMapping.FixedPosInAbsolutePosScrollView_vectors` |
| map_coordinates_test.cc:647 | MapCoordinatesTest.FixedPosInTransform | geometry | formalized | `TestsMapping.FixedPosInTransform_vectors` |
| map_coordinates_test.cc:689 | MapCoordinatesTest.FixedPosInContainPaint | geometry | formalized | `TestsMapping.FixedPosInContainPaint_vectors` |
| map_coordinates_test.cc:732 | MapCoordinatesTest.FixedPosInIFrameWhenMainFrameScrolled | geometry | formalized | `TestsMapping.FixedPosInIFrameWhenMainFrameScrolled_vectors` |
| map_coordinates_test.cc:763 | MapCoordinatesTest.IFrameTransformed | geometry | formalized | `TestsMapping.IFrameTransformed_vectors` |
| map_coordinates_test.cc:797 | MapCoordinatesTest.FixedPosInScrolledIFrameWithTransform | geometry | blocked | a fixed box with auto offsets keeps its layout-time viewport position under a scrolled frame; static position of a fixed box under scroll is not modelled |
| map_coordinates_test.cc:828 | MapCoordinatesTest.MulticolWithText | geometry | formalized | `TestsMapping.MulticolWithText_vectors` |
| map_coordinates_test.cc:849 | MapCoordinatesTest.MulticolWithInline | geometry | formalized | `TestsMapping.MulticolWithInline_vectors` |
| map_coordinates_test.cc:868 | MapCoordinatesTest.MulticolWithBlock | geometry | formalized | `TestsMapping.MulticolWithBlock_vectors` |
| map_coordinates_test.cc:889 | MapCoordinatesTest.MulticolWithBlockAbove | geometry | formalized | `TestsMapping.MulticolWithBlockAbove_vectors` |
| map_coordinates_test.cc:907 | MapCoordinatesTest.NestedMulticolWithBlock | geometry | blocked | nested multicol: the inner balanced multicol is itself fragmented across outer columns; balancing and fragmenting an inner container are not in Mapping.Cols |
| map_coordinates_test.cc:945 | MapCoordinatesTest.MulticolWithAbsPosInRelPos | geometry | formalized | `TestsMapping.MulticolWithAbsPosInRelPos_vectors` |
| map_coordinates_test.cc:981 | MapCoordinatesTest.MulticolWithAbsPosInInlineRelPos | geometry | formalized | `TestsMapping.MulticolWithAbsPosInInlineRelPos_vectors` |
| map_coordinates_test.cc:1019 | MapCoordinatesTest.MulticolWithAbsPosNotContained | geometry | formalized | `TestsMapping.MulticolWithAbsPosNotContained_vectors` |
| map_coordinates_test.cc:1060 | MapCoordinatesTest.MulticolRtl | geometry | formalized | `TestsMapping.MulticolRtl_vectors` |
| map_coordinates_test.cc:1079 | MapCoordinatesTest.MulticolWithLargeBorder | geometry | formalized | `TestsMapping.MulticolWithLargeBorder_vectors` |
| map_coordinates_test.cc:1099 | MapCoordinatesTest.FlippedBlocksWritingModeWithText | geometry | formalized | `TestsMapping.FlippedBlocksWritingModeWithText_vectors` |
| map_coordinates_test.cc:1131 | MapCoordinatesTest.FlippedBlocksWritingModeWithInline | geometry | formalized | `TestsMapping.FlippedBlocksWritingModeWithInline_vectors` |
| map_coordinates_test.cc:1183 | MapCoordinatesTest.FlippedBlocksWritingModeWithBlock | geometry | formalized | `TestsMapping.FlippedBlocksWritingModeWithBlock_vectors` |
| map_coordinates_test.cc:1217 | MapCoordinatesTest.Table | geometry | blocked | table cell positions (border-spacing, section order, vertical-align middle) come from the table lane model TableLayout, not modelled in Mapping |
| map_coordinates_test.cc:1318 | MapCoordinatesTest.Transforms | geometry | blocked | rotation by 45 degrees needs irrational (square root of 2) matrix entries; MappingTransform.Aff is integer-exact |
| map_coordinates_test.cc:1378 | MapCoordinatesTest.SVGShape | geometry | formalized | `TestsMapping.SVGShape_vectors` |
| map_coordinates_test.cc:1397 | MapCoordinatesTest.SVGShapeScale | geometry | formalized | `TestsMapping.SVGShapeScale_vectors` |
| map_coordinates_test.cc:1417 | MapCoordinatesTest.SVGShapeWithViewBoxWithoutScale | geometry | formalized | `TestsMapping.SVGShapeWithViewBoxWithoutScale_vectors` |
| map_coordinates_test.cc:1436 | MapCoordinatesTest.SVGShapeWithViewBoxWithScale | geometry | formalized | `TestsMapping.SVGShapeWithViewBoxWithScale_vectors` |
| map_coordinates_test.cc:1455 | MapCoordinatesTest.SVGShapeWithViewBoxWithNonZeroOffset | geometry | formalized | `TestsMapping.SVGShapeWithViewBoxWithNonZeroOffset_vectors` |
| map_coordinates_test.cc:1475 | MapCoordinatesTest.SVGShapeWithViewBoxWithNonZeroOffsetAndScale | geometry | formalized | `TestsMapping.SVGShapeWithViewBoxWithNonZeroOffsetAndScale_vectors` |
| map_coordinates_test.cc:1495 | MapCoordinatesTest.SVGForeignObject | geometry | formalized | `TestsMapping.SVGForeignObject_vectors` |
| map_coordinates_test.cc:1532 | MapCoordinatesTest.LocalToAbsoluteTransform | geometry | formalized | `TestsMapping.LocalToAbsoluteTransform_vectors` |
| map_coordinates_test.cc:1555 | MapCoordinatesTest.LocalToAncestorTransform | geometry | blocked | rotation by 45 degrees needs irrational (square root of 2) matrix entries; MappingTransform.Aff is integer-exact |
| map_coordinates_test.cc:1600 | MapCoordinatesTest.LocalToAbsoluteTransformFlattens | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| map_coordinates_test.cc:1645 | MapCoordinatesTest.Transform3DWithOffset | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| map_coordinates_test.cc:1668 | MapCoordinatesTest.Transform3DWithOffset2 | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| map_coordinates_test.cc:1693 | MapCoordinatesTest.IgnoreScrollOffset | geometry | formalized | `TestsMapping.IgnoreScrollOffset_vectors` |
| map_coordinates_test.cc:1732 | MapCoordinatesTest.IgnoreScrollOffsetForInline | geometry | blocked | position:sticky offset (CSS Positioned Layout 3 §3.4) is not modelled |
| map_coordinates_test.cc:1770 | MapCoordinatesTest.IgnoreScrollOffsetWithWritingModes | geometry | blocked | scroll origin and scrollable-overflow width of a vertical-rl scroller are not modelled |
| map_coordinates_test.cc:1818 | MapCoordinatesTest.FixedPositionWithScrollOffset | geometry | formalized | `TestsMapping.FixedScrollOffset_vectors`, `Mapping.mapRange_oof` |
| map_coordinates_test.cc:1853 | MapCoordinatesTest.FixedPositionWithScrollOffsetVerticalRL | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| map_coordinates_test.cc:1889 | MapCoordinatesTest.FixedPositionUnderTransformWithScrollOffset | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| map_coordinates_test.cc:1931 | MapCoordinatesTest.IgnoreScrollOffsetWithWritingModesAndNonOverlayScrollbar | geometry | blocked | scrollbar themes: engine service, parked |
| map_coordinates_test.cc:1975 | MapCoordinatesTest.ElementCanvasTransform | geometry | formalized | `TestsMapping.ElementCanvasTransform_vectors` |
| map_coordinates_test.cc:1996 | MapCoordinatesTest.NestedElementCanvasTransform | geometry | formalized | `TestsMapping.NestedElementCanvasTransform_vectors` |
| map_coordinates_test.cc:2021 | MapCoordinatesTest.NestedElementCanvasTransformWithOffset | geometry | formalized | `TestsMapping.NestedElementCanvasTransformWithOffset_vectors` |
| map_coordinates_test.cc:2046 | MapCoordinatesTest.NestedElementCanvasTransformChildWithoutCanvasTransform | geometry | formalized | `TestsMapping.NestedElementCanvasTransformChildWithoutCanvasTransform_vectors` |
| map_coordinates_test.cc:2069 | MapCoordinatesTest.NestedElementCanvasTransformNonDrawableChild | geometry | formalized | `TestsMapping.NestedElementCanvasTransformNonDrawableChild_vectors` |
| map_coordinates_test.cc:2093 | MapCoordinatesTest.NestedElementCanvasTransformInline | geometry | formalized | `TestsMapping.NestedElementCanvasTransformInline_vectors` |
| visual_rect_mapping_test.cc:126 | VisualRectMappingTest.LayoutText | geometry | formalized | `TestsMapping.LayoutText_vectors` |
| visual_rect_mapping_test.cc:165 | VisualRectMappingTest.LayoutTextContainerFlippedWritingMode | geometry | formalized | `TestsMapping.LayoutTextContainerFlippedWritingMode_vectors` |
| visual_rect_mapping_test.cc:202 | VisualRectMappingTest.LayoutInline | geometry | formalized | `TestsMapping.LayoutInline_vectors` |
| visual_rect_mapping_test.cc:240 | VisualRectMappingTest.LayoutInlineContainerFlippedWritingMode | geometry | formalized | `TestsMapping.LayoutInlineContainerFlippedWritingMode_vectors` |
| visual_rect_mapping_test.cc:281 | VisualRectMappingTest.SkipAncestorAndViewportClipFlag | geometry | formalized | `TestsMapping.SkipAncestorAndViewportClipFlag_vectors` |
| visual_rect_mapping_test.cc:338 | VisualRectMappingTest.SkipAncestorAndViewportClipFlagViewportSpace | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| visual_rect_mapping_test.cc:419 | VisualRectMappingTest.SkipAncestorAndViewportClipsInSubframe | geometry | formalized | `TestsMapping.SkipAncestorAndViewportClipsInSubframe_vectors` |
| visual_rect_mapping_test.cc:488 | VisualRectMappingTest.RegressionTest_SkipAncestorClipExpansion | geometry | blocked | rotation by 45 degrees needs irrational (square root of 2) matrix entries; MappingTransform.Aff is integer-exact |
| visual_rect_mapping_test.cc:542 | VisualRectMappingTest.LayoutView | geometry | formalized | `TestsMapping.LayoutView_vectors` |
| visual_rect_mapping_test.cc:588 | VisualRectMappingTest.LayoutViewSubpixelRounding | geometry | blocked | fractional LayoutUnit positions and enclosing-rect snapping are not modelled (Mapping coordinates are whole pixels) |
| visual_rect_mapping_test.cc:619 | VisualRectMappingTest.LayoutViewDisplayNone | behaviour | blocked | display:none on an iframe destroys its layout objects; object lifecycle, not coordinate mapping |
| visual_rect_mapping_test.cc:658 | VisualRectMappingTest.SelfFlippedWritingMode | geometry | formalized | `TestsMapping.SelfFlippedWritingMode_vectors` |
| visual_rect_mapping_test.cc:681 | VisualRectMappingTest.ContainerFlippedWritingMode | geometry | formalized | `TestsMapping.ContainerFlippedWritingMode_vectors` |
| visual_rect_mapping_test.cc:722 | VisualRectMappingTest.ContainerOverflowScroll | geometry | formalized | `TestsMapping.ContainerOverflowScroll_vectors` |
| visual_rect_mapping_test.cc:778 | VisualRectMappingTest.ContainerFlippedWritingModeAndOverflowScroll | geometry | formalized | `TestsMapping.ContainerFlippedWritingModeAndOverflowScroll_vectors` |
| visual_rect_mapping_test.cc:842 | VisualRectMappingTest.ContainerOverflowHidden | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| visual_rect_mapping_test.cc:873 | VisualRectMappingTest.ContainerFlippedWritingModeAndOverflowHidden | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| visual_rect_mapping_test.cc:912 | VisualRectMappingTest.ContainerAndTargetDifferentFlippedWritingMode | geometry | formalized | `TestsMapping.ContainerAndTargetDifferentFlippedWritingMode_vectors` |
| visual_rect_mapping_test.cc:955 | VisualRectMappingTest.DifferentPaintInvalidaitionContainerForAbsolutePosition | behaviour | blocked | engine service, parked |
| visual_rect_mapping_test.cc:996 | VisualRectMappingTest.ContainerOfAbsoluteAbovePaintInvalidationContainer | behaviour | blocked | engine service, parked |
| visual_rect_mapping_test.cc:1031 | VisualRectMappingTest.CSSClip | geometry | formalized | `TestsMapping.CSSClip_vectors` |
| visual_rect_mapping_test.cc:1046 | VisualRectMappingTest.ContainPaint | geometry | formalized | `TestsMapping.ContainPaint_vectors` |
| visual_rect_mapping_test.cc:1061 | VisualRectMappingTest.FloatUnderInline | geometry | formalized | `TestsMapping.FloatUnderInline_vectors` |
| visual_rect_mapping_test.cc:1089 | VisualRectMappingTest.FloatUnderInlineVerticalRL | geometry | formalized | `TestsMapping.FloatUnderInlineVerticalRL_vectors` |
| visual_rect_mapping_test.cc:1120 | VisualRectMappingTest.InlineBlock | geometry | formalized | `TestsMapping.InlineBlock_vectors` |
| visual_rect_mapping_test.cc:1145 | VisualRectMappingTest.InlineBlockVerticalRL | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| visual_rect_mapping_test.cc:1174 | VisualRectMappingTest.AbsoluteUnderRelativeInline | geometry | formalized | `TestsMapping.AbsoluteUnderRelativeInline_vectors` |
| visual_rect_mapping_test.cc:1199 | VisualRectMappingTest.AbsoluteUnderRelativeInlineVerticalRL | geometry | formalized | `TestsMapping.AbsoluteUnderRelativeInlineVerticalRL_vectors` |
| visual_rect_mapping_test.cc:1228 | VisualRectMappingTest.ShouldAccountForPreserve3d | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1258 | VisualRectMappingTest.ShouldAccountForPreserve3dNested | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1287 | VisualRectMappingTest.ShouldAccountForPerspective | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1320 | VisualRectMappingTest.ShouldAccountForPerspectiveNested | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1352 | VisualRectMappingTest.PerspectivePlusScroll | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1392 | VisualRectMappingTest.FixedContentsInIframe | geometry | formalized | `TestsMapping.FixedContentsInIframe_vectors` |
| visual_rect_mapping_test.cc:1431 | VisualRectMappingTest.FixedContentsWithScrollOffset | geometry | formalized | `TestsMapping.FixedContentsWithScrollOffset_vectors` |
| visual_rect_mapping_test.cc:1464 | VisualRectMappingTest.FixedContentsUnderViewWithScrollOffset | geometry | formalized | `TestsMapping.FixedContentsUnderViewWithScrollOffset_vectors` |
| visual_rect_mapping_test.cc:1492 | VisualRectMappingTest.InclusiveIntersect | geometry | blocked | edge-inclusive intersection and the boolean result of MapToVisualRectInAncestorSpace are not modelled |
| visual_rect_mapping_test.cc:1522 | VisualRectMappingTest.Perspective | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1542 | VisualRectMappingTest.PerspectiveWithAnonymousTable | geometry | blocked | 3D transforms (rotateX/rotateY, perspective, preserve-3d flattening) need a 4x4 matrix model with irrational entries; not modelled |
| visual_rect_mapping_test.cc:1561 | VisualRectMappingTest.MapToVisualRectFastPathMapsToViewport | geometry | formalized | `TestsMapping.MapToVisualRectFastPathMapsToViewport_vectors` |
| visual_rect_mapping_test.cc:1592 | VisualRectMappingTest.AnchorPositionScroll | geometry | blocked | anchor positioning with scroll snapshots belongs to the anchor lane (CSS Anchor Positioning 1) |
| visual_rect_mapping_test.cc:1656 | VisualRectMappingTest.IgnoreFilters | geometry | blocked | filter blur visual extent (CSS Filter Effects 1) is not modelled |
| visual_rect_mapping_test.cc:1688 | VisualRectMappingTest.NestedTransformsFastVsSlowPath | geometry | blocked | rotation by 45 degrees needs irrational (square root of 2) matrix entries; MappingTransform.Aff is integer-exact |
| visual_rect_mapping_test.cc:1741 | VisualRectMappingTest.SVGTransformsFastVsSlowPath | geometry | blocked | preserveAspectRatio="none" and the enclosing rect of a fractional result are not modelled |
| visual_rect_mapping_test.cc:1787 | VisualRectMappingTest.NestedTransformsGeometryMapperFlag | geometry | blocked | rotation by 45 degrees needs irrational (square root of 2) matrix entries; MappingTransform.Aff is integer-exact |
| visual_rect_mapping_test.cc:1838 | VisualRectMappingTest.NestedTransformsComposeAngles | geometry | blocked | rotation by an angle that is not a multiple of 90 degrees needs trigonometric values; not modelled |
| visual_rect_mapping_test.cc:1891 | VisualRectMappingTest.NestedTransformsFractionalPositionSnapsOnce | geometry | blocked | rotation by an angle that is not a multiple of 90 degrees needs trigonometric values; not modelled |
| visual_rect_mapping_test.cc:1941 | VisualRectMappingTest.FractionalSnapping | geometry | blocked | fractional LayoutUnit positions and enclosing-rect snapping are not modelled (Mapping coordinates are whole pixels) |
| visual_rect_mapping_test.cc:2001 | VisualRectMappingTest.ViewportMappingIsConsistentWithAndWithoutGeometryMapperUnderPinchZoom | geometry | blocked | visual viewport pinch-zoom transform is not modelled |
| visual_rect_mapping_test.cc:2054 | VisualRectMappingTest.ViewportMappingAppliesVisualViewportTransformButClipsToLayoutViewport | geometry | blocked | visual viewport pinch-zoom transform is not modelled |
| visual_rect_mapping_test.cc:2143 | VisualRectMappingTest.ElementCanvasTransformVisualRectMapping | geometry | formalized | `TestsMapping.ElementCanvasTransformVisualRectMapping_vectors` |
| visual_rect_mapping_test.cc:2172 | VisualRectMappingTest.NestedElementCanvasTransformVisualRectMapping | geometry | formalized | `TestsMapping.NestedElementCanvasTransformVisualRectMapping_vectors` |
| visual_rect_mapping_test.cc:2205 | VisualRectMappingTest.NestedElementCanvasTransformWithOffsetVisualRectMapping | geometry | formalized | `TestsMapping.NestedElementCanvasTransformWithOffsetVisualRectMapping_vectors` |
| visual_rect_mapping_test.cc:2239 | VisualRectMappingTest.NestedElementCanvasTransformChildWithoutCanvasTransformVisualRectMapping | geometry | formalized | `TestsMapping.NestedElementCanvasTransformChildWithoutCanvasTransformVisualRectMapping_vectors` |
| visual_rect_mapping_test.cc:2273 | VisualRectMappingTest.NestedElementCanvasTransformNonDrawableChildVisualRectMapping | geometry | formalized | `TestsMapping.NestedElementCanvasTransformNonDrawableChildVisualRectMapping_vectors` |
| visual_rect_mapping_test.cc:2306 | VisualRectMappingTest.NestedElementCanvasTransformInlineVisualRectMapping | geometry | formalized | `TestsMapping.NestedElementCanvasTransformInlineVisualRectMapping_vectors` |
