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
| map_coordinates_test.cc:171 | MapCoordinatesTest.OverflowClip | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:210 | MapCoordinatesTest.TextInRelPosInline | geometry | formalized | `TestsMapping.TextInRelPosInline_vectors` |
| map_coordinates_test.cc:225 | MapCoordinatesTest.RelposInline | geometry | formalized | `TestsMapping.RelposInline_vectors` |
| map_coordinates_test.cc:240 | MapCoordinatesTest.RelposInlineInRelposInline | geometry | formalized | `TestsMapping.RelposInlineInRelposInline_vectors` |
| map_coordinates_test.cc:274 | MapCoordinatesTest.RelPosBlock | geometry | formalized | `TestsMapping.RelPosBlock_vectors` |
| map_coordinates_test.cc:311 | MapCoordinatesTest.AbsPos | geometry | formalized | `TestsMapping.AbsPos_vectors` |
| map_coordinates_test.cc:348 | MapCoordinatesTest.AbsPosAuto | geometry | formalized | `TestsMapping.AbsPosAuto_vectors` |
| map_coordinates_test.cc:385 | MapCoordinatesTest.FixedPos | geometry | blocked | held-out row (tools/heldout-inline.txt); left to the examiner lane |
| map_coordinates_test.cc:444 | MapCoordinatesTest.FixedPosAuto | geometry | formalized | `TestsMapping.FixedPosAuto_vectors` |
| map_coordinates_test.cc:504 | MapCoordinatesTest.FixedPosInFixedPos | geometry | formalized | `TestsMapping.FixedPosInFixedPos_vectors` |
| map_coordinates_test.cc:573 | MapCoordinatesTest.FixedPosInFixedPosScrollView | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:610 | MapCoordinatesTest.FixedPosInAbsolutePosScrollView | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:647 | MapCoordinatesTest.FixedPosInTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:689 | MapCoordinatesTest.FixedPosInContainPaint | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:732 | MapCoordinatesTest.FixedPosInIFrameWhenMainFrameScrolled | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:763 | MapCoordinatesTest.IFrameTransformed | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:797 | MapCoordinatesTest.FixedPosInScrolledIFrameWithTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:828 | MapCoordinatesTest.MulticolWithText | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:849 | MapCoordinatesTest.MulticolWithInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:868 | MapCoordinatesTest.MulticolWithBlock | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:889 | MapCoordinatesTest.MulticolWithBlockAbove | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:907 | MapCoordinatesTest.NestedMulticolWithBlock | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:945 | MapCoordinatesTest.MulticolWithAbsPosInRelPos | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:981 | MapCoordinatesTest.MulticolWithAbsPosInInlineRelPos | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1019 | MapCoordinatesTest.MulticolWithAbsPosNotContained | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1060 | MapCoordinatesTest.MulticolRtl | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1079 | MapCoordinatesTest.MulticolWithLargeBorder | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1099 | MapCoordinatesTest.FlippedBlocksWritingModeWithText | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1131 | MapCoordinatesTest.FlippedBlocksWritingModeWithInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1183 | MapCoordinatesTest.FlippedBlocksWritingModeWithBlock | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1217 | MapCoordinatesTest.Table | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1318 | MapCoordinatesTest.Transforms | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1378 | MapCoordinatesTest.SVGShape | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1397 | MapCoordinatesTest.SVGShapeScale | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1417 | MapCoordinatesTest.SVGShapeWithViewBoxWithoutScale | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1436 | MapCoordinatesTest.SVGShapeWithViewBoxWithScale | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1455 | MapCoordinatesTest.SVGShapeWithViewBoxWithNonZeroOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1475 | MapCoordinatesTest.SVGShapeWithViewBoxWithNonZeroOffsetAndScale | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1495 | MapCoordinatesTest.SVGForeignObject | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1532 | MapCoordinatesTest.LocalToAbsoluteTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1555 | MapCoordinatesTest.LocalToAncestorTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1600 | MapCoordinatesTest.LocalToAbsoluteTransformFlattens | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1645 | MapCoordinatesTest.Transform3DWithOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1668 | MapCoordinatesTest.Transform3DWithOffset2 | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1693 | MapCoordinatesTest.IgnoreScrollOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1732 | MapCoordinatesTest.IgnoreScrollOffsetForInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1770 | MapCoordinatesTest.IgnoreScrollOffsetWithWritingModes | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1818 | MapCoordinatesTest.FixedPositionWithScrollOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1853 | MapCoordinatesTest.FixedPositionWithScrollOffsetVerticalRL | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1889 | MapCoordinatesTest.FixedPositionUnderTransformWithScrollOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1931 | MapCoordinatesTest.IgnoreScrollOffsetWithWritingModesAndNonOverlayScrollbar | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1975 | MapCoordinatesTest.ElementCanvasTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:1996 | MapCoordinatesTest.NestedElementCanvasTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:2021 | MapCoordinatesTest.NestedElementCanvasTransformWithOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:2046 | MapCoordinatesTest.NestedElementCanvasTransformChildWithoutCanvasTransform | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:2069 | MapCoordinatesTest.NestedElementCanvasTransformNonDrawableChild | geometry | blocked | not yet modelled (mapping lane, pending) |
| map_coordinates_test.cc:2093 | MapCoordinatesTest.NestedElementCanvasTransformInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:126 | VisualRectMappingTest.LayoutText | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:165 | VisualRectMappingTest.LayoutTextContainerFlippedWritingMode | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:202 | VisualRectMappingTest.LayoutInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:240 | VisualRectMappingTest.LayoutInlineContainerFlippedWritingMode | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:281 | VisualRectMappingTest.SkipAncestorAndViewportClipFlag | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:338 | VisualRectMappingTest.SkipAncestorAndViewportClipFlagViewportSpace | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:419 | VisualRectMappingTest.SkipAncestorAndViewportClipsInSubframe | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:488 | VisualRectMappingTest.RegressionTest_SkipAncestorClipExpansion | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:542 | VisualRectMappingTest.LayoutView | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:588 | VisualRectMappingTest.LayoutViewSubpixelRounding | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:619 | VisualRectMappingTest.LayoutViewDisplayNone | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:658 | VisualRectMappingTest.SelfFlippedWritingMode | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:681 | VisualRectMappingTest.ContainerFlippedWritingMode | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:722 | VisualRectMappingTest.ContainerOverflowScroll | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:778 | VisualRectMappingTest.ContainerFlippedWritingModeAndOverflowScroll | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:842 | VisualRectMappingTest.ContainerOverflowHidden | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:873 | VisualRectMappingTest.ContainerFlippedWritingModeAndOverflowHidden | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:912 | VisualRectMappingTest.ContainerAndTargetDifferentFlippedWritingMode | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:955 | VisualRectMappingTest.DifferentPaintInvalidaitionContainerForAbsolutePosition | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:996 | VisualRectMappingTest.ContainerOfAbsoluteAbovePaintInvalidationContainer | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1031 | VisualRectMappingTest.CSSClip | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1046 | VisualRectMappingTest.ContainPaint | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1061 | VisualRectMappingTest.FloatUnderInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1089 | VisualRectMappingTest.FloatUnderInlineVerticalRL | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1120 | VisualRectMappingTest.InlineBlock | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1145 | VisualRectMappingTest.InlineBlockVerticalRL | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1174 | VisualRectMappingTest.AbsoluteUnderRelativeInline | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1199 | VisualRectMappingTest.AbsoluteUnderRelativeInlineVerticalRL | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1228 | VisualRectMappingTest.ShouldAccountForPreserve3d | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1258 | VisualRectMappingTest.ShouldAccountForPreserve3dNested | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1287 | VisualRectMappingTest.ShouldAccountForPerspective | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1320 | VisualRectMappingTest.ShouldAccountForPerspectiveNested | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1352 | VisualRectMappingTest.PerspectivePlusScroll | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1392 | VisualRectMappingTest.FixedContentsInIframe | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1431 | VisualRectMappingTest.FixedContentsWithScrollOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1464 | VisualRectMappingTest.FixedContentsUnderViewWithScrollOffset | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1492 | VisualRectMappingTest.InclusiveIntersect | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1522 | VisualRectMappingTest.Perspective | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1542 | VisualRectMappingTest.PerspectiveWithAnonymousTable | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1561 | VisualRectMappingTest.MapToVisualRectFastPathMapsToViewport | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1592 | VisualRectMappingTest.AnchorPositionScroll | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1656 | VisualRectMappingTest.IgnoreFilters | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1688 | VisualRectMappingTest.NestedTransformsFastVsSlowPath | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1741 | VisualRectMappingTest.SVGTransformsFastVsSlowPath | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1787 | VisualRectMappingTest.NestedTransformsGeometryMapperFlag | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1838 | VisualRectMappingTest.NestedTransformsComposeAngles | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1891 | VisualRectMappingTest.NestedTransformsFractionalPositionSnapsOnce | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:1941 | VisualRectMappingTest.FractionalSnapping | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2001 | VisualRectMappingTest.ViewportMappingIsConsistentWithAndWithoutGeometryMapperUnderPinchZoom | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2054 | VisualRectMappingTest.ViewportMappingAppliesVisualViewportTransformButClipsToLayoutViewport | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2143 | VisualRectMappingTest.ElementCanvasTransformVisualRectMapping | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2172 | VisualRectMappingTest.NestedElementCanvasTransformVisualRectMapping | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2205 | VisualRectMappingTest.NestedElementCanvasTransformWithOffsetVisualRectMapping | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2239 | VisualRectMappingTest.NestedElementCanvasTransformChildWithoutCanvasTransformVisualRectMapping | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2273 | VisualRectMappingTest.NestedElementCanvasTransformNonDrawableChildVisualRectMapping | geometry | blocked | not yet modelled (mapping lane, pending) |
| visual_rect_mapping_test.cc:2306 | VisualRectMappingTest.NestedElementCanvasTransformInlineVisualRectMapping | geometry | blocked | not yet modelled (mapping lane, pending) |
