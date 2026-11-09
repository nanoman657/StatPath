# Anchor lane test manifest

Branch `claude/adoring-tesla-vr51jc`, pin `36c121be58126ddbb0686965897b8c8ff9b246fb`,
folder `third_party/blink/renderer/core/layout/`. The tests are the specification: rows record what
each test says anchor maps, anchor scroll data and scroll ranges must do.

Rule (a)-(c) for `formalized`: (a) the test's HTML/CSS is written as a value of a model input type
(`BlockFlow.BF` box tree plus the `Anchor.AN` name/transform/scroller tree); (b) a general model
function that mentions no test computes the anchor map or scroll value; (c) the theorem compares it
with the test's `EXPECT_*` values as literals. Classes: `geometry`, `behaviour`, `internal`. Status:
`formalized`, `partly formalized`, `blocked` (reason given), `internal`.

Model module: `Anchor.lean`. Vectors: `tests/TestsAnchor_<File>.lean`. Chromium/spec
disagreements: `SPEC-DIFF-anchor.md`.

Disclosure: `anchor_scope_test.cc` line 33 (HashInsertDuplicate) was opened before the held-out list
had been checked; it is on that list, it is not formalized, and nothing was derived from it.
Rows marked held-out are left to the examiner lane.

| file:line | test | class | status | evidence / reason |
|---|---|---|---|---|
| anchor_evaluator_impl_test.cc:71 | AnchorEvaluatorImplTest.AnchorNameAdd | geometry | formalized | `TestsAnchor.AnchorNameAdd_before`, `AnchorNameAdd_after` |
| anchor_evaluator_impl_test.cc:104 | AnchorEvaluatorImplTest.AnchorNameChange | geometry | formalized | `TestsAnchor.AnchorNameChange_before`, `AnchorNameChange_after` |
| anchor_evaluator_impl_test.cc:141 | AnchorEvaluatorImplTest.AnchorNameRemove | geometry | formalized | `TestsAnchor.AnchorNameRemove_before`, `AnchorNameRemove_after` |
| anchor_evaluator_impl_test.cc:175 | AnchorEvaluatorImplTest.BlockFlow | geometry | formalized | `TestsAnchor.BlockFlow_before`, `BlockFlow_after` |
| anchor_evaluator_impl_test.cc:221 | AnchorEvaluatorImplTest.Inline | geometry | blocked | needs inline layout with Ahem text, culled and non-culled spans, `img` and inline-block anchors; the anchor model only reuses block layout |
| anchor_evaluator_impl_test.cc:284 | AnchorEvaluatorImplTest.OutOfFlow | geometry | blocked | `BlockFlow.BF` has no out-of-flow boxes; propagation of anchors to the out-of-flow containing block is not modelled |
| anchor_evaluator_impl_test.cc:310 | AnchorEvaluatorImplTest.Relative | geometry | blocked | held-out row, left to the examiner lane |
| anchor_evaluator_impl_test.cc:330 | AnchorEvaluatorImplTest.Transform | geometry | formalized | `TestsAnchor.Transform_translate` |
| anchor_evaluator_impl_test.cc:351 | AnchorEvaluatorImplTest.Scroll | geometry | partly formalized | `TestsAnchor.Scroll_inner`: the map is independent of scrolling because scroll offset is not an input to `anchorMap`; the scroll step itself is not simulated |
| anchor_evaluator_impl_test.cc:375 | AnchorEvaluatorImplTest.FragmentedContainingBlock | geometry | blocked | per-fragment anchor maps across column fragments are not modelled |
| anchor_evaluator_impl_test.cc:437 | AnchorEvaluatorImplTest.FragmentHasRunningAnchorTransformAnimation | behaviour | blocked | compositor animation state is not modelled |
| anchor_evaluator_impl_test.cc:446 | AnchorEvaluatorImplTest.FrameViewHasRunningAnchorTransformAnimation | behaviour | blocked | compositor animation state is not modelled |
| anchor_position_scroll_data_test.cc:45 | AnchorPositionScrollDataTest.HasDataAndScrollAdjustment | behaviour | partly formalized | `TestsAnchor.HasData_anchored`, `HasData_noAnchorUsage`, `HasData_noAnchor`, `HasData_notAnchorPositioned`; the inline span anchor is modelled as a block box |
| anchor_position_scroll_data_test.cc:94 | AnchorPositionScrollDataTest.Detach | behaviour | partly formalized | `TestsAnchor.Detach_before`, `Detach_removed`, `Detach_displayNone`, `Detach_inFlow`; that no new frame is scheduled is not modelled |
| anchor_position_scroll_data_test.cc:142 | AnchorPositionScrollDataTest.ScrollerSizeChange | geometry | partly formalized | `TestsAnchor.ScrollerSizeChange_values`; frame scheduling and the applied offset at the last scroll end are fed in as inputs |
| anchor_position_scroll_data_test.cc:205 | AnchorPositionScrollDataTest.ScrollContentSizeChange | geometry | partly formalized | `TestsAnchor.ScrollContentSizeChange_values`; same limitation |
| anchor_position_scroll_data_test.cc:266 | AnchorPositionScrollDataTest.RelayoutOnScrollEnd | geometry | partly formalized | `TestsAnchor.RelayoutOnScrollEnd_values`; same limitation |
| anchor_position_scroll_data_test.cc:327 | AnchorPositionScrollDataTest.RelayoutOnScrollEndSimpleTranslation | geometry | blocked | held-out row, left to the examiner lane |
| anchor_position_scroll_data_test.cc:392 | AnchorPositionScrollDataTest.ScrollableOverflowDuringAndAfterScroll | geometry | partly formalized | `TestsAnchor.ScrollableOverflow_values`; same limitation |
| anchor_scope_test.cc:33 | AnchorScopedNameTest.HashInsertDuplicate | internal | blocked | held-out row, left to the examiner lane (see disclosure above) |
| anchor_scope_test.cc:44 | AnchorScopedNameTest.HashDifferentNames | internal | internal | identity of garbage-collected hash-set entries (`AnchorScopedName`); not layout |
| anchor_scope_test.cc:56 | AnchorScopedNameTest.HashEqualNames | internal | internal | same |
| anchor_scope_test.cc:72 | AnchorScopedNameTest.LookupEmpty | internal | internal | same |
| anchor_scope_test.cc:80 | AnchorScopedNameTest.LookupDeleted | internal | internal | same |
| anchor_scope_test.cc:93 | AnchorScopedNameTest.ElementEquality | internal | internal | same |
| anchor_scope_test.cc:115 | AnchorScopedNameTest.TreeScopeEquality | internal | internal | same |
