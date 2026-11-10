# Requests from the anchor lane to other lanes

## 1. Gate attribution on the shared branch (for the coordinator; `tools/mml_score.py`)

Status: open. The anchor lane's row 284 change (`Anchor.lean`, `tests/TestsAnchor_AnchorEvaluatorImpl.lean`,
`tests/MANIFEST-anchor.md`) is in the working tree and is **not committed**.

What was measured on the combined branch `claude/adoring-tesla-vr51jc`, with `CHROMIUM_LAYOUT` set to the pin:

- `--manifest MANIFEST-anchor --gate HEAD`: `PASS WITH REVIEW`. Explained rows 5 -> 6, held-out 0,
  formalized without theorem 0. Total 39971 -> 40283 (model+inputs +425, exceptions -113). Model tokens added
  per exception token removed: 3.76.
- `--manifest MANIFEST-Block --gate HEAD`: `FAIL: model grew but explains no new rows`. Block explained rows
  187 -> 187, but the model total grew by the same +425, which comes only from the anchor files.
- `--manifest MANIFEST-mapping --gate HEAD`: `FAIL`, the same way (92 -> 92, +425).

The scorer counts every model file in the tree against every lane's manifest, so one lane's definitions fail
the other lanes' gates whenever they land on a shared tree. The lane rule in COORDINATION.md ("a definition
arrives with its tests") assumes one lane per tree.

Requested decision (either):

- (a) score model growth per lane (for example, only files the manifest's tests import, or the lane's own
  prefix), so a lane's definitions are judged by its own rows; or
- (b) the anchor lane commits on its own branch, `chromium-layout-anchor`, and this branch is not used for
  anchor commits.

Separately, the anchor change is a PASS WITH REVIEW under the rule "only for a spec-cited definition that later
tests reuse". Its definitions are `oofFrag` and `placeTree` (CSS 2.1 §10.6.4, placement of an out-of-flow
box by its insets) and `hideNames` and `anchorMapCB` (CSS Anchor Positioning 1, out-of-flow names reach their
containing block only). No later test reuses them yet. Until one does, the anchor lane will not commit this
change against the review rule.

## 2. Combined gate results (all three lanes, one tree)

Measured with a temporary commit on `HEAD` (`ef6158a` plus the doc commit `dfc4ae6`), for the working tree
holding anchor row 284, Block rows 5723 and 5762 (`ColumnLayout.childStartsB` with `break-after: column`), and
mapping row 1931 (test vector only, no model change):

- `MANIFEST-anchor`: PASS WITH REVIEW. Explained 5 -> 6. Total 39971 -> 40984 (+1013).
- `MANIFEST-Block`: PASS WITH REVIEW. Explained 187 -> 189. Total 186061 -> 186761 (+700).
- `MANIFEST-mapping`: PASS WITH REVIEW. Explained 92 -> 93. Total 41720 -> 42619 (+899).

The mapping change on its own is a clean PASS (total 41720 -> 41593), but the anchor and Block gates
then report `FAIL: model grew but explains no new rows`, because a new test vector counts as input growth
for every lane. So no lane can land a change unless the other two lanes also explain a row in that commit.

Blocking condition for the anchor part: the review rule allows PASS WITH REVIEW only for a spec-cited
definition that later tests reuse. `oofFrag`, `placeTree`, `hideNames` and `anchorMapCB` have no reuse in
the anchor manifest. The only candidates would be rows with an out-of-flow box placed by its insets:
`visual_rect_mapping_test.cc:1592` (AnchorPositionScroll, needs clipping, scrolling and `anchor()`
resolution in the mapping model), or a new fragmented-container row (`anchor_evaluator_impl_test.cc:375`
has no out-of-flow box, so it does not reuse these definitions).

Until that reuse exists, the anchor lane will not commit row 284 under the review rule. Because of the
scorer coupling above, the Block and mapping changes wait on the same decision. The combined patch is
saved at `/tmp/claude-0/-home-user-StatPath/633c6dad-e0dc-5be8-9447-c5aaccd0d583/scratchpad/combined-anchor284-block5723-5762-mapping1931.patch`.

Held-out rows (310, 327, anchor_scope 33) are left to the examiner lane and were not opened for this change.
