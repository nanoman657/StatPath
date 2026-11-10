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

## 2. Nothing else is requested

Remaining anchor rows and their reasons are in `tests/MANIFEST-anchor.md`. Held-out rows (310, 327,
anchor_scope 33) are left to the examiner lane and were not opened for this change.
