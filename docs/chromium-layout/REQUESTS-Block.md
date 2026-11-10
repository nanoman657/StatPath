# Requests from the Block lane to other lanes

## 1. Cross-lane edit flagged (uncommitted)

The Block-lane rows 5723 (`AvoidBreakBetween_vectors`) and 5762 (`AvoidAndForceBreakBetween_vectors`) are formalized
in the working tree. Their model support is `ColumnLayout.childStartsB` with `ColChild` fields `breakBeforeAvoid`
and `breakAfterColumn`, plus law `childStartsB_eq_childStarts`. Their manifest rows in `tests/MANIFEST-Block.md` were
changed by the anchor-side session, against COORDINATION (which forbids editing another lane's manifest). They are
flagged here and not committed. The Block lane owner should confirm or drop them.

## 2. Coupling blocks the Block commit

On a joint tree, Block's model+inputs growth (+1339, shared with anchor and mapping) exceeds its own exception drop
(-426). Block's total rises to 187074 (from 186161), so the gate is PASS WITH REVIEW. The review rule needs a
spec-cited definition that later Block tests reuse. Full numbers and the decision request are in
`REQUESTS-anchor.md` section 3.
