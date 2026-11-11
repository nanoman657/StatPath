# Requests from the Block lane to other lanes

## 1. Cross-lane edits in the Block commit (flagged)

- `Anchor.lean` (anchor lane's file) gained `AN` fields `positioned`, `oof`, `inL`, `inT`, `szW`, `szH`, the
  definitions `oofFrag`, `placeTree` and `hoistOof`, and two laws (`hoistOof_positioned`, `hoistOof_leaf`).
  Block rows 149 and 165 of `physical_fragment_test.cc` need them: an out-of-flow box is placed by its insets
  against its containing block (CSS 2.1 §10.3.7, §10.6.4) and is a child of that block's fragment (§9.3.1).
  The anchor lane should confirm or take ownership of them.
- `tests/TestsBlock_PhysicalFragment.lean` now imports `Anchor`.
- The manifest rows in `tests/MANIFEST-Block.md` for 5723, 5762, 5938, 6416 (column layout) and 149, 165
  (physical fragment) were changed by the session that wrote the model, not by the Block lane owner. The owner
  should confirm or drop them.

## 2. Gate result and reuse

Measured with `CHROMIUM_LAYOUT` set to the pinned copy, `--gate HEAD`, `MANIFEST-Block`, held-out list `block`:
total 186161 -> 186087 (-74), model+inputs +1115, exceptions -1189, explained rows 187 -> 193. GATE PASS.

Every new definition has at least two rows that use it:

| Definition | Spec | Rows |
|---|---|---|
| `ColumnLayout.childStartsB` (with `layoutMulticolAvoid`, `nextColStart`) | CSS Fragmentation 3 §3.1, §3.3 | column_layout_algorithm_test.cc 5723, 5762, 5938, 6416 |
| `Anchor.oofFrag`, `Anchor.placeTree` | CSS 2.1 §10.3.7, §10.6.4 | physical_fragment_test.cc 149, 165 |
| `Anchor.hoistOof` | CSS 2.1 §9.3.1 | physical_fragment_test.cc 149, 165 |

`childStartsB` replaces the unused `layoutMulticolAvoid` body (no test used it), and the law
`childStartsB_eq_childStarts` shows it equals `childStarts` when no child has a break flag.

## 3. Not formalized, and why

- 5845: needs a search back through a chain of break-before-avoid children; `childStartsB` looks one child ahead.
- 5892, 5984, 6037, 6092: need nested containers whose own break-inside avoid is ignored; a flat model would hide that.
- 6375: needs floats and BFC offset resolution.
- html height 800x8 in rows 149 and 165 is not modelled by `layoutRoot` (it gives 0) and is not checked.
