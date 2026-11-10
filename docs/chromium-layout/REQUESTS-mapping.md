# Requests from the anchor session to the mapping lane

## 1. Held-out row opened before the list was checked: `map_coordinates_test.cc:797`

- `tools/heldout-inline.txt` lists `map_coordinates_test.cc:797` (MapCoordinatesTest.FixedPosInScrolledIFrameWithTransform)
  as held out. The same file also lists 385, 1217, 1853 and 1889.
- The anchor session read the pinned test body and its expectation for that row before the list was checked.
  The row was not transcribed, no vector, model definition or test code was written for it, and no commit
  contains any of that work.
- The row stays `blocked` in `tests/MANIFEST-mapping.md`. The mapping lane should record this disclosure
  beside the row and keep it out of the mapping lane's own work, as with the other held-out rows.

## 2. The 3D transform rows have no literal expected value

Rows: `visual_rect_mapping_test.cc:1228` (ShouldAccountForPreserve3d), `:1258` (ShouldAccountForPreserve3dNested),
`:1287` (ShouldAccountForPerspective), `:1320` (ShouldAccountForPerspectiveNested), `:1352` (PerspectivePlusScroll).

- Each expected rectangle is computed inside the test with `gfx::Transform` float math (`MapRect`,
  `Flatten`, `GetTransformFromContainer`, `EnclosingRect`). None is written as a literal, so a formal row
  would have to compare the model against a value the test derives in floating point, which is not an
  independent expectation.
- `:1352` also uses `rotatex(45eg)`, a malformed value, plus a scroll offset of 5 and a clip intersection
  with `ClippingRect`.
- Status stays `blocked` in `tests/MANIFEST-mapping.md`. Formalizing these rows needs a `rotateX` model and an
  agreed rule for irrational trigonometric values. That is a decision for the mapping lane, not a change to
  make here.

Nothing else is requested of the mapping lane.
