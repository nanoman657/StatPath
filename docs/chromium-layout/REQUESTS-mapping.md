# Requests from the anchor session to the mapping lane

## 1. Held-out row opened before the list was checked: `map_coordinates_test.cc:797`

- `tools/heldout-inline.txt` lists `map_coordinates_test.cc:797` (MapCoordinatesTest.FixedPosInScrolledIFrameWithTransform)
  as held out. The same file also lists 385, 1217, 1853 and 1889.
- The anchor session read the pinned test body and its expectation for that row before the list was checked.
  The row was not transcribed, no vector, model definition or test code was written for it, and no commit
  contains any of that work.
- The row stays `blocked` in `tests/MANIFEST-mapping.md`. The mapping lane should record this disclosure
  beside the row and keep it out of the mapping lane's own work, as with the other held-out rows.

Nothing else is requested of the mapping lane.
