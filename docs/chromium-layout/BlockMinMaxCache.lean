/-
  BlockMinMaxCache.lean: N-way LRU cache for min/max sizes against initial block-size,
  written from min_max_sizes_cache_test.cc (`MinMaxSizesCacheTest.Eviction`).
  Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockMinMaxCache

/-- Maximum cache entries (MinMaxSizesCache::kMaxCacheEntries = 8). -/
def maxEntries : Nat := 8

/-- Look up a key: if present, moves it to the most-recently used position (tail). -/
def find (c : List Nat) (k : Nat) : Option (List Nat) :=
  if c.contains k then
    some (c.erase k ++ [k])
  else
    none

/-- Add a key: if already present, moves to most-recently used; if not and at capacity,
    evicts the least recently used (head); then appends key to tail. -/
def add (c : List Nat) (k : Nat) : List Nat :=
  let c' := c.erase k
  let trimmed := if c'.length ≥ maxEntries then c'.tail else c'
  trimmed ++ [k]

/-- The cache state after the test sequence in `MinMaxSizesCacheTest.Eviction`. -/
def cacheAfterEviction : List Nat :=
  let c0 := [0, 1, 2, 3, 4, 5, 6, 7]
  let c1 := match find c0 0 with | some c => c | none => []
  add c1 8

/-- Most-recently used item moved to the back is preserved when adding an entry at capacity,
    while the least-recently used (unreferenced) entry 1 is evicted. -/
theorem lru_eviction :
    (find cacheAfterEviction 0).isSome = true ∧ (find cacheAfterEviction 1).isSome = false := by
  decide

end BlockMinMaxCache
end ChromiumLayout
