import BlockMinMaxCache

namespace TestsBlock

open ChromiumLayout.BlockMinMaxCache

-- min_max_sizes_cache_test.cc:14: Eviction
theorem Eviction_vectors :
    (find cacheAfterEviction 0).isSome = true ∧
    (find cacheAfterEviction 1).isSome = false :=
  lru_eviction

end TestsBlock
