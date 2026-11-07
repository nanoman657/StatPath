/-
  ColumnWidth.lean: used multicol column count and width, written from length_utils_test.cc
  (`TestColumnWidthAndCount`). Owned by the block lane (Column*). `0` means `auto` for the
  computed count and width, as in the test's wrappers.
-/
namespace ChromiumLayout
namespace ColumnWidth

/-- Used column count (`ResolveUsedColumnCount`): with only `column-width`, as many as fit; with
    only `column-count`, that many; with both, at most `count` and at most what fits; at least 1. -/
def usedCount (count width gap avail : Nat) : Nat :=
  if width = 0 then Nat.max count 1
  else
    let fit := Nat.max ((avail + gap) / (width + gap)) 1
    if count = 0 then fit else Nat.min count fit

/-- Used column width (`ResolveUsedColumnInlineSize`): the space left after the gaps, shared
    equally; never negative. -/
def usedWidth (count width gap avail : Nat) : Nat :=
  (avail - (usedCount count width gap avail - 1) * gap) / usedCount count width gap avail

/-- The used columns plus gaps fit the available inline size whenever the gaps themselves fit
    (generalises the `TestColumnWidthAndCount` vectors). -/
theorem columns_fit (count width gap avail : Nat) (h : (usedCount count width gap avail - 1) * gap ≤ avail) :
    usedCount count width gap avail * usedWidth count width gap avail
      + (usedCount count width gap avail - 1) * gap ≤ avail := by
  dsimp [usedWidth]
  have := Nat.mul_div_le (avail - (usedCount count width gap avail - 1) * gap)
    (usedCount count width gap avail)
  omega

end ColumnWidth
end ChromiumLayout
