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

/-- Intrinsic min/max sizes for a multi-column container.
    CSS Intrinsic & Retargeted Sizing 3 / 4 (CSS Sizing 3 §4, CSS Sizing 4 §4.1; CSS Multicol 1 §4).
    If column-width is non-auto, column-count is ignored for min inline size and clamped down to
    the specified column-width. With column-count auto, max-content is column-width. -/
def multicolMinMax (contentMin contentMax : Nat) (colCount : Option Nat)
    (colWidth : Option Nat) (gap : Nat) : Nat × Nat :=
  let minSz := match colWidth with
    | some cw => min contentMin cw
    | none => match colCount with
      | some n => n * contentMin + if n > 0 then (n - 1) * gap else 0
      | none => contentMin
  let maxSz := match colCount, colWidth with
    | some n, some cw => n * (max contentMax cw) + if n > 0 then (n - 1) * gap else 0
    | some n, none => n * contentMax + if n > 0 then (n - 1) * gap else 0
    | none, some cw => cw
    | none, none => contentMax
  (minSz, maxSz)

/-- Law: Specified column-width clamps the container's min-content inline size.
    CSS Sizing 3 §4. -/
theorem col_width_clamps_min (cMin cMax cw gap : Nat) (count : Option Nat) :
    (multicolMinMax cMin cMax count (some cw) gap).1 ≤ cw := by
  dsimp [multicolMinMax]
  omega

/-- Law: Auto column-width scales min-content inline size with column count and gaps.
    CSS Sizing 3 §4. -/
theorem auto_width_scales_min (cMin cMax n gap : Nat) :
    (multicolMinMax cMin cMax (some n) none gap).1 = n * cMin + if n > 0 then (n - 1) * gap else 0 :=
  rfl

/-- Law: Auto column-count with specified column-width sets max-content inline size to column-width.
    CSS Sizing 4 §4.1. -/
theorem auto_count_width_max (cMin cMax cw gap : Nat) :
    (multicolMinMax cMin cMax none (some cw) gap).2 = cw :=
  rfl

end ColumnWidth
end ChromiumLayout
