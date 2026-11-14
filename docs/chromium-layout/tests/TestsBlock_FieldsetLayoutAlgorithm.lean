import BlockFieldset

namespace TestsBlock

open ChromiumLayout.BlockWritingMode ChromiumLayout.BlockFieldset

private def b3 : Phys := ⟨3, 3, 3, 3⟩
private def p10 : Phys := ⟨10, 10, 10, 10⟩
private def base : Fieldset := { border := b3, padding := p10, inlineSize := 100 }
private def leg (w h : Nat) (m : Phys := ⟨0, 0, 0, 0⟩) : Option Legend := some ⟨w, h, m⟩

-- forms/fieldset_layout_algorithm_test.cc:59: FieldsetLayoutAlgorithmTest.Empty
theorem FieldsetEmpty_vectors :
    let r := layout base
    r.size = (126, 26) ∧ r.legend = none ∧ r.anon = (3, 3, 120, 20) ∧ r.child = none := by decide

-- :78 NoLegend
theorem FieldsetNoLegend_vectors :
    let r := layout { base with child := .fixed 100 }
    r.size = (126, 126) ∧ r.anon = (3, 3, 120, 120) ∧ r.child = some (10, 10, 100, 100) := by decide

-- :100 Legend
theorem FieldsetLegend_vectors :
    let r := layout { base with legend := leg 50 200, child := .fixed 100 }
    r.size = (126, 323) ∧ r.legend = some (13, 0, 50, 200) ∧ r.anon = (3, 200, 120, 120) ∧
      r.child = some (10, 10, 100, 100) := by decide

-- :124 SmallLegendLargeBorder
theorem FieldsetSmallLegendLargeBorder_vectors :
    let r := layout { base with border := ⟨40, 40, 40, 40⟩, legend := leg 10 10 ⟨5, 0, 15, 0⟩,
                                child := .fixed 100 }
    r.size = (200, 200) ∧ r.legend = some (50, 15, 10, 10) ∧ r.anon = (40, 40, 120, 120) ∧
      r.child = some (10, 10, 100, 100) := by decide

-- :150 LegendOrthogonalWritingMode (legend is 10 wide, 50 tall in the fieldset's frame)
theorem FieldsetLegendOrthogonal_vectors :
    let r := layout { base with legend := leg 10 50 ⟨10, 15, 20, 30⟩, child := .fixed 100 }
    r.size = (126, 193) ∧ r.legend = some (43, 0, 10, 50) ∧ r.anon = (3, 70, 120, 120) ∧
      r.child = some (10, 10, 100, 100) := by decide

-- :176 VerticalLr (height:100px is the inline size; the child's width 100px is its block size)
theorem FieldsetVerticalLr_vectors :
    let r := layout { base with wm := .verticalLr, legend := leg 10 50 ⟨10, 15, 20, 30⟩,
                                child := .fixed 100 }
    r.size = (148, 126) ∧ r.legend = some (0, 23, 10, 50) ∧ r.anon = (25, 3, 120, 120) ∧
      r.child = some (10, 10, 100, 100) := by decide

-- :202 VerticalRl
theorem FieldsetVerticalRl_vectors :
    let r := layout { base with wm := .verticalRl, legend := leg 10 50 ⟨10, 15, 20, 30⟩,
                                child := .fixed 100 }
    r.size = (163, 126) ∧ r.legend = some (153, 23, 10, 50) ∧ r.anon = (3, 3, 120, 120) ∧
      r.child = some (10, 10, 100, 100) := by decide

-- :257 PercentageHeightChild
theorem FieldsetPercentageHeightChild_vectors :
    let r := layout { base with height := some 100, legend := leg 30 30, child := .percent 100 }
    r.size = (126, 126) ∧ r.legend = some (13, 0, 30, 30) ∧ r.anon = (3, 30, 120, 93) ∧
      r.child = some (10, 10, 100, 73) := by decide

-- :283 AbsposChild
theorem FieldsetAbsposChild_vectors :
    let r := layout { base with height := some 100, legend := leg 30 30, child := .absFill }
    r.size = (126, 126) ∧ r.legend = some (13, 0, 30, 30) ∧ r.anon = (3, 30, 120, 93) ∧
      r.child = some (0, 0, 120, 93) := by decide

-- :312 ZeroHeight
theorem FieldsetZeroHeight_vectors :
    let r := layout { base with height := some 0, legend := leg 30 30, child := .fixed 200 }
    r.size = (126, 53) ∧ r.legend = some (13, 0, 30, 30) ∧ r.anon = (3, 30, 120, 20) ∧
      r.child = some (10, 10, 100, 200) := by decide

-- :340 ZeroMaxHeight
theorem FieldsetZeroMaxHeight_vectors :
    let r := layout { base with maxHeight := some 0, legend := leg 30 30, child := .fixed 200 }
    r.size = (126, 53) ∧ r.legend = some (13, 0, 30, 30) ∧ r.anon = (3, 30, 120, 20) ∧
      r.child = some (10, 10, 100, 200) := by decide

-- :433 FieldsetPaddingWithLegend
theorem FieldsetPaddingWithLegend_vectors :
    let r := layout { border := ⟨0, 0, 0, 0⟩, padding := p10, inlineSize := 150, height := some 100,
                      legend := leg 50 120, child := .fixed 40 (some 100) }
    r.size = (170, 140) ∧ r.legend = some (10, 0, 50, 120) ∧ r.anon = (0, 120, 170, 20) ∧
      r.child = some (10, 10, 100, 40) := by decide

-- :472 MinMax (chrome = border 6 + padding 20; legend margin box = 2*20 + 2*11 + 2*7 = 76)
theorem FieldsetMinMax_vectors :
    minMax 26 (0, 0) (0, 0) = (26, 26) ∧
    minMax 26 (76, 76) (0, 0) = (102, 102) ∧
    minMax 26 (76, 76) (50, 100) = (102, 126) ∧
    minMax 26 (126, 176) (50, 50) = (152, 202) ∧
    minMax 26 (126, 126) (50, 150) = (152, 176) ∧
    minMax 26 (0, 0) (50, 100) = (76, 126) := by decide

-- :540 NoFragmentation (size only; fragmentainer 200 > 126 so the fieldset is one fragment)
theorem FieldsetNoFragmentation_size :
    (layout { base with inlineSize := 150, height := some 100 }).size = (176, 126) := by decide

end TestsBlock
