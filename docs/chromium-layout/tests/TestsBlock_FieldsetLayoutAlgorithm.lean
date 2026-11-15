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

-- :540 NoFragmentation (fragmentainer 200 > 126 so the fieldset is one fragment with no break token)
theorem FieldsetNoFragmentation_size :
    (fragment 200 { base with inlineSize := 150, height := some 100 }).map (·.size) = [(176, 126)] := by
  decide +kernel

-- :228 LegendAutoSize (two 25x200 left floats in legend -> legend shrink-to-fit 50x200)
theorem FieldsetLegendAutoSize_vectors :
    let r := layout { base with legend := leg (25 + 25) 200, child := .fixed 100 }
    r.size = (126, 323) ∧ r.legend = some (13, 0, 50, 200) ∧ r.anon = (3, 200, 120, 120) ∧
      r.child = some (10, 10, 100, 100) := by decide

-- :372 PercentHeightQuirks and :404 LegendPercentHeightQuirks (container height 200: 50% -> 100, 20% -> 40)
theorem FieldsetPercentHeightQuirks_vectors :
    let r := layout { base with legend := leg 100 (200 * 50 / 100), child := .fixed (200 * 20 / 100) (some 40) }
    r.size = (126, 163) ∧ r.legend = some (13, 0, 100, 100) ∧ r.anon = (3, 100, 120, 60) ∧
      r.child = some (10, 10, 40, 40) := by decide

private def p0 : Phys := ⟨0, 0, 0, 0⟩
private def fs150 : Fieldset := { base with inlineSize := 150 }

-- :567 SimpleFragmentation (width 150, height 500, fragH 200 -> 3 fragments)
theorem FieldsetSimpleFragmentation_vectors :
    (fragment 200 { fs150 with height := some 500 }).map (·.size) =
      [(176, 200), (176, 200), (176, 126)] := by decide +kernel

-- :604 FragmentationNoPadding (border 10, padding 0, width 100, fragH 10 -> 2 fragments)
theorem FieldsetFragmentationNoPadding_vectors :
    fragment 10 { border := ⟨10, 10, 10, 10⟩, padding := p0, inlineSize := 100 } =
      [{ size := (120, 10), anon := some (10, 10, 100, 0) }, { size := (120, 10) }] := by decide +kernel

-- :645 FieldsetContentFragmentationAutoHeight (auto height, child 50x500, fragH 200)
theorem FieldsetContentFragmentationAutoHeight_vectors :
    fragment 200 { fs150 with child := .fixed 500 (some 50) } =
      [{ size := (176, 200), anon := some (3, 3, 170, 197), child := some (10, 10, 50, 187) },
       { size := (176, 200), anon := some (3, 0, 170, 200), child := some (10, 0, 50, 200) },
       { size := (176, 126), anon := some (3, 0, 170, 123), child := some (10, 0, 50, 113) }] := by decide +kernel

-- :708 FieldsetContentFragmentation (height 100, child 50x500, fragH 200)
theorem FieldsetContentFragmentation_vectors :
    fragment 200 { fs150 with height := some 100, child := .fixed 500 (some 50) } =
      [{ size := (176, 126), anon := some (3, 3, 170, 120), child := some (10, 10, 50, 187) },
       { size := (176, 0), anon := some (3, 0, 170, 0), child := some (10, 0, 50, 200) },
       { size := (176, 0), anon := some (3, 0, 170, 0), child := some (10, 0, 50, 113) }] := by decide +kernel

-- :771 LegendFragmentationAutoHeight and :821 LegendFragmentation (legend 50x500, fragH 200)
theorem FieldsetLegendFragmentation_vectors :
    fragment 200 { fs150 with legend := leg 50 500 } =
      [{ size := (176, 500), legend := some (13, 0, 50, 500) },
       { size := (176, 23), anon := some (3, 0, 170, 20) }] ∧
    fragment 200 { fs150 with height := some 100, legend := leg 50 500 } =
      [{ size := (176, 500), legend := some (13, 0, 50, 500) },
       { size := (176, 23), anon := some (3, 0, 170, 20) }] := by decide +kernel

-- :871 LegendAndContentFragmentationAutoHeight and :937 LegendAndContentFragmentation
theorem FieldsetLegendAndContentFragmentation_vectors :
    fragment 200 { fs150 with legend := leg 50 500, child := .fixed 200 (some 100) } =
      [{ size := (176, 500), legend := some (13, 0, 50, 500) },
       { size := (176, 200), anon := some (3, 0, 170, 200), child := some (10, 10, 100, 190) },
       { size := (176, 23), anon := some (3, 0, 170, 20), child := some (10, 0, 100, 10) }] ∧
    fragment 200 { fs150 with height := some 100, legend := leg 50 500, child := .fixed 200 (some 100) } =
      [{ size := (176, 500), legend := some (13, 0, 50, 500) },
       { size := (176, 23), anon := some (3, 0, 170, 20), child := some (10, 10, 100, 190) },
       { size := (176, 0), anon := some (3, 0, 170, 0), child := some (10, 0, 100, 10) }] := by decide +kernel

-- :1001 LegendFragmentationWithOverflow (legend 55x30 with overflowing child, child 44x150, fragH 100)
theorem FieldsetLegendFragmentationWithOverflow_vectors :
    fragment 100 { border := p0, padding := p0, inlineSize := 1000, legend := leg 55 30,
                   child := .fixed 150 (some 44) } =
      [{ size := (1000, 100), legend := some (0, 0, 55, 30), anon := some (0, 30, 1000, 70),
         child := some (0, 0, 44, 70) },
       { size := (1000, 80), anon := some (0, 0, 1000, 80), child := some (0, 0, 44, 80) }] := by decide +kernel

-- :1107 OverflowedLegend (width 100, height 100, legend 75x60, child 85x10, fragH 100)
theorem FieldsetOverflowedLegend_vectors :
    fragment 100 { border := p0, padding := p0, inlineSize := 100, height := some 100,
                   legend := leg 75 60, child := .fixed 10 (some 85) } =
      [{ size := (100, 100), legend := some (0, 0, 75, 60), anon := some (0, 60, 100, 40),
         child := some (0, 0, 85, 10) }] := by decide +kernel

-- :1594 MarginBottomPastEndOfFragmentainer (legend 0x90 with margin-bottom 20, child 20x20, fragH 100)
theorem FieldsetMarginBottomPastEnd_vectors :
    fragment 100 { border := p0, padding := p0, inlineSize := 100, height := some 100,
                   legend := leg 0 90 ⟨0, 0, 20, 0⟩, child := .fixed 20 (some 20) } =
      [{ size := (100, 110), legend := some (0, 0, 0, 90) },
       { size := (100, 0), anon := some (0, 0, 100, 0), child := some (0, 0, 20, 20) }] := by decide +kernel

-- :1650 SmallLegendLargeBorderFragmentation (border 60, width 100, height 10, legend 10x50, fragH 40)
theorem FieldsetSmallLegendLargeBorderFragmentation_vectors :
    fragment 40 { border := ⟨60, 60, 60, 60⟩, padding := p0, inlineSize := 100, height := some 10,
                  legend := leg 10 50 } =
      [{ size := (220, 60), legend := some (60, 5, 10, 50) },
       { size := (220, 10), anon := some (60, 0, 100, 10) },
       { size := (220, 60) }] := by decide +kernel

end TestsBlock
