import InlineGeometry
import InlineFieldset

namespace ChromiumLayout

/-! ## Fieldset Layout Algorithm Tests
    Formalizing Chromium's `forms/fieldset_layout_algorithm_test.cc` test cases.
    Specifications:
    - HTML 5.2 §4.10.16 The fieldset element
    - CSS 2.1 §10 Visual formatting model details
    - CSS Writing Modes 3 §4.2 Inline-level Alignment
-/

/-- Test `FieldsetLayoutAlgorithmTest, Empty` (`forms/fieldset_layout_algorithm_test.cc:59`). -/
theorem fieldset_empty :
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100 }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 26 } ∧
    res.contentOffset = { left := 3, top := 3 } ∧
    res.contentSize = { width := 120, height := 20 } :=
  ⟨rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, NoLegend` (`forms/fieldset_layout_algorithm_test.cc:78`). -/
theorem fieldset_noLegend :
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 126 } ∧
    res.contentOffset = { left := 3, top := 3 } ∧
    res.contentSize = { width := 120, height := 120 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] ∧
    res.childSizes = [{ width := 100, height := 100 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, Legend` (`forms/fieldset_layout_algorithm_test.cc:100`). -/
theorem fieldset_legend :
    let leg : LegendInput := { size := { width := 50, height := 200 } }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 323 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 50, height := 200 } ∧
    res.contentOffset = { left := 3, top := 200 } ∧
    res.contentSize = { width := 120, height := 120 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, SmallLegendLargeBorder` (`forms/fieldset_layout_algorithm_test.cc:124`). -/
theorem fieldset_smallLegendLargeBorder :
    let leg : LegendInput := { size := { width := 10, height := 10 },
                               margins := { top := 5, bottom := 15 } }
    let inp : FieldsetInput := { borderTop := 40, borderRight := 40, borderBottom := 40, borderLeft := 40,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 200, height := 200 } ∧
    res.legendOffset = some { left := 50, top := 15 } ∧
    res.legendSize = some { width := 10, height := 10 } ∧
    res.contentOffset = { left := 40, top := 40 } ∧
    res.contentSize = { width := 120, height := 120 } :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, LegendOrthogonalWritingMode` (`forms/fieldset_layout_algorithm_test.cc:150`). -/
theorem fieldset_legendOrthogonalWritingMode :
    let leg : LegendInput := { size := { width := 10, height := 50 },
                               margins := { top := 10, right := 15, bottom := 20, left := 30 },
                               writingMode := WritingMode.verticalRl }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 193 } ∧
    res.legendOffset = some { left := 43, top := 0 } ∧
    res.contentOffset = { left := 3, top := 70 } ∧
    res.contentSize = { width := 120, height := 120 } :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, VerticalLr` (`forms/fieldset_layout_algorithm_test.cc:176`). -/
theorem fieldset_verticalLr :
    let leg : LegendInput := { size := { width := 10, height := 50 },
                               margins := { top := 10, right := 15, bottom := 20, left := 30 } }
    let inp : FieldsetInput := { writingMode := WritingMode.verticalLr,
                                 borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedHeight := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 148, height := 126 } ∧
    res.legendOffset = some { left := 0, top := 23 } ∧
    res.contentOffset = { left := 25, top := 3 } ∧
    res.contentSize = { width := 120, height := 120 } :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, VerticalRl` (`forms/fieldset_layout_algorithm_test.cc:202`). -/
theorem fieldset_verticalRl :
    let leg : LegendInput := { size := { width := 10, height := 50 },
                               margins := { top := 10, right := 15, bottom := 20, left := 30 } }
    let inp : FieldsetInput := { writingMode := WritingMode.verticalRl,
                                 borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedHeight := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 163, height := 126 } ∧
    res.legendOffset = some { left := 153, top := 23 } ∧
    res.contentOffset = { left := 3, top := 3 } ∧
    res.contentSize = { width := 120, height := 120 } :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, LegendAutoSize` (`forms/fieldset_layout_algorithm_test.cc:228`). -/
theorem fieldset_legendAutoSize :
    let float1 : ChildBoxInput := { size := { width := 25, height := 200 }, offset := some { left := 0, top := 0 } }
    let float2 : ChildBoxInput := { size := { width := 25, height := 200 }, offset := some { left := 25, top := 0 } }
    let leg : LegendInput := { size := { width := 50, height := 200 }, children := [float1, float2] }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 100 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 323 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 50, height := 200 } ∧
    res.legendChildren = [({ left := 0, top := 0 }, { width := 25, height := 200 }),
                          ({ left := 25, top := 0 }, { width := 25, height := 200 })] ∧
    res.contentOffset = { left := 3, top := 200 } ∧
    res.contentSize = { width := 120, height := 120 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, PercentageHeightChild` (`forms/fieldset_layout_algorithm_test.cc:257`). -/
theorem fieldset_percentageHeightChild :
    let leg : LegendInput := { size := { width := 30, height := 30 } }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100, specifiedHeight := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 0 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 126 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 30, height := 30 } ∧
    res.contentOffset = { left := 3, top := 30 } ∧
    res.contentSize = { width := 120, height := 93 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] ∧
    res.childSizes = [{ width := 100, height := 73 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, AbsposChild` (`forms/fieldset_layout_algorithm_test.cc:283`). -/
theorem fieldset_absposChild :
    let leg : LegendInput := { size := { width := 30, height := 30 } }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100, specifiedHeight := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 0, height := 0 }, isAbspos := true }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 126 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 30, height := 30 } ∧
    res.contentOffset = { left := 3, top := 30 } ∧
    res.contentSize = { width := 120, height := 93 } ∧
    res.childOffsets = [{ left := 0, top := 0 }] ∧
    res.childSizes = [{ width := 120, height := 93 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, ZeroMaxHeight` (`forms/fieldset_layout_algorithm_test.cc:340`). -/
theorem fieldset_zeroMaxHeight :
    let leg : LegendInput := { size := { width := 30, height := 30 } }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100, maxHeight := some 0,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 200 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 53 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 30, height := 30 } ∧
    res.contentOffset = { left := 3, top := 30 } ∧
    res.contentSize = { width := 120, height := 20 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] ∧
    res.childSizes = [{ width := 100, height := 200 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, PercentHeightQuirks` (`forms/fieldset_layout_algorithm_test.cc:372`). -/
theorem fieldset_percentHeightQuirks :
    let legChild : ChildBoxInput := { size := { width := 100, height := 100 } }
    let leg : LegendInput := { size := { width := 100, height := 100 }, children := [legChild] }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 40, height := 40 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 163 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 100, height := 100 } ∧
    res.contentOffset = { left := 3, top := 100 } ∧
    res.contentSize = { width := 120, height := 60 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] ∧
    res.childSizes = [{ width := 40, height := 40 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, LegendPercentHeightQuirks` (`forms/fieldset_layout_algorithm_test.cc:404`). -/
theorem fieldset_legendPercentHeightQuirks :
    let leg : LegendInput := { size := { width := 100, height := 100 } }
    let inp : FieldsetInput := { borderTop := 3, borderRight := 3, borderBottom := 3, borderLeft := 3,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 40, height := 40 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 126, height := 163 } ∧
    res.legendOffset = some { left := 13, top := 0 } ∧
    res.legendSize = some { width := 100, height := 100 } ∧
    res.contentOffset = { left := 3, top := 100 } ∧
    res.contentSize = { width := 120, height := 60 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] ∧
    res.childSizes = [{ width := 40, height := 40 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, FieldsetPaddingWithLegend` (`forms/fieldset_layout_algorithm_test.cc:433`). -/
theorem fieldset_fieldsetPaddingWithLegend :
    let leg : LegendInput := { size := { width := 50, height := 120 } }
    let inp : FieldsetInput := { borderTop := 0, borderRight := 0, borderBottom := 0, borderLeft := 0,
                                 paddingTop := 10, paddingRight := 10, paddingBottom := 10, paddingLeft := 10,
                                 specifiedWidth := some 150, specifiedHeight := some 100,
                                 legend := some leg,
                                 children := [{ size := { width := 100, height := 40 } }] }
    let res := layoutFieldset inp
    res.fieldsetSize = { width := 170, height := 140 } ∧
    res.legendOffset = some { left := 10, top := 0 } ∧
    res.legendSize = some { width := 50, height := 120 } ∧
    res.contentOffset = { left := 0, top := 120 } ∧
    res.contentSize = { width := 170, height := 20 } ∧
    res.childOffsets = [{ left := 10, top := 10 }] ∧
    res.childSizes = [{ width := 100, height := 40 }] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Test `FieldsetLayoutAlgorithmTest, MinMax` (`forms/fieldset_layout_algorithm_test.cc:472`).
    HTML 5.2 §4.10.16 & CSS Sizing 3 §5:
    Computes min/max content sizes for 6 fieldset/legend configurations. -/
theorem fieldset_minMax :
    let fs1 : FieldsetMinMaxInput := { borderPadding := 26, hasLegend := false }
    let fs2 : FieldsetMinMaxInput := { borderPadding := 26, hasLegend := true, legendBorderPaddingMargin := 76 }
    let fs3 : FieldsetMinMaxInput := { borderPadding := 26, hasLegend := true, legendBorderPaddingMargin := 76, contentFloats := [50, 50] }
    let fs4 : FieldsetMinMaxInput := { borderPadding := 26, hasLegend := true, legendBorderPaddingMargin := 76, legendFloats := [50, 50], contentFloats := [50] }
    let fs5 : FieldsetMinMaxInput := { borderPadding := 26, hasLegend := true, legendBorderPaddingMargin := 76, legendFloats := [50], contentFloats := [50, 50, 50] }
    let fs6 : FieldsetMinMaxInput := { borderPadding := 26, hasLegend := false, contentFloats := [50, 50] }
    computeFieldsetMinMaxSizes fs1 = { minSize := 26, maxSize := 26 } ∧
    computeFieldsetMinMaxSizes fs2 = { minSize := 102, maxSize := 102 } ∧
    computeFieldsetMinMaxSizes fs3 = { minSize := 102, maxSize := 126 } ∧
    computeFieldsetMinMaxSizes fs4 = { minSize := 152, maxSize := 202 } ∧
    computeFieldsetMinMaxSizes fs5 = { minSize := 152, maxSize := 176 } ∧
    computeFieldsetMinMaxSizes fs6 = { minSize := 76, maxSize := 126 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ChromiumLayout
