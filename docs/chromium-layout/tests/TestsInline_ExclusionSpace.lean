import InlineExclusionSpace

namespace Chromium.Layout

/-!
# Exclusion Space Tests

Formalization of unit tests from `exclusions/exclusion_space_test.cc`.
Cites:
- CSS 2.1 §9.5: Visual formatting model - Floats
- CSS Inline 3 §3: Initial Letters
- CSS Exclusions 1 §3: Exclusion Areas and Opportunities
-/


/-! ## 1. exclusions/exclusion_space_test.cc:92 - Empty -/
theorem exclusionSpace_empty :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp : ExclusionSpace := {}
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 =
      [testOpportunity 0 0 100] ∧
    sp.allLayoutOpportunities { line_offset := -30, block_offset := -100 } 50 =
      [testOpportunity (-30) (-100) 20] ∧
    sp.allLayoutOpportunities { line_offset := 30, block_offset := 100 } 50 =
      [testOpportunity 30 100 80] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 2. exclusions/exclusion_space_test.cc:122 - LineLayoutOpportunityClampsNonDominantSide -/
theorem exclusionSpace_lineLayoutOpportunityClampsNonDominantSide :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let ltr_space : ConstraintSpace :=
      { direction := TextDirection.kLtr,
        bfc_offset := { line_offset := 10, block_offset := 0 },
        available_inline_size := 100, available_block_size := 100 }
    let ltr_opp : LayoutOpportunity := testOpportunity 20 0 150 100
    let ltr_line := ltr_opp.computeLineLayoutOpportunity ltr_space 10 0
    let ltr_opp_past : LayoutOpportunity := testOpportunity 120 0 150 100
    let ltr_line_past := ltr_opp_past.computeLineLayoutOpportunity ltr_space 10 0
    let rtl_space : ConstraintSpace :=
      { direction := TextDirection.kRtl,
        bfc_offset := { line_offset := 10, block_offset := 0 },
        available_inline_size := 100, available_block_size := 100 }
    let rtl_opp : LayoutOpportunity := testOpportunity (-50) 0 100 100
    let rtl_line := rtl_opp.computeLineLayoutOpportunity rtl_space 10 0
    let rtl_opp_past : LayoutOpportunity := testOpportunity (-50) 0 0 100
    let rtl_line_past := rtl_opp_past.computeLineLayoutOpportunity rtl_space 10 0
    ltr_line.line_left_offset = 20 ∧ ltr_line.line_right_offset = 110 ∧
    ltr_line_past.line_left_offset = 120 ∧ ltr_line_past.line_right_offset = 120 ∧
    rtl_line.line_left_offset = 10 ∧ rtl_line.line_right_offset = 100 ∧
    rtl_line_past.line_left_offset = 0 ∧ rtl_line_past.line_right_offset = 0 := by
  dsimp [LayoutOpportunity.computeLineLayoutOpportunity,
         BfcRect.lineStartOffset, BfcRect.lineEndOffset]
  decide

/-! ## 3. exclusions/exclusion_space_test.cc:169 - SingleExclusion -/
theorem exclusionSpace_singleExclusion :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 10, block_offset := 20 },
        end_offset := { line_offset := 60, block_offset := 90 } } EFloat.kLeft)
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 =
      [testOpportunity 0 0 100 20, testOpportunity 60 0 100, testOpportunity 0 90 100] ∧
    sp.allLayoutOpportunities { line_offset := -10, block_offset := -100 } 100 =
      [testOpportunity (-10) (-100) 90 20, testOpportunity 60 (-100) 90, testOpportunity (-10) 90 90] ∧
    sp.allLayoutOpportunities { line_offset := 10, block_offset := 10 } 50 =
      [testOpportunity 10 10 60 20, testOpportunity 60 10 60, testOpportunity 10 90 60] ∧
    sp.allLayoutOpportunities { line_offset := 10, block_offset := 10 } 49 =
      [testOpportunity 10 10 59 20, testOpportunity 60 10 60, testOpportunity 10 90 59] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 4. exclusions/exclusion_space_test.cc:232 - TwoExclusions -/
theorem exclusionSpace_twoExclusions :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := (ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 150, block_offset := 75 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 100, block_offset := 75 },
        end_offset := { line_offset := 400, block_offset := 150 } } EFloat.kRight)
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 400 =
      [testOpportunity 150 0 400 75, testOpportunity 0 75 100, testOpportunity 0 150 400] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 5. exclusions/exclusion_space_test.cc:273 - SolidEdges -/
theorem exclusionSpace_solidEdges :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ((((ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 20, block_offset := 15 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 65, block_offset := 0 },
        end_offset := { line_offset := 85, block_offset := 15 } } EFloat.kRight)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 10, block_offset := 25 },
        end_offset := { line_offset := 30, block_offset := 40 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 50, block_offset := 25 },
        end_offset := { line_offset := 70, block_offset := 35 } } EFloat.kRight))
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 80 =
      [testOpportunity 20 0 65 25,
       testOpportunity 30 0 50,
       testOpportunity 0 15 80 25,
       testOpportunity 30 35 80,
       testOpportunity 0 40 80] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 6. exclusions/exclusion_space_test.cc:325 - OverlappingWithShelf -/
theorem exclusionSpace_overlappingWithShelf :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := (((ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 20, block_offset := 15 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 65, block_offset := 0 },
        end_offset := { line_offset := 85, block_offset := 15 } } EFloat.kRight)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 70, block_offset := 25 },
        end_offset := { line_offset := 90, block_offset := 35 } } EFloat.kRight))
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 80 =
      [testOpportunity 20 0 65,
       testOpportunity 0 15 80 25,
       testOpportunity 0 15 70,
       testOpportunity 0 35 80] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 7. exclusions/exclusion_space_test.cc:373 - InsertBetweenShelves -/
theorem exclusionSpace_insertBetweenShelves :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := (((ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 30, block_offset := 10 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 65, block_offset := 0 },
        end_offset := { line_offset := 85, block_offset := 35 } } EFloat.kRight)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 10, block_offset := 15 },
        end_offset := { line_offset := 30, block_offset := 25 } } EFloat.kLeft))
    sp.allLayoutOpportunities { line_offset := 30, block_offset := 15 } 30 =
      [testOpportunity 30 15 60,
       testOpportunity 30 25 60,
       testOpportunity 30 35 60] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 8. exclusions/exclusion_space_test.cc:408 - InitialLetterBasic -/
theorem exclusionSpace_initialLetterBasic :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ExclusionSpace.add {} (ExclusionArea.createForInitialLetterBox
      { start_offset := { line_offset := 9, block_offset := 9 },
        end_offset := { line_offset := 73, block_offset := 73 } } EFloat.kLeft)
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 32 } 300 =
      [testOpportunity 73 32 309, testOpportunity 9 73 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 55 } 300 =
      [testOpportunity 73 55 309, testOpportunity 9 73 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 78 } 300 =
      [testOpportunity 9 78 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 101 } 300 =
      [testOpportunity 9 101 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 124 } 300 =
      [testOpportunity 9 124 309] ∧
    sp.initialLetterClearanceOffsets = [73, 73, layoutUnitMin] := by
  dsimp [ExclusionSpace.allLayoutOpportunities, ExclusionSpace.initialLetterClearanceOffsets]
  decide

/-! ## 9. exclusions/exclusion_space_test.cc:451 - InitialLetterDirectionRight -/
theorem exclusionSpace_initialLetterDirectionRight :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp1 := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 9, block_offset := 9 },
        end_offset := { line_offset := 59, block_offset := 59 } } EFloat.kLeft)
    let opp1 := sp1.findLayoutOpportunity { line_offset := 9, block_offset := 9 } 300 TextDirection.kLtr 100
    let sp2 := sp1.add (ExclusionArea.create
      { start_offset := { line_offset := 209, block_offset := 9 },
        end_offset := { line_offset := 309, block_offset := 59 } } EFloat.kLeft)
    let opps2 := sp2.allLayoutOpportunities { line_offset := 9, block_offset := 9 } 300
    let sp3 := sp2.add (ExclusionArea.createForInitialLetterBox
      { start_offset := { line_offset := 117, block_offset := 9 },
        end_offset := { line_offset := 182, block_offset := 73 } } EFloat.kLeft)
    opp1 = testOpportunity 59 9 309 ∧
    opps2 = [testOpportunity 309 9 309, testOpportunity 9 59 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 32 } 300 =
      [testOpportunity 309 32 309, testOpportunity 182 59 309, testOpportunity 9 73 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 55 } 300 =
      [testOpportunity 309 55 309, testOpportunity 182 59 309, testOpportunity 9 73 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 78 } 300 =
      [testOpportunity 9 78 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 101 } 300 =
      [testOpportunity 9 101 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 124 } 300 =
      [testOpportunity 9 124 309] ∧
    sp3.initialLetterClearanceOffsets = [73, 73, layoutUnitMin] := by
  dsimp [ExclusionSpace.allLayoutOpportunities, ExclusionSpace.findLayoutOpportunity,
         ExclusionSpace.initialLetterClearanceOffsets]
  decide

/-! ## 10. exclusions/exclusion_space_test.cc:560 - InitialLetterFloatLeft2 -/
theorem exclusionSpace_initialLetterFloatLeft2 :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ((ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 9, block_offset := 59 },
        end_offset := { line_offset := 59, block_offset := 59 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 59, block_offset := 59 },
        end_offset := { line_offset := 159, block_offset := 59 } } EFloat.kLeft)).add
      (ExclusionArea.createForInitialLetterBox
      { start_offset := { line_offset := 159, block_offset := 9 },
        end_offset := { line_offset := 223, block_offset := 73 } } EFloat.kLeft)
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 32 } 300 =
      [testOpportunity 223 32 309, testOpportunity 223 59 309, testOpportunity 9 73 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 55 } 300 =
      [testOpportunity 223 55 309, testOpportunity 223 59 309, testOpportunity 9 73 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 78 } 300 =
      [testOpportunity 9 78 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 101 } 300 =
      [testOpportunity 9 101 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 124 } 300 =
      [testOpportunity 9 124 309] ∧
    sp.initialLetterClearanceOffsets = [73, 73, layoutUnitMin] := by
  dsimp [ExclusionSpace.allLayoutOpportunities, ExclusionSpace.initialLetterClearanceOffsets]
  decide

/-! ## 11. exclusions/exclusion_space_test.cc:615 - InitialLetterFloatLeft2ClearLeft -/
theorem exclusionSpace_initialLetterFloatLeft2ClearLeft :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ((ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 9, block_offset := 59 },
        end_offset := { line_offset := 59, block_offset := 59 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 9, block_offset := 59 },
        end_offset := { line_offset := 109, block_offset := 109 } } EFloat.kLeft)).add
      (ExclusionArea.createForInitialLetterBox
      { start_offset := { line_offset := 109, block_offset := 9 },
        end_offset := { line_offset := 223, block_offset := 73 } } EFloat.kLeft)
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 32 } 300 =
      [testOpportunity 223 32 309, testOpportunity 109 73 309, testOpportunity 9 109 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 55 } 300 =
      [testOpportunity 223 55 309, testOpportunity 109 73 309, testOpportunity 9 109 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 78 } 300 =
      [testOpportunity 109 78 309, testOpportunity 9 109 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 101 } 300 =
      [testOpportunity 109 101 309, testOpportunity 9 109 309] ∧
    sp.allLayoutOpportunities { line_offset := 9, block_offset := 124 } 300 =
      [testOpportunity 9 124 309] ∧
    sp.initialLetterClearanceOffsets = [73, 73, layoutUnitMin] := by
  dsimp [ExclusionSpace.allLayoutOpportunities, ExclusionSpace.initialLetterClearanceOffsets]
  decide

/-! ## 12. exclusions/exclusion_space_test.cc:672 - InitialLetterFloatLeftAndRight -/
theorem exclusionSpace_initialLetterFloatLeftAndRight :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp1 := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 9, block_offset := 59 },
        end_offset := { line_offset := 59, block_offset := 59 } } EFloat.kLeft)
    let opp1 := sp1.findLayoutOpportunity { line_offset := 9, block_offset := 9 } 300 TextDirection.kLtr 100
    let sp2 := sp1.add (ExclusionArea.create
      { start_offset := { line_offset := 9, block_offset := 59 },
        end_offset := { line_offset := 109, block_offset := 109 } } EFloat.kLeft)
    let opps2 := sp2.allLayoutOpportunities { line_offset := 9, block_offset := 9 } 300
    let sp3 := sp2.add (ExclusionArea.createForInitialLetterBox
      { start_offset := { line_offset := 59, block_offset := 9 },
        end_offset := { line_offset := 123, block_offset := 73 } } EFloat.kLeft)
    opp1 = testOpportunity 9 9 309 59 ∧
    opps2 = [testOpportunity 9 9 309 59, testOpportunity 109 9 309, testOpportunity 9 109 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 32 } 300 =
      [testOpportunity 123 32 309, testOpportunity 109 73 309, testOpportunity 9 109 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 55 } 300 =
      [testOpportunity 123 55 309, testOpportunity 109 73 309, testOpportunity 9 109 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 78 } 300 =
      [testOpportunity 109 78 309, testOpportunity 9 109 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 101 } 300 =
      [testOpportunity 109 101 309, testOpportunity 9 109 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 124 } 300 =
      [testOpportunity 9 124 309] ∧
    sp3.initialLetterClearanceOffsets = [73, 73, layoutUnitMin] := by
  dsimp [ExclusionSpace.allLayoutOpportunities, ExclusionSpace.findLayoutOpportunity,
         ExclusionSpace.initialLetterClearanceOffsets]
  decide

/-! ## 13. exclusions/exclusion_space_test.cc:796 - InitialLetterFloatRight2 -/
theorem exclusionSpace_initialLetterFloatRight2 :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp1 := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 259, block_offset := 9 },
        end_offset := { line_offset := 309, block_offset := 59 } } EFloat.kLeft)
    let opp1 := sp1.findLayoutOpportunity { line_offset := 9, block_offset := 9 } 300 TextDirection.kLtr 200
    let sp2 := sp1.add (ExclusionArea.create
      { start_offset := { line_offset := 59, block_offset := 9 },
        end_offset := { line_offset := 259, block_offset := 59 } } EFloat.kLeft)
    let opps2 := sp2.allLayoutOpportunities { line_offset := 9, block_offset := 9 } 300
    let sp3 := sp2.add (ExclusionArea.createForInitialLetterBox
      { start_offset := { line_offset := 9, block_offset := 59 },
        end_offset := { line_offset := 73, block_offset := 123 } } EFloat.kLeft)
    opp1 = testOpportunity 9 59 309 ∧
    opps2 = [testOpportunity 309 9 309, testOpportunity 9 59 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 82 } 300 =
      [testOpportunity 73 82 309, testOpportunity 9 123 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 105 } 300 =
      [testOpportunity 73 105 309, testOpportunity 9 123 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 128 } 300 =
      [testOpportunity 9 128 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 151 } 300 =
      [testOpportunity 9 151 309] ∧
    sp3.allLayoutOpportunities { line_offset := 9, block_offset := 174 } 300 =
      [testOpportunity 9 174 309] ∧
    sp3.initialLetterClearanceOffsets = [123, 123, layoutUnitMin] := by
  dsimp [ExclusionSpace.allLayoutOpportunities, ExclusionSpace.findLayoutOpportunity,
         ExclusionSpace.initialLetterClearanceOffsets]
  decide

/-! ## 14. exclusions/exclusion_space_test.cc:857 - ZeroInlineSizeOpportunity -/
theorem exclusionSpace_zeroInlineSizeOpportunity :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 100, block_offset := 10 } } EFloat.kLeft)
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 =
      [testOpportunity 100 0 100, testOpportunity 0 10 100] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 15. exclusions/exclusion_space_test.cc:877 - NegativeInlineSizeOpportunityLeft -/
theorem exclusionSpace_negativeInlineSizeOpportunityLeft :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 120, block_offset := 10 } } EFloat.kLeft)
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 TextDirection.kLtr =
      [testOpportunity 120 0 120, testOpportunity 0 10 100] ∧
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 TextDirection.kRtl =
      [testOpportunity 100 0 100, testOpportunity 0 10 100] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 16. exclusions/exclusion_space_test.cc:907 - NegativeInlineSizeOpportunityRight -/
theorem exclusionSpace_negativeInlineSizeOpportunityRight :
    let testOpportunity (inline_start block_start inline_end : Int) (block_end : Int := layoutUnitMax) : LayoutOpportunity :=
      { rect := { start_offset := { line_offset := inline_start, block_offset := block_start },
                  end_offset := { line_offset := inline_end, block_offset := block_end } } }
    let sp := ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := -20, block_offset := 0 },
        end_offset := { line_offset := 100, block_offset := 10 } } EFloat.kRight)
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 TextDirection.kLtr =
      [testOpportunity 0 0 0, testOpportunity 0 10 100] ∧
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 TextDirection.kRtl =
      [testOpportunity (-20) 0 (-20), testOpportunity 0 10 100] ∧
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 TextDirection.kLtr =
      [testOpportunity 0 0 0, testOpportunity 0 10 100] ∧
    sp.allLayoutOpportunities { line_offset := 0, block_offset := 0 } 100 TextDirection.kRtl =
      [testOpportunity (-20) 0 (-20), testOpportunity 0 10 100] := by
  dsimp [ExclusionSpace.allLayoutOpportunities]
  decide

/-! ## 17. exclusions/exclusion_space_test.cc:937 - PreInitialization -/
theorem exclusionSpace_preInitialization :
    let orig := (ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 20, block_offset := 15 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 65, block_offset := 0 },
        end_offset := { line_offset := 85, block_offset := 15 } } EFloat.kRight)
    let sp1 := (ExclusionSpace.add {} (ExclusionArea.create
      { start_offset := { line_offset := 0, block_offset := 0 },
        end_offset := { line_offset := 20, block_offset := 15 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 65, block_offset := 0 },
        end_offset := { line_offset := 85, block_offset := 15 } } EFloat.kRight)
    let sp1_extra := sp1.add (ExclusionArea.create
      { start_offset := { line_offset := 10, block_offset := 25 },
        end_offset := { line_offset := 30, block_offset := 40 } } EFloat.kLeft)
    sp1 = orig ∧ sp1_extra ≠ orig := by
  dsimp [ExclusionSpace.add]
  decide

/-! ## 18. exclusions/exclusion_space_test.cc:992 - MergeExclusionSpacesNoPreviousExclusions -/
theorem exclusionSpace_mergeExclusionSpacesNoPreviousExclusions :
    let old_input : ExclusionSpace := {}
    let old_output := old_input.add (ExclusionArea.create
      { start_offset := { line_offset := 10, block_offset := 25 },
        end_offset := { line_offset := 30, block_offset := 40 } } EFloat.kLeft)
    let new_input : ExclusionSpace := {}
    let new_output := ExclusionSpace.mergeExclusionSpaces old_output old_input new_input
      { line_offset := 10, block_offset := 20 }
    let expected := ({} : ExclusionSpace).add (ExclusionArea.create
      { start_offset := { line_offset := 20, block_offset := 45 },
        end_offset := { line_offset := 40, block_offset := 60 } } EFloat.kLeft)
    new_output = expected := by
  dsimp [ExclusionSpace.mergeExclusionSpaces, ExclusionSpace.add]
  decide

/-! ## 19. exclusions/exclusion_space_test.cc:1020 - MergeExclusionSpacesPreviousExclusions -/
theorem exclusionSpace_mergeExclusionSpacesPreviousExclusions :
    let old_input := ({} : ExclusionSpace).add (ExclusionArea.create
      { start_offset := { line_offset := 20, block_offset := 45 },
        end_offset := { line_offset := 40, block_offset := 60 } } EFloat.kLeft)
    let old_output := old_input.add (ExclusionArea.create
      { start_offset := { line_offset := 100, block_offset := 45 },
        end_offset := { line_offset := 140, block_offset := 60 } } EFloat.kRight)
    let new_input := ({} : ExclusionSpace).add (ExclusionArea.create
      { start_offset := { line_offset := 20, block_offset := 45 },
        end_offset := { line_offset := 40, block_offset := 50 } } EFloat.kLeft)
    let new_output := ExclusionSpace.mergeExclusionSpaces old_output old_input new_input
      { line_offset := 10, block_offset := 20 }
    let expected := new_input.add (ExclusionArea.create
      { start_offset := { line_offset := 110, block_offset := 65 },
        end_offset := { line_offset := 150, block_offset := 80 } } EFloat.kRight)
    new_output = expected := by
  dsimp [ExclusionSpace.mergeExclusionSpaces, ExclusionSpace.add]
  decide

/-! ## 20. exclusions/exclusion_space_test.cc:1060 - MergeExclusionSpacesNoOutputExclusions -/
theorem exclusionSpace_mergeExclusionSpacesNoOutputExclusions :
    let old_input := ((({} : ExclusionSpace).add (ExclusionArea.create
      { start_offset := { line_offset := 20, block_offset := 45 },
        end_offset := { line_offset := 40, block_offset := 60 } } EFloat.kLeft)).add
      (ExclusionArea.create
      { start_offset := { line_offset := 100, block_offset := 45 },
        end_offset := { line_offset := 140, block_offset := 60 } } EFloat.kRight))
    let old_output := old_input
    let new_input : ExclusionSpace := {}
    let new_output := ExclusionSpace.mergeExclusionSpaces old_output old_input new_input
      { line_offset := 10, block_offset := 20 }
    new_output = ({} : ExclusionSpace) := by
  dsimp [ExclusionSpace.mergeExclusionSpaces]
  decide

end Chromium.Layout
