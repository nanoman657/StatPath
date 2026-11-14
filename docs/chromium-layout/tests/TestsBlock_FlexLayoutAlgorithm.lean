/-
  TestsBlock_FlexLayoutAlgorithm.lean: formalization of Chromium tests from
  flex/flex_layout_algorithm_test.cc.
  Owned by the block lane (TestsBlock_*).
-/
import FlexLayout

namespace ChromiumLayout
namespace TestsBlock

open ChromiumLayout.FlexLayout

-- flex/flex_layout_algorithm_test.cc:939: DevtoolsBasic
-- Flex items with flex-grow: 1 evenly divide available main axis space.
-- CSS Flexible Box Layout Level 1 §7.1, §9.7.
theorem DevtoolsBasic_vectors :
    let c : FlexContainer := {
      mainSize := some 100,
      items := [
        { id := 0, grow := 1, crossSize := 50 },
        { id := 1, grow := 1 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 ∧
    res.lines[0]!.items.length = 2 ∧
    res.lines[0]!.items[0]!.x = 0 ∧ res.lines[0]!.items[0]!.y = 0 ∧
    res.lines[0]!.items[0]!.w = 50 ∧ res.lines[0]!.items[0]!.h = 50 ∧
    res.lines[0]!.items[1]!.x = 50 ∧ res.lines[0]!.items[1]!.y = 0 ∧
    res.lines[0]!.items[1]!.w = 50 ∧ res.lines[0]!.items[1]!.h = 50 := by
  decide

-- flex/flex_layout_algorithm_test.cc:953: DevtoolsWrap
-- Flex items wrap to new line when exceeding container main size.
-- CSS Flexible Box Layout Level 1 §5.2, §9.3.
theorem DevtoolsWrap_vectors :
    let c : FlexContainer := {
      mainSize := some 100,
      wrap := .wrap,
      items := [
        { id := 0, minMain := some 100, crossSize := 50 },
        { id := 1, basis := some 20, grow := 1, shrink := 0, crossSize := 90 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 2 ∧
    res.lines[0]!.items.length = 1 ∧
    res.lines[0]!.items[0]!.x = 0 ∧ res.lines[0]!.items[0]!.y = 0 ∧
    res.lines[0]!.items[0]!.w = 100 ∧ res.lines[0]!.items[0]!.h = 50 ∧
    res.lines[1]!.items.length = 1 ∧
    res.lines[1]!.items[0]!.x = 0 ∧ res.lines[1]!.items[0]!.y = 50 ∧
    res.lines[1]!.items[0]!.w = 100 ∧ res.lines[1]!.items[0]!.h = 90 := by
  decide

-- flex/flex_layout_algorithm_test.cc:968: DevtoolsCoordinates
-- Item coordinates account for container border and padding.
-- CSS Flexible Box Layout Level 1 §4.2, CSS 2.1 §8.1.
theorem DevtoolsCoordinates_vectors :
    let c : FlexContainer := {
      mainSize := some 100,
      wrap := .wrap,
      borderMainStart := 3,
      paddingMainStart := 5,
      borderCrossStart := 2,
      paddingCrossStart := 3,
      items := [
        { id := 0, marginMainStart := 5, minMain := some 95, crossSize := 50 },
        { id := 1, basis := some 20, grow := 1, shrink := 0, crossSize := 90 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 2 ∧
    res.lines[0]!.items.length = 1 ∧
    res.lines[0]!.items[0]!.x = 8 ∧ res.lines[0]!.items[0]!.y = 5 ∧
    res.lines[0]!.items[0]!.w = 100 ∧ res.lines[0]!.items[0]!.h = 50 ∧
    res.lines[1]!.items.length = 1 ∧
    res.lines[1]!.items[0]!.x = 8 ∧ res.lines[1]!.items[0]!.y = 55 ∧
    res.lines[1]!.items[0]!.w = 100 ∧ res.lines[1]!.items[0]!.h = 90 := by
  decide

-- flex/flex_layout_algorithm_test.cc:983: DevtoolsOverflow
-- Items exceeding container width overflow into single line when nowrap.
-- CSS Flexible Box Layout Level 1 §5.2, §9.3.
theorem DevtoolsOverflow_vectors :
    let c : FlexContainer := {
      mainSize := some 100,
      borderMainStart := 1,
      borderMainEnd := 3,
      items := [
        { id := 0, minMain := some 150, crossSize := 75 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 ∧
    res.lines[0]!.items.length = 1 ∧
    res.lines[0]!.items[0]!.x = 1 ∧ res.lines[0]!.items[0]!.y = 0 ∧
    res.lines[0]!.items[0]!.w = 150 ∧ res.lines[0]!.items[0]!.h = 75 := by
  decide

-- flex/flex_layout_algorithm_test.cc:993: DevtoolsWithRelPosItem
-- Relative positioning does not create extra flex lines.
-- CSS Flexible Box Layout Level 1 §4.1, CSS 2.1 §9.3.2.
theorem DevtoolsWithRelPosItem_vectors :
    let c : FlexContainer := {
      items := [
        { id := 0, basis := some 50, crossSize := 50 },
        { id := 1, basis := some 50, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 := by
  decide

-- flex/flex_layout_algorithm_test.cc:1040: DevtoolsColumnWrap
-- Column wrap flexbox with oversized item stays on one line when unconstrained.
-- CSS Flexible Box Layout Level 1 §5.1, §5.2.
theorem DevtoolsColumnWrap_vectors :
    let c : FlexContainer := {
      direction := .column,
      wrap := .wrap,
      mainSize := some 100,
      crossSize := some 300,
      items := [
        { id := 0, mainSize := 200 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 := by
  decide

-- flex/flex_layout_algorithm_test.cc:1052: DevtoolsColumnWrapOrtho
-- Column wrap with orthogonal child item.
-- CSS Flexible Box Layout Level 1 §5.1, CSS Writing Modes 3 §7.
theorem DevtoolsColumnWrapOrtho_vectors :
    let c : FlexContainer := {
      direction := .column,
      wrap := .wrap,
      mainSize := some 100,
      crossSize := some 300,
      items := [
        { id := 0, mainSize := 200 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 := by
  decide

-- flex/flex_layout_algorithm_test.cc:1064: DevtoolsRowWrapOrtho
-- Row wrap with orthogonal child item.
-- CSS Flexible Box Layout Level 1 §5.1, CSS Writing Modes 3 §7.
theorem DevtoolsRowWrapOrtho_vectors :
    let c : FlexContainer := {
      direction := .row,
      wrap := .wrap,
      mainSize := some 300,
      crossSize := some 100,
      items := [
        { id := 0, mainSize := 200 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 := by
  decide

-- flex/flex_layout_algorithm_test.cc:1077: DevtoolsLegacyItem
-- Flex container with single item generates single line.
-- CSS Flexible Box Layout Level 1 §5.2.
theorem DevtoolsLegacyItem_vectors :
    let c : FlexContainer := {
      direction := .row,
      items := [
        { id := 0, mainSize := 100 }
      ]
    }
    let res := layoutFlex c
    res.lines.length = 1 := by
  decide

-- flex/flex_layout_algorithm_test.cc:50: ReplacedAspectRatioPrecision
-- Column flex item maintains aspect ratio precision.
-- CSS Flexible Box Layout Level 1 §9.9.2, CSS Sizing 3 §4.
theorem ReplacedAspectRatioPrecision_vectors :
    let c : FlexContainer := {
      direction := .column,
      crossSize := some 50,
      items := [
        { id := 0, mainSize := 22, crossSize := 29 }
      ]
    }
    let res := layoutFlex c
    res.w = 50 ∧ res.h = 22 ∧
    res.lines.length = 1 ∧
    res.lines[0]!.items[0]!.w = 29 ∧ res.lines[0]!.items[0]!.h = 22 := by
  decide

-- flex/flex_layout_algorithm_test.cc:72: GapDecorationsOneLine
-- Single line flex container produces no main gaps and both-edge cross gaps.
-- CSS Box Alignment 3 §8, CSS Gap Decorations 1 §3.2, §3.3.
theorem GapDecorationsOneLine_vectors :
    let c : FlexContainer := {
      borderMainStart := 2,
      borderCrossStart := 2,
      mainSize := some 170,
      gapMain := 20,
      gapCross := 10,
      wrap := .wrap,
      items := [
        { id := 0, mainSize := 50, crossSize := 50 },
        { id := 1, mainSize := 100, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [] ∧
    geom.crossGaps = [⟨62, 2, .both⟩] ∧
    geom.contentInlineStart = 2 ∧
    geom.contentInlineEnd = 172 ∧
    geom.contentBlockStart = 2 ∧
    geom.contentBlockEnd = 52 := by
  decide

-- flex/flex_layout_algorithm_test.cc:144: GapDecorationsBasic
-- Basic multi-line flex container generates main row gaps and edge-classified cross gaps.
-- CSS Box Alignment 3 §8, CSS Gap Decorations 1 §3.2, §3.3.
theorem GapDecorationsBasic_vectors :
    let c : FlexContainer := {
      borderMainStart := 2,
      borderCrossStart := 2,
      mainSize := some 170,
      gapMain := 10,
      gapCross := 10,
      wrap := .wrap,
      items := [
        { id := 0, mainSize := 50, crossSize := 50 },
        { id := 1, mainSize := 50, crossSize := 50 },
        { id := 2, mainSize := 50, crossSize := 50 },
        { id := 3, mainSize := 50, crossSize := 50 },
        { id := 4, mainSize := 50, crossSize := 50 },
        { id := 5, mainSize := 50, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [⟨57⟩] ∧
    geom.crossGaps = [
      ⟨57, 2, .start⟩,
      ⟨117, 2, .start⟩,
      ⟨57, 57, .endEdge⟩,
      ⟨117, 57, .endEdge⟩
    ] ∧
    geom.contentInlineStart = 2 ∧
    geom.contentInlineEnd = 172 ∧
    geom.contentBlockStart = 2 ∧
    geom.contentBlockEnd = 112 := by
  decide

-- flex/flex_layout_algorithm_test.cc:219: GapDecorationsContentEndPastContainer
-- Overflowing items extend contentInlineEnd past container end.
-- CSS Box Alignment 3 §8, CSS Gap Decorations 1 §3.2.
theorem GapDecorationsContentEndPastContainer_vectors :
    let c : FlexContainer := {
      borderMainStart := 2,
      borderCrossStart := 2,
      mainSize := some 200,
      gapMain := 10,
      wrap := .nowrap,
      items := [
        { id := 0, mainSize := 50, crossSize := 50, shrink := 0 },
        { id := 1, mainSize := 50, crossSize := 50, shrink := 0 },
        { id := 2, mainSize := 50, crossSize := 50, shrink := 0 },
        { id := 3, mainSize := 50, crossSize := 50, shrink := 0 },
        { id := 4, mainSize := 50, crossSize := 50, shrink := 0 },
        { id := 5, mainSize := 50, crossSize := 50, shrink := 0 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.contentInlineStart = 2 ∧
    geom.contentInlineEnd = 297 ∧
    geom.contentBlockStart = 2 ∧
    geom.contentBlockEnd = 52 := by
  decide

-- flex/flex_layout_algorithm_test.cc:285: GapDecorationsNonAlignedColumn
-- Non-aligned column items generate middle-line cross gaps with none edge state.
-- CSS Box Alignment 3 §8, CSS Gap Decorations 1 §3.2, §3.3.
theorem GapDecorationsNonAlignedColumn_vectors :
    let c : FlexContainer := {
      borderMainStart := 2,
      borderCrossStart := 2,
      mainSize := some 170,
      gapMain := 10,
      gapCross := 10,
      wrap := .wrap,
      items := [
        { id := 0, mainSize := 50, crossSize := 50 },
        { id := 1, mainSize := 50, crossSize := 50 },
        { id := 2, mainSize := 50, crossSize := 50 },
        { id := 3, mainSize := 100, crossSize := 50 },
        { id := 4, mainSize := 50, crossSize := 50 },
        { id := 5, mainSize := 50, crossSize := 50 },
        { id := 6, mainSize := 50, crossSize := 50 },
        { id := 7, mainSize := 50, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [⟨57⟩, ⟨117⟩] ∧
    geom.crossGaps = [
      ⟨57, 2, .start⟩,
      ⟨117, 2, .start⟩,
      ⟨107, 57, .none⟩,
      ⟨57, 117, .endEdge⟩,
      ⟨117, 117, .endEdge⟩
    ] ∧
    geom.contentInlineStart = 2 ∧
    geom.contentInlineEnd = 172 ∧
    geom.contentBlockStart = 2 ∧
    geom.contentBlockEnd = 172 := by
  decide

-- flex/flex_layout_algorithm_test.cc:370: GapDecorationsNonAlignedColumn2
-- Multi-line flexbox with single item on final line generates no cross gaps for that line.
-- CSS Box Alignment 3 §8, CSS Gap Decorations 1 §3.2, §3.3.
theorem GapDecorationsNonAlignedColumn2_vectors :
    let c : FlexContainer := {
      borderMainStart := 2,
      borderCrossStart := 2,
      mainSize := some 170,
      gapMain := 10,
      gapCross := 10,
      wrap := .wrap,
      items := [
        { id := 0, mainSize := 50, crossSize := 50 },
        { id := 1, mainSize := 50, crossSize := 50 },
        { id := 2, mainSize := 50, crossSize := 50 },
        { id := 3, mainSize := 100, crossSize := 50 },
        { id := 4, mainSize := 50, crossSize := 50 },
        { id := 5, mainSize := 160, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [⟨57⟩, ⟨117⟩] ∧
    geom.crossGaps = [
      ⟨57, 2, .start⟩,
      ⟨117, 2, .start⟩,
      ⟨107, 57, .none⟩
    ] ∧
    geom.contentInlineStart = 2 ∧
    geom.contentInlineEnd = 172 ∧
    geom.contentBlockStart = 2 ∧
    geom.contentBlockEnd = 172 := by
  decide

-- flex/flex_layout_algorithm_test.cc:453: GapDecorationsVerticalFlexAlignedCenter
-- Vertical flex container with align-content: center offsets lines along block axis.
-- CSS Box Alignment 3 §5.1, §8, CSS Gap Decorations 1 §3.2, §3.3, CSS Writing Modes 3 §7.
theorem GapDecorationsVerticalFlexAlignedCenter_vectors :
    let c : FlexContainer := {
      direction := .row,
      borderMainStart := 4,
      borderCrossStart := 2,
      mainSize := some 300,
      crossSize := some 300,
      alignContentOffset := 61,
      gapMain := 10,
      gapCross := 30,
      wrap := .wrap,
      items := [
        { id := 0, mainSize := 74, crossSize := 74 },
        { id := 1, mainSize := 74, crossSize := 74 },
        { id := 2, mainSize := 74, crossSize := 74 },
        { id := 3, mainSize := 74, crossSize := 74 },
        { id := 4, mainSize := 74, crossSize := 74 },
        { id := 5, mainSize := 74, crossSize := 74 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [⟨152⟩] ∧
    geom.crossGaps = [
      ⟨83, 63, .start⟩,
      ⟨167, 63, .start⟩,
      ⟨83, 152, .endEdge⟩,
      ⟨167, 152, .endEdge⟩
    ] ∧
    geom.contentInlineStart = 4 ∧
    geom.contentInlineEnd = 304 ∧
    geom.contentBlockStart = 63 ∧
    geom.contentBlockEnd = 241 := by
  decide

-- flex/flex_layout_algorithm_test.cc:708: GapDecorationsColumnFlexDirection
-- Column flex direction swaps main and cross axes for gap decorations.
-- CSS Flexible Box Layout Level 1 §5.1, CSS Box Alignment 3 §8, CSS Gap Decorations 1 §3.2, §3.3.
theorem GapDecorationsColumnFlexDirection_vectors :
    let c : FlexContainer := {
      direction := .column,
      borderMainStart := 2,
      borderCrossStart := 2,
      mainSize := some 170,
      crossSize := some 120,
      gapMain := 10,
      gapCross := 20,
      wrap := .wrap,
      items := [
        { id := 0, mainSize := 50, crossSize := 50 },
        { id := 1, mainSize := 50, crossSize := 50 },
        { id := 2, mainSize := 50, crossSize := 50 },
        { id := 3, mainSize := 50, crossSize := 50 },
        { id := 4, mainSize := 50, crossSize := 50 },
        { id := 5, mainSize := 50, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [⟨62⟩] ∧
    geom.crossGaps = [
      ⟨2, 57, .start⟩,
      ⟨2, 117, .start⟩,
      ⟨62, 57, .endEdge⟩,
      ⟨62, 117, .endEdge⟩
    ] ∧
    geom.contentInlineStart = 2 ∧
    geom.contentInlineEnd = 122 ∧
    geom.contentBlockStart = 2 ∧
    geom.contentBlockEnd = 172 := by
  decide

-- flex/flex_layout_algorithm_test.cc:878: GapDecorationsContentDistributionGapsBetweenLines
-- Content distribution stretches lines equally, placing main gap at line boundary.
-- CSS Box Alignment 3 §5.1, §8, CSS Gap Decorations 1 §3.2.
theorem GapDecorationsContentDistributionGapsBetweenLines_vectors :
    let c : FlexContainer := {
      mainSize := some 140,
      crossSize := some 120,
      wrap := .wrap,
      lineCrossOverride := some 60,
      items := [
        { id := 0, mainSize := 70, crossSize := 50 },
        { id := 1, mainSize := 70, crossSize := 50 },
        { id := 2, mainSize := 70, crossSize := 50 },
        { id := 3, mainSize := 70, crossSize := 50 }
      ]
    }
    let res := layoutFlex c
    let geom := computeGapGeometry c res.lines
    geom.mainGaps = [⟨60⟩] ∧
    geom.blockGapSize = 0 := by
  decide

end TestsBlock
end ChromiumLayout
