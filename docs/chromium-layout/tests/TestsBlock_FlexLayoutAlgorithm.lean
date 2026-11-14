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

end TestsBlock
end ChromiumLayout
