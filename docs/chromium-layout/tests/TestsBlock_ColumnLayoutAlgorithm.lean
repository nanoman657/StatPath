import ColumnLayout

namespace ChromiumLayout
namespace TestsBlock

open ColumnLayout

-- column_layout_algorithm_test.cc:73: EmptyMulticol
def emptyMulticol_input : Multicol :=
  { cols := 2, gap := 10, width := 210, height := 100 }

theorem EmptyMulticol_vectors :
    let res := layoutMulticol emptyMulticol_input
    res.w = 210 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 1 ∧
    (res.columns[0]!).w = 100 ∧ (res.columns[0]!).h = 100 ∧
    (res.columns[0]!).slices.length = 0 := by
  decide

-- column_layout_algorithm_test.cc:111: EmptyBlock
def emptyBlock_input : Multicol :=
  { cols := 2, gap := 10, width := 210, height := 100,
    children := [ { id := 1, width := .auto, height := 0 } ] }

theorem EmptyBlock_vectors :
    let res := layoutMulticol emptyBlock_input
    res.columns.length = 1 ∧
    let col0 := res.columns[0]!
    col0.relX = 0 ∧ col0.relY = 0 ∧ col0.w = 100 ∧ col0.h = 100 ∧
    col0.slices.length = 1 ∧
    let s0 := col0.slices[0]!
    s0.relX = 0 ∧ s0.relY = 0 ∧ s0.w = 100 ∧ s0.h = 0 := by
  decide

-- column_layout_algorithm_test.cc:160: BlockInOneColumn
def blockInOneColumn_input : Multicol :=
  { cols := 2, gap := 10, width := 310, height := 100,
    children := [ { id := 1, width := .pct 60, height := 100 } ] }

theorem BlockInOneColumn_vectors :
    let res := layoutMulticol blockInOneColumn_input
    res.colWidth = 150 ∧ res.columns.length = 1 ∧
    let col0 := res.columns[0]!
    col0.w = 150 ∧ col0.h = 100 ∧
    col0.slices.length = 1 ∧
    let s0 := col0.slices[0]!
    s0.w = 90 ∧ s0.h = 100 ∧ s0.relX = 0 ∧ s0.relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:210: ZeroHeightBlockAtFragmentainerBoundary
def zeroHeightBlockAtFragmentainerBoundary_input : Multicol :=
  { cols := 2, gap := 10, width := 210, height := 100,
    children := [
      { id := 1, width := .px 33, height := 200 },
      { id := 2, width := .px 44, height := 0 }
    ] }

theorem ZeroHeightBlockAtFragmentainerBoundary_vectors :
    let res := layoutMulticol zeroHeightBlockAtFragmentainerBoundary_input
    res.columns.length = 2 ∧
    let col0 := res.columns[0]!
    let col1 := res.columns[1]!
    col0.relX = 0 ∧ col0.w = 100 ∧ col0.h = 100 ∧
    col1.relX = 110 ∧ col1.w = 100 ∧ col1.h = 100 ∧
    col0.slices.length = 1 ∧
    (col0.slices[0]!).w = 33 ∧ (col0.slices[0]!).h = 100 ∧
    col1.slices.length = 2 ∧
    (col1.slices[0]!).w = 33 ∧ (col1.slices[0]!).h = 100 ∧
    (col1.slices[1]!).w = 44 ∧ (col1.slices[1]!).h = 0 ∧
    (col1.slices[1]!).relY = 100 := by
  decide

-- column_layout_algorithm_test.cc:242: BlockInTwoColumns
def blockInTwoColumns_input : Multicol :=
  { cols := 2, gap := 10, width := 210, height := 100,
    children := [ { id := 1, width := .pct 75, height := 150 } ] }

theorem BlockInTwoColumns_vectors :
    let res := layoutMulticol blockInTwoColumns_input
    res.columns.length = 2 ∧
    let col0 := res.columns[0]!
    let col1 := res.columns[1]!
    col0.relX = 0 ∧ col1.relX = 110 ∧
    col0.slices.length = 1 ∧ (col0.slices[0]!).w = 75 ∧ (col0.slices[0]!).h = 100 ∧
    col1.slices.length = 1 ∧ (col1.slices[0]!).w = 75 ∧ (col1.slices[0]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:272: BlockInThreeColumns
def blockInThreeColumns_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .pct 75, height := 250 } ] }

theorem BlockInThreeColumns_vectors :
    let res := layoutMulticol blockInThreeColumns_input
    res.columns.length = 3 ∧
    let col0 := res.columns[0]!
    let col1 := res.columns[1]!
    let col2 := res.columns[2]!
    col0.relX = 0 ∧ col1.relX = 110 ∧ col2.relX = 220 ∧
    (col0.slices[0]!).w = 75 ∧ (col0.slices[0]!).h = 100 ∧
    (col1.slices[0]!).w = 75 ∧ (col1.slices[0]!).h = 100 ∧
    (col2.slices[0]!).w = 75 ∧ (col2.slices[0]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:304: ActualColumnCountGreaterThanSpecified
def actualColumnCountGreaterThanSpecified_input : Multicol :=
  { cols := 2, gap := 10, width := 210, height := 100,
    children := [ { id := 1, width := .px 1, height := 250 } ] }

theorem ActualColumnCountGreaterThanSpecified_vectors :
    let res := layoutMulticol actualColumnCountGreaterThanSpecified_input
    res.columns.length = 3 ∧
    let col0 := res.columns[0]!
    let col1 := res.columns[1]!
    let col2 := res.columns[2]!
    col0.relX = 0 ∧ col1.relX = 110 ∧ col2.relX = 220 ∧
    (col0.slices[0]!).w = 1 ∧ (col0.slices[0]!).h = 100 ∧
    (col1.slices[0]!).w = 1 ∧ (col1.slices[0]!).h = 100 ∧
    (col2.slices[0]!).w = 1 ∧ (col2.slices[0]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:336: TwoBlocksInTwoColumns
def twoBlocksInTwoColumns_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [
      { id := 1, width := .pct 75, height := 60 },
      { id := 2, width := .pct 85, height := 60 }
    ] }

theorem TwoBlocksInTwoColumns_vectors :
    let res := layoutMulticol twoBlocksInTwoColumns_input
    res.columns.length = 2 ∧
    let col0 := res.columns[0]!
    let col1 := res.columns[1]!
    col0.relX = 0 ∧ col1.relX = 110 ∧
    col0.slices.length = 2 ∧
    (col0.slices[0]!).w = 75 ∧ (col0.slices[0]!).h = 60 ∧ (col0.slices[0]!).relY = 0 ∧
    (col0.slices[1]!).w = 85 ∧ (col0.slices[1]!).h = 40 ∧ (col0.slices[1]!).relY = 60 ∧
    col1.slices.length = 1 ∧
    (col1.slices[0]!).w = 85 ∧ (col1.slices[0]!).h = 20 ∧ (col1.slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:368: ZeroHeight
def zeroHeight_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 0 }

theorem ZeroHeight_vectors :
    let res := layoutMulticol zeroHeight_input
    res.columns.length = 1 ∧
    let col0 := res.columns[0]!
    col0.relX = 0 ∧ col0.w = 100 ∧ col0.h = 0 ∧ col0.slices.length = 0 := by
  decide

-- column_layout_algorithm_test.cc:393: ZeroHeightWithContent
def zeroHeightWithContent_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 0,
    children := [ { id := 1, width := .px 20, height := 5 } ] }

theorem ZeroHeightWithContent_vectors :
    let res := layoutMulticol zeroHeightWithContent_input
    res.columns.length = 5 ∧
    let c0 := res.columns[0]!
    let c1 := res.columns[1]!
    let c2 := res.columns[2]!
    let c3 := res.columns[3]!
    let c4 := res.columns[4]!
    c0.relX = 0 ∧ c0.w = 100 ∧ c0.h = 0 ∧
    c1.relX = 110 ∧ c1.w = 100 ∧ c1.h = 0 ∧
    c2.relX = 220 ∧ c2.w = 100 ∧ c2.h = 0 ∧
    c3.relX = 330 ∧ c3.w = 100 ∧ c3.h = 0 ∧
    c4.relX = 440 ∧ c4.w = 100 ∧ c4.h = 0 ∧
    (c0.slices[0]!).w = 20 ∧ (c0.slices[0]!).h = 1 ∧
    (c1.slices[0]!).w = 20 ∧ (c1.slices[0]!).h = 1 ∧
    (c2.slices[0]!).w = 20 ∧ (c2.slices[0]!).h = 1 ∧
    (c3.slices[0]!).w = 20 ∧ (c3.slices[0]!).h = 1 ∧
    (c4.slices[0]!).w = 20 ∧ (c4.slices[0]!).h = 1 := by
  decide

end TestsBlock
end ChromiumLayout
