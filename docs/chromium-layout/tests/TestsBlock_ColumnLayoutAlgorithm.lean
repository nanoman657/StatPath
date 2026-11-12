import ColumnLayout
import ColumnBreak

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

-- column_layout_algorithm_test.cc:2361: BorderAndPadding
def borderAndPadding_input : Multicol := {
  cols := 3,
  gap := 10,
  width := 320,
  height := 100,
  border := 3,
  padding := 2,
  children := [{ id := 0, width := .px 30, height := 150 }]
}

theorem BorderAndPadding_vectors :
    let res := layoutMulticol borderAndPadding_input
    res.w = 330 ∧ res.h = 110 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).colIdx = 0 ∧ (res.columns[0]!).relX = 5 ∧ (res.columns[0]!).relY = 5 ∧
    (res.columns[0]!).w = 100 ∧ (res.columns[0]!).h = 100 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).relX = 0 ∧ ((res.columns[0]!).slices[0]!).relY = 0 ∧
    ((res.columns[0]!).slices[0]!).w = 30 ∧ ((res.columns[0]!).slices[0]!).h = 100 ∧
    (res.columns[1]!).colIdx = 1 ∧ (res.columns[1]!).relX = 115 ∧ (res.columns[1]!).relY = 5 ∧
    (res.columns[1]!).w = 100 ∧ (res.columns[1]!).h = 100 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).relX = 0 ∧ ((res.columns[1]!).slices[0]!).relY = 0 ∧
    ((res.columns[1]!).slices[0]!).w = 30 ∧ ((res.columns[1]!).slices[0]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:429: OverflowedBlock
theorem OverflowedBlock_vectors :
    let nodes := [
      BNode.box (.pct 75) .auto [
        BNode.leaf (.px 50) 120,
        BNode.leaf (.px 40) 20
      ] (some 60),
      BNode.leaf (.pct 85) 10
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 75 ∧ res[0]!.h = 60 ∧
    res[0]!.kids.length = 1 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 50 ∧ res[0]!.kids[0]!.h = 100 ∧
    res[1]!.col = 0 ∧ res[1]!.y = 60 ∧ res[1]!.w = 85 ∧ res[1]!.h = 10 ∧
    res[2]!.col = 1 ∧ res[2]!.y = 0 ∧ res[2]!.w = 75 ∧ res[2]!.h = 0 ∧
    res[2]!.kids.length = 2 ∧
    res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 50 ∧ res[2]!.kids[0]!.h = 20 ∧
    res[2]!.kids[1]!.y = 20 ∧ res[2]!.kids[1]!.w = 40 ∧ res[2]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:467: OverflowedBlock2
theorem OverflowedBlock2_vectors :
    let nodes := [
      BNode.box (.pct 75) .auto [BNode.leaf (.px 50) 220] (some 10),
      BNode.leaf (.pct 85) 10,
      BNode.box (.pct 65) .auto [BNode.leaf (.px 51) 220] (some 10)
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 7 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 75 ∧ res[0]!.h = 10 ∧
    res[0]!.kids.length = 1 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 50 ∧ res[0]!.kids[0]!.h = 100 ∧
    res[1]!.col = 0 ∧ res[1]!.y = 10 ∧ res[1]!.w = 85 ∧ res[1]!.h = 10 ∧
    res[2]!.col = 0 ∧ res[2]!.y = 20 ∧ res[2]!.w = 65 ∧ res[2]!.h = 10 ∧
    res[2]!.kids.length = 1 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 51 ∧ res[2]!.kids[0]!.h = 80 ∧
    res[3]!.col = 1 ∧ res[3]!.y = 0 ∧ res[3]!.w = 75 ∧ res[3]!.h = 0 ∧
    res[3]!.kids.length = 1 ∧ res[3]!.kids[0]!.y = 0 ∧ res[3]!.kids[0]!.w = 50 ∧ res[3]!.kids[0]!.h = 100 ∧
    res[4]!.col = 1 ∧ res[4]!.y = 0 ∧ res[4]!.w = 65 ∧ res[4]!.h = 0 ∧
    res[4]!.kids.length = 1 ∧ res[4]!.kids[0]!.y = 0 ∧ res[4]!.kids[0]!.w = 51 ∧ res[4]!.kids[0]!.h = 100 ∧
    res[5]!.col = 2 ∧ res[5]!.y = 0 ∧ res[5]!.w = 75 ∧ res[5]!.h = 0 ∧
    res[5]!.kids.length = 1 ∧ res[5]!.kids[0]!.y = 0 ∧ res[5]!.kids[0]!.w = 50 ∧ res[5]!.kids[0]!.h = 20 ∧
    res[6]!.col = 2 ∧ res[6]!.y = 0 ∧ res[6]!.w = 65 ∧ res[6]!.h = 0 ∧
    res[6]!.kids.length = 1 ∧ res[6]!.kids[0]!.y = 0 ∧ res[6]!.kids[0]!.w = 51 ∧ res[6]!.kids[0]!.h = 40 := by
  decide

-- column_layout_algorithm_test.cc:515: OverflowedBlock3
theorem OverflowedBlock3_vectors :
    let nodes := [
      BNode.box (.pct 75) .auto [BNode.leaf (.px 50) 220] (some 60),
      BNode.leaf (.pct 85) 10
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 4 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 75 ∧ res[0]!.h = 60 ∧
    res[0]!.kids.length = 1 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 50 ∧ res[0]!.kids[0]!.h = 100 ∧
    res[1]!.col = 0 ∧ res[1]!.y = 60 ∧ res[1]!.w = 85 ∧ res[1]!.h = 10 ∧
    res[2]!.col = 1 ∧ res[2]!.y = 0 ∧ res[2]!.w = 75 ∧ res[2]!.h = 0 ∧
    res[2]!.kids.length = 1 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 50 ∧ res[2]!.kids[0]!.h = 100 ∧
    res[3]!.col = 2 ∧ res[3]!.y = 0 ∧ res[3]!.w = 75 ∧ res[3]!.h = 0 ∧
    res[3]!.kids.length = 1 ∧ res[3]!.kids[0]!.y = 0 ∧ res[3]!.kids[0]!.w = 50 ∧ res[3]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:554: UnusedSpaceInBlock
theorem UnusedSpaceInBlock_vectors :
    let nodes := [
      BNode.box .auto .auto [BNode.leaf (.px 20) 20] (some 300)
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 100 ∧
    res[0]!.kids.length = 1 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 20 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 100 ∧
    res[1]!.kids.isEmpty = true ∧
    res[2]!.col = 2 ∧ res[2]!.y = 0 ∧ res[2]!.w = 100 ∧ res[2]!.h = 100 ∧
    res[2]!.kids.isEmpty = true := by
  decide

-- column_layout_algorithm_test.cc:617: TwoFloatsInOneColumn
theorem TwoFloatsInOneColumn_vectors :
    let nodes := [
      BNode.leaf (.pct 15) 100 .auto .left,
      BNode.leaf (.pct 16) 100 .auto .right
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 15 ∧ res[0]!.h = 100 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 84 ∧ res[1]!.y = 0 ∧ res[1]!.w = 16 ∧ res[1]!.h = 100 := by
  decide

-- column_layout_algorithm_test.cc:647: TwoFloatsInTwoColumns
theorem TwoFloatsInTwoColumns_vectors :
    let nodes := [
      BNode.leaf (.pct 15) 150 .auto .left,
      BNode.leaf (.pct 16) 150 .auto .right
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 4 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 15 ∧ res[0]!.h = 100 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 84 ∧ res[1]!.y = 0 ∧ res[1]!.w = 16 ∧ res[1]!.h = 100 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 15 ∧ res[2]!.h = 50 ∧
    res[3]!.col = 1 ∧ res[3]!.x = 84 ∧ res[3]!.y = 0 ∧ res[3]!.w = 16 ∧ res[3]!.h = 50 := by
  decide

-- column_layout_algorithm_test.cc:717: FloatWithMargin
theorem FloatWithMargin_vectors :
    let nodes := [
      BNode.leaf (.px 77) 140 .auto .left 10
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 10 ∧ res[0]!.w = 77 ∧ res[0]!.h = 90 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 77 ∧ res[1]!.h = 50 := by
  decide

-- column_layout_algorithm_test.cc:779: FloatWithLastResortBreak
theorem FloatWithLastResortBreak_vectors :
    let nodes := [
      BNode.leaf (.px 99) 90,
      BNode.box (.px 88) .avoid [BNode.leaf (.px 0) 20] none .left
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 99 ∧ res[0]!.h = 90 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 88 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:818: FloatWithAvoidBreak
theorem FloatWithAvoidBreak_vectors :
    let nodes := [
      BNode.leaf (.px 99) 90,
      BNode.box (.px 88) .auto [BNode.leaf (.px 77) 20 .avoid] none .left
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 99 ∧ res[0]!.h = 90 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 88 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 77 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:855: FloatWithMarginAndAvoidBreak
theorem FloatWithMarginAndAvoidBreak_vectors :
    let nodes := [
      BNode.leaf (.px 99) 90,
      BNode.box (.px 88) .auto [BNode.leaf (.px 77) 20 .avoid] none .left 5
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 99 ∧ res[0]!.h = 90 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 5 ∧ res[1]!.w = 88 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 77 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:893: UnbreakableFloatBeforeBreakable
theorem UnbreakableFloatBeforeBreakable_vectors :
    let nodes := [
      BNode.leaf (.px 99) 90,
      BNode.box (.px 22) .auto [BNode.leaf (.px 11) 20 .avoid] (some 50) .left,
      BNode.leaf (.px 33) 50 .auto .left
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 99 ∧ res[0]!.h = 90 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 22 ∧ res[1]!.h = 50 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.w = 11 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 22 ∧ res[2]!.y = 0 ∧ res[2]!.w = 33 ∧ res[2]!.h = 50 := by
  decide

-- column_layout_algorithm_test.cc:1430: LinesInMulticolExtraSpace
theorem LinesInMulticolExtraSpace_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 50 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 50 ∧
    res[0]!.kids.length = 2 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1470: LinesInMulticolExactFit
theorem LinesInMulticolExactFit_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 40 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 40 ∧
    res[0]!.kids.length = 2 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1510: LinesInMulticolChildExtraSpace
theorem LinesInMulticolChildExtraSpace_vectors :
    let nodes := [
      BNode.box (.px 77) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 50 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 77 ∧ res[0]!.h = 50 ∧
    res[0]!.kids.length = 2 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 77 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1552: LinesInMulticolChildExactFit
theorem LinesInMulticolChildExactFit_vectors :
    let nodes := [
      BNode.box (.px 77) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 40 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 77 ∧ res[0]!.h = 40 ∧
    res[0]!.kids.length = 2 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 77 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1594: LinesInMulticolChildNoSpaceForFirst
theorem LinesInMulticolChildNoSpaceForFirst_vectors :
    let nodes := [
      BNode.leaf (.px 100) 50,
      BNode.box (.px 77) .auto (List.replicate 3 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 50 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 50 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 77 ∧ res[1]!.h = 50 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 ∧
    res[2]!.col = 2 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 77 ∧ res[2]!.h = 20 ∧
    res[2]!.kids.length = 1 ∧
    res[2]!.kids[0]!.col = 2 ∧ res[2]!.kids[0]!.x = 0 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 0 ∧ res[2]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1637: LinesInMulticolChildInsufficientSpaceForFirst
theorem LinesInMulticolChildInsufficientSpaceForFirst_vectors :
    let nodes := [
      BNode.leaf (.px 100) 40,
      BNode.box (.px 77) .auto (List.replicate 3 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 50 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 40 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 77 ∧ res[1]!.h = 50 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 ∧
    res[2]!.col = 2 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 77 ∧ res[2]!.h = 20 ∧
    res[2]!.kids.length = 1 ∧
    res[2]!.kids[0]!.col = 2 ∧ res[2]!.kids[0]!.x = 0 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 0 ∧ res[2]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1681: LineAtColumnBoundaryInFirstBlock
theorem LineAtColumnBoundaryInFirstBlock_vectors :
    let nodes := [
      BNode.box (.px 66) .auto [
        BNode.leaf (.px 0) 20 .avoid
      ] none .none 0 false false 0 0 false 1 1 40
    ]
    let res := layoutNodes 50 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 66 ∧ res[0]!.h = 50 ∧ res[0]!.kids.isEmpty ∧
    res[1]!.col = 1 ∧ res[1]!.y = 0 ∧ res[1]!.w = 66 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧
    res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1861: OrphansUnsatisfiable
theorem OrphansUnsatisfiable_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 6 (BNode.leaf (.px 0) 20 .avoid)) none .none 0 false false 0 0 false 100 1
    ]
    let res := layoutNodes 90 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[0]!.kids.length = 4 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[0]!.kids[2]!.col = 0 ∧ res[0]!.kids[2]!.x = 0 ∧ res[0]!.kids[2]!.y = 40 ∧ res[0]!.kids[2]!.w = 0 ∧ res[0]!.kids[2]!.h = 20 ∧
    res[0]!.kids[3]!.col = 0 ∧ res[0]!.kids[3]!.x = 0 ∧ res[0]!.kids[3]!.y = 60 ∧ res[0]!.kids[3]!.w = 0 ∧ res[0]!.kids[3]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1905: Widows
theorem Widows_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 7 (BNode.leaf (.px 0) 20 .avoid)) none .none 0 false false 0 0 false 1 3
    ]
    let res := layoutNodes 110 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 110 ∧
    res[0]!.kids.length = 4 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[0]!.kids[2]!.col = 0 ∧ res[0]!.kids[2]!.x = 0 ∧ res[0]!.kids[2]!.y = 40 ∧ res[0]!.kids[2]!.w = 0 ∧ res[0]!.kids[2]!.h = 20 ∧
    res[0]!.kids[3]!.col = 0 ∧ res[0]!.kids[3]!.x = 0 ∧ res[0]!.kids[3]!.y = 60 ∧ res[0]!.kids[3]!.w = 0 ∧ res[0]!.kids[3]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 60 ∧
    res[1]!.kids.length = 3 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 ∧
    res[1]!.kids[2]!.col = 1 ∧ res[1]!.kids[2]!.x = 0 ∧ res[1]!.kids[2]!.y = 40 ∧ res[1]!.kids[2]!.w = 0 ∧ res[1]!.kids[2]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1951: WidowsUnsatisfiable
theorem WidowsUnsatisfiable_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 14 (BNode.leaf (.px 0) 20 .avoid)) none .none 0 false false 0 0 false 1 100
    ]
    let res := layoutNodes 90 100 5 nodes
    res.length = 5 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[0]!.kids.length = 1 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 90 ∧
    res[1]!.kids.length = 4 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 ∧
    res[1]!.kids[2]!.col = 1 ∧ res[1]!.kids[2]!.x = 0 ∧ res[1]!.kids[2]!.y = 40 ∧ res[1]!.kids[2]!.w = 0 ∧ res[1]!.kids[2]!.h = 20 ∧
    res[1]!.kids[3]!.col = 1 ∧ res[1]!.kids[3]!.x = 0 ∧ res[1]!.kids[3]!.y = 60 ∧ res[1]!.kids[3]!.w = 0 ∧ res[1]!.kids[3]!.h = 20 ∧
    res[2]!.col = 2 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 100 ∧ res[2]!.h = 90 ∧
    res[2]!.kids.length = 4 ∧
    res[3]!.col = 3 ∧ res[3]!.x = 0 ∧ res[3]!.y = 0 ∧ res[3]!.w = 100 ∧ res[3]!.h = 90 ∧
    res[3]!.kids.length = 4 ∧
    res[4]!.col = 4 ∧ res[4]!.x = 0 ∧ res[4]!.y = 0 ∧ res[4]!.w = 100 ∧ res[4]!.h = 20 ∧
    res[4]!.kids.length = 1 ∧
    res[4]!.kids[0]!.col = 4 ∧ res[4]!.kids[0]!.x = 0 ∧ res[4]!.kids[0]!.y = 0 ∧ res[4]!.kids[0]!.w = 0 ∧ res[4]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2017: OrphansAndUnsatisfiableWidows
theorem OrphansAndUnsatisfiableWidows_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid)) none .none 0 false false 0 0 false 2 3
    ]
    let res := layoutNodes 70 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 70 ∧
    res[0]!.kids.length = 2 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 1 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2057: UnsatisfiableOrphansAndWidows
theorem UnsatisfiableOrphansAndWidows_vectors :
    let nodes := [
      BNode.box (.px 100) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid)) none .none 0 false false 0 0 false 4 4
    ]
    let res := layoutNodes 70 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 70 ∧
    res[0]!.kids.length = 3 ∧
    res[0]!.kids[0]!.col = 0 ∧ res[0]!.kids[0]!.x = 0 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 0 ∧ res[0]!.kids[0]!.h = 20 ∧
    res[0]!.kids[1]!.col = 0 ∧ res[0]!.kids[1]!.x = 0 ∧ res[0]!.kids[1]!.y = 20 ∧ res[0]!.kids[1]!.w = 0 ∧ res[0]!.kids[1]!.h = 20 ∧
    res[0]!.kids[2]!.col = 0 ∧ res[0]!.kids[2]!.x = 0 ∧ res[0]!.kids[2]!.y = 40 ∧ res[0]!.kids[2]!.w = 0 ∧ res[0]!.kids[2]!.h = 20 ∧
    res[1]!.col = 1 ∧ res[1]!.x = 0 ∧ res[1]!.y = 0 ∧ res[1]!.w = 100 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧
    res[1]!.kids[0]!.col = 1 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2147: BreakBetweenLinesNotBefore
theorem BreakBetweenLinesNotBefore_vectors :
    let nodes := [
      BNode.leaf (.px 44) 60,
      BNode.box (.px 55) .auto (List.replicate 4 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 44 ∧ res[0]!.h = 60 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 0 ∧ res[1]!.y = 60 ∧ res[1]!.w = 55 ∧ res[1]!.h = 40 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.col = 0 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[1]!.kids[1]!.col = 0 ∧ res[1]!.kids[1]!.x = 0 ∧ res[1]!.kids[1]!.y = 20 ∧ res[1]!.kids[1]!.w = 0 ∧ res[1]!.kids[1]!.h = 20 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 55 ∧ res[2]!.h = 40 ∧
    res[2]!.kids.length = 2 ∧
    res[2]!.kids[0]!.col = 1 ∧ res[2]!.kids[0]!.x = 0 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 0 ∧ res[2]!.kids[0]!.h = 20 ∧
    res[2]!.kids[1]!.col = 1 ∧ res[2]!.kids[1]!.x = 0 ∧ res[2]!.kids[1]!.y = 20 ∧ res[2]!.kids[1]!.w = 0 ∧ res[2]!.kids[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2194: BreakBetweenLinesNotBefore2
theorem BreakBetweenLinesNotBefore2_vectors :
    let nodes := [
      BNode.leaf (.px 44) 80,
      BNode.box (.px 55) .auto (List.replicate 2 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 44 ∧ res[0]!.h = 80 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 0 ∧ res[1]!.y = 80 ∧ res[1]!.w = 55 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧
    res[1]!.kids[0]!.col = 0 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 55 ∧ res[2]!.h = 20 ∧
    res[2]!.kids.length = 1 ∧
    res[2]!.kids[0]!.col = 1 ∧ res[2]!.kids[0]!.x = 0 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 0 ∧ res[2]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2236: BreakBetweenLinesNotBefore3
theorem BreakBetweenLinesNotBefore3_vectors :
    let nodes := [
      BNode.leaf (.px 44) 80,
      BNode.box (.px 55) .auto (List.replicate 2 (BNode.leaf (.px 0) 20 .avoid))
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 44 ∧ res[0]!.h = 80 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 0 ∧ res[1]!.y = 80 ∧ res[1]!.w = 55 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧
    res[1]!.kids[0]!.col = 0 ∧ res[1]!.kids[0]!.x = 0 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 0 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 55 ∧ res[2]!.h = 20 ∧
    res[2]!.kids.length = 1 ∧
    res[2]!.kids[0]!.col = 1 ∧ res[2]!.kids[0]!.x = 0 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 0 ∧ res[2]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2391: BreakInsideWithBorder
theorem BreakInsideWithBorder_vectors :
    let nodes := [
      BNode.leaf .auto 85,
      BNode.box .auto .auto [
        BNode.leaf .auto 10
      ] none .none 0 false false 10 0
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 85 ∧
    res[1]!.col = 0 ∧ res[1]!.y = 85 ∧ res[1]!.w = 100 ∧ res[1]!.h = 15 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.x = 10 ∧ res[1]!.kids[0]!.y = 10 ∧ res[1]!.kids[0]!.w = 80 ∧ res[1]!.kids[0]!.h = 5 ∧
    res[2]!.col = 1 ∧ res[2]!.y = 0 ∧ res[2]!.w = 100 ∧ res[2]!.h = 15 ∧
    res[2]!.kids.length = 1 ∧ res[2]!.kids[0]!.x = 10 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 80 ∧ res[2]!.kids[0]!.h = 5 := by
  decide

-- column_layout_algorithm_test.cc:2480: ForcedBreakInSecondChild
theorem ForcedBreakInSecondChild_vectors :
    let nodes := [
      BNode.leaf (.px 33) 20,
      BNode.box (.px 34) .auto [
        BNode.leaf (.px 35) 20,
        BNode.leaf (.px 36) 20 .auto .none 0 true
      ]
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 33 ∧ res[0]!.h = 20 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 0 ∧ res[1]!.y = 20 ∧ res[1]!.w = 34 ∧ res[1]!.h = 80 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 35 ∧ res[1]!.kids[0]!.h = 20 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 34 ∧ res[2]!.h = 20 ∧
    res[2]!.kids.length = 1 ∧ res[2]!.kids[0]!.y = 0 ∧ res[2]!.kids[0]!.w = 36 ∧ res[2]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2517: ForcedAndUnforcedBreaksAtSameBoundary
theorem ForcedAndUnforcedBreaksAtSameBoundary_vectors :
    let nodes := [
      BNode.box (.px 33) .auto [
        BNode.leaf (.px 10) 70,
        BNode.leaf (.px 20) 20 .auto .none 50 true
      ] none .left,
      BNode.box (.px 34) .auto [
        BNode.leaf (.px 10) 70,
        BNode.leaf (.px 20) 20 .auto .none 50 false
      ] none .left
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 4 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 33 ∧ res[0]!.h = 100 ∧
    res[0]!.kids.length = 1 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 10 ∧ res[0]!.kids[0]!.h = 70 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 33 ∧ res[1]!.y = 0 ∧ res[1]!.w = 34 ∧ res[1]!.h = 100 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 10 ∧ res[1]!.kids[0]!.h = 70 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 33 ∧ res[2]!.h = 70 ∧
    res[2]!.kids.length = 1 ∧ res[2]!.kids[0]!.y = 50 ∧ res[2]!.kids[0]!.w = 20 ∧ res[2]!.kids[0]!.h = 20 ∧
    res[3]!.col = 1 ∧ res[3]!.x = 33 ∧ res[3]!.y = 0 ∧ res[3]!.w = 34 ∧ res[3]!.h = 20 ∧
    res[3]!.kids.length = 1 ∧ res[3]!.kids[0]!.y = 0 ∧ res[3]!.kids[0]!.w = 20 ∧ res[3]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2568: ResumeInsideFormattingContextRoot
theorem ResumeInsideFormattingContextRoot_vectors :
    let nodes := [
      BNode.box (.px 33) .auto [
        BNode.leaf (.px 10) 70,
        BNode.leaf (.px 20) 20 .auto .none 50
      ]
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 33 ∧ res[0]!.h = 100 ∧
    res[0]!.kids.length = 1 ∧ res[0]!.kids[0]!.y = 0 ∧ res[0]!.kids[0]!.w = 10 ∧ res[0]!.kids[0]!.h = 70 ∧
    res[1]!.col = 1 ∧ res[1]!.y = 0 ∧ res[1]!.w = 33 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.y = 0 ∧ res[1]!.kids[0]!.w = 20 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2665: NewFcBelowFloat
theorem NewFcBelowFloat_vectors :
    let nodes := [
      BNode.leaf (.px 22) 50 .auto .left,
      BNode.leaf (.px 88) 70 .auto .none 40 false false true
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.x = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 22 ∧ res[0]!.h = 50 ∧
    res[1]!.col = 0 ∧ res[1]!.x = 0 ∧ res[1]!.y = 50 ∧ res[1]!.w = 88 ∧ res[1]!.h = 50 ∧
    res[2]!.col = 1 ∧ res[2]!.x = 0 ∧ res[2]!.y = 0 ∧ res[2]!.w = 88 ∧ res[2]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:4415: Spanner
def spanner_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, border := 1,
  items := (List.replicate 5 { height := 20, avoid := true }) ++
           [{ isSpanner := true, height := 44, width := .auto }] ++
           (List.replicate 5 { height := 20, avoid := true })
}

theorem Spanner_vectors :
    let res := layoutMulticolWithSpanners spanner_input
    res.w = 322 ∧ res.h = 126 ∧ res.fragments.length = 7 ∧
    (res.fragments[0]!).relX = 1 ∧ (res.fragments[0]!).relY = 1 ∧ (res.fragments[0]!).w = 100 ∧ (res.fragments[0]!).h = 40 ∧
    (res.fragments[1]!).relX = 111 ∧ (res.fragments[1]!).relY = 1 ∧ (res.fragments[1]!).w = 100 ∧ (res.fragments[1]!).h = 40 ∧
    (res.fragments[2]!).relX = 221 ∧ (res.fragments[2]!).relY = 1 ∧ (res.fragments[2]!).w = 100 ∧ (res.fragments[2]!).h = 40 ∧
    (res.fragments[3]!).isSpanner = true ∧
    (res.fragments[3]!).relX = 1 ∧ (res.fragments[3]!).relY = 41 ∧ (res.fragments[3]!).w = 320 ∧ (res.fragments[3]!).h = 44 ∧
    (res.fragments[4]!).relX = 1 ∧ (res.fragments[4]!).relY = 85 ∧ (res.fragments[4]!).w = 100 ∧ (res.fragments[4]!).h = 40 ∧
    (res.fragments[5]!).relX = 111 ∧ (res.fragments[5]!).relY = 85 ∧ (res.fragments[5]!).w = 100 ∧ (res.fragments[5]!).h = 40 ∧
    (res.fragments[6]!).relX = 221 ∧ (res.fragments[6]!).relY = 85 ∧ (res.fragments[6]!).w = 100 ∧ (res.fragments[6]!).h = 40 := by
  decide

-- column_layout_algorithm_test.cc:4468: SpannerWithContent
def spannerWithContent_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, border := 1,
  items := (List.replicate 5 { height := 20, avoid := true }) ++
           [{ isSpanner := true, height := 62, width := .auto }] ++
           (List.replicate 5 { height := 20, avoid := true })
}

theorem SpannerWithContent_vectors :
    let res := layoutMulticolWithSpanners spannerWithContent_input
    res.w = 322 ∧ res.h = 144 ∧ res.fragments.length = 7 ∧
    (res.fragments[0]!).relX = 1 ∧ (res.fragments[0]!).relY = 1 ∧ (res.fragments[0]!).w = 100 ∧ (res.fragments[0]!).h = 40 ∧
    (res.fragments[3]!).isSpanner = true ∧
    (res.fragments[3]!).relX = 1 ∧ (res.fragments[3]!).relY = 41 ∧ (res.fragments[3]!).w = 320 ∧ (res.fragments[3]!).h = 62 ∧
    (res.fragments[4]!).relX = 1 ∧ (res.fragments[4]!).relY = 103 ∧ (res.fragments[4]!).w = 100 ∧ (res.fragments[4]!).h = 40 := by
  decide

-- column_layout_algorithm_test.cc:4528: TwoSpannersPercentWidth
def twoSpannersPercentWidth_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, border := 1,
  items := (List.replicate 5 { height := 20, avoid := true }) ++
           [{ isSpanner := true, height := 44, width := .pct 50 },
            { isSpanner := true, height := 1, width := .pct 50 }] ++
           (List.replicate 5 { height := 20, avoid := true })
}

theorem TwoSpannersPercentWidth_vectors :
    let res := layoutMulticolWithSpanners twoSpannersPercentWidth_input
    res.w = 322 ∧ res.h = 127 ∧ res.fragments.length = 8 ∧
    (res.fragments[3]!).w = 160 ∧ (res.fragments[3]!).h = 44 ∧ (res.fragments[3]!).relY = 41 ∧
    (res.fragments[4]!).w = 160 ∧ (res.fragments[4]!).h = 1 ∧ (res.fragments[4]!).relY = 85 ∧
    (res.fragments[5]!).relX = 1 ∧ (res.fragments[5]!).relY = 86 ∧ (res.fragments[5]!).h = 40 ∧
    (res.fragments[6]!).relX = 111 ∧ (res.fragments[6]!).relY = 86 ∧ (res.fragments[6]!).h = 40 ∧
    (res.fragments[7]!).relX = 221 ∧ (res.fragments[7]!).relY = 86 ∧ (res.fragments[7]!).h = 40 := by
  decide

-- column_layout_algorithm_test.cc:4583: SpannerNoBalancing
def spannerNoBalancing_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, height := 200, border := 1, fillAuto := true,
  items := (List.replicate 5 { height := 20, avoid := true }) ++
           [{ isSpanner := true, height := 44, width := .auto }] ++
           (List.replicate 5 { height := 20, avoid := true })
}

theorem SpannerNoBalancing_vectors :
    let res := layoutMulticolWithSpanners spannerNoBalancing_input
    res.w = 322 ∧ res.h = 202 ∧
    (res.fragments[3]!).isSpanner = true ∧
    (res.fragments[3]!).relY = 41 ∧ (res.fragments[3]!).w = 320 ∧ (res.fragments[3]!).h = 44 ∧
    (res.fragments[4]!).relX = 1 ∧ (res.fragments[4]!).relY = 85 ∧ (res.fragments[4]!).w = 100 ∧ (res.fragments[4]!).h = 116 ∧
    (res.fragments[4]!).slices.length = 5 := by
  decide

-- column_layout_algorithm_test.cc:4638: SpannerAtStart
def spannerAtStart_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, border := 1,
  items := [{ isSpanner := true, height := 44, width := .auto }] ++
           (List.replicate 5 { height := 20, avoid := true })
}

theorem SpannerAtStart_vectors :
    let res := layoutMulticolWithSpanners spannerAtStart_input
    res.w = 322 ∧ res.h = 86 ∧ res.fragments.length = 5 ∧
    (res.fragments[0]!).isSpanner = false ∧ (res.fragments[0]!).relX = 1 ∧ (res.fragments[0]!).relY = 1 ∧ (res.fragments[0]!).h = 0 ∧
    (res.fragments[1]!).isSpanner = true ∧ (res.fragments[1]!).relX = 1 ∧ (res.fragments[1]!).relY = 1 ∧ (res.fragments[1]!).w = 320 ∧ (res.fragments[1]!).h = 44 ∧
    (res.fragments[2]!).relX = 1 ∧ (res.fragments[2]!).relY = 45 ∧ (res.fragments[2]!).h = 40 ∧
    (res.fragments[3]!).relX = 111 ∧ (res.fragments[3]!).relY = 45 ∧ (res.fragments[3]!).h = 40 ∧
    (res.fragments[4]!).relX = 221 ∧ (res.fragments[4]!).relY = 45 ∧ (res.fragments[4]!).h = 40 := by
  decide

-- column_layout_algorithm_test.cc:4679: SpannerAtEnd
def spannerAtEnd_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, border := 1,
  items := (List.replicate 5 { height := 20, avoid := true }) ++
           [{ isSpanner := true, height := 44, width := .auto }]
}

theorem SpannerAtEnd_vectors :
    let res := layoutMulticolWithSpanners spannerAtEnd_input
    res.w = 322 ∧ res.h = 86 ∧ res.fragments.length = 4 ∧
    (res.fragments[0]!).relX = 1 ∧ (res.fragments[0]!).relY = 1 ∧ (res.fragments[0]!).h = 40 ∧
    (res.fragments[1]!).relX = 111 ∧ (res.fragments[1]!).relY = 1 ∧ (res.fragments[1]!).h = 40 ∧
    (res.fragments[2]!).relX = 221 ∧ (res.fragments[2]!).relY = 1 ∧ (res.fragments[2]!).h = 40 ∧
    (res.fragments[3]!).isSpanner = true ∧ (res.fragments[3]!).relX = 1 ∧ (res.fragments[3]!).relY = 41 ∧ (res.fragments[3]!).w = 320 ∧ (res.fragments[3]!).h = 44 := by
  decide

-- column_layout_algorithm_test.cc:4719: SpannerAlone
def spannerAlone_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, border := 1,
  items := [{ isSpanner := true, height := 44, width := .auto }]
}

theorem SpannerAlone_vectors :
    let res := layoutMulticolWithSpanners spannerAlone_input
    res.w = 322 ∧ res.h = 46 ∧ res.fragments.length = 2 ∧
    (res.fragments[0]!).isSpanner = false ∧ (res.fragments[0]!).relX = 1 ∧ (res.fragments[0]!).relY = 1 ∧ (res.fragments[0]!).h = 0 ∧
    (res.fragments[1]!).isSpanner = true ∧ (res.fragments[1]!).relX = 1 ∧ (res.fragments[1]!).relY = 1 ∧ (res.fragments[1]!).w = 320 ∧ (res.fragments[1]!).h = 44 := by
  decide

-- column_layout_algorithm_test.cc:4866: SpannerMargins
def spannerMargins_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320,
  items := [
    { isSpanner := true, height := 10, width := .px 33, marginTop := 10, marginBottom := 10, marginStart := 10 },
    { height := 20, avoid := true },
    { isSpanner := true, height := 10, width := .px 44, marginTop := 10, marginBottom := 10, autoMargin := true },
    { isSpanner := true, height := 0, width := .px 55, marginTop := 20, marginBottom := 20, marginStart := 20 },
    { isSpanner := true, height := 10, width := .px 66, marginTop := 10, marginBottom := 10, marginStart := 10 }
  ]
}

theorem SpannerMargins_vectors :
    let res := layoutMulticolWithSpanners spannerMargins_input
    res.w = 320 ∧ res.h = 130 ∧ res.fragments.length = 6 ∧
    (res.fragments[0]!).h = 0 ∧
    (res.fragments[1]!).relX = 10 ∧ (res.fragments[1]!).relY = 10 ∧ (res.fragments[1]!).w = 33 ∧ (res.fragments[1]!).h = 10 ∧
    (res.fragments[2]!).relX = 0 ∧ (res.fragments[2]!).relY = 30 ∧ (res.fragments[2]!).w = 100 ∧ (res.fragments[2]!).h = 20 ∧
    (res.fragments[3]!).relX = 138 ∧ (res.fragments[3]!).relY = 60 ∧ (res.fragments[3]!).w = 44 ∧ (res.fragments[3]!).h = 10 ∧
    (res.fragments[4]!).relX = 20 ∧ (res.fragments[4]!).relY = 90 ∧ (res.fragments[4]!).w = 55 ∧ (res.fragments[4]!).h = 0 ∧
    (res.fragments[5]!).relX = 10 ∧ (res.fragments[5]!).relY = 110 ∧ (res.fragments[5]!).w = 66 ∧ (res.fragments[5]!).h = 10 := by
  decide

-- column_layout_algorithm_test.cc:4902: SpannerMarginsRtl
def spannerMarginsRtl_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, isRtl := true,
  items := [
    { isSpanner := true, height := 10, width := .px 33, marginTop := 10, marginBottom := 10, marginStart := 10 },
    { height := 20, avoid := true },
    { isSpanner := true, height := 10, width := .px 44, marginTop := 10, marginBottom := 10, autoMargin := true },
    { isSpanner := true, height := 0, width := .px 55, marginTop := 20, marginBottom := 20, marginStart := 20 },
    { isSpanner := true, height := 10, width := .px 66, marginTop := 10, marginBottom := 10, marginStart := 10 }
  ]
}

theorem SpannerMarginsRtl_vectors :
    let res := layoutMulticolWithSpanners spannerMarginsRtl_input
    res.w = 320 ∧ res.h = 130 ∧ res.fragments.length = 6 ∧
    (res.fragments[0]!).relX = 220 ∧ (res.fragments[0]!).h = 0 ∧
    (res.fragments[1]!).relX = 277 ∧ (res.fragments[1]!).relY = 10 ∧ (res.fragments[1]!).w = 33 ∧ (res.fragments[1]!).h = 10 ∧
    (res.fragments[2]!).relX = 220 ∧ (res.fragments[2]!).relY = 30 ∧ (res.fragments[2]!).w = 100 ∧ (res.fragments[2]!).h = 20 ∧
    (res.fragments[3]!).relX = 138 ∧ (res.fragments[3]!).relY = 60 ∧ (res.fragments[3]!).w = 44 ∧ (res.fragments[3]!).h = 10 ∧
    (res.fragments[4]!).relX = 245 ∧ (res.fragments[4]!).relY = 90 ∧ (res.fragments[4]!).w = 55 ∧ (res.fragments[4]!).h = 0 ∧
    (res.fragments[5]!).relX = 244 ∧ (res.fragments[5]!).relY = 110 ∧ (res.fragments[5]!).w = 66 ∧ (res.fragments[5]!).h = 10 := by
  decide

-- column_layout_algorithm_test.cc:4939: FixedSizeMulticolWithSpanner
def fixedSizeMulticolWithSpanner_input : MulticolWithSpanners := {
  cols := 3, gap := 10, width := 320, height := 300, fillAuto := true,
  items := [
    { height := 300, width := .px 33 },
    { isSpanner := true, height := 50, width := .px 44 },
    { height := 450, width := .px 55 }
  ]
}

theorem FixedSizeMulticolWithSpanner_vectors :
    let res := layoutMulticolWithSpanners fixedSizeMulticolWithSpanner_input
    res.w = 320 ∧ res.h = 300 ∧ res.fragments.length = 7 ∧
    (res.fragments[0]!).relX = 0 ∧ (res.fragments[0]!).relY = 0 ∧ (res.fragments[0]!).w = 100 ∧ (res.fragments[0]!).h = 100 ∧
    (res.fragments[1]!).relX = 110 ∧ (res.fragments[1]!).relY = 0 ∧ (res.fragments[1]!).w = 100 ∧ (res.fragments[1]!).h = 100 ∧
    (res.fragments[2]!).relX = 220 ∧ (res.fragments[2]!).relY = 0 ∧ (res.fragments[2]!).w = 100 ∧ (res.fragments[2]!).h = 100 ∧
    (res.fragments[3]!).isSpanner = true ∧
    (res.fragments[3]!).relX = 0 ∧ (res.fragments[3]!).relY = 100 ∧ (res.fragments[3]!).w = 44 ∧ (res.fragments[3]!).h = 50 ∧
    (res.fragments[4]!).relX = 0 ∧ (res.fragments[4]!).relY = 150 ∧ (res.fragments[4]!).w = 100 ∧ (res.fragments[4]!).h = 150 ∧
    (res.fragments[5]!).relX = 110 ∧ (res.fragments[5]!).relY = 150 ∧ (res.fragments[5]!).w = 100 ∧ (res.fragments[5]!).h = 150 ∧
    (res.fragments[6]!).relX = 220 ∧ (res.fragments[6]!).relY = 150 ∧ (res.fragments[6]!).w = 100 ∧ (res.fragments[6]!).h = 150 := by
  decide

-- Column balancing. Container border and padding (5px) and child overflow are omitted;
-- the checks are on column offsets, sizes and the container's content height.
-- One breakable 150px child in three 100px columns with a 10px gap.
def balance150_children : List ColChild := [ { id := 1, width := .px 30, height := 150 } ]
-- One 100px child (auto width) in three columns.
def balance100_children : List ColChild := [ { id := 1, height := 100 } ]

-- column_layout_algorithm_test.cc:2799: ColumnBalancing
theorem ColumnBalancing_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 none none balance150_children
    res.h = 50 ∧ res.w = 320 ∧ res.colWidth = 100 ∧ res.columns.length = 3 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧ (res.columns[2]!).relX = 220 ∧
    (res.columns[0]!).h = 50 ∧ (res.columns[1]!).h = 50 ∧ (res.columns[2]!).h = 50 ∧
    (res.columns[0]!).slices.length = 1 ∧ (res.columns[2]!).slices.length = 1 := by
  decide

-- column_layout_algorithm_test.cc:2829: ColumnBalancingFixedHeightExactMatch
theorem ColumnBalancingFixedHeightExactMatch_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 (some 50) none balance150_children
    res.h = 50 ∧ res.columns.length = 3 ∧
    (res.columns[0]!).h = 50 ∧ (res.columns[1]!).h = 50 ∧ (res.columns[2]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:2860: ColumnBalancingFixedHeightLessContent
theorem ColumnBalancingFixedHeightLessContent_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 (some 100) none balance150_children
    res.h = 100 ∧ res.columns.length = 3 ∧
    (res.columns[0]!).h = 50 ∧ (res.columns[1]!).h = 50 ∧ (res.columns[2]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:2891: ColumnBalancingFixedHeightOverflowingContent
theorem ColumnBalancingFixedHeightOverflowingContent_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 (some 35) none balance150_children
    res.h = 35 ∧ res.columns.length = 5 ∧
    (res.columns[0]!).h = 35 ∧ (res.columns[4]!).h = 35 ∧
    ((res.columns[4]!).slices[0]!).h = 10 := by
  decide

-- column_layout_algorithm_test.cc:2927: ColumnBalancingMinHeight
theorem ColumnBalancingMinHeight_vectors :
    let res := layoutMulticolBalanced 3 10 320 70 none none balance150_children
    res.h = 70 ∧ res.columns.length = 3 ∧
    (res.columns[0]!).h = 50 ∧ (res.columns[1]!).h = 50 ∧ (res.columns[2]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:2960: ColumnBalancingMaxHeight
theorem ColumnBalancingMaxHeight_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 none (some 40) balance150_children
    res.h = 40 ∧ res.columns.length = 4 ∧
    (res.columns[0]!).h = 40 ∧ (res.columns[3]!).h = 40 ∧
    ((res.columns[3]!).slices[0]!).h = 30 := by
  decide

-- column_layout_algorithm_test.cc:2993: ColumnBalancingMinHeightLargerThanMaxHeight
theorem ColumnBalancingMinHeightLargerThanMaxHeight_vectors :
    let res := layoutMulticolBalanced 3 10 320 70 none (some 50) balance150_children
    res.h = 70 ∧ res.columns.length = 3 ∧
    (res.columns[0]!).h = 50 ∧ (res.columns[2]!).h = 50 := by
  decide

-- column_layout_algorithm_test.cc:3027: ColumnBalancingFixedHeightMinHeight
theorem ColumnBalancingFixedHeightMinHeight_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 (some 40) (some 30) balance150_children
    res.h = 30 ∧ res.columns.length = 5 ∧
    (res.columns[0]!).h = 30 ∧ (res.columns[4]!).h = 30 := by
  decide

-- column_layout_algorithm_test.cc:3063: ColumnBalancing100By3
theorem ColumnBalancing100By3_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 none none balance100_children
    res.columns.length = 3 := by
  decide

-- column_layout_algorithm_test.cc:3086: ColumnBalancingEmpty
theorem ColumnBalancingEmpty_vectors :
    let res := layoutMulticolBalanced 3 10 320 0 none none ([] : List ColChild)
    res.h = 0 ∧ res.columns.length = 1 ∧
    (res.columns[0]!).w = 100 ∧ (res.columns[0]!).h = 0 ∧
    (res.columns[0]!).slices.length = 0 := by
  decide

-- Break-inside avoid. A 10px block of 50px, then a 20px block of h2px in three 100px columns.
def breakAvoid_mc (h2 : Nat) (avoid2 : Bool) : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 10, height := 50 },
                  { id := 2, width := .px 20, height := h2, avoid := avoid2 } ] }

-- column_layout_algorithm_test.cc:973: BlockStartAtColumnBoundary
-- Two 100px children and no margins. The first fills column 1 exactly, so the second starts
-- column 2. The container asks for three columns, but only two are needed.
def blockStartAtColumnBoundary_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 50, height := 100 },
                  { id := 2, width := .px 60, height := 100 } ] }

-- column_layout_algorithm_test.cc:3109: ColumnBalancingEmptyBlock
-- Three columns, 320px wide, and one 20px child with zero height. The container is 0px tall and
-- has one column of width 100 that holds the child.
def columnBalancingEmptyBlock_children : List ColChild :=
  [ { id := 1, width := .px 20, height := 0 } ]

theorem ColumnBalancingEmptyBlock_vectors :
    let res := layoutMulticolBalancedAll 3 10 320 0 none none columnBalancingEmptyBlock_children
    res.w = 320 ∧ res.h = 0 ∧ res.columns.length = 1 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[0]!).w = 100 ∧ (res.columns[0]!).h = 0 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 20 ∧ ((res.columns[0]!).slices[0]!).h = 0 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:939: BlockWithTopMarginInThreeColumns
-- A 70px block, then a block with a 10px top margin and 150px height. The margin is inside the
-- first column, so the second block starts at y = 80 and fills 20px of column 1, then 100px of
-- column 2 and 30px of column 3.
def blockWithTopMarginInThreeColumns_children : List MarginChild :=
  [ { child := { id := 1, width := .px 50, height := 70 } },
    { child := { id := 2, width := .px 60, height := 150 }, marginTop := 10 } ]

-- column_layout_algorithm_test.cc:1292: MarginTopPastEndOfFragmentainer
-- The first block fills 90px of column 1. The second block's 20px top margin would put its
-- border box at y = 110, past the column end at 100. The margin is cut there, so the block starts
-- at the top of column 2.
def marginTopPastEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 } },
    { child := { id := 2, width := .px 20, height := 20 }, marginTop := 20 } ]

-- column_layout_algorithm_test.cc:1327: MarginBottomPastEndOfFragmentainer
-- The first block has a 20px bottom margin. The gap to the next block is the collapsed margin
-- of 20px, which puts its border box at y = 110, past the column end. The margin is cut there.
def marginBottomPastEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 }, marginBottom := 20 },
    { child := { id := 2, width := .px 20, height := 20 } } ]

-- column_layout_algorithm_test.cc:1362: MarginTopAtEndOfFragmentainer
-- The 10px top margin ends exactly at the column end, y = 100. The block is flush with the end of
-- column 1, so it starts column 2 with one fragment and no empty fragment in column 1.
def marginTopAtEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 } },
    { child := { id := 2, width := .px 20, height := 20 }, marginTop := 10 } ]

-- column_layout_algorithm_test.cc:1396: MarginBottomAtEndOfFragmentainer
-- The 10px bottom margin gives a collapsed gap that ends exactly at the column end, y = 100.
-- The block starts column 2 with one fragment.
def marginBottomAtEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 }, marginBottom := 10 },
    { child := { id := 2, width := .px 20, height := 20 } } ]

-- column_layout_algorithm_test.cc:2602: NewFcAtColumnBoundary
-- A 100px block fills column 1. A 50px new formatting context root (`display: flow-root`, with no
-- floats) starts column 2. The model has no formatting-context flag; the root is a plain block.
def newFcAtColumnBoundary_children : List MarginChild :=
  [ { child := { id := 1, width := .px 22, height := 100 } },
    { child := { id := 2, width := .px 33, height := 50 } } ]

theorem NewFcAtColumnBoundary_vectors :
    let res := layoutMulticolMargins 3 10 320 100 newFcAtColumnBoundary_children
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 22 ∧ ((res.columns[0]!).slices[0]!).h = 100 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 33 ∧ ((res.columns[1]!).slices[0]!).h = 50 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:2633: NewFcWithMargin
-- A 50px block, then a 50px new formatting context root with a 30px top margin. The margin and
-- the first 20px of the root stay in column 1, and the last 30px go to column 2.
def newFcWithMargin_children : List MarginChild :=
  [ { child := { id := 1, width := .px 22, height := 50 } },
    { child := { id := 2, width := .px 33, height := 50 }, marginTop := 30 } ]

theorem NewFcWithMargin_vectors :
    let res := layoutMulticolMargins 3 10 320 100 newFcWithMargin_children
    res.columns.length = 2 ∧
    (res.columns[0]!).slices.length = 2 ∧
    ((res.columns[0]!).slices[0]!).w = 22 ∧ ((res.columns[0]!).slices[0]!).h = 50 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    ((res.columns[0]!).slices[1]!).w = 33 ∧ ((res.columns[0]!).slices[1]!).h = 20 ∧
    ((res.columns[0]!).slices[1]!).relY = 80 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 33 ∧ ((res.columns[1]!).slices[0]!).h = 30 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:2697: NewFcWithMarginPastColumnBoundary
-- An 80px block, then a new formatting context root with a 30px top margin. The margin would end
-- at y = 110, past the column end, so it is cut at 100 and the root starts column 2.
def newFcWithMarginPastColumnBoundary_children : List MarginChild :=
  [ { child := { id := 1, width := .px 22, height := 80 } },
    { child := { id := 2, width := .px 33, height := 50 }, marginTop := 30 } ]

theorem NewFcWithMarginPastColumnBoundary_vectors :
    let res := layoutMulticolMargins 3 10 320 100 newFcWithMarginPastColumnBoundary_children
    res.columns.length = 2 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 22 ∧ ((res.columns[0]!).slices[0]!).h = 80 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 33 ∧ ((res.columns[1]!).slices[0]!).h = 50 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:939: BlockWithTopMarginInThreeColumns
theorem BlockWithTopMarginInThreeColumns_vectors :
    let res := layoutFragmentedBlocks 100 100 [
      { id := 1, width := .px 50, height := 70 },
      { id := 2, width := .px 60, height := 150, marginTop := 10 }
    ]
    res[0]!.colIdx = 0 ∧ res[0]!.relY = 0 ∧ res[0]!.w = 50 ∧ res[0]!.h = 70 ∧
    res[1]!.colIdx = 0 ∧ res[1]!.relY = 80 ∧ res[1]!.w = 60 ∧ res[1]!.h = 20 ∧
    res[2]!.colIdx = 1 ∧ res[2]!.relY = 0 ∧ res[2]!.w = 60 ∧ res[2]!.h = 100 ∧
    res[3]!.colIdx = 2 ∧ res[3]!.relY = 0 ∧ res[3]!.w = 60 ∧ res[3]!.h = 30 := by
  decide

-- column_layout_algorithm_test.cc:973: BlockStartAtColumnBoundary
theorem BlockStartAtColumnBoundary_vectors :
    let res := layoutFragmentedBlocks 100 100 [
      { id := 1, width := .px 50, height := 100 },
      { id := 2, width := .px 60, height := 100 }
    ]
    res[0]!.colIdx = 0 ∧ res[0]!.relY = 0 ∧ res[0]!.w = 50 ∧ res[0]!.h = 100 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 60 ∧ res[1]!.h = 100 := by
  decide

-- column_layout_algorithm_test.cc:1292: MarginTopPastEndOfFragmentainer
theorem MarginTopPastEndOfFragmentainer_vectors :
    let res := layoutFragmentedBlocks 100 100 [
      { id := 1, width := .auto, height := 90 },
      { id := 2, width := .px 20, height := 20, marginTop := 20 }
    ]
    res[0]!.colIdx = 0 ∧ res[0]!.relY = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 20 ∧ res[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1327: MarginBottomPastEndOfFragmentainer
theorem MarginBottomPastEndOfFragmentainer_vectors :
    let res := layoutFragmentedBlocks 100 100 [
      { id := 1, width := .auto, height := 90, marginBottom := 20 },
      { id := 2, width := .px 20, height := 20 }
    ]
    res[0]!.colIdx = 0 ∧ res[0]!.relY = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 20 ∧ res[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1362: MarginTopAtEndOfFragmentainer
theorem MarginTopAtEndOfFragmentainer_vectors :
    let res := layoutFragmentedBlocks 100 100 [
      { id := 1, width := .auto, height := 90 },
      { id := 2, width := .px 20, height := 20, marginTop := 10 }
    ]
    res[0]!.colIdx = 0 ∧ res[0]!.relY = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 20 ∧ res[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1396: MarginBottomAtEndOfFragmentainer
theorem MarginBottomAtEndOfFragmentainer_vectors :
    let res := layoutFragmentedBlocks 100 100 [
      { id := 1, width := .auto, height := 90, marginBottom := 10 },
      { id := 2, width := .px 20, height := 20 }
    ]
    res[0]!.colIdx = 0 ∧ res[0]!.relY = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 20 ∧ res[1]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:1042/1073/1137: break-inside on a 70px (170px) block after a
-- 50px block in a 100px column.
def breakInside_input (bi : BreakInside) (h : Nat) : List ColChildWithMargin :=
  [{ id := 1, width := .px 10, height := 50 },
   { id := 2, width := .px 20, height := h, breakInside := bi }]

theorem BreakInsideAvoid_vectors :
    let res := layoutFragmentedBlocks 100 100 (breakInside_input .avoid 70)
    res.length = 2 ∧ res[0]!.colIdx = 0 ∧ res[0]!.h = 50 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 20 ∧ res[1]!.h = 70 := by
  decide

theorem BreakInsideAvoidColumn_vectors :
    let res := layoutFragmentedBlocks 100 100 (breakInside_input .avoidColumn 70)
    res.length = 2 ∧ res[0]!.colIdx = 0 ∧ res[0]!.h = 50 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.w = 20 ∧ res[1]!.h = 70 := by
  decide

theorem BreakInsideAvoidTallBlock_vectors :
    let res := layoutFragmentedBlocks 100 100 (breakInside_input .avoid 170)
    res.length = 3 ∧ res[0]!.colIdx = 0 ∧ res[0]!.h = 50 ∧
    res[1]!.colIdx = 1 ∧ res[1]!.relY = 0 ∧ res[1]!.h = 100 ∧
    res[2]!.colIdx = 2 ∧ res[2]!.relY = 0 ∧ res[2]!.h = 70 := by
  decide

-- column_layout_algorithm_test.cc:5723: AvoidBreakBetween. `#parent{columns:3; gap 10; height 100;
-- width 320}` with four 30px `break-inside:avoid` children; the fourth has `break-before:avoid`, so
-- the break moves before the third child. The 1000px outer container is not part of the multicol model.
def avoidBreakBetween_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 81, height := 30, avoid := true },
                  { id := 2, width := .px 82, height := 30, avoid := true },
                  { id := 3, width := .px 83, height := 30, avoid := true },
                  { id := 4, width := .px 84, height := 30, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidBreakBetween_vectors :
    let res := layoutMulticolAvoid avoidBreakBetween_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 81, 30), (2, 30, 82, 30)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(3, 0, 83, 30), (4, 30, 84, 30)] := by
  decide

-- column_layout_algorithm_test.cc:5762: AvoidAndForceBreakBetween. The same columns; the third child
-- has `break-after:column` and the fourth `break-before:avoid`. The forced break wins, so the
-- fourth child is the only one in the second column and the first three stay together.
def avoidAndForceBreakBetween_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 81, height := 30, avoid := true },
                  { id := 2, width := .px 82, height := 30, avoid := true },
                  { id := 3, width := .px 83, height := 30, avoid := true, breakAfterColumn := true },
                  { id := 4, width := .px 84, height := 30, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidAndForceBreakBetween_vectors :
    let res := layoutMulticolAvoid avoidAndForceBreakBetween_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 81, 30), (2, 30, 82, 30), (3, 60, 83, 30)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(4, 0, 84, 30)] := by
  decide

-- column_layout_algorithm_test.cc:5938: AvoidBreakBetweenAndInside. `#middle` (80px, `break-inside:avoid`,
-- `break-after:avoid`) would fit in the first column after the 20px first child, but then the break
-- would fall between `#middle` and the last child. The only break that violates no rule is before
-- `#middle`. `break-after:avoid` on `#middle` is the same constraint as `break-before:avoid` on the
-- next sibling. The four children inside `#middle` stay in one column and are not modelled.
def avoidBreakBetweenAndInside_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 32, height := 20, avoid := true },
                  { id := 2, width := .auto, height := 80, avoid := true },
                  { id := 3, width := .px 37, height := 20, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidBreakBetweenAndInside_vectors :
    let res := layoutMulticolAvoid avoidBreakBetweenAndInside_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 32, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(2, 0, 100, 80), (3, 80, 37, 20)] := by
  decide

-- column_layout_algorithm_test.cc:6416: AvoidBreakBeforeBlockReplacedContent. Replaced content is
-- unbreakable, so the `img` is a child with `avoid := true`. It does not fit after the second child
-- and has `break-before:avoid`, so the second child moves to the second column with it.
def avoidBreakBeforeReplaced_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 22, height := 40 },
                  { id := 2, width := .px 33, height := 50, avoid := true },
                  { id := 3, width := .px 44, height := 50, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidBreakBeforeBlockReplacedContent_vectors :
    let res := layoutMulticolAvoid avoidBreakBeforeReplaced_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 22, 40)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(2, 0, 33, 50), (3, 50, 44, 50)] := by
  decide

-- column_layout_algorithm_test.cc:5845: IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid. Four 30px
-- `break-inside:avoid` children; children 2-4 have `break-before:avoid`, so the whole run of 120px
-- cannot fit in one 100px column and no break before any child is allowed. The third child may not
-- move (its own break-before), so the fourth child is split: 10px in column 1 and 20px in column 2.
def ignoreBreakInsideAvoidBecauseBreakBetweenAvoid_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 81, height := 30, avoid := true },
                  { id := 2, width := .px 82, height := 30, avoid := true, breakBeforeAvoid := true },
                  { id := 3, width := .px 83, height := 30, avoid := true, breakBeforeAvoid := true },
                  { id := 4, width := .px 84, height := 30, avoid := true, breakBeforeAvoid := true } ] }

theorem IgnoreBreakInsideAvoidBecauseBreakBetweenAvoid_vectors :
    let res := layoutMulticolAvoid ignoreBreakInsideAvoidBecauseBreakBetweenAvoid_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 81, 30), (2, 30, 82, 30), (3, 60, 83, 30), (4, 90, 84, 10)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(4, 0, 84, 20)] := by
  decide

-- column_layout_algorithm_test.cc:5892: AvoidBreakBetweenAndInsideIgnoreInside. The outer box has
-- `break-inside:avoid` but is 110px, taller than a column, so its own avoid is ignored. Its children
-- are flattened into the sequence (the box has no other break flags). The last child has
-- `break-before:avoid`, so the third child moves to the second column with it.
def avoidBreakBetweenAndInsideIgnoreInside_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 80, height := 20 },
                  { id := 2, width := .px 81, height := 30, avoid := true },
                  { id := 3, width := .px 82, height := 30, avoid := true },
                  { id := 4, width := .px 83, height := 30, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidBreakBetweenAndInsideIgnoreInside_vectors :
    let res := layoutMulticolAvoid avoidBreakBetweenAndInsideIgnoreInside_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 80, 20), (2, 20, 81, 30)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(3, 0, 82, 30), (4, 30, 83, 30)] := by
  decide

-- column_layout_algorithm_test.cc:5984 (AvoidBreakBetweenInsideBreakableParent) and :6037
-- (AvoidBreakBetweenAfterBreakableSibling). Both have a breakable parent around the first children
-- and a second block whose first child has no break flag. Flattened, both give the same sequence:
-- `#first` has no break restriction of its own, so the first three children are plain; the fourth
-- children from the fourth on have `break-before:avoid`: directly in 5984, and in 6037 the fifth one
-- comes from `break-after:avoid` on the first block. The run of the last three children is kept
-- together and moves to the second column with the third child, the only break that violates no rule.
def breakableParentSequence_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 33, height := 20, avoid := true },
                  { id := 2, width := .px 34, height := 20, avoid := true },
                  { id := 3, width := .px 35, height := 20, avoid := true },
                  { id := 4, width := .px 36, height := 20, avoid := true, breakBeforeAvoid := true },
                  { id := 5, width := .px 37, height := 20, avoid := true, breakBeforeAvoid := true },
                  { id := 6, width := .px 38, height := 20, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidBreakBetweenInsideBreakableParent_vectors :
    let res := layoutMulticolAvoid breakableParentSequence_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 33, 20), (2, 20, 34, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) =
      [(3, 0, 35, 20), (4, 20, 36, 20), (5, 40, 37, 20), (6, 60, 38, 20)] := by
  decide

theorem AvoidBreakBetweenAfterBreakableSibling_vectors :
    let res := layoutMulticolAvoid breakableParentSequence_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(1, 0, 33, 20), (2, 20, 34, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) =
      [(3, 0, 35, 20), (4, 20, 36, 20), (5, 40, 37, 20), (6, 60, 38, 20)] := by
  decide

-- column_layout_algorithm_test.cc:6092: AvoidBreakBetweenBreakInsidePreviousSibling. The container of
-- four 20px children has `break-after:avoid`, so the next child (the last, 37px) is
-- `break-before:avoid` in the flattened sequence. The fourth child moves to the second column with it.
def avoidBreakBetweenBreakInsidePreviousSibling_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 32, height := 20, avoid := true },
                  { id := 2, width := .px 33, height := 20, avoid := true },
                  { id := 3, width := .px 34, height := 20, avoid := true },
                  { id := 4, width := .px 35, height := 20, avoid := true },
                  { id := 5, width := .px 36, height := 20, avoid := true },
                  { id := 6, width := .px 37, height := 20, avoid := true, breakBeforeAvoid := true } ] }

theorem AvoidBreakBetweenBreakInsidePreviousSibling_vectors :
    let res := layoutMulticolAvoid avoidBreakBetweenBreakInsidePreviousSibling_input
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) =
      [(1, 0, 32, 20), (2, 20, 33, 20), (3, 40, 34, 20), (4, 60, 35, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.w, s.h)) = [(5, 0, 36, 20), (6, 20, 37, 20)] := by
  decide

-- column_layout_algorithm_test.cc:1174: NestedBreakInsideAvoid
theorem NestedBreakInsideAvoid_vectors :
    let nodes := [
      BNode.leaf (.px 10) 50 .auto,
      BNode.box (.px 30) .avoid [
        BNode.leaf (.px 21) 30 .avoid,
        BNode.leaf (.px 22) 30 .avoid
      ]
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.y = 0 ∧ res[0]!.w = 10 ∧ res[0]!.h = 50 ∧
    res[1]!.col = 1 ∧ res[1]!.y = 0 ∧ res[1]!.w = 30 ∧ res[1]!.h = 60 ∧
    res[1]!.kids.length = 2 ∧
    res[1]!.kids[0]!.w = 21 ∧ res[1]!.kids[0]!.h = 30 ∧
    res[1]!.kids[1]!.w = 22 ∧ res[1]!.kids[1]!.h = 30 := by
  decide

-- column_layout_algorithm_test.cc:1215: NestedBreakInsideAvoidTall
theorem NestedBreakInsideAvoidTall_vectors :
    let nodes := [
      BNode.leaf (.px 10) 50 .auto,
      BNode.box (.px 30) .avoid [
        BNode.leaf (.px 21) 30 .auto,
        BNode.leaf (.px 22) 80 .avoid
      ]
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 3 ∧
    res[0]!.col = 0 ∧ res[0]!.h = 50 ∧
    res[1]!.col = 1 ∧ res[1]!.y = 0 ∧ res[1]!.w = 30 ∧ res[1]!.h = 100 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.w = 21 ∧ res[1]!.kids[0]!.h = 30 ∧
    res[2]!.col = 2 ∧ res[2]!.y = 0 ∧ res[2]!.w = 30 ∧ res[2]!.h = 80 ∧
    res[2]!.kids.length = 1 ∧ res[2]!.kids[0]!.w = 22 ∧ res[2]!.kids[0]!.h = 80 := by
  decide

-- column_layout_algorithm_test.cc:1258: BreakInsideAvoidAtColumnBoundary
theorem BreakInsideAvoidAtColumnBoundary_vectors :
    let nodes := [
      BNode.leaf .auto 90 .auto,
      BNode.box .auto .auto [
        BNode.leaf (.px 20) 20 .avoid
      ]
    ]
    let res := layoutNodes 100 100 3 nodes
    res.length = 2 ∧
    res[0]!.col = 0 ∧ res[0]!.w = 100 ∧ res[0]!.h = 90 ∧
    res[1]!.col = 1 ∧ res[1]!.w = 100 ∧ res[1]!.h = 20 ∧
    res[1]!.kids.length = 1 ∧ res[1]!.kids[0]!.w = 20 ∧ res[1]!.kids[0]!.h = 20 := by
  decide

-- column_layout_algorithm_test.cc:2728: MinMax
-- Intrinsic sizes for multicolumn: column-count + column-width, count-only, width-only.
-- CSS Sizing 3 §4, CSS Sizing 4 §4.1.
theorem MinMax_vectors :
    -- Both column-count: 3 and column-width: 80 set (gap: 10, contentMin: 50, contentMax: 100)
    (ColumnWidth.multicolMinMax 50 100 (some 3) (some 80) 10).1 = 50 ∧
    (ColumnWidth.multicolMinMax 50 100 (some 3) (some 80) 10).2 = 320 ∧
    -- Only column-count: 3 set
    (ColumnWidth.multicolMinMax 50 100 (some 3) none 10).1 = 170 ∧
    (ColumnWidth.multicolMinMax 50 100 (some 3) none 10).2 = 320 ∧
    -- Only column-width: 80 set
    (ColumnWidth.multicolMinMax 50 100 none (some 80) 10).1 = 50 ∧
    (ColumnWidth.multicolMinMax 50 100 none (some 80) 10).2 = 80 := by
  decide

-- column_layout_algorithm_test.cc:6326: AvoidBreakBetweenLinesInsideBreakAvoid
-- Two avoid children (33px and 34px, 20px tall), then a 40px break-inside:avoid block of two 20px
-- line boxes, then a 30px child (36px wide) with break-before:avoid, in 100px columns with
-- orphans:1 and widows:1. The avoid block forbids a break before its second line, so that line is
-- break-before:avoid. The first line moves with the run of the second line and the last child,
-- which fits in one column (childStartsB). The line fragments are compared; the avoid block's own
-- box is not (as for 5984).
theorem AvoidBreakBetweenLinesInsideBreakAvoid_vectors :
    let res := layoutMulticolAvoid
      { cols := 3, gap := 10, width := 320, height := 100,
        children := [ { id := 1, width := .px 33, height := 20, avoid := true },
                      { id := 2, width := .px 34, height := 20, avoid := true },
                      { id := 3, height := 20 },
                      { id := 4, height := 20, breakBeforeAvoid := true },
                      { id := 5, width := .px 36, height := 30, avoid := true,
                        breakBeforeAvoid := true } ] }
    res.w = 320 ∧ res.h = 100 ∧ res.colWidth = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.h)) = [(1, 0, 20), (2, 20, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.h)) = [(3, 0, 20), (4, 20, 20), (5, 40, 30)] ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.w)) = [(1, 33), (2, 34)] ∧
    ((res.columns[1]!).slices.filter (fun s => s.id == 5)).map (fun s => s.w) = [36] := by
  decide

-- column_layout_algorithm_test.cc:6136: AvoidBreakBetweenHonorOrphansWidows
-- Four 20px line boxes (orphans:2, widows:2) and a 30px block with break-inside:avoid and
-- break-before:avoid, in 100px columns. A break before line j of a block of n lines needs
-- j-1 >= orphans and n-j+1 >= widows, so only the break before line 3 is allowed. The lines that
-- may not start a column are break-before:avoid. The line fragments are compared; the wrapper
-- blocks around the lines are not (as for 5984).
theorem AvoidBreakBetweenHonorOrphansWidows_vectors :
    let res := layoutMulticolAvoid
      { cols := 3, gap := 10, width := 320, height := 100,
        children := [ { id := 1, height := 20 },
                      { id := 2, height := 20, breakBeforeAvoid := true },
                      { id := 3, height := 20 },
                      { id := 4, height := 20, breakBeforeAvoid := true },
                      { id := 5, height := 30, avoid := true, breakBeforeAvoid := true } ] }
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.h)) = [(1, 0, 20), (2, 20, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.h)) =
      [(3, 0, 20), (4, 20, 20), (5, 40, 30)] := by
  decide

-- column_layout_algorithm_test.cc:6182: AvoidBreakBetweenHonorOrphansWidows2
-- A 40px block, then two 20px line boxes (orphans:2, widows:2) and a 30px block with
-- break-before:avoid. Two lines cannot be split (orphans + widows = 4 > 2), so the second line is
-- break-before:avoid and the first line may move with it. The line fragments are compared; the
-- wrapper block around the lines is not (as for 5984).
theorem AvoidBreakBetweenHonorOrphansWidows2_vectors :
    let res := layoutMulticolAvoid
      { cols := 3, gap := 10, width := 320, height := 100,
        children := [ { id := 1, height := 40 },
                      { id := 2, height := 20 },
                      { id := 3, height := 20, breakBeforeAvoid := true },
                      { id := 4, height := 30, avoid := true, breakBeforeAvoid := true } ] }
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.h)) = [(1, 0, 40)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.h)) =
      [(2, 0, 20), (3, 20, 20), (4, 40, 30)] := by
  decide

-- column_layout_algorithm_test.cc:6225: AvoidBreakBetweenHonorOrphansWidows3
-- Four 20px line boxes (orphans:2, widows:2), then a block of three lines with break-before:avoid.
-- The only allowed break in the first block is before line 3. The three lines of the second block
-- cannot be split (orphans + widows = 4 > 3), so each of them is break-before:avoid, and the
-- second block is break-before:avoid itself. The line fragments are compared; the wrapper blocks
-- are not (as for 5984).
theorem AvoidBreakBetweenHonorOrphansWidows3_vectors :
    let res := layoutMulticolAvoid
      { cols := 3, gap := 10, width := 320, height := 100,
        children := [ { id := 1, height := 20 },
                      { id := 2, height := 20, breakBeforeAvoid := true },
                      { id := 3, height := 20 },
                      { id := 4, height := 20, breakBeforeAvoid := true },
                      { id := 5, height := 20, breakBeforeAvoid := true },
                      { id := 6, height := 20, breakBeforeAvoid := true },
                      { id := 7, height := 20, breakBeforeAvoid := true } ] }
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.map (fun s => (s.id, s.relY, s.h)) = [(1, 0, 20), (2, 20, 20)] ∧
    (res.columns[1]!).slices.map (fun s => (s.id, s.relY, s.h)) =
      [(3, 0, 20), (4, 20, 20), (5, 40, 20), (6, 60, 20), (7, 80, 20)] := by
  decide

end TestsBlock
end ChromiumLayout
