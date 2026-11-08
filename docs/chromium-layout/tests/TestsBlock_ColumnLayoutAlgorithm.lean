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

end TestsBlock
end ChromiumLayout
