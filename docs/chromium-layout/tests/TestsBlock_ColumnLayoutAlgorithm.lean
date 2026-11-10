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

-- column_layout_algorithm_test.cc:1042: BreakInsideAvoid
theorem BreakInsideAvoid_vectors :
    let res := layoutMulticolAvoid (breakAvoid_mc 70 true)
    res.h = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧ ((res.columns[0]!).slices[0]!).h = 50 ∧
    (res.columns[1]!).relX = 110 ∧ (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 ∧ ((res.columns[1]!).slices[0]!).h = 70 ∧
    ((res.columns[1]!).slices[0]!).w = 20 := by
  decide

-- column_layout_algorithm_test.cc:1073: BreakInsideAvoidColumn (avoid-column shares the
-- avoid flag in a column-only layout)
theorem BreakInsideAvoidColumn_vectors :
    let res := layoutMulticolAvoid (breakAvoid_mc 70 true)
    res.h = 100 ∧ res.columns.length = 2 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧ ((res.columns[0]!).slices[0]!).h = 50 ∧
    (res.columns[1]!).relX = 110 ∧ (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 ∧ ((res.columns[1]!).slices[0]!).h = 70 ∧
    ((res.columns[1]!).slices[0]!).w = 20 := by
  decide

-- column_layout_algorithm_test.cc:1137: BreakInsideAvoidTallBlock (moved once, then breaks)
theorem BreakInsideAvoidTallBlock_vectors :
    let res := layoutMulticolAvoid (breakAvoid_mc 170 true)
    res.columns.length = 3 ∧
    (res.columns[1]!).slices.length = 1 ∧ ((res.columns[1]!).slices[0]!).h = 100 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 ∧
    ((res.columns[2]!).slices[0]!).h = 70 ∧ ((res.columns[2]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:973: BlockStartAtColumnBoundary
-- Two 100px children and no margins. The first fills column 1 exactly, so the second starts
-- column 2. The container asks for three columns, but only two are needed.
def blockStartAtColumnBoundary_input : Multicol :=
  { cols := 3, gap := 10, width := 320, height := 100,
    children := [ { id := 1, width := .px 50, height := 100 },
                  { id := 2, width := .px 60, height := 100 } ] }

theorem BlockStartAtColumnBoundary_vectors :
    let res := layoutMulticol blockStartAtColumnBoundary_input
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 50 ∧ ((res.columns[0]!).slices[0]!).h = 100 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 60 ∧ ((res.columns[1]!).slices[0]!).h = 100 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

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

theorem BlockWithTopMarginInThreeColumns_vectors :
    let res := layoutMulticolMargins 3 10 320 100 blockWithTopMarginInThreeColumns_children
    res.w = 320 ∧ res.h = 100 ∧ res.columns.length = 3 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧ (res.columns[2]!).relX = 220 ∧
    (res.columns[0]!).slices.length = 2 ∧
    ((res.columns[0]!).slices[0]!).w = 50 ∧ ((res.columns[0]!).slices[0]!).h = 70 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    ((res.columns[0]!).slices[1]!).w = 60 ∧ ((res.columns[0]!).slices[1]!).h = 20 ∧
    ((res.columns[0]!).slices[1]!).relY = 80 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 60 ∧ ((res.columns[1]!).slices[0]!).h = 100 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 ∧
    (res.columns[2]!).slices.length = 1 ∧
    ((res.columns[2]!).slices[0]!).w = 60 ∧ ((res.columns[2]!).slices[0]!).h = 30 ∧
    ((res.columns[2]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:1292: MarginTopPastEndOfFragmentainer
-- The first block fills 90px of column 1. The second block's 20px top margin would put its
-- border box at y = 110, past the column end at 100. The margin is cut there, so the block starts
-- at the top of column 2.
def marginTopPastEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 } },
    { child := { id := 2, width := .px 20, height := 20 }, marginTop := 20 } ]

theorem MarginTopPastEndOfFragmentainer_vectors :
    let res := layoutMulticolMargins 3 10 320 100 marginTopPastEnd_children
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 100 ∧ ((res.columns[0]!).slices[0]!).h = 90 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 20 ∧ ((res.columns[1]!).slices[0]!).h = 20 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:1327: MarginBottomPastEndOfFragmentainer
-- The first block has a 20px bottom margin. The gap to the next block is the collapsed margin
-- of 20px, which puts its border box at y = 110, past the column end. The margin is cut there.
def marginBottomPastEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 }, marginBottom := 20 },
    { child := { id := 2, width := .px 20, height := 20 } } ]

theorem MarginBottomPastEndOfFragmentainer_vectors :
    let res := layoutMulticolMargins 3 10 320 100 marginBottomPastEnd_children
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 100 ∧ ((res.columns[0]!).slices[0]!).h = 90 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 20 ∧ ((res.columns[1]!).slices[0]!).h = 20 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:1362: MarginTopAtEndOfFragmentainer
-- The 10px top margin ends exactly at the column end, y = 100. The block is flush with the end of
-- column 1, so it starts column 2 with one fragment and no empty fragment in column 1.
def marginTopAtEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 } },
    { child := { id := 2, width := .px 20, height := 20 }, marginTop := 10 } ]

theorem MarginTopAtEndOfFragmentainer_vectors :
    let res := layoutMulticolMargins 3 10 320 100 marginTopAtEnd_children
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 100 ∧ ((res.columns[0]!).slices[0]!).h = 90 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 20 ∧ ((res.columns[1]!).slices[0]!).h = 20 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

-- column_layout_algorithm_test.cc:1396: MarginBottomAtEndOfFragmentainer
-- The 10px bottom margin gives a collapsed gap that ends exactly at the column end, y = 100.
-- The block starts column 2 with one fragment.
def marginBottomAtEnd_children : List MarginChild :=
  [ { child := { id := 1, height := 90 }, marginBottom := 10 },
    { child := { id := 2, width := .px 20, height := 20 } } ]

theorem MarginBottomAtEndOfFragmentainer_vectors :
    let res := layoutMulticolMargins 3 10 320 100 marginBottomAtEnd_children
    res.columns.length = 2 ∧
    (res.columns[0]!).relX = 0 ∧ (res.columns[1]!).relX = 110 ∧
    (res.columns[0]!).slices.length = 1 ∧
    ((res.columns[0]!).slices[0]!).w = 100 ∧ ((res.columns[0]!).slices[0]!).h = 90 ∧
    ((res.columns[0]!).slices[0]!).relY = 0 ∧
    (res.columns[1]!).slices.length = 1 ∧
    ((res.columns[1]!).slices[0]!).w = 20 ∧ ((res.columns[1]!).slices[0]!).h = 20 ∧
    ((res.columns[1]!).slices[0]!).relY = 0 := by
  decide

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

end TestsBlock
end ChromiumLayout
