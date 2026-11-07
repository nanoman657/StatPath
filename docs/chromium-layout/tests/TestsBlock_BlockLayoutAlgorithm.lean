/-
  Test vectors transcribed from block_layout_algorithm_test.cc (pin 36c121be).
  Each theorem names the TEST_F it transcribes; expected numbers are the test's EXPECT_* values.
-/
import BlockFlow
import BlockFragmentation

namespace ChromiumLayout
namespace TestsBlock
open BlockFlow

/-- A fixed-size leaf: `width`/`height` in px. -/
def leaf (id w h : Nat) : BF := { id := id, width := .px w, height := some h }

/-! ### FixedSize (line 90): `<div style="width:30px; height:40px">`, available inline 100 -/
theorem FixedSize_size :
    let f := layoutRoot 100 (leaf 1 30 40)
    f.w = 30 ∧ f.h = 40 := by decide

/-! ### LayoutBlockChildren (line 341) -/
def lbc : BF :=
  { id := 0, width := .px 30, children :=
    [ { id := 1, height := some 20 },
      { id := 2, height := some 30, mt := 5, mb := 20 } ] }

theorem LayoutBlockChildren_container :
    let f := layoutRoot 100 lbc
    f.w = 30 ∧ f.h = 55 ∧ f.kids.length = 2 := by decide

theorem LayoutBlockChildren_children :
    let f := layoutRoot 100 lbc
    (f.kid 0).h = 20 ∧ f.relY (f.kid 0) = 0 ∧
    (f.kid 1).h = 30 ∧ f.relY (f.kid 1) = 25 := by decide

/-! ### CollapsingMarginsCase3 (line 568): `#container{margin-bottom:20px}`
    `#child{margin-bottom:200px;height:50px}`, container height auto / 50px, in `html > body`. -/
def case3 (containerH : Option Nat) : BF :=
  htmlBody [ { id := 2, mb := 20, height := containerH, children :=
                [ { id := 3, mb := 200, height := some 50 } ] } ]

theorem CollapsingMarginsCase3_auto :
    (layoutRoot 800 (case3 none)).h = 258 := by decide

theorem CollapsingMarginsCase3_fixed :
    (layoutRoot 800 (case3 (some 50))).h = 78 := by decide

/-! ### CollapsingMarginsCase4 (line 618): `#container{margin:30px 0;width:200px}`
    `#child{margin:200px 0;height:50px}`; container padding-top 20px / 0. -/
def case4 (padTop : Nat) : BF :=
  htmlBody [ { id := 2, mt := 30, mb := 30, width := .px 200, pt := padTop, children :=
                [ { id := 3, mt := 200, mb := 200, height := some 50 } ] } ]

def case4Frag (padTop : Nat) : Frag := layoutRoot 800 (case4 padTop)

theorem CollapsingMarginsCase4_with_padding :
    let f := case4Frag 20
    let body := f.kid 0
    let container := body.kid 0
    let child := container.kid 0
    f.h = 500 ∧ f.relY body = 30 ∧ container.relY child = 220 := by decide

theorem CollapsingMarginsCase4_without_padding :
    let f := case4Frag 0
    let body := f.kid 0
    let container := body.kid 0
    let child := container.kid 0
    f.h = 450 ∧ f.relY body = 200 ∧ container.relY child = 0 := by decide

/-! ### BorderAndPadding (line 1062) -/
def bap : BF :=
  { id := 0, children :=
    [ { id := 1, width := .px 100, height := some 100,
        bt := 1, br := 2, bb := 3, bl := 4, pt := 5, pr := 6, pb := 7, pl := 8,
        children := [ { id := 2 } ] } ] }

theorem BorderAndPadding_div1 :
    let f := layoutRoot 1000 bap
    let d1 := f.kid 0
    d1.w = 4 + 8 + 100 + 6 + 2 ∧ d1.h = 1 + 5 + 100 + 7 + 3 := by decide

theorem BorderAndPadding_div2_offset :
    let f := layoutRoot 1000 bap
    let d1 := f.kid 0
    d1.relY (d1.kid 0) = 1 + 5 ∧ d1.relX (d1.kid 0) = 4 + 8 := by decide

/-! ### PercentageResolutionSize (line 1118): container `width:30px; padding-left:10px`,
    child `width:40%`. -/
def prs : BF :=
  { id := 0, width := .px 30, pl := 10, children := [ { id := 1, width := .pct 40 } ] }

theorem PercentageResolutionSize_widths :
    let f := layoutRoot 100 prs
    f.w = 40 ∧ (f.kid 0).w = 12 := by decide

/-! ### AutoMargin (line 1145): `#first{width:10px; margin-left:auto; margin-right:auto}` in
    `width:30px; padding-left:10px` -/
def am : BF :=
  { id := 0, width := .px 30, pl := 10, children :=
    [ { id := 1, width := .px 10, ml := .auto, mr := .auto, height := some 5 } ] }

theorem AutoMargin_offsets :
    let f := layoutRoot 100 am
    let c := f.kid 0
    f.w = 40 ∧ c.w = 10 ∧ f.relX c = 20 ∧ f.relY c = 0 := by decide

/-! ### ComputeMinMaxContent (line 1516) and ShrinkToFit (line 1637):
    children `width:20px` and `width:30px` -/
def mmc : BF :=
  { id := 0, children := [ { id := 1, width := .px 20 }, { id := 2, width := .px 30 } ] }

theorem ComputeMinMaxContent_sizes : maxContent fuel mmc = 30 := by decide

theorem ShrinkToFit_width :
    shrinkToFit 100 (maxContent fuel mmc) (maxContent fuel mmc) = 30 := by decide

/-! ### ZeroBlockSizeAboveEdge (line 2321): new-BFC container; `#inflow` 50x50 `margin-top:-70px`;
    `#zero` `width:70px; margin:10px 0 30px 0`. -/
def zbsae : BF :=
  { id := 0, width := .px 200, newBfc := true, children :=
    [ { id := 1, width := .px 50, height := some 50, mt := -70 },
      { id := 2, width := .px 70, mt := 10, mb := 30 } ] }

theorem ZeroBlockSizeAboveEdge_vectors :
    let f := layoutRoot 1000 zbsae
    f.w = 200 ∧ f.h = 10 ∧
    (f.kid 0).w = 50 ∧ (f.kid 0).h = 50 ∧ f.relY (f.kid 0) = -70 ∧
    (f.kid 1).w = 70 ∧ (f.kid 1).h = 0 ∧ f.relY (f.kid 1) = -10 := by decide

/-! ### NewFcFirstChildIsZeroBlockSize (line 2357) -/
def nfczbs : BF :=
  { id := 0, width := .px 200, newBfc := true, children :=
    [ { id := 1, width := .px 50, mt := -30, mb := 10 },
      { id := 2, width := .px 70, mt := 20, mb := -40 },
      { id := 3, width := .px 90, height := some 20, mt := 30 } ] }

theorem NewFcFirstChildIsZeroBlockSize_vectors :
    let f := layoutRoot 1000 nfczbs
    f.w = 200 ∧ f.h = 10 ∧
    (f.kid 0).w = 50 ∧ (f.kid 0).h = 0 ∧ f.relY (f.kid 0) = -30 ∧
    (f.kid 1).w = 70 ∧ (f.kid 1).h = 0 ∧ f.relY (f.kid 1) = -10 ∧
    (f.kid 2).w = 90 ∧ (f.kid 2).h = 20 ∧ f.relY (f.kid 2) = -10 := by decide

/-! ### Fragmentation tests (lines 1778-2023), fragmentainer block size 200 -/

/-- `NoFragmentation` (line 1778): `width:150px; height:200px`: one 150x200 fragment, no token. -/
theorem NoFragmentation_vectors :
    let f := layoutRoot 1000 { id := 0, width := .px 150, height := some 200 }
    sliceSize 200 f.y f.h.toNat 0 = 200 ∧ f.w = 150 ∧ hasBreakToken 200 f 0 = false := by decide

/-- `SimpleFragmentation` (line 1806): height 300 gives 200 (token) then 100 (no token). -/
theorem SimpleFragmentation_vectors :
    let f := layoutRoot 1000 { id := 0, width := .px 150, height := some 300 }
    sliceSize 200 f.y f.h.toNat 0 = 200 ∧ hasBreakToken 200 f 0 = true ∧
    sliceSize 200 f.y f.h.toNat 1 = 100 ∧ hasBreakToken 200 f 1 = false := by decide

/-- Shared tree of `InnerChildrenFragmentation` (line 1838) and
    `InnerFormattingContextChildrenFragmentation` (line 1900; `contain: paint` children, same
    expected values): container `padding-top:20px`, child1 200 tall `margin-bottom:20px`,
    child2 100 tall `margin-top:20px`. -/
def innerFrag (fc : Bool) (containerH : Option Nat) : BF :=
  { id := 0, width := .px 150, pt := 20, height := containerH, children :=
    [ { id := 1, height := some 200, mb := 20, newBfc := fc },
      { id := 2, height := some 100, mt := 20, newBfc := fc } ] }

def InnerFragSpec (fc : Bool) : Prop :=
    let f := layoutRoot 1000 (innerFrag fc none)
    let c1 := f.kid 0
    let c2 := f.kid 1
    -- container: 200 then 140, break token on the first only
    sliceSize 200 f.y f.h.toNat 0 = 200 ∧ hasBreakToken 200 f 0 = true ∧
    sliceSize 200 f.y f.h.toNat 1 = 140 ∧ hasBreakToken 200 f 1 = false ∧
    -- first fragment holds only child1: 180 tall at offset 20
    inSlice 200 c1 0 = true ∧ inSlice 200 c2 0 = false ∧
    sliceSize 200 c1.y c1.h.toNat 0 = 180 ∧ sliceOffset 200 f.y c1.y 0 = 20 ∧
    -- second fragment: child1 remainder 20 at 0, child2 100 at 40
    inSlice 200 c1 1 = true ∧ inSlice 200 c2 1 = true ∧
    sliceSize 200 c1.y c1.h.toNat 1 = 20 ∧ sliceOffset 200 f.y c1.y 1 = 0 ∧
    sliceSize 200 c2.y c2.h.toNat 1 = 100 ∧ sliceOffset 200 f.y c2.y 1 = 40

theorem innerFrag_expected (fc : Bool) : InnerFragSpec fc := by
  cases fc <;> (unfold InnerFragSpec; decide)

theorem InnerChildrenFragmentation_vectors : InnerFragSpec false := innerFrag_expected false
theorem InnerFormattingContextChildrenFragmentation_vectors : InnerFragSpec true :=
  innerFrag_expected true

/-- `InnerChildrenFragmentationSmallHeight` (line 1964): container `height:50px` +
    `padding-top:20px`: first fragment 70 (token, because child1 overflows), second 0. -/
theorem InnerChildrenFragmentationSmallHeight_vectors :
    let f := layoutRoot 1000 (innerFrag false (some 50))
    let c1 := f.kid 0
    let c2 := f.kid 1
    sliceSize 200 f.y f.h.toNat 0 = 70 ∧ hasBreakToken 200 f 0 = true ∧
    sliceSize 200 f.y f.h.toNat 1 = 0 ∧ hasBreakToken 200 f 1 = false ∧
    sliceSize 200 c1.y c1.h.toNat 0 = 180 ∧ sliceOffset 200 f.y c1.y 0 = 20 ∧
    sliceSize 200 c1.y c1.h.toNat 1 = 20 ∧ sliceOffset 200 f.y c1.y 1 = 0 ∧
    sliceSize 200 c2.y c2.h.toNat 1 = 100 ∧ sliceOffset 200 f.y c2.y 1 = 40 := by decide

end TestsBlock
end ChromiumLayout
