/-
  Test vectors transcribed from map_coordinates_test.cc (pin 36c121be).
  Each theorem names the TEST_P it transcribes; expected numbers are the test's EXPECT_* values.
  Every test runs twice (with and without the geometry mapper); both runs expect the same values
  except where a row says otherwise.
-/
import Mapping
import MappingTransform

namespace ChromiumLayout
namespace TestsMapping
open BlockFlow Mapping BlockRelative BlockAbsolute

/-- `position:relative; left:l; top:t` (right/bottom auto). -/
def rp (l t : Int) : Option Insets := some (computeRelativeInsets (some t) none none (some l))

/-! ### SimpleText (127), SimpleInline (140): the text / span is mapped to its parent -/
theorem SimpleText_vectors :
    mapRange [.inline] 0 1 ⟨10, 30⟩ = ⟨10, 30⟩ ∧ mapRangeDown [.inline] 0 1 ⟨10, 30⟩ = ⟨10, 30⟩ := by
  decide

theorem SimpleInline_vectors :
    mapRange [.inline] 0 1 ⟨10, 10⟩ = ⟨10, 10⟩ ∧ mapRangeDown [.inline] 0 1 ⟨10, 10⟩ = ⟨10, 10⟩ := by
  decide

/-! ### SimpleBlock (153): `margin:666px; border:8px solid; padding:7px` around
    `#target{margin:10px; border:666px; padding:666px}` (`border:666px` has no style, so width 0). -/
def simpleBlock : BF :=
  { mt := 666, mb := 666, ml := .px 666, mr := .px 666, bt := 8, bb := 8, bl := 8, br := 8,
    pt := 7, pb := 7, pl := 7, pr := 7,
    children := [{ id := 1, mt := 10, mb := 10, ml := .px 10, mr := .px 10 }] }

theorem SimpleBlock_vectors :
    let f := layoutRoot 800 simpleBlock
    let ns := [Node.block f (f.kid 0)]
    mapRange ns 0 1 ⟨100, 100⟩ = ⟨125, 125⟩ ∧ mapRangeDown ns 0 1 ⟨125, 125⟩ = ⟨100, 100⟩ := by decide

/-! ### TextInRelPosInline (210): text in `span{position:relative; left:7px; top:4px}`
    mapped to the containing div: text, then the span. -/
theorem TextInRelPosInline_vectors :
    let ns := [Node.inline, .inline (rp 7 4)]
    mapRange ns 0 2 ⟨10, 30⟩ = ⟨10, 30⟩ ∧ mapRangeDown ns 0 2 ⟨10, 30⟩ = ⟨10, 30⟩ := by decide

/-! ### RelposInline (225): `span{position:relative; left:50px; top:100px}` -/
theorem RelposInline_vectors :
    let ns := [Node.inline (rp 50 100)]
    mapRange ns 0 1 ⟨10, 10⟩ = ⟨10, 10⟩ ∧ mapRangeDown ns 0 1 ⟨10, 10⟩ = ⟨10, 10⟩ := by decide

/-! ### RelposInlineInRelposInline (240): inner `left:50; top:100` in outer `left:5; top:6`,
    both in a div with `padding-left:10px`. -/
theorem RelposInlineInRelposInline_vectors :
    let ns := [Node.inline (rp 50 100), .inline (rp 5 6)]
    let p : Pt := ⟨20, 10⟩
    mapRange ns 0 2 p = p ∧ mapRangeDown ns 0 2 p = p ∧
    mapRange ns 0 1 p = p ∧ mapRange ns 1 2 p = p ∧
    mapRangeDown ns 1 2 p = p ∧ mapRangeDown ns 0 1 p = p := by decide

/-! ### RelPosBlock (274): container `margin:666px; border:8px; padding:7px` >
    middle `margin:30px; border:1px` > target `position:relative; left:50px; top:50px; margin:10px`. -/
def relPosBlock : BF :=
  { mt := 666, mb := 666, ml := .px 666, mr := .px 666, bt := 8, bb := 8, bl := 8, br := 8,
    pt := 7, pb := 7, pl := 7, pr := 7,
    children := [{ id := 1, mt := 30, mb := 30, ml := .px 30, mr := .px 30,
                   bt := 1, bb := 1, bl := 1, br := 1,
                   children := [{ id := 2, mt := 10, mb := 10, ml := .px 10, mr := .px 10 }] }] }

theorem RelPosBlock_vectors :
    let f := layoutRoot 800 relPosBlock
    let m := f.kid 0
    let ns := [Node.block m (m.kid 0) (rp 50 50), .block f m]
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨106, 106⟩ ∧
    mapRangeDown ns 0 2 ⟨110, 110⟩ = ⟨4, 4⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨61, 61⟩ ∧
    mapRange ns 1 2 ⟨61, 61⟩ = ⟨106, 106⟩ ∧
    mapRangeDown ns 1 2 ⟨106, 106⟩ = ⟨61, 61⟩ ∧
    mapRangeDown ns 0 1 ⟨61, 61⟩ = ⟨0, 0⟩ := by decide

/-- A box with all four margins `m`, as a block child. -/
def mg (m : Int) (b : BF) : BF := { b with mt := m, mb := m, ml := .px m, mr := .px m }

/-- Border `bw` and padding `pw` on all sides. -/
def bp (bw pw : Nat) (b : BF) : BF :=
  { b with bt := bw, bb := bw, bl := bw, br := bw, pt := pw, pb := pw, pl := pw, pr := pw }

/-! ### AbsPos (311): `#container{position:relative; margin:666px; border:8px; padding:7px}` >
    `#staticChild{margin:30px; padding-top:666px}` > [`div{padding-top:666px}`, `#target` absolute
    `left:-1px; top:-1px; margin:10px`]. The target's marker is the second child of `#staticChild`. -/
def absPos : BF :=
  mg 666 (bp 8 7 { children := [mg 30 { id := 1, pt := 666, children := [{ pt := 666 }, { id := 2 }] }] })

theorem AbsPos_vectors :
    let f := layoutRoot 800 absPos
    let sc := f.kid 0
    let ns := [Node.oof 1 (.box absPos) (offIn sc (sc.kid 1)) (.px (-1)) (.px (-1)) (.px 10) (.px 10),
               .block f sc]
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨17, 17⟩ ∧ mapRangeDown ns 0 2 ⟨18, 18⟩ = ⟨1, 1⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨-28, -28⟩ ∧ mapRange ns 1 2 ⟨-28, -28⟩ = ⟨17, 17⟩ ∧
    mapRangeDown ns 1 2 ⟨17, 17⟩ = ⟨-28, -28⟩ ∧ mapRangeDown ns 0 1 ⟨-28, -28⟩ = ⟨0, 0⟩ := by
  decide

/-! ### AbsPosAuto (348): `#container{position:absolute; margin:666px; border:8px; padding:7px}` >
    `#staticChild{margin:30px; padding-top:5px}` > [`div{padding-top:20px}`, `#target` absolute with
    auto insets, `margin:10px`]. -/
def absPosAuto : BF :=
  mg 666 (bp 8 7 { children := [mg 30 { id := 1, pt := 5, children := [{ pt := 20 }, { id := 2 }] }] })

theorem AbsPosAuto_vectors :
    let f := layoutRoot 800 absPosAuto
    let sc := f.kid 0
    let ns := [Node.oof 1 (.box absPosAuto) (offIn sc (sc.kid 1)) .auto .auto (.px 10) (.px 10),
               .block f sc]
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨55, 80⟩ ∧ mapRangeDown ns 0 2 ⟨56, 82⟩ = ⟨1, 2⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨10, 35⟩ ∧ mapRange ns 1 2 ⟨10, 35⟩ = ⟨55, 80⟩ ∧
    mapRangeDown ns 1 2 ⟨55, 80⟩ = ⟨10, 35⟩ ∧ mapRangeDown ns 0 1 ⟨10, 35⟩ = ⟨0, 0⟩ := by
  decide

/-- The viewport (`LayoutView`) is the origin of the page; `html > body` is `htmlBody`. -/
def view : Frag := {}

/-- Shared page for the fixed-position tests: body margin 8px; `#container{position:absolute;
    margin:4px; border:5px; padding:7px}` > `#staticChild{padding-top:666px}` > [`div{padding-top:666px}`,
    a fixed-position marker]. The container's marker is the only in-flow body child. -/
def fixedPosC : BF :=
  mg 4 (bp 5 7 { children := [{ id := 1, pt := 666, children := [{ pt := 666 }, { id := 2 }] }] })

/-! ### FixedPosAuto (444): `#container{position:absolute; margin:3px; border:8px; padding:7px}` >
    `#staticChild{padding-top:5px}` > [`div{padding-top:20px}`, `#target` fixed, auto insets,
    `margin:10px`]. -/
def fixedPosAutoC : BF :=
  mg 3 (bp 8 7 { children := [{ id := 1, pt := 5, children := [{ pt := 20 }, { id := 2 }] }] })

theorem FixedPosAuto_vectors :
    let h := layoutRoot 800 (htmlBody [{ id := 5 }])
    let body := h.kid 0
    let c := layoutRoot 800 fixedPosAutoC
    let sc := c.kid 0
    let ns := [Node.oof 4 (.box {}) (offIn sc (sc.kid 1)) .auto .auto (.px 10) (.px 10),
               .block c sc, .oof 2 (.box {}) (offIn body (body.kid 0)) .auto .auto (.px 3) (.px 3),
               .block h body, .block view h]
    mapRange ns 0 5 ⟨0, 0⟩ = ⟨36, 61⟩ ∧ mapRangeDown ns 0 5 ⟨36, 61⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨10, 35⟩ ∧ mapRange ns 1 2 ⟨10, 35⟩ = ⟨25, 50⟩ ∧
    mapRange ns 2 3 ⟨25, 50⟩ = ⟨28, 53⟩ ∧ mapRange ns 3 4 ⟨28, 53⟩ = ⟨36, 61⟩ ∧
    mapRange ns 4 5 ⟨36, 61⟩ = ⟨36, 61⟩ ∧ mapRangeDown ns 4 5 ⟨36, 61⟩ = ⟨36, 61⟩ ∧
    mapRangeDown ns 3 4 ⟨36, 61⟩ = ⟨28, 53⟩ ∧ mapRangeDown ns 2 3 ⟨28, 53⟩ = ⟨25, 50⟩ ∧
    mapRangeDown ns 1 2 ⟨25, 50⟩ = ⟨10, 35⟩ ∧ mapRangeDown ns 0 1 ⟨10, 35⟩ = ⟨0, 0⟩ := by
  decide

/-! ### FixedPosInFixedPos (504): `fixedPosC` with `#outerFixed{position:fixed; left:100px;
    top:100px; margin:10px}` between `#staticChild` and a fixed `#target{left:-1px; top:-1px;
    margin:10px}`. -/
theorem FixedPosInFixedPos_vectors :
    let h := layoutRoot 800 (htmlBody [{ id := 5 }])
    let body := h.kid 0
    let c := layoutRoot 800 fixedPosC
    let sc := c.kid 0
    let ns := [Node.oof 5 (.box {}) ⟨0, 0⟩ (.px (-1)) (.px (-1)) (.px 10) (.px 10),
               .oof 4 (.box {}) (offIn sc (sc.kid 1)) (.px 100) (.px 100) (.px 10) (.px 10),
               .block c sc, .oof 2 (.box {}) (offIn body (body.kid 0)) .auto .auto (.px 4) (.px 4),
               .block h body, .block view h]
    mapRange ns 0 6 ⟨0, 0⟩ = ⟨9, 9⟩ ∧ mapRangeDown ns 0 6 ⟨9, 9⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨-101, -101⟩ ∧ mapRange ns 1 2 ⟨-101, -101⟩ = ⟨-15, -15⟩ ∧
    mapRange ns 2 3 ⟨-15, -15⟩ = ⟨-3, -3⟩ ∧ mapRange ns 3 4 ⟨-3, -3⟩ = ⟨1, 1⟩ ∧
    mapRange ns 4 5 ⟨1, 1⟩ = ⟨9, 9⟩ ∧ mapRange ns 5 6 ⟨9, 9⟩ = ⟨9, 9⟩ ∧
    mapRangeDown ns 5 6 ⟨9, 9⟩ = ⟨9, 9⟩ ∧ mapRangeDown ns 4 5 ⟨9, 9⟩ = ⟨1, 1⟩ ∧
    mapRangeDown ns 3 4 ⟨1, 1⟩ = ⟨-3, -3⟩ ∧ mapRangeDown ns 2 3 ⟨-3, -3⟩ = ⟨-15, -15⟩ ∧
    mapRangeDown ns 1 2 ⟨-15, -15⟩ = ⟨-101, -101⟩ ∧ mapRangeDown ns 0 1 ⟨-101, -101⟩ = ⟨0, 0⟩ := by
  decide

/-! ### Multi-column (CSS Multi-column 1): children are laid out in a flow thread of one column's
    width, which is a block formatting context, then placed in their columns. -/
def flowThread (cs : Cols) (kids : List BF) : BF :=
  { width := .px cs.colW, newBfc := true, children := kids }

/-- Multicol container with padding `pw` and border `bw`, `columns:n; column-gap:g`, content `w`×`h`. -/
def mcBox (bw pw w h : Nat) : BF := bp bw pw { width := .px w, height := some h }

/-! ### MulticolWithText (828), MulticolWithInline (849): the point of a text or inline box is
    shifted by the multicol container's content-box origin (`padding:5px`). -/
theorem MulticolWithText_vectors :
    let ns := [Node.inlineIn (bp 0 5 { width := .px 400 })]
    mapRange ns 0 1 ⟨220, 20⟩ = ⟨225, 25⟩ ∧ mapRangeDown ns 0 1 ⟨225, 25⟩ = ⟨220, 20⟩ := by decide

theorem MulticolWithInline_vectors :
    let ns := [Node.inlineIn (bp 0 5 { width := .px 400 })]
    mapRange ns 0 1 ⟨220, 20⟩ = ⟨225, 25⟩ ∧ mapRangeDown ns 0 1 ⟨225, 25⟩ = ⟨220, 20⟩ := by decide

/-! ### MulticolWithBlock (868): `columns:3; column-gap:0; column-fill:auto; width:300px;
    height:100px; border:8px; padding:7px`; a 110px spacer, then `#target{margin:10px; padding:13px}`. -/
def mcBlockCols : Cols := { count := 3, gap := 0, w := 300, h := 100 }

theorem MulticolWithBlock_vectors :
    let ft := layoutRoot 800 (flowThread mcBlockCols [{ height := some 110 }, mg 10 (bp 0 13 { id := 1 })])
    let ns := [Node.col (mcBox 8 7 300 100) mcBlockCols ft (ft.kid 1)]
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨125, 35⟩ ∧ mapRangeDown ns 0 1 ⟨125, 35⟩ = ⟨0, 0⟩ := by decide

/-! ### MulticolWithBlockAbove (889): `columns:3; width:300px; height:200px`; `#target{margin-top:-50px;
    height:100px}` stays in the first column. -/
def mcAboveCols : Cols := { count := 3, gap := 0, w := 300, h := 200 }

theorem MulticolWithBlockAbove_vectors :
    let ft := layoutRoot 800 (flowThread mcAboveCols [{ mt := -50, height := some 100 }])
    let ns := [Node.col (mcBox 0 0 300 200) mcAboveCols ft (ft.kid 0)]
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨0, -50⟩ ∧ mapRangeDown ns 0 1 ⟨0, -50⟩ = ⟨0, 0⟩ := by decide

/-! ### MulticolRtl (1060): `columns:4; width:400px; height:200px; direction:rtl`; a 200px spacer,
    then `#target{height:50px}`: the second column from the right. -/
def mcRtlCols : Cols := { count := 4, gap := 0, w := 400, h := 200, rtl := true }

theorem MulticolRtl_vectors :
    let ft := layoutRoot 800 (flowThread mcRtlCols [{ height := some 200 }, { id := 1, height := some 50 }])
    let ns := [Node.col (mcBox 0 0 400 200) mcRtlCols ft (ft.kid 1)]
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨200, 0⟩ ∧ mapRangeDown ns 0 1 ⟨200, 0⟩ = ⟨0, 0⟩ := by decide

/-! ### MulticolWithLargeBorder (1079): `columns:3; width:300px; height:200px; border:200px`,
    spacers of 200px around `#target{height:50px}`. -/
theorem MulticolWithLargeBorder_vectors :
    let ft := layoutRoot 800 (flowThread mcAboveCols
      [{ height := some 200 }, { id := 1, height := some 50 }, { height := some 200 }])
    let ns := [Node.col (mcBox 200 0 300 200) mcAboveCols ft (ft.kid 1)]
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨300, 200⟩ ∧ mapRangeDown ns 0 1 ⟨300, 200⟩ = ⟨0, 0⟩ := by decide

/-! ### MulticolWithAbsPosInRelPos (945): as MulticolWithBlock, a 110px spacer then
    `#relpos{position:relative; left:4px; top:4px}` holding `#target{position:absolute; left:15px;
    top:15px; margin:10px}`. -/
theorem MulticolWithAbsPosInRelPos_vectors :
    let ft := layoutRoot 800 (flowThread mcBlockCols [{ height := some 110 }, { id := 1, children := [{ id := 2 }] }])
    let rp1 := ft.kid 1
    let ns := [Node.oof 0 (.box {}) (offIn rp1 (rp1.kid 0)) (.px 15) (.px 15) (.px 10) (.px 10),
               .col (mcBox 8 7 300 100) mcBlockCols ft rp1 (rp 4 4)]
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨144, 54⟩ ∧ mapRangeDown ns 0 2 ⟨144, 54⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨25, 25⟩ ∧ mapRangeDown ns 0 1 ⟨25, 25⟩ = ⟨0, 0⟩ ∧
    mapRange ns 1 2 ⟨25, 25⟩ = ⟨144, 54⟩ ∧ mapRangeDown ns 1 2 ⟨144, 54⟩ = ⟨25, 25⟩ := by decide

/-! ### MulticolWithAbsPosInInlineRelPos (981): the same target inside
    `<span style='position:relative; left:4px; top:4px'>` in `#container`, after the spacer. -/
theorem MulticolWithAbsPosInInlineRelPos_vectors :
    let ft := layoutRoot 800 (flowThread mcBlockCols [{ height := some 110 }, { id := 1 }])
    let ns := [Node.oof 0 (.inline ⟨0, 0⟩ (rp 4 4)) ⟨0, 0⟩ (.px 15) (.px 15) (.px 10) (.px 10),
               .inline (rp 4 4), .col (mcBox 8 7 300 100) mcBlockCols ft (ft.kid 1)]
    mapRange ns 0 3 ⟨0, 0⟩ = ⟨144, 54⟩ ∧ mapRangeDown ns 0 3 ⟨144, 54⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨29, 29⟩ ∧ mapRangeDown ns 0 2 ⟨29, 29⟩ = ⟨0, 0⟩ ∧
    mapRange ns 2 3 ⟨29, 29⟩ = ⟨144, 54⟩ ∧ mapRangeDown ns 2 3 ⟨144, 54⟩ = ⟨29, 29⟩ := by decide

/-! ### MulticolWithAbsPosNotContained (1019): `#container{position:relative; margin:666px;
    border:7px; padding:3px}` > multicol (as MulticolWithBlock) > spacer, `#target{position:absolute;
    left:-1px; top:-1px; margin:10px}`; the multicol is not in the target's containing-block chain. -/
def notContained : BF := mg 666 (bp 7 3 { children := [mcBox 8 7 300 100] })

theorem MulticolWithAbsPosNotContained_vectors :
    let f := layoutRoot 800 notContained
    let ns := [Node.oof 1 (.box notContained) ⟨0, 0⟩ (.px (-1)) (.px (-1)) (.px 10) (.px 10),
               .block f (f.kid 0)]
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨16, 16⟩ ∧ mapRangeDown ns 0 2 ⟨16, 16⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨6, 6⟩ ∧ mapRange ns 1 2 ⟨6, 6⟩ = ⟨16, 16⟩ ∧
    mapRangeDown ns 1 2 ⟨16, 16⟩ = ⟨6, 6⟩ ∧ mapRangeDown ns 0 1 ⟨6, 6⟩ = ⟨0, 0⟩ := by decide

/-! ### OverflowClip (171): `#overflow{height:100px; width:100px; border:8px; padding:7px;
    overflow:scroll}` > [`div{height:200px}`, `#target{margin:10px; padding:666px}`]; scrolled to
    (32, 54). The geometry-mapper run still reads the previous paint properties right after
    `ScrollToAbsolutePositionForTest` (125,325); that stale state is not modelled, so the row is
    `partly formalized`: these are the values of the updated state and of the unscrolled one. -/
def overflowClip : BF :=
  bp 8 7 { width := .px 100, height := some 100,
           children := [{ height := some 200 }, mg 10 (bp 0 666 { id := 1 })] }

theorem OverflowClip_vectors :
    let f := layoutRoot 800 overflowClip
    let ns (s : Pt) := [Node.scrolled s (.block f (f.kid 1))]
    mapRange (ns ⟨0, 0⟩) 0 1 ⟨100, 100⟩ = ⟨125, 325⟩ ∧
    mapRangeDown (ns ⟨0, 0⟩) 0 1 ⟨125, 325⟩ = ⟨100, 100⟩ ∧
    mapRange (ns ⟨32, 54⟩) 0 1 ⟨100, 100⟩ = ⟨93, 271⟩ ∧
    mapRangeDown (ns ⟨32, 54⟩) 0 1 ⟨93, 271⟩ = ⟨100, 100⟩ := by decide

/-! ### Shared page for the scrolled-viewport tests: `body` (margin 8px) with the page scrolled by
    `s`; the `html > view` step carries the viewport's scroll offset. -/
def pageNodes (h body : Frag) (s : Pt) : List Node := [.block h body, .scrolled s (.block view h)]

/-! ### FixedPosInFixedPosScrollView (573): `#container{position:fixed; top:100px; left:100px}` >
    `#target{position:fixed; top:200px; left:200px}`, viewport scrolled by (0, 50). -/
theorem FixedPosInFixedPosScrollView_vectors :
    let h := layoutRoot 800 (htmlBody [{ id := 5 }])
    let body := h.kid 0
    let ns := [Node.oof 3 (.box {}) ⟨0, 0⟩ (.px 200) (.px 200) (.px 0) (.px 0),
               .oof 2 (.box {}) (offIn body (body.kid 0)) (.px 100) (.px 100) (.px 0) (.px 0)]
              ++ pageNodes h body ⟨0, 50⟩
    mapRange ns 0 4 ⟨0, 0⟩ = ⟨200, 200⟩ ∧ mapRangeDown ns 0 4 ⟨200, 200⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨100, 100⟩ ∧ mapRangeDown ns 0 1 ⟨100, 100⟩ = ⟨0, 0⟩ := by decide

/-! ### FixedPosInAbsolutePosScrollView (610): `#container{position:absolute; top:100px; left:100px}`
    (its containing block, the initial one, scrolls with the page) > fixed `#target{top:200px;
    left:200px}`; viewport scrolled by (0, 50). -/
theorem FixedPosInAbsolutePosScrollView_vectors :
    let h := layoutRoot 800 (htmlBody [{ id := 5 }])
    let body := h.kid 0
    let ns := [Node.oof 3 (.box {}) ⟨0, 0⟩ (.px 200) (.px 200) (.px 0) (.px 0),
               .oof 2 (.box {} ⟨0, 50⟩) (offIn body (body.kid 0)) (.px 100) (.px 100) (.px 0) (.px 0)]
              ++ pageNodes h body ⟨0, 50⟩
    mapRange ns 0 4 ⟨0, 0⟩ = ⟨200, 200⟩ ∧ mapRangeDown ns 0 4 ⟨200, 200⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨100, 150⟩ ∧ mapRangeDown ns 0 1 ⟨100, 150⟩ = ⟨0, 0⟩ := by decide

/-! ### IgnoreScrollOffset (1693): `#scroller{position:absolute; top:100px; overflow:scroll;
    100×100}` > `#box{position:absolute; top:10px; 10×10}`; scrolled to (0, 50). -/
def ignoreScrollNodes (s : Pt) : List Node :=
  [Node.oof 0 (.box { width := .px 100, height := some 100 } s) ⟨0, 0⟩ (.px 10) .auto (.px 0) (.px 0)]

theorem IgnoreScrollOffset_vectors :
    mapRange (ignoreScrollNodes ⟨0, 0⟩) 0 1 ⟨0, 0⟩ = ⟨0, 10⟩ ∧
    mapRange ((ignoreScrollNodes ⟨0, 0⟩).map Node.ignoreScroll) 0 1 ⟨0, 0⟩ = ⟨0, 10⟩ ∧
    mapRange (ignoreScrollNodes ⟨0, 50⟩) 0 1 ⟨0, 0⟩ = ⟨0, -40⟩ ∧
    mapRange ((ignoreScrollNodes ⟨0, 50⟩).map Node.ignoreScroll) 0 1 ⟨0, 0⟩ = ⟨0, 10⟩ := by decide

/-! ### FixedPositionWithScrollOffset (1818): `#target{position:fixed;
    top:200px; left:100px}` in `body`; whatever the scroll offset of the page, with or without
    ignoring it, the target is mapped to the viewport at (100, 200). -/
theorem FixedPositionWithScrollOffset_vectors (s : Pt) :
    let h := layoutRoot 800 (htmlBody [{ id := 5 }])
    let body := h.kid 0
    let ns := Node.oof 2 (.box {}) ⟨0, 0⟩ (.px 200) (.px 100) (.px 0) (.px 0) :: pageNodes h body s
    mapRange ns 0 3 ⟨0, 0⟩ = ⟨100, 200⟩ ∧ mapRange (ns.map Node.ignoreScroll) 0 3 ⟨0, 0⟩ = ⟨100, 200⟩ := by
  intro h body ns
  have key := fun rest => mapRange_oof 2 (.box {}) ⟨0, 0⟩ 200 100 (.px 0) (.px 0) rest ⟨0, 0⟩
  exact ⟨key (pageNodes h body s), key ((pageNodes h body s).map Node.ignoreScroll)⟩

/-! ### Flipped blocks (CSS Writing Modes 3 §7): the CSS `width` of a child of a `vertical-rl`
    container is its block size, its `height` its inline size; the container's own width is the
    sum of its children's block sizes. -/

/-- FlippedBlocksWritingModeWithText (1099): `vertical-rl` container > [`div{width:13px}`,
    `div{width:200px; height:400px}` with the text, `div{width:5px}`]. -/
def flipped (last : Nat) : BF :=
  { children := [{ height := some 13 }, { id := 1, width := .px 400, height := some 200 },
                 { height := some last }] }

theorem FlippedBlocksWritingModeWithText_vectors :
    let f := layoutRoot 800 (flipped 5)
    let ns := [Node.inline, Node.flow .verticalRl f (f.kid 1)]
    mapRange ns 0 1 ⟨75, 10⟩ = ⟨75, 10⟩ ∧ mapRangeDown ns 0 1 ⟨75, 10⟩ = ⟨75, 10⟩ ∧
    mapRange ns 0 2 ⟨75, 10⟩ = ⟨80, 10⟩ ∧ mapRangeDown ns 0 2 ⟨80, 10⟩ = ⟨75, 10⟩ := by decide

/-- FlippedBlocksWritingModeWithInline (1131): the same with the text in
    `<span><span id=target>` and a last sibling of width 7. -/
theorem FlippedBlocksWritingModeWithInline_vectors :
    let f := layoutRoot 800 (flipped 7)
    let ns := [Node.inline, Node.inline, Node.flow .verticalRl f (f.kid 1)]
    let p : Pt := ⟨75, 10⟩
    mapRange ns 0 1 p = p ∧ mapRangeDown ns 0 1 p = p ∧
    mapRange ns 1 2 p = p ∧ mapRangeDown ns 1 2 p = p ∧
    mapRange ns 0 2 p = p ∧ mapRangeDown ns 0 2 p = p ∧
    mapRange ns 0 3 p = ⟨82, 10⟩ ∧ mapRangeDown ns 0 3 ⟨82, 10⟩ = p := by decide

/-- FlippedBlocksWritingModeWithBlock (1183): `#container{vertical-rl; border:8px; padding:7px;
    width:200px; height:200px}` > `#middle{border:1px}` > [`div{width:30px}`,
    `#target{margin:6px; width:25px}`]. -/
def flippedBlock : BF :=
  bp 8 7 { width := .px 200, height := some 200,
           children := [bp 1 0 { children := [{ height := some 30 }, mg 6 { id := 1, height := some 25 }] }] }

theorem FlippedBlocksWritingModeWithBlock_vectors :
    let f := layoutRoot 800 flippedBlock
    let m := f.kid 0
    let ns := [Node.flow .verticalRl m (m.kid 1), Node.flow .verticalRl f m]
    mapRange ns 0 2 ⟨0, 0⟩ = ⟨153, 22⟩ ∧ mapRangeDown ns 0 2 ⟨153, 22⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨7, 7⟩ ∧ mapRangeDown ns 0 1 ⟨7, 7⟩ = ⟨0, 0⟩ ∧
    mapRange ns 1 2 ⟨7, 7⟩ = ⟨153, 22⟩ ∧ mapRangeDown ns 1 2 ⟨153, 22⟩ = ⟨7, 7⟩ := by decide

/-! ### Transforms and containing blocks of fixed boxes (CSS Transforms 1 §2, §6; CSS Containment 2
    §3.3). The page is scrolled by `(0, 50)`; mapping to the view is mapping into its border box. -/
def z : Pt := ⟨0, 0⟩

/-- A page: `html` (a new formatting context) > `body` with margin `m` > `kids`. -/
def bodyPage (m : Int) (kids : List BF) : BF :=
  { newBfc := true, children := [{ mt := m, mb := m, ml := .px m, mr := .px m, children := kids }] }

def page0 (kids : List BF) := layoutRoot 800 (htmlBody kids)

/-- FixedPosInTransform (647): `#container{transform:translateY(100px); position:absolute; left:0;
    top:100px}` > `.fixed{position:fixed; top:0}`. -/
theorem FixedPosInTransform_vectors :
    let h := page0 [{ id := 5 }]
    let body := h.kid 0
    let s : Pt := ⟨0, 50⟩
    let cont : BF := { id := 1, children := [{ id := 2 }] }
    let ns := [Node.oof (cbSteps [{ transform := true }, {}, {}]) (.box cont) z (.px 0) .auto (.px 0) (.px 0),
               .oof 2 (.box {} s) z (.px 100) (.px 0) (.px 0) (.px 0), .block h body, .scrolled s (.block view h)]
    let affs := affChain ns [none, some (z, Aff.translate ⟨0, 100⟩), none, none]
    cbSteps [{ transform := true }, {}, {}] = 0 ∧
    (mapA affs 0 4 (RPt.ofPt z)).toPt = ⟨0, 150⟩ ∧ (mapADown affs 0 4 (RPt.ofPt ⟨0, 150⟩)).toPt = z ∧
    (mapA affs 0 1 (RPt.ofPt z)).toPt = z ∧ (mapADown affs 0 1 (RPt.ofPt z)).toPt = z ∧
    (mapA affs 1 4 (RPt.ofPt z)).toPt = ⟨0, 150⟩ ∧ (mapADown affs 1 4 (RPt.ofPt ⟨0, 150⟩)).toPt = z := by
  decide

/-- FixedPosInContainPaint (689): `#container{contain:paint; position:absolute; left:0;
    top:100px}` > `.fixed{position:fixed; top:0}`. -/
theorem FixedPosInContainPaint_vectors :
    let h := page0 [{ id := 5 }]
    let body := h.kid 0
    let s : Pt := ⟨0, 50⟩
    let cont : BF := { id := 1, children := [{ id := 2 }] }
    let ns := [Node.oof (cbSteps [{ containPaint := true }, {}, {}]) (.box cont) z (.px 0) .auto (.px 0) (.px 0),
               .oof 2 (.box {} s) z (.px 100) (.px 0) (.px 0) (.px 0), .block h body, .scrolled s (.block view h)]
    let affs := affChain ns [none, none, none, none]
    cbSteps [{ containPaint := true }, {}, {}] = 0 ∧
    (mapA affs 0 4 (RPt.ofPt z)).toPt = ⟨0, 50⟩ ∧ (mapADown affs 0 4 (RPt.ofPt ⟨0, 50⟩)).toPt = z ∧
    (mapA affs 0 1 (RPt.ofPt z)).toPt = z ∧ (mapADown affs 0 1 (RPt.ofPt z)).toPt = z ∧
    (mapA affs 1 4 (RPt.ofPt z)).toPt = ⟨0, 50⟩ ∧ (mapADown affs 1 4 (RPt.ofPt ⟨0, 50⟩)).toPt = z := by
  decide

/-- LocalToAbsoluteTransform (1532): `#container{position:absolute; left:0; top:0}` >
    `#scale{transform:scale(2); transform-origin:left top}` > `#child`. -/
theorem LocalToAbsoluteTransform_vectors :
    let page := layoutRoot 800 (htmlBody [{ id := 5 }])
    let body := page.kid 0
    let cb : BF := { id := 1, children := [{ id := 2, children := [{ id := 3 }] }] }
    let cf := layoutRoot 800 cb
    let sd := cf.kid 0
    let ns := [Node.block sd (sd.kid 0), .block cf sd, .oof 2 (.box {}) z (.px 0) (.px 0) (.px 0) (.px 0),
               .block page body, .block view page]
    let affs := affChain ns [none, some (z, Aff.scale 2 2), none, none, none]
    (composeAll (affs.drop 2)).isId = true ∧
    (composeAll affs).isTranslation = false ∧
    ((composeAll affs).map (RPt.ofPt z)).toPt = z ∧
    ((composeAll affs).map (RPt.ofPt ⟨10, 20⟩)).toPt = ⟨20, 40⟩ := by decide

/-- IFrameTransformed (763): `iframe{width:500px; height:500px; transform:scale(2)}` (origin at its
    centre) holds a document scrolled by (0, 1000); a point of the viewport maps down into the
    frame's `#target` with the scale undone around the centre and the scroll added back. -/
theorem IFrameTransformed_vectors :
    let mp := layoutRoot 800 (bodyPage 0 [BF.ofPhys .horizontalTb (some 500) (some 500) {}])
    let mb := mp.kid 0
    let ifr := mb.kid 0
    let cp := layoutRoot 800 (bodyPage 0 [BF.ofPhys .horizontalTb (some 200) (some 8000) {}])
    let cbody := cp.kid 0
    let ns := [Node.block cbody (cbody.kid 0), .block cp cbody, .scrolled ⟨0, 1000⟩ (.block view cp), .inline,
               .block mb ifr, .block mp mb, .block view mp]
    let affs := affChain ns [none, none, none, none, some (Aff.center ifr, Aff.scale 2 2), none, none]
    (mapADown affs 0 7 (RPt.ofPt ⟨200, 200⟩)).toPt = ⟨225, 1225⟩ := by decide

/-! ### SVG (SVG 2 §8.2 viewBox, §8.5 `transform`): a chain of translations and scales from the
    shape up to the `<svg>` box, the last step being the viewBox transform. -/
def tr (x y : Int) : Aff := Aff.translate ⟨x, y⟩

/-- Round trip through steps `i..j` of a chain at the origin. -/
def svgAt (affs : List Aff) (j : Nat) : Pt := (mapA affs 0 j (RPt.ofPt z)).toPt

theorem SVGShape_vectors :
    let affs := [tr 100 200]
    svgAt affs 1 = ⟨100, 200⟩ ∧ (mapADown affs 0 1 (RPt.ofPt ⟨100, 200⟩)).toPt = z := by decide

theorem SVGShapeScale_vectors :
    let affs := [tr 50 80, (Aff.scale 2 2).comp (tr 50 40)]
    svgAt affs 2 = ⟨200, 240⟩ ∧ (mapADown affs 0 2 (RPt.ofPt ⟨200, 240⟩)).toPt = z := by decide

theorem SVGShapeWithViewBoxWithoutScale_vectors :
    let affs := [tr 100 50, viewBoxAff 0 0 200 200 400 200]
    svgAt affs 2 = ⟨200, 50⟩ ∧ (mapADown affs 0 2 (RPt.ofPt ⟨200, 50⟩)).toPt = z := by decide

theorem SVGShapeWithViewBoxWithScale_vectors :
    let affs := [tr 50 50, viewBoxAff 0 0 100 100 400 200]
    svgAt affs 2 = ⟨200, 100⟩ ∧ (mapADown affs 0 2 (RPt.ofPt ⟨200, 100⟩)).toPt = z := by decide

theorem SVGShapeWithViewBoxWithNonZeroOffset_vectors :
    let affs := [tr 100 100, tr 100 50, viewBoxAff 100 100 200 200 400 200]
    svgAt affs 3 = ⟨200, 50⟩ ∧ (mapADown affs 0 3 (RPt.ofPt ⟨200, 50⟩)).toPt = z := by decide

theorem SVGShapeWithViewBoxWithNonZeroOffsetAndScale_vectors :
    let affs := [tr 100 100, tr 50 50, viewBoxAff 100 100 100 100 400 200]
    svgAt affs 3 = ⟨200, 100⟩ ∧ (mapADown affs 0 3 (RPt.ofPt ⟨200, 100⟩)).toPt = z := by decide

/-- SVGForeignObject (1495): `<g transform='translate(50 50)'><foreignObject transform='translate(-25
    -25)'><div id=target style='margin-left:50px; padding:84px; 50×50'>` under `viewBox='0 0 100
    100'` in a 400×200 `<svg>`. -/
theorem SVGForeignObject_vectors :
    let fo := layoutRoot 800 { id := 1, children :=
      [{ id := 2, ml := .px 50, pl := 84, pr := 84, pt := 84, pb := 84, width := .px 50, height := some 50 }] }
    let affs := affChain [Node.block fo (fo.kid 0)] [none] ++ [tr (-25) (-25), tr 50 50, viewBoxAff 0 0 100 100 400 200]
    svgAt affs 4 = ⟨250, 50⟩ ∧ (mapADown affs 0 4 (RPt.ofPt ⟨250, 50⟩)).toPt = z ∧
    (mapADown affs 4 4 (RPt.ofPt ⟨250, 50⟩)).toPt = ⟨250, 50⟩ ∧
    (mapADown affs 2 4 (RPt.ofPt ⟨250, 50⟩)).toPt = ⟨25, -25⟩ ∧
    (mapADown affs 1 4 (RPt.ofPt ⟨250, 50⟩)).toPt = ⟨50, 0⟩ := by decide

/-! ### Elements drawn into a canvas (ElementCanvasTransform 1975 and the nested rows): a drawable
    element is mapped to the canvas by its own canvas transform alone. -/
def canvasPt (l : List CN) : Pt := canvasShift l

theorem ElementCanvasTransform_vectors :
    canvasPt [.drawable ⟨50, 60⟩] = ⟨50, 60⟩ := by decide

theorem NestedElementCanvasTransform_vectors :
    canvasPt [.drawable ⟨0, 100⟩, .drawable ⟨100, 0⟩] = ⟨0, 100⟩ := by decide

theorem NestedElementCanvasTransformWithOffset_vectors :
    let a := layoutRoot 800 { id := 1, children := [{ id := 2, mt := 20 }] }
    canvasPt [.drawable ⟨0, 100⟩, .plain ((Node.block a (a.kid 0)).hop []), .drawable ⟨100, 0⟩] = ⟨0, 100⟩ := by decide

theorem NestedElementCanvasTransformChildWithoutCanvasTransform_vectors :
    canvasPt [.drawable ⟨0, 0⟩, .drawable ⟨100, 0⟩] = ⟨0, 0⟩ := by decide

theorem NestedElementCanvasTransformNonDrawableChild_vectors :
    let a := layoutRoot 800 { id := 1, height := some 100, children := [{ id := 2, height := some 50 }] }
    canvasPt [.plain ((Node.block a (a.kid 0)).hop []), .drawable ⟨100, 0⟩] = ⟨100, 0⟩ := by decide

theorem NestedElementCanvasTransformInline_vectors :
    canvasPt [.drawable ⟨0, 100⟩, .drawable ⟨100, 0⟩] = ⟨0, 100⟩ := by decide

end TestsMapping
end ChromiumLayout
