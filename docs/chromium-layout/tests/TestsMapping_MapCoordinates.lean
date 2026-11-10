/-
  Test vectors transcribed from map_coordinates_test.cc (pin 36c121be).
  Each theorem names the TEST_P it transcribes; expected numbers are the test's EXPECT_* values.
  Every test runs twice (with and without the geometry mapper); both runs expect the same values
  except where a row says otherwise.
-/
import Mapping
import MappingTransform
import MappingTransform3

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
theorem FixedScrollOffset_vectors (s : Pt) :
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

/-- FixedPosInIFrameWhenMainFrameScrolled (732): `body{margin:0}` with an 8000px spacer, then a
    500×500 iframe whose document has `#target{position:fixed; 200×200}`; the main frame is scrolled
    by (0, 1000). A viewport point maps down into the frame with the iframe's 8000px offset and the
    scroll (the test then subtracts the scroll again, `AdjustForFrameScroll`). -/
theorem FixedPosInIFrameWhenMainFrameScrolled_vectors :
    let mp := layoutRoot 800 (bodyPage 0 [{ height := some 8000 }, BF.ofPhys .horizontalTb (some 500) (some 500) { id := 3 }])
    let mb := mp.kid 0
    let ifr := mb.kid 1
    let cp := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
    let ns := [Node.oof 2 (.box {}) z .auto .auto (.px 0) (.px 0), .block cp (cp.kid 0), .block view cp, .inline,
               .block mb ifr, .block mp mb, .scrolled ⟨0, 1000⟩ (.block view mp)]
    let affs := affChain ns [none, none, none, none, none, none, none]
    let q := (mapADown affs 0 7 (RPt.ofPt ⟨10, 70⟩)).toPt
    q = ⟨10, -6930⟩ ∧ (⟨q.x, q.y - 1000⟩ : Pt) = ⟨10, -7930⟩ := by decide

/-- Transforms (1318): `#container` > `#outerTransform{rotate(45deg); 200×200}` >
    `#innerTransform{rotate(45deg); 200×200}` > `#target{200×200}`; quads within 0.01. -/
def quadPts : List Pt := [⟨0, 0⟩, ⟨200, 0⟩, ⟨200, 200⟩, ⟨0, 200⟩]

/-- Do the mapped points match the expected hundredths within 0.01? -/
def nearAll (ps : List RPt) (es : List (Int × Int)) : Bool :=
  (ps.zip es).all (fun (p, e) => p.near e.1 e.2 100 1 100) && ps.length == es.length

theorem Transforms_vectors :
    let f := layoutRoot 800 { id := 1, children := [{ id := 2, width := .px 200, height := some 200, children :=
      [{ id := 3, width := .px 200, height := some 200, children := [{ id := 4, width := .px 200, height := some 200 }] }] }] }
    let outer := f.kid 0
    let inner := outer.kid 0
    let ns := [Node.block inner (inner.kid 0), .block outer inner, .block f outer]
    let affs := affChain ns [none, some (Aff.center inner, rotation 45), some (Aff.center outer, rotation 45)]
    let up (i j : Nat) (qs : List RPt) := qs.map (fun p => mapA affs i j p)
    let q0 := quadPts.map RPt.ofPt
    let down (i j : Nat) (qs : List RPt) := qs.map (fun p => mapADown affs i j p)
    let unit := quadPts.map (fun p => (p.x * 100, p.y * 100))
    let mid : List (Int × Int) := [(100 * 100, -4142), (24142, 10000), (10000, 24142), (-4142, 10000)]
    let top : List (Int × Int) := [(20000, 0), (20000, 20000), (0, 20000), (0, 0)]
    nearAll (up 0 3 q0) top = true ∧ nearAll (down 0 3 (up 0 3 q0)) unit = true ∧
    nearAll (up 0 1 q0) unit = true ∧ nearAll (down 0 1 (up 0 1 q0)) unit = true ∧
    nearAll (up 1 2 q0) mid = true ∧ nearAll (down 1 2 (up 1 2 q0)) unit = true ∧
    nearAll (up 2 3 (mid.map (fun e => (⟨e.1, e.2, 100⟩ : RPt)))) top = true := by decide

/-- LocalToAncestorTransform (1555): `#container` > `#rotate1{rotate(45deg); origin: left top}` >
    `#rotate2{rotate(90deg); origin: left top}` > `#child`; points within `LayoutUnit::Epsilon`
    (1/64). -/
theorem LocalToAncestorTransform_vectors :
    let f := layoutRoot 800 { id := 1, children := [{ id := 2, children := [{ id := 3, children := [{ id := 4 }] }] }] }
    let r1 := f.kid 0
    let r2 := r1.kid 0
    let ns := [Node.block r2 (r2.kid 0), .block r1 r2, .block f r1]
    let affs := affChain ns [none, some (z, rotation 90), some (z, rotation 45)]
    let p : RPt := RPt.ofPt ⟨100, 0⟩
    (composeAll (affs.take 1)).isId = true ∧
    (composeAll (affs.take 2)).isId = false ∧
    ((composeAll (affs.take 2)).map p).near 0 100 1 1 64 = true ∧
    (composeAll affs).isId = false ∧
    ((composeAll affs).map p).near (-7071068) 7071068 100000 1 64 = true := by decide

/-! ### 3D (CSS Transforms 2): Transform3DWithOffset (1645), Transform3DWithOffset2 (1668): a
    `perspective:400px` box (0×0) > `div` (with `transform-style: preserve-3d` in the second) > a
    100px spacer and a `preserve-3d; rotateY(0deg)` div > `#target{100×100; translateZ(200px)}`. -/
def quad3 (M : Mat) : List RPt :=
  [⟨0, 0⟩, ⟨100, 0⟩, ⟨100, 100⟩, ⟨0, 100⟩].map (fun p : Pt => Vec.project (M.apply (Vec.plane p.x p.y)))

def scene3 (mid : Bool) : List (Box3 × Pt) :=
  [({ origin := ⟨50, 50⟩, xf := Mat.translate3 0 0 200 }, ⟨0, 0⟩),
   ({ xf := Mat.rotY 0, preserve := true }, ⟨0, 100⟩),
   ({ preserve := mid }, ⟨0, 0⟩),
   ({ persp := some (400, ⟨0, 0⟩) }, ⟨0, 0⟩)]

theorem Transform3DWithOffset_vectors :
    nearAll (quad3 (chain3 (scene3 false) Mat.id)) [(0, 10000), (10000, 10000), (10000, 20000), (0, 20000)] = true := by
  decide

theorem Transform3DWithOffset2_vectors :
    nearAll (quad3 (chain3 (scene3 true) Mat.id)) [(0, 20000), (20000, 20000), (20000, 40000), (0, 40000)] = true := by
  decide

/-- LocalToAbsoluteTransformFlattens (1600): inside an absolutely positioned (0×0) box, `rotateY(45deg)`
    over `rotateY(-45deg)` cancel with `preserve-3d` and flatten (each keeps `cos 45 = 1/2` of x
    squared) without. -/
def flat3 (pres : Bool) : List (Box3 × Pt) :=
  [({}, ⟨0, 0⟩), ({ xf := Mat.rotY (-45), preserve := pres }, ⟨0, 0⟩),
   ({ xf := Mat.rotY 45, preserve := pres }, ⟨0, 0⟩), ({}, ⟨0, 0⟩)]

theorem LocalToAbsoluteTransformFlattens_vectors :
    let at3 (pres : Bool) (x y : Int) := Vec.project ((chain3 (flat3 pres) Mat.id).apply (Vec.plane x y))
    (at3 true 100 50).near 100 50 1 1 64 = true ∧ (at3 true 50 100).near 50 100 1 1 64 = true ∧
    (at3 false 100 50).near 50 50 1 1 64 = true ∧ (at3 false 50 100).near 25 100 1 1 64 = true := by
  decide

/-- IgnoreScrollOffsetWithWritingModes (1770): `.scroller{vertical-rl; overflow:scroll; 100×100}` >
    [`.box{position:absolute; top:10px; 10×10}`, `.spacer{2000×2000}`]. Scroll positions are
    measured from the left; the initial position is the right end (the scroll origin, 1900). -/
def vrlScroller : BF := BF.ofPhys .verticalRl (some 100) (some 100) { children := [BF.ofPhys .verticalRl (some 2000) (some 2000) {}] }

def vrlBox (pos : Pt) : List Node :=
  let f := layoutRoot 800 vrlScroller
  let o := scrollOrigin .verticalRl vrlScroller f
  let q := (LRect.mk 0 0 10 10).toPhys .verticalRl f.h
  [Node.scrolled ⟨pos.x - o.x, pos.y - o.y⟩ (.oof 0 (.box vrlScroller) ⟨q.x, q.y⟩ (.px 10) .auto (.px 0) (.px 0)) o]

theorem IgnoreScrollOffsetWithWritingModes_vectors :
    let at1 (ign : Bool) (pos : Pt) := mapRange (if ign then (vrlBox pos).map Node.ignoreScroll else vrlBox pos) 0 1 z
    scrollOrigin .verticalRl vrlScroller (layoutRoot 800 vrlScroller) = ⟨1900, 0⟩ ∧
    at1 false ⟨1900, 0⟩ = ⟨90, 10⟩ ∧ at1 true ⟨1900, 0⟩ = ⟨1990, 10⟩ ∧
    at1 false ⟨0, 50⟩ = ⟨1990, -40⟩ ∧ at1 true ⟨0, 50⟩ = ⟨1990, 10⟩ ∧
    at1 false ⟨1900, 50⟩ = ⟨90, -40⟩ ∧ at1 true ⟨1900, 50⟩ = ⟨1990, 10⟩ := by decide

/-- IgnoreScrollOffsetWithWritingModesAndNonOverlayScrollbar (1931): the scroller of 1770 with
    non-overlay scrollbars. The vertical scrollbar takes `scrollbar` px on the right and the
    horizontal one as much at the bottom, so the client box is `100 - scrollbar` square. The box
    sits at the block start, the right edge of the client box; the scroll origin is the scrollable
    overflow's block extent (the 2000px spacer) minus the client block size. The 15px scrollbar is a
    platform input of the test's `USE_NON_OVERLAY_SCROLLBARS_OR_QUIT` setting; the layout folder
    does not define it, so the value is recorded here and not checked against the platform code. -/
def vrlBarBox (scrollbar : Int) (pos : Pt) : List Node :=
  let client : Int := 100 - scrollbar
  let o : Pt := ⟨2000 - client, 0⟩
  let q := (LRect.mk 0 0 10 10).toPhys .verticalRl client
  [Node.scrolled ⟨pos.x - o.x, pos.y - o.y⟩ (.oof 0 (.box vrlScroller) ⟨q.x, q.y⟩ (.px 10) .auto (.px 0) (.px 0)) o]

theorem IgnoreScrollOffsetWithScrollbar_vectors :
    let at1 (ign : Bool) (pos : Pt) := mapRange (if ign then (vrlBarBox 15 pos).map Node.ignoreScroll else vrlBarBox 15 pos) 0 1 z
    at1 false ⟨1915, 0⟩ = ⟨75, 10⟩ ∧ at1 true ⟨1915, 0⟩ = ⟨1990, 10⟩ ∧
    at1 false ⟨0, 0⟩ = ⟨1990, 10⟩ ∧ at1 true ⟨0, 0⟩ = ⟨1990, 10⟩ := by decide

/-- IgnoreScrollOffsetForInline (1732): `.scroller{overflow:scroll; 100×100}` > `.box{display:inline;
    position:sticky; top:10px}` scrolled by 0 and by 50: the sticky box stays 10px from the top of
    the scrollport; ignoring the scroll offset leaves it at its content position. -/
theorem IgnoreScrollOffsetForInline_vectors :
    let ns (s : Pt) := [Node.scrolled s (.sticky 10 s .inline)]
    let at1 (ign : Bool) (s : Pt) := mapRange (if ign then (ns s).map Node.ignoreScroll else ns s) 0 1 z
    at1 false ⟨0, 0⟩ = ⟨0, 10⟩ ∧ at1 true ⟨0, 0⟩ = ⟨0, 10⟩ ∧
    at1 false ⟨0, 50⟩ = ⟨0, 10⟩ ∧ at1 true ⟨0, 50⟩ = ⟨0, 60⟩ := by decide

end TestsMapping
end ChromiumLayout
