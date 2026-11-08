/-
  Test vectors transcribed from map_coordinates_test.cc (pin 36c121be).
  Each theorem names the TEST_P it transcribes; expected numbers are the test's EXPECT_* values.
  Every test runs twice (with and without the geometry mapper); both runs expect the same values
  except where a row says otherwise.
-/
import Mapping

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
    let ns := [Node.oof 1 absPos (offIn sc (sc.kid 1)) (.px (-1)) (.px (-1)) (.px 10) (.px 10),
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
    let ns := [Node.oof 1 absPosAuto (offIn sc (sc.kid 1)) .auto .auto (.px 10) (.px 10),
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
    let ns := [Node.oof 4 {} (offIn sc (sc.kid 1)) .auto .auto (.px 10) (.px 10),
               .block c sc, .oof 2 {} (offIn body (body.kid 0)) .auto .auto (.px 3) (.px 3),
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
    let ns := [Node.oof 5 {} ⟨0, 0⟩ (.px (-1)) (.px (-1)) (.px 10) (.px 10),
               .oof 4 {} (offIn sc (sc.kid 1)) (.px 100) (.px 100) (.px 10) (.px 10),
               .block c sc, .oof 2 {} (offIn body (body.kid 0)) .auto .auto (.px 4) (.px 4),
               .block h body, .block view h]
    mapRange ns 0 6 ⟨0, 0⟩ = ⟨9, 9⟩ ∧ mapRangeDown ns 0 6 ⟨9, 9⟩ = ⟨0, 0⟩ ∧
    mapRange ns 0 1 ⟨0, 0⟩ = ⟨-101, -101⟩ ∧ mapRange ns 1 2 ⟨-101, -101⟩ = ⟨-15, -15⟩ ∧
    mapRange ns 2 3 ⟨-15, -15⟩ = ⟨-3, -3⟩ ∧ mapRange ns 3 4 ⟨-3, -3⟩ = ⟨1, 1⟩ ∧
    mapRange ns 4 5 ⟨1, 1⟩ = ⟨9, 9⟩ ∧ mapRange ns 5 6 ⟨9, 9⟩ = ⟨9, 9⟩ ∧
    mapRangeDown ns 5 6 ⟨9, 9⟩ = ⟨9, 9⟩ ∧ mapRangeDown ns 4 5 ⟨9, 9⟩ = ⟨1, 1⟩ ∧
    mapRangeDown ns 3 4 ⟨1, 1⟩ = ⟨-3, -3⟩ ∧ mapRangeDown ns 2 3 ⟨-3, -3⟩ = ⟨-15, -15⟩ ∧
    mapRangeDown ns 1 2 ⟨-15, -15⟩ = ⟨-101, -101⟩ ∧ mapRangeDown ns 0 1 ⟨-101, -101⟩ = ⟨0, 0⟩ := by
  decide

end TestsMapping
end ChromiumLayout
