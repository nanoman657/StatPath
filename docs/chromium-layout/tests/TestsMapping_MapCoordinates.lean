/-
  Test vectors transcribed from map_coordinates_test.cc (pin 36c121be).
  Each theorem names the TEST_P it transcribes; expected numbers are the test's EXPECT_* values.
  Every test runs twice (with and without the geometry mapper); both runs expect the same values
  except where a row says otherwise.
-/
import Mapping

namespace ChromiumLayout
namespace TestsMapping
open BlockFlow Mapping BlockRelative

/-- `position:relative; left:l; top:t` (right/bottom auto). -/
def rp (l t : Int) : Option Insets := some (computeRelativeInsets (some t) none none (some l))

/-! ### SimpleText (127), SimpleInline (140): the text / span is mapped to its parent -/
theorem SimpleText_vectors :
    mapUp (chain [.inline]) ⟨10, 30⟩ = ⟨10, 30⟩ ∧ mapDown (chain [.inline]) ⟨10, 30⟩ = ⟨10, 30⟩ := by
  decide

theorem SimpleInline_vectors :
    mapUp (chain [.inline]) ⟨10, 10⟩ = ⟨10, 10⟩ ∧ mapDown (chain [.inline]) ⟨10, 10⟩ = ⟨10, 10⟩ := by
  decide

/-! ### SimpleBlock (153): `margin:666px; border:8px solid; padding:7px` around
    `#target{margin:10px; border:666px; padding:666px}` (`border:666px` has no style, so width 0). -/
def simpleBlock : BF :=
  { mt := 666, mb := 666, ml := .px 666, mr := .px 666, bt := 8, bb := 8, bl := 8, br := 8,
    pt := 7, pb := 7, pl := 7, pr := 7,
    children := [{ id := 1, mt := 10, mb := 10, ml := .px 10, mr := .px 10 }] }

theorem SimpleBlock_vectors :
    let f := layoutRoot 800 simpleBlock
    let c := chain [.block f (f.kid 0)]
    mapUp c ⟨100, 100⟩ = ⟨125, 125⟩ ∧ mapDown c ⟨125, 125⟩ = ⟨100, 100⟩ := by decide

/-! ### TextInRelPosInline (210): text in `span{position:relative; left:7px; top:4px}`
    mapped to the containing div: text, then the span. -/
theorem TextInRelPosInline_vectors :
    let c := chain [.inline, .inline (rp 7 4)]
    mapUp c ⟨10, 30⟩ = ⟨10, 30⟩ ∧ mapDown c ⟨10, 30⟩ = ⟨10, 30⟩ := by decide

/-! ### RelposInline (225): `span{position:relative; left:50px; top:100px}` -/
theorem RelposInline_vectors :
    let c := chain [.inline (rp 50 100)]
    mapUp c ⟨10, 10⟩ = ⟨10, 10⟩ ∧ mapDown c ⟨10, 10⟩ = ⟨10, 10⟩ := by decide

/-! ### RelposInlineInRelposInline (240): inner `left:50; top:100` in outer `left:5; top:6`,
    both in a div with `padding-left:10px`. -/
theorem RelposInlineInRelposInline_vectors :
    let target := Node.inline (rp 50 100)
    let parent := Node.inline (rp 5 6)
    let p : Pt := ⟨20, 10⟩
    mapUp (chain [target, parent]) p = p ∧ mapDown (chain [target, parent]) p = p ∧
    mapUp (chain [target]) p = p ∧ mapUp (chain [parent]) p = p ∧
    mapDown (chain [parent]) p = p ∧ mapDown (chain [target]) p = p := by decide

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
    let tm := Node.block m (m.kid 0) (rp 50 50)
    let mc := Node.block f m
    mapUp (chain [tm, mc]) ⟨0, 0⟩ = ⟨106, 106⟩ ∧
    mapDown (chain [tm, mc]) ⟨110, 110⟩ = ⟨4, 4⟩ ∧
    mapUp (chain [tm]) ⟨0, 0⟩ = ⟨61, 61⟩ ∧
    mapUp (chain [mc]) ⟨61, 61⟩ = ⟨106, 106⟩ ∧
    mapDown (chain [mc]) ⟨106, 106⟩ = ⟨61, 61⟩ ∧
    mapDown (chain [tm]) ⟨61, 61⟩ = ⟨0, 0⟩ := by decide

end TestsMapping
end ChromiumLayout
