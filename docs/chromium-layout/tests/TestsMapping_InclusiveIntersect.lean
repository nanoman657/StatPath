/-
  Test vectors transcribed from visual_rect_mapping_test.cc, `InclusiveIntersect` (1492), pin
  36c121be. The test's HTML:
    `#ancestor{position:relative}` > `div{50×50; overflow:hidden}` >
    `#child{10×10; position:relative; left:50px}`.
-/
import Mapping

namespace ChromiumLayout
namespace TestsMapping
open BlockFlow Mapping BlockRelative

def z : Pt := ⟨0, 0⟩

theorem InclusiveIntersect_vectors :
    let child := BF.ofPhys .horizontalTb (some 10) (some 10) { id := 3 }
    let ov := BF.ofPhys .horizontalTb (some 50) (some 50) { id := 2, children := [child] }
    let f := layoutRoot 800 { id := 1, children := [ov] }
    let ovF := f.kid 0
    let childF := ovF.kid 0
    let rel : Option Insets := some (computeRelativeInsets (some 0) none none (some 50))
    let os : List (Hop × VP) :=
      vchain [.block ovF childF rel, .block f ovF none]
        [{}, VP.ofBox .horizontalTb ov ovF { overflow := true }]
    -- kEdgeInclusive: the child is moved to x = 50, touching the clip edge; the rect keeps zero width
    mapVis true false z os ⟨0, 0, 10, 10⟩ = (⟨50, 0, 0, 10⟩, true) ∧
    -- (1,1,10,10) moves to x = 51, beyond the clip: not visible
    mapVis true false z os ⟨1, 1, 10, 10⟩ = (⟨0, 0, 0, 0⟩, false) ∧
    -- without the flag, a zero-width overlap is not visible
    mapVis false false z os ⟨0, 0, 10, 10⟩ = (⟨0, 0, 0, 0⟩, false) ∧
    -- child to child: no hops, nothing clips
    mapVis false false z [] ⟨1, 1, 10, 10⟩ = (⟨1, 1, 10, 10⟩, true) := by decide

end TestsMapping
end ChromiumLayout
