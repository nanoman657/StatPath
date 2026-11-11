import BlockFlow
import Anchor

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow
open Anchor

-- physical_fragment_test.cc:134: DumpFragmentTreeBasic
-- Input: HTML/body with <div id="block"></div>
def basicDoc : BF := htmlBody [{ id := 2 }]

theorem DumpFragmentTreeBasic_vectors :
    let f := layoutRoot 800 basicDoc
    let body := f.kid 0
    let block := body.kid 0
    body.w = 784 ∧ body.h = 0 ∧
    block.w = 784 ∧ block.h = 0 ∧
    f.relX body = 8 ∧ f.relY body = 8 ∧
    body.relX block = 0 ∧ body.relY block = 0 := by
  decide

-- physical_fragment_test.cc:149: DumpFragmentTreeWithAbspos
-- Input: `<div id="abs" style="position:absolute;">` in the body. The box is laid out in flow only to get
-- its static position (`basicDoc`'s block; being empty, it changes nothing else). Its auto width is the
-- shrink-to-fit width of its content. The view is the containing block, so the box moves under the view.
def absBox : BF := { id := 2 }

def absAN : AN := { positioned := true, oof := true, szW := some (maxContent fuel absBox) }

theorem DumpFragmentTreeWithAbspos_vectors :
    let view : Frag := { w := 800, h := 600, kids := [layoutRoot 800 basicDoc] }
    let an : AN := { positioned := true, kids := [{ kids := [{ kids := [absAN] }] }] }
    let t := (hoistOof fuel (placeTree fuel view view an) an).1
    let html := t.kid 0
    let abs := t.kid 1
    t.kids.length = 2 ∧ html.w = 800 ∧ html.relX (html.kid 0) = 8 ∧
    (html.kid 0).kids.length = 0 ∧
    t.relX abs = 8 ∧ t.relY abs = 8 ∧ abs.w = 0 ∧ abs.h = 0 := by
  decide

-- physical_fragment_test.cc:165: DumpFragmentTreeWithAbsposInRelpos
-- Input: a `position:relative` block with `<div id="abs" style="position:absolute; left:10px; top:20px;">`.
-- The relative block is the containing block, so the box is its child, at the insets.
def relDoc : BF := htmlBody [{ id := 2, children := [absBox] }]

theorem DumpFragmentTreeWithAbsposInRelpos_vectors :
    let view : Frag := { w := 800, h := 600, kids := [layoutRoot 800 relDoc] }
    let absIn : AN := { absAN with inL := some 10, inT := some 20 }
    let an : AN :=
      { positioned := true, kids := [{ kids := [{ kids := [{ positioned := true, kids := [absIn] }] }] }] }
    let t := (hoistOof fuel (placeTree fuel view view an) an).1
    let rel := ((t.kid 0).kid 0).kid 0
    let abs := rel.kid 0
    t.kids.length = 1 ∧ rel.w = 784 ∧ rel.h = 0 ∧ rel.kids.length = 1 ∧
    rel.relX abs = 10 ∧ rel.relY abs = 20 ∧ abs.w = 0 ∧ abs.h = 0 := by
  decide

end TestsBlock
end ChromiumLayout
