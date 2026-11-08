/-
  Test vectors transcribed from visual_rect_mapping_test.cc (pin 36c121be).
  `MapToVisualRectInAncestorSpace(ancestor, rect)` is `mapV false d objs rect` over the objects from
  the target up to the child of the ancestor; `kSkipAncestorAndViewportClips` is `mapV true`.
  The destination's own scroll is not applied (the tests move the rect by it themselves).
-/
import Mapping

namespace ChromiumLayout
namespace TestsMapping
open BlockFlow Mapping BlockAbsolute

/-- A page: `html` (a new formatting context) > `body` with margin `m` > `kids`. -/
def bodyPage (m : Int) (kids : List BF) : BF :=
  { newBfc := true, children := [{ mt := m, mb := m, ml := .px m, mr := .px m, children := kids }] }

def z : Pt := ⟨0, 0⟩

/-- The viewport (`LayoutView`) at the page origin. -/
def view : Frag := {}

/-- Border width `bw` on all sides. -/
def bd (bw : Nat) (b : BF) : BF := { b with bt := bw, bb := bw, bl := bw, br := bw }

/-- The chain from a box in `body` (margin 0) up to the view: box, body, html. -/
def upToView (h body : Frag) : List Node := [.block h body, .block view h]

/-! ### LayoutText (126) and LayoutTextContainerFlippedWritingMode (165):
    `#container{overflow:scroll; width:50px; height:50px}` scrolled to y = 50, holding a text whose
    rect `(0,60,20,80)` is in the container's contents space. -/
def scroller (wm : WM) : BF := BF.ofPhys wm (some 50) (some 50) {}

def textScene (wm : WM) :=
  let h := layoutRoot 800 (bodyPage 0 [scroller wm])
  let body := h.kid 0
  let c := body.kid 0
  let ns := [Node.inline, .block body c] ++ upToView h body
  let ps := [{}, VP.ofBox wm (scroller wm) c { overflow := true } ⟨0, 50⟩, {}, {}]
  (vchain ns ps)

theorem LayoutText_vectors :
    let os := textScene .horizontalTb
    let r : PRect := ⟨0, 60, 20, 80⟩
    (mapV false z (os.take 1) r).translate ⟨0, -50⟩ = ⟨0, 10, 20, 80⟩ ∧
    mapV false z os r = ⟨0, 10, 20, 40⟩ ∧
    (mapV false z (os.take 1) ⟨0, 60, 80, 0⟩).translate ⟨0, -50⟩ = ⟨0, 10, 80, 0⟩ := by decide

theorem LayoutTextContainerFlippedWritingMode_vectors :
    let os := textScene .verticalRl
    let r : PRect := ⟨0, 60, 20, 80⟩
    (mapV false z (os.take 1) r).translate ⟨0, -50⟩ = ⟨0, 10, 20, 80⟩ ∧
    mapV false z os r = ⟨0, 10, 20, 40⟩ ∧
    (mapV false z (os.take 1) ⟨0, 60, 80, 0⟩).translate ⟨0, -50⟩ = ⟨0, 10, 80, 0⟩ := by decide

/-! ### LayoutInline (202), LayoutInlineContainerFlippedWritingMode (240): as above for an empty
    `<span id=leaf>` in the container; the empty span's visual rect stays empty. -/
theorem LayoutInline_vectors :
    let os := textScene .horizontalTb
    let r : PRect := ⟨0, 60, 20, 80⟩
    (mapV false z (os.take 1) r).translate ⟨0, -50⟩ = ⟨0, 10, 20, 80⟩ ∧
    mapV false z os r = ⟨0, 10, 20, 40⟩ ∧
    (mapV false z os ⟨0, 0, 0, 0⟩).isEmpty = true ∧
    (mapV false z (os.take 1) ⟨0, 60, 80, 0⟩).translate ⟨0, -50⟩ = ⟨0, 10, 80, 0⟩ := by decide

theorem LayoutInlineContainerFlippedWritingMode_vectors :
    let os := textScene .verticalRl
    let r : PRect := ⟨0, 60, 20, 80⟩
    (mapV false z (os.take 1) r).translate ⟨0, -50⟩ = ⟨0, 10, 20, 80⟩ ∧
    mapV false z os r = ⟨0, 10, 20, 40⟩ ∧
    (mapV false z os ⟨0, 0, 0, 0⟩).isEmpty = true ∧
    (mapV false z (os.take 1) ⟨0, 60, 80, 0⟩).translate ⟨0, -50⟩ = ⟨0, 10, 80, 0⟩ := by decide

/-! ### SkipAncestorAndViewportClipFlag (281): `#clipper{position:absolute; left:10px; top:15px;
    60×60; overflow:hidden}` > `#target{position:absolute; left:40px; top:40px; 80×80}`. -/
def clipperBF : BF := BF.ofPhys .horizontalTb (some 60) (some 60) {}

def clipScene (cl ct tl tt : Int) (w h : Nat) : List (Hop × VP) :=
  let page := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
  let body := page.kid 0
  let cb := BF.ofPhys .horizontalTb (some w) (some h) {}
  let cf := layoutRoot 800 cb
  let ns := [Node.oof 0 (.box cb) z (.px tt) (.px tl) (.px 0) (.px 0),
             .oof 2 (.box {}) z (.px ct) (.px cl) (.px 0) (.px 0)] ++ upToView page body
  vchain ns [{}, VP.ofBox .horizontalTb cb cf { overflow := true }, {}, {}]

theorem SkipAncestorAndViewportClipFlag_vectors :
    let os := clipScene 10 15 40 40 60 60
    mapV false z os ⟨0, 0, 80, 80⟩ = ⟨50, 55, 20, 20⟩ ∧
    mapV true z os ⟨0, 0, 80, 80⟩ = ⟨50, 55, 80, 80⟩ := by decide

/-! ### SkipAncestorAndViewportClipsInSubframe (419): `iframe{100×100}` in `body{margin:0}`; in the
    frame `#target{position:absolute; left:-20px; top:-30px; 80×80}`. Mapping to the viewport leaves
    the frame's view (clipped to the iframe) and the main view (the 800×600 viewport). -/
def frameScene : List (Hop × VP) :=
  let cp := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
  let mp := layoutRoot 800 (bodyPage 0 [BF.ofPhys .horizontalTb (some 100) (some 100) {}])
  let ifr := (mp.kid 0).kid 0
  vchain
    [Node.oof 2 (.box {}) z (.px (-30)) (.px (-20)) (.px 0) (.px 0), .block cp (cp.kid 0),
     .block view cp, .inline, .block (mp.kid 0) ifr, .block mp (mp.kid 0), .block view mp, .inline]
    [{}, {}, {}, { clip := some (physBox .horizontalTb ifr) }, {}, {}, {}, { clip := some ⟨0, 0, 800, 600⟩ }]

theorem SkipAncestorAndViewportClipsInSubframe_vectors :
    mapV false z frameScene ⟨0, 0, 80, 80⟩ = ⟨0, 0, 60, 50⟩ ∧
    mapV true z frameScene ⟨0, 0, 80, 80⟩ = ⟨-20, -30, 80, 80⟩ := by decide

/-- An absolutely positioned container at `(left, top)` of `body{margin:0}` with a single child `kid`
    (and its page); the container is laid out in writing mode `wm` with shrink-to-fit size. -/
def absScene (wm : WM) (kids : List BF) (st : ClipStyle) (left top : Int) (border : Nat)
    (scroll origin : Pt) (cw ch : Option Nat) :=
  let cb := bd border (shrinkWrap (BF.ofPhys wm cw ch { children := kids }))
  let cf := layoutRoot 800 cb
  let page := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
  let body := page.kid 0
  (cf, vchain ([Node.flow wm cf (cf.kid 0), .oof 2 (.box {}) z (.px top) (.px left) (.px 0) (.px 0)]
                 ++ upToView page body)
              [{}, VP.ofBox wm cb cf st scroll origin, {}, {}])

/-- Box shadow `40px 20px` on the target. -/
def shadow : List (Int × Int × Int) := [(40, 20, 0)]

/-! ### SelfFlippedWritingMode (658): `#target{writing-mode:vertical-rl; box-shadow:40px 20px;
    100×50; position:absolute; top:111px; left:222px}`. -/
theorem SelfFlippedWritingMode_vectors :
    let tb := BF.ofPhys .verticalRl (some 100) (some 50) {}
    let tf := layoutRoot 800 tb
    let page := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
    let os := vchain (Node.oof 2 (.box {}) z (.px 111) (.px 222) (.px 0) (.px 0) :: upToView page (page.kid 0))
                     [{}, {}, {}]
    let lv := visualOverflow (physBox .verticalRl tf) shadow
    lv = ⟨0, 0, 140, 70⟩ ∧ mapV false z [] lv = ⟨0, 0, 140, 70⟩ ∧
    mapV false z os lv = ⟨222, 111, 140, 70⟩ := by decide

/-! ### ContainerFlippedWritingMode (681): `#container{vertical-rl; position:absolute; top:111px;
    left:222px}` > [`#target{box-shadow:40px 20px; 100×90}`, `div{100×100}`]. -/
def flippedKids : List BF :=
  [BF.ofPhys .verticalRl (some 100) (some 90) { id := 1 }, BF.ofPhys .verticalRl (some 100) (some 100) {}]

theorem ContainerFlippedWritingMode_vectors :
    let sc := absScene .verticalRl flippedKids {} 222 111 0 z z none none
    let cf := sc.1
    let os := sc.2
    let tl := visualOverflow (physBox .verticalRl (cf.kid 0)) shadow
    let cl := physBox .verticalRl cf
    tl = ⟨0, 0, 140, 110⟩ ∧ mapV false z [] tl = ⟨0, 0, 140, 110⟩ ∧
    mapV false z (os.take 1) tl = ⟨100, 0, 140, 110⟩ ∧ mapV false z os tl = ⟨322, 111, 140, 110⟩ ∧
    cl = ⟨0, 0, 200, 100⟩ ∧ mapV false z [] cl = ⟨0, 0, 200, 100⟩ ∧
    mapV false z (os.drop 1) cl = ⟨222, 111, 200, 100⟩ := by decide

/-! ### ContainerOverflowScroll (722): `#container{position:absolute; top:111px; left:222px;
    border:10px; overflow:scroll; 50×80}` scrolled to (8, 7), holding `#target{box-shadow:40px 20px;
    100×90}`. -/
def boxKid : List BF := [BF.ofPhys .horizontalTb (some 100) (some 90) { id := 1 }]

theorem ContainerOverflowScroll_vectors :
    let sc := absScene .horizontalTb boxKid { overflow := true } 222 111 10 ⟨8, 7⟩ z (some 50) (some 80)
    let cf := sc.1
    let os := sc.2
    let tl := visualOverflow (physBox .horizontalTb (cf.kid 0)) shadow
    let cl := physBox .horizontalTb cf
    tl = ⟨0, 0, 140, 110⟩ ∧ mapV false z [] tl = ⟨0, 0, 140, 110⟩ ∧
    (mapV false z (os.take 1) tl).translate ⟨-8, -7⟩ = ⟨2, 3, 140, 110⟩ ∧
    mapV false z os tl = ⟨232, 121, 50, 80⟩ ∧
    cl = ⟨0, 0, 70, 100⟩ ∧ mapV false z [] cl = ⟨0, 0, 70, 100⟩ ∧
    mapV false z (os.drop 1) cl = ⟨222, 111, 70, 100⟩ := by decide

/-! ### CSSClip (1031): `#container{position:absolute; top:0; left:0; clip:rect(0,200px,200px,0)}`
    > `#target{400×400}`; ContainPaint (1046): `#container{position:absolute; 200×200;
    contain:paint}` > `#target{400×400}`. -/
def bigKid : List BF := [BF.ofPhys .horizontalTb (some 400) (some 400) { id := 1 }]

theorem CSSClip_vectors :
    let sc := absScene .horizontalTb bigKid { css := some (0, 200, 200, 0) } 0 0 0 z z none none
    let tl := physBox .horizontalTb (sc.1.kid 0)
    tl = ⟨0, 0, 400, 400⟩ ∧ mapV false z sc.2 tl = ⟨0, 0, 200, 200⟩ := by decide

theorem ContainPaint_vectors :
    let sc := absScene .horizontalTb bigKid { containPaint := true } 0 0 0 z z (some 200) (some 200)
    let tl := physBox .horizontalTb (sc.1.kid 0)
    tl = ⟨0, 0, 400, 400⟩ ∧ mapV false z sc.2 tl = ⟨0, 0, 200, 200⟩ := by decide

end TestsMapping
end ChromiumLayout
