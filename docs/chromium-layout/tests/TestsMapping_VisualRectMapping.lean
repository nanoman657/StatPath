/-
  Test vectors transcribed from visual_rect_mapping_test.cc (pin 36c121be).
  `MapToVisualRectInAncestorSpace(ancestor, rect)` is `mapV false d objs rect` over the objects from
  the target up to the child of the ancestor; `kSkipAncestorAndViewportClips` is `mapV true`.
  The destination's own scroll is not applied (the tests move the rect by it themselves).
-/
import Mapping
import MappingTransform
import MappingTransform3

namespace ChromiumLayout
namespace TestsMapping
open BlockFlow Mapping BlockAbsolute BlockRelative

/-- A page: `html` (a new formatting context) > `body` with margin `m` > `kids`. -/
def bodyPage (m : Int) (kids : List BF) : BF :=
  { newBfc := true, children := [{ mt := m, mb := m, ml := .px m, mr := .px m, children := kids }] }

def z : Pt := ⟨0, 0⟩

/-- `position:relative; left:l; top:t` (right/bottom auto). -/
def rp (l t : Int) : Option Insets := some (computeRelativeInsets (some t) none none (some l))

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

/-! ### Inline containers (FloatUnderInline 1061, InlineBlock 1120, AbsoluteUnderRelativeInline 1174
    and their `vertical-rl` variants 1089, 1199): `div{position:absolute; top:55px; left:66px}`
    (`vertical-rl`: `width:600px; height:400px`) > `span{position:relative; top:100px; left:200px}`
    (`vertical-rl`: `left:-200px`) > a 33×44 float, inline-block or absolutely positioned box. -/
def inlineHost (wm : WM) (first : Nat → Node) : List (Hop × VP) :=
  let hb := BF.ofPhys wm (some 600) (some 400) {}
  let cw := (physBox wm (layoutRoot 800 hb)).w
  let page := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
  vchain ([first cw.toNat, Node.inline, Node.oof 2 (.box {}) z (.px 55) (.px 66) (.px 0) (.px 0)]
            ++ upToView page (page.kid 0)) [{}, {}, {}, {}, {}]

def relH : Option BlockRelative.Insets := rp 200 100
def relV : Option BlockRelative.Insets := rp (-200) 100

theorem FloatUnderInline_vectors :
    let os := inlineHost .horizontalTb (fun cw => .boxInInline .horizontalTb cw 33 44 relH)
    let tl := physBox .horizontalTb (layoutRoot 800 (BF.ofPhys .horizontalTb (some 33) (some 44) {}))
    tl = ⟨0, 0, 33, 44⟩ ∧ mapV false z os tl = ⟨266, 155, 33, 44⟩ ∧
    mapV false z (os.take 1) tl = ⟨200, 100, 33, 44⟩ := by decide

theorem FloatUnderInlineVerticalRL_vectors :
    let os := inlineHost .verticalRl (fun cw => .boxInInline .verticalRl cw 44 33 relV)
    let tl := physBox .horizontalTb (layoutRoot 800 (BF.ofPhys .horizontalTb (some 33) (some 44) {}))
    tl = ⟨0, 0, 33, 44⟩ ∧ mapV false z os tl = ⟨433, 155, 33, 44⟩ ∧
    mapV false z (os.take 1) tl = ⟨367, 100, 33, 44⟩ := by decide

theorem InlineBlock_vectors :
    let os := inlineHost .horizontalTb (fun cw => .boxInInline .horizontalTb cw 33 44 relH)
    let tl := physBox .horizontalTb (layoutRoot 800 (BF.ofPhys .horizontalTb (some 33) (some 44) {}))
    tl = ⟨0, 0, 33, 44⟩ ∧ mapV false z os tl = ⟨266, 155, 33, 44⟩ ∧
    mapV false z (os.take 1) tl = ⟨200, 100, 33, 44⟩ := by decide

theorem AbsoluteUnderRelativeInline_vectors :
    let os := inlineHost .horizontalTb (fun cw =>
      .oof 0 (.inline (inlineOrigin .horizontalTb cw) relH) z (.px 50) (.px 100) (.px 0) (.px 0))
    let tl := physBox .horizontalTb (layoutRoot 800 (BF.ofPhys .horizontalTb (some 33) (some 44) {}))
    tl = ⟨0, 0, 33, 44⟩ ∧ mapV false z os tl = ⟨366, 205, 33, 44⟩ ∧
    mapV false z (os.take 1) tl = ⟨300, 150, 33, 44⟩ := by decide

theorem AbsoluteUnderRelativeInlineVerticalRL_vectors :
    let os := inlineHost .verticalRl (fun cw =>
      .oof 0 (.inline (inlineOrigin .verticalRl cw) relV) z (.px 50) (.px 100) (.px 0) (.px 0))
    let tl := physBox .horizontalTb (layoutRoot 800 (BF.ofPhys .horizontalTb (some 33) (some 44) {}))
    tl = ⟨0, 0, 33, 44⟩ ∧ mapV false z os tl = ⟨566, 205, 33, 44⟩ ∧
    mapV false z (os.take 1) tl = ⟨500, 150, 33, 44⟩ := by decide

/-! ### Elements drawn into a canvas (2143 ... 2306): the visual rect of a drawable element in its
    canvas is the rect moved by its canvas transform alone. -/
theorem ElementCanvasTransformVisualRectMapping_vectors :
    mapCanvas [.drawable ⟨50, 60⟩] ⟨0, 0, 100, 100⟩ = ⟨50, 60, 100, 100⟩ := by decide

theorem NestedElementCanvasTransformVisualRectMapping_vectors :
    mapCanvas [.drawable ⟨0, 100⟩, .drawable ⟨100, 0⟩] ⟨0, 0, 50, 50⟩ = ⟨0, 100, 50, 50⟩ := by decide

theorem NestedElementCanvasTransformWithOffsetVisualRectMapping_vectors :
    let a := layoutRoot 800 { id := 1, children := [{ id := 2, mt := 20, height := some 50 }] }
    mapCanvas [.drawable ⟨0, 100⟩, .plain ((Node.block a (a.kid 0)).hop []), .drawable ⟨100, 0⟩] ⟨0, 0, 50, 50⟩
      = ⟨0, 100, 50, 50⟩ := by decide

theorem NestedElementCanvasTransformChildWithoutCanvasTransformVisualRectMapping_vectors :
    mapCanvas [.drawable ⟨0, 0⟩, .drawable ⟨100, 0⟩] ⟨0, 0, 50, 50⟩ = ⟨0, 0, 50, 50⟩ := by decide

theorem NestedElementCanvasTransformNonDrawableChildVisualRectMapping_vectors :
    let a := layoutRoot 800 { id := 1, height := some 100, children := [{ id := 2, height := some 50 }] }
    mapCanvas [.plain ((Node.block a (a.kid 0)).hop []), .drawable ⟨100, 0⟩] ⟨0, 0, 50, 50⟩
      = ⟨100, 0, 50, 50⟩ := by decide

theorem NestedElementCanvasTransformInlineVisualRectMapping_vectors :
    mapCanvas [.drawable ⟨0, 100⟩, .drawable ⟨100, 0⟩] ⟨0, 0, 50, 50⟩ = ⟨0, 100, 50, 50⟩ := by decide

/-! ### Fixed contents (FixedContentsWithScrollOffset 1431, FixedContentsUnderViewWithScrollOffset
    1464): a `position:fixed; top:0; left:0; 400×300` box. The viewport sits at the page's scroll
    offset in the view's contents space, so a fixed box does not move with the scroll. -/
def viewportCB (s : Pt) : CB := .box {} ⟨-s.x, -s.y⟩

theorem FixedContentsWithScrollOffset_vectors :
    let page := layoutRoot 800 (bodyPage 0 [{ id := 3, height := some 10 }, { id := 4, children := [{ id := 5 }] }])
    let body := page.kid 0
    let anc := body.kid 1
    let os (s : Pt) := vchain [Node.oof 3 (viewportCB s) z (.px 0) (.px 0) (.px 0) (.px 0),
                                .block body anc, .block page body, .block view page] [{}, {}, {}, {}]
    mapV false z ((os z).take 1) ⟨0, 0, 400, 300⟩ = ⟨0, -10, 400, 300⟩ ∧
    mapV false z ((os ⟨0, 50⟩).take 1) ⟨0, 0, 400, 300⟩ = ⟨0, 40, 400, 300⟩ := by decide

theorem FixedContentsUnderViewWithScrollOffset_vectors :
    let page := layoutRoot 800 (bodyPage 0 [{ id := 3 }])
    let body := page.kid 0
    let os (s : Pt) := vchain [Node.oof 2 (viewportCB s) z (.px 0) (.px 0) (.px 0) (.px 0),
                                .block page body, .block view page] [{}, {}, {}]
    mapV false z (os z) ⟨0, 0, 400, 300⟩ = ⟨0, 0, 400, 300⟩ ∧
    mapV false z (os ⟨0, 50⟩) ⟨0, 0, 400, 300⟩ = ⟨0, 50, 400, 300⟩ := by decide

/-- FixedContentsInIframe (1392): a fixed box in a 500×500 iframe: the frame's scroll does not move
    its mapped rect. -/
theorem FixedContentsInIframe_vectors :
    let mp := layoutRoot 800 (bodyPage 0 [BF.ofPhys .horizontalTb (some 500) (some 500) {}])
    let mb := mp.kid 0
    let ifr := mb.kid 0
    let cp := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
    let os (s : Pt) := vchain [Node.oof 2 (viewportCB s) z (.px 0) (.px 0) (.px 0) (.px 0),
                                .block cp (cp.kid 0), .block view cp, .inline, .block mb ifr,
                                .block mp mb, .block view mp]
                               [{}, {}, {}, { scroll := s, clip := some (physBox .horizontalTb ifr) }, {}, {}, {}]
    mapV false z (os z) ⟨0, 0, 400, 300⟩ = ⟨0, 0, 400, 300⟩ ∧
    mapV false z (os ⟨0, 50⟩) ⟨0, 0, 400, 300⟩ = ⟨0, 0, 400, 300⟩ := by decide

/-- LayoutView (542): a 50×50 iframe in `#frameContainer`; its document is scrolled by (0, 47). A text
    rect `(4, 60, 20, 80)` of the frame is scrolled and clipped to the frame. -/
theorem LayoutView_vectors :
    let mp := layoutRoot 800 (bodyPage 0 [{ id := 3, children := [BF.ofPhys .horizontalTb (some 50) (some 50) { id := 4 }] }])
    let mb := mp.kid 0
    let fc := mb.kid 0
    let ifr := fc.kid 0
    let cp := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
    let os := vchain [Node.inline, .block cp (cp.kid 0), .block view cp, .inline, .block fc ifr,
                      .block mb fc, .block mp mb, .block view mp]
                     [{}, {}, {}, { scroll := ⟨0, 47⟩, clip := some (physBox .horizontalTb ifr) }, {}, {}, {}, {}]
    mapV false z (os.take 5) ⟨4, 60, 20, 80⟩ = ⟨4, 13, 20, 37⟩ ∧
    mapV false z os ⟨4, 60, 20, 80⟩ = ⟨4, 13, 20, 37⟩ ∧
    (mapV false z os ⟨0, 0, 0, 0⟩).isEmpty = true ∧
    mapV false z (os.take 5) ⟨4, 60, 0, 80⟩ = ⟨4, 13, 0, 37⟩ := by decide

/-- MapToVisualRectFastPathMapsToViewport (1561): `#target{position:absolute; left:15px; top:25px;
    60×40}`; mapped to the viewport (the 800×600 view clips). -/
theorem MapToVisualRectFastPathMapsToViewport_vectors :
    let page := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
    let os := vchain [Node.oof 2 (.box {}) z (.px 25) (.px 15) (.px 0) (.px 0), .block page (page.kid 0),
                      .block view page, .inline] [{}, {}, {}, { clip := some ⟨0, 0, 800, 600⟩ }]
    mapV false z os ⟨0, 0, 60, 40⟩ = ⟨15, 25, 60, 40⟩ := by decide

/-! ### Flipped scrollers (778, 912): `#container{vertical-rl; position:absolute; top:111px; left:222px;
    border-width:10px 20px 30px 40px; overflow:scroll; 50×80}` > [`#target{box-shadow:40px 20px;
    100×90}`, `div{100×100}`], scrolled to (142, 7). The scroll origin is the right edge. -/
def flipScene (tw : WM) (st : ClipStyle) (pos : Pt) :=
  let cb := withBorders .verticalRl ⟨10, 20, 30, 40⟩
    (BF.ofPhys .verticalRl (some 50) (some 80)
      { children := [BF.ofPhys tw (some 100) (some 90) { id := 1 }, BF.ofPhys .verticalRl (some 100) (some 100) {}] })
  let cf := layoutRoot 800 cb
  let page := layoutRoot 800 (bodyPage 0 [{ id := 7 }])
  (cb, cf, vchain ([Node.flow .verticalRl cf (cf.kid 0), .oof 2 (.box {}) z (.px 111) (.px 222) (.px 0) (.px 0)]
                    ++ upToView page (page.kid 0))
                  [{}, VP.ofScroller .verticalRl cb cf st pos, {}, {}])

theorem ContainerFlippedWritingModeAndOverflowScroll_vectors :
    let sc := flipScene .verticalRl { overflow := true } ⟨142, 7⟩
    let tl := visualOverflow (physBox .verticalRl (sc.2.1.kid 0)) shadow
    let cl := physBox .verticalRl sc.2.1
    scrollOrigin .verticalRl sc.1 sc.2.1 = ⟨150, 0⟩ ∧
    tl = ⟨0, 0, 140, 110⟩ ∧
    (mapV false z (sc.2.2.take 1) tl).translate ⟨8, -7⟩ = ⟨-2, 3, 140, 110⟩ ∧
    mapV false z sc.2.2 tl = ⟨262, 121, 50, 80⟩ ∧
    cl = ⟨0, 0, 110, 120⟩ ∧ mapV false z (sc.2.2.drop 1) cl = ⟨222, 111, 110, 120⟩ := by decide

theorem ContainerAndTargetDifferentFlippedWritingMode_vectors :
    let sc := flipScene .verticalLr { overflow := true } ⟨142, 7⟩
    let tl := visualOverflow (physBox .verticalLr (sc.2.1.kid 0)) shadow
    scrollOrigin .verticalRl sc.1 sc.2.1 = ⟨150, 0⟩ ∧
    tl = ⟨0, 0, 140, 110⟩ ∧
    (mapV false z (sc.2.2.take 1) tl).translate ⟨8, -7⟩ = ⟨-2, 3, 140, 110⟩ := by decide

/-! ### Rotated boxes: Perspective (1522), PerspectiveWithAnonymousTable (1542), NestedTransformsComposeAngles
    (1838), NestedTransformsFractionalPositionSnapsOnce (1891). The enclosing rect of the mapped
    corners; `perspective` applies only to the children of its box. -/
theorem Perspective_vectors :
    -- `#ancestor{perspective:100px}` > `div` > `#child{10×10; rotateY(45deg)}`: the perspective
    -- reaches only the plain `div`, which flattens
    enclose ((chain3 [({ origin := ⟨5, 5⟩, xf := Mat.rotY 45 }, ⟨0, 0⟩), ({}, ⟨0, 0⟩),
        ({ persp := some (100, ⟨400, 0⟩) }, ⟨0, 0⟩)] Mat.id).corners ⟨0, 0, 10, 10⟩) = ⟨1, 0, 8, 10⟩ := by decide

theorem PerspectiveWithAnonymousTable_vectors :
    -- `#ancestor{display:table; perspective:100px; 10×10}` > `#child{table-cell; rotateY(45deg)}`
    enclose ((chain3 [({ origin := ⟨5, 5⟩, xf := Mat.rotY 45 }, ⟨0, 0⟩),
        ({ persp := some (100, ⟨5, 5⟩) }, ⟨0, 0⟩)] Mat.id).corners ⟨0, 0, 10, 10⟩) = ⟨1, -1, 8, 12⟩ := by decide

/-- NestedTransformsComposeAngles (1838): `#parent{100×50; origin:0 0; rotate(10deg)}` >
    `#child{100×50; origin:0 0; rotate(35deg)}`: the bounding box of the 45-degree rotation of the
    child's rect is about `(-35.4, 0)` with size `106.1`, within 1.5. -/
theorem NestedTransformsComposeAngles_vectors :
    let f := layoutRoot 800 (bodyPage 0 [{ id := 1, children := [{ id := 2, height := some 50 }] }])
    let ns := [Node.block (f.kid 0) ((f.kid 0).kid 0), .block f (f.kid 0)]
    let affs := affChain ns [some (z, rotation 35), some (z, rotation 10)]
    let b := bboxOf ((composeAll affs).corners ⟨0, 0, 100, 50⟩)
    b.1.near (-354) 0 10 3 2 = true ∧ b.2.near 1061 1061 10 3 2 = true := by decide

/-- NestedTransformsFractionalPositionSnapsOnce (1891): `#container{rotate(15deg) scale(1.2)}` >
    `#child{position:absolute; left:10.25px; top:20.75px; 40×30}`: the mapped rect is non-empty and
    larger than 30 on both axes. -/
theorem NestedTransformsFractionalPositionSnapsOnce_vectors :
    let A := (Aff.about ⟨400, 0⟩ ((rotation 15).comp (Aff.scale 6 6 5))).comp ⟨4, 0, 0, 4, 41, 83, 4⟩
    let b := bboxOf (A.corners ⟨0, 0, 40, 30⟩)
    30 * (b.2.den : Int) < b.2.x ∧ 30 * (b.2.den : Int) < b.2.y := by decide

/-- RegressionTest_SkipAncestorClipExpansion (488): `#grandparent{position:relative; left:100px;
    top:100px}` > `#parent{100×100; rotate(45deg); overflow:hidden}` > `#child{20×20; rotate(-45deg)}`,
    clips skipped: the opposite rotations cancel, so the child's rect keeps its 20×20 size. -/
theorem RegressionTest_SkipAncestorClipExpansion_vectors :
    let f := layoutRoot 800 (bodyPage 0 [{ id := 1, children := [{ id := 2, width := .px 100, height := some 100, children := [{ id := 3, width := .px 20, height := some 20 }] }] }])
    let gp := f.kid 0
    let par := gp.kid 0
    let ns := [Node.block par (par.kid 0), .block gp par, .block (f) gp (rp 100 100)]
    let affs := affChain ns [some (Aff.center (par.kid 0), rotation (-45)), some (Aff.center par, rotation 45), none]
    let b := bboxOf ((composeAll (affs.take 2)).corners ⟨0, 0, 20, 20⟩)
    b.2.near 20 20 1 1 10 = true := by decide

/-- FractionalSnapping (1941): `#container{position:relative; transform-origin:0 0; transform:scale(100)}`
    holding `#a{position:absolute; left:0.25px; 1×1}` and `#b` at `0.75px`: `(25,0,100,100)` and
    `(75,0,100,100)`. -/
theorem FractionalSnapping_vectors :
    let scale100 := Aff.scale 100 100
    let pt (n : Int) := (scale100.comp ⟨4, 0, 0, 4, n, 0, 4⟩).corners ⟨0, 0, 1, 1⟩
    (bboxOf (pt 1)).1.lu = (25 * 64, 0) ∧ (bboxOf (pt 1)).2.lu = (100 * 64, 100 * 64) ∧
    (bboxOf (pt 3)).1.lu = (75 * 64, 0) ∧ (bboxOf (pt 3)).2.lu = (100 * 64, 100 * 64) := by decide

/-- SVGTransformsFastVsSlowPath (1741): `<svg width=100 height=100 viewBox="-10 10 100 200"
    preserveAspectRatio="none">` with a `20×20` rect at the user-space origin: it maps to
    `(10,-5,20,10)` and the part above the svg box is clipped away. -/
theorem SVGTransformsFastVsSlowPath_vectors :
    let A := viewBoxNone (-10) 10 100 200 100 100
    enclose (A.corners ⟨0, 0, 20, 20⟩) = ⟨10, -5, 20, 10⟩ ∧
    (enclose (A.corners ⟨0, 0, 20, 20⟩)).inter ⟨0, 0, 100, 100⟩ = ⟨10, 0, 20, 5⟩ := by decide

/-- LayoutViewDisplayNone (619): the frame's `div{100×100}` maps as in LayoutView (scrolled by
    (0, 47), clipped to the 50×50 iframe) to `(4,13,20,37)`; with `display:none` on the iframe the
    frame's body has no layout object. -/
theorem LayoutViewDisplayNone_vectors :
    let mp := layoutRoot 800 (bodyPage 0 [{ id := 3, children := [BF.ofPhys .horizontalTb (some 50) (some 50) { id := 4 }] }])
    let mb := mp.kid 0
    let fc := mb.kid 0
    let ifr := fc.kid 0
    let cp := layoutRoot 800 (bodyPage 0 [{ id := 7, width := .px 100, height := some 100 }])
    let os := vchain [Node.block (cp.kid 0) ((cp.kid 0).kid 0), .block cp (cp.kid 0), .block view cp, .inline, .block fc ifr]
                     [{}, {}, {}, { scroll := ⟨0, 47⟩, clip := some (physBox .horizontalTb ifr) }, {}]
    mapV false z os ⟨4, 60, 20, 80⟩ = ⟨4, 13, 20, 37⟩ ∧
    (layoutBox? .none (BF.ofPhys .horizontalTb (some 50) (some 50) {})).isNone = true ∧
    (layoutBox? .block (BF.ofPhys .horizontalTb (some 50) (some 50) {})).isSome = true := by decide

end TestsMapping
end ChromiumLayout
