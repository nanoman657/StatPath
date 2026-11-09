/-
  Test vectors transcribed from anchor_evaluator_impl_test.cc (pin 36c121be).
  Each theorem names the TEST_F it transcribes; expected rectangles are the test's EXPECT_* values.
  `anchorMap` returns the entries in tree order; the tests compare as sets (sorted/unordered).
  An empty list stands for the test's `EXPECT_FALSE(anchor_map)` (no anchor map).
-/
import Anchor

namespace ChromiumLayout
namespace TestsAnchor
open BlockFlow Anchor

/-- `html, body { margin: 0; width: 800px }` wrapping the test's `#container` children. -/
def page (container : BF) : BF := { newBfc := true, width := .px 800, children := [container] }

def entry (s : String) (x y : Int) (w : Nat) (h : Int) : AEntry := ⟨s, ⟨x, y, w, h⟩, false⟩

/-! ### AnchorNameAdd (line 71): `#div1 {width:50px;height:20px}`, `.after #div1 {anchor-name:--div1a}` -/
def oneDiv : BF := page { children := [ { id := 2, width := .px 50, height := some 20 } ] }
def oneAN (n : Option String) : AN := { kids := [ { name := n } ] }

theorem AnchorNameAdd_before :
    anchorMap ((layoutRoot 800 oneDiv).kid 0) (oneAN none) = [] := by decide

theorem AnchorNameAdd_after :
    anchorMap ((layoutRoot 800 oneDiv).kid 0) (oneAN (some "--div1a")) =
      [entry "--div1a" 0 0 50 20] := by decide

/-! ### AnchorNameChange (line 104): `anchor-name: --div1` becomes `--div1a` -/
theorem AnchorNameChange_before :
    anchorMap ((layoutRoot 800 oneDiv).kid 0) (oneAN (some "--div1")) =
      [entry "--div1" 0 0 50 20] := by decide

theorem AnchorNameChange_after :
    anchorMap ((layoutRoot 800 oneDiv).kid 0) (oneAN (some "--div1a")) =
      [entry "--div1a" 0 0 50 20] := by decide

/-! ### AnchorNameRemove (line 141): `anchor-name: --div1` becomes `none` -/
theorem AnchorNameRemove_before :
    anchorMap ((layoutRoot 800 oneDiv).kid 0) (oneAN (some "--div1")) =
      [entry "--div1" 0 0 50 20] := by decide

theorem AnchorNameRemove_after :
    anchorMap ((layoutRoot 800 oneDiv).kid 0) (oneAN none) = [] := by decide

/-! ### BlockFlow (line 175): `#div1 {height:20px}` (40px with `.after`), three named blocks -/
def blockFlowPage (h1 : Nat) : BF :=
  page { children :=
    [ { id := 2, width := .px 400, height := some h1 },
      { id := 3 },
      { id := 4, children := [ { id := 5, height := some 30 }, { id := 6 } ] } ] }

def blockFlowAN : AN :=
  { kids := [ { name := some "--div1" }, { name := some "--div2" }, { kids := [ {}, { name := some "--div3" } ] } ] }

theorem BlockFlow_before :
    anchorMap ((layoutRoot 800 (blockFlowPage 20)).kid 0) blockFlowAN =
      [entry "--div1" 0 0 400 20, entry "--div2" 0 20 800 0, entry "--div3" 0 50 800 0] := by decide

theorem BlockFlow_after :
    anchorMap ((layoutRoot 800 (blockFlowPage 40)).kid 0) blockFlowAN =
      [entry "--div1" 0 0 400 40, entry "--div2" 0 40 800 0, entry "--div3" 0 70 800 0] := by decide

/-! ### Transform (line 330): `transform: translate(100px, 100px)` on an empty block -/
theorem Transform_translate :
    anchorMap ((layoutRoot 800 (page { children := [ { id := 2 } ] })).kid 0)
      { kids := [ { name := some "--transform", tx := 100, ty := 100 } ] } =
      [entry "--transform" 100 100 800 0] := by decide

/-! ### Scroll (line 351): a 200x200 scroller holds a 400x500 anchor; scrolling to (30, 20) must not
    shift the rectangle. The scroll offset is not an input of `anchorMap`, so the layout-time
    rectangle is the answer for every scroll offset. -/
def scrollPage : BF :=
  { newBfc := true, width := .px 200, height := some 200,
    children := [ { id := 2, width := .px 400, height := some 500 } ] }

theorem Scroll_inner :
    anchorMap (layoutRoot 800 scrollPage) { kids := [ { name := some "--inner" } ] } =
      [entry "--inner" 0 0 400 500] := by decide

end TestsAnchor
end ChromiumLayout
