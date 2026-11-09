/-
  Test vectors transcribed from anchor_position_scroll_data_test.cc (pin 36c121be).
  Each theorem names the TEST_F it transcribes; expected values are the test's EXPECT_* values.
-/
import Anchor

namespace ChromiumLayout
namespace TestsAnchor
open BlockFlow Anchor

/-! ### HasDataAndScrollAdjustment (line 45)
    A 20px `overflow: scroll` box holds the anchor `--a1` (modelled as a block box: only its name and
    its scroller ancestry matter here, not its geometry). Four elements follow it. -/
def hdPage : BF :=
  { newBfc := true, width := .px 300,
    children := [ { id := 2, newBfc := true, height := some 20, children := [ { id := 3, height := some 10 } ] } ] }

def hdMap : List AEntry :=
  anchorMap (layoutRoot 300 hdPage) { kids := [ { scrolls := true, kids := [ { name := some "--a1" } ] } ] }

def anchored : Positioned := { absolute := true, positionAnchor := some "--a1", usesAnchorFn := true }
def noAnchorUsage : Positioned := { absolute := true, positionAnchor := some "--a1", usesAnchorFn := false }
def noAnchor : Positioned := { absolute := true, positionAnchor := some "--b1", usesAnchorFn := true }
def notAnchorPositioned : Positioned := { positionAnchor := some "--a1", usesAnchorFn := true }

theorem HasData_anchored :
    hasScrollData anchored = true ∧ needsScrollAdjustment anchored hdMap = true := by decide

theorem HasData_noAnchorUsage :
    hasScrollData noAnchorUsage = true ∧ needsScrollAdjustment noAnchorUsage hdMap = false := by decide

theorem HasData_noAnchor :
    hasScrollData noAnchor = true ∧ needsScrollAdjustment noAnchor hdMap = false := by decide

theorem HasData_notAnchorPositioned : hasScrollData notAnchorPositioned = false := by decide

/-! ### Detach (line 94): `.anchored {position:absolute; position-anchor:--a1}` elements that are
    removed, made `display: none`, or made `position: static` lose their scroll data. -/
def detachable : Positioned := { absolute := true, positionAnchor := some "--a1" }

theorem Detach_before : hasScrollData detachable = true := by decide
theorem Detach_removed : hasScrollData { detachable with hasBox := false } = false := by decide
theorem Detach_displayNone : hasScrollData { detachable with hasBox := false } = false := by decide
theorem Detach_inFlow : hasScrollData { detachable with absolute := false } = false := by decide

/-! ### ScrollerSizeChange (line 142) and ScrollContentSizeChange (line 205)
    `#scroller {overflow:scroll; height:100px}` holds `#anchor` (empty) and `#spacer {height:400px}`.
    Scrolled to 300; then the scroller grows to 200px, or the spacer shrinks to 300px. -/
def scrollerBox (viewH spacerH : Nat) : Frag :=
  layoutRoot 300 { newBfc := true, height := some viewH,
                   children := [ { id := 2 }, { id := 3, height := some spacerH } ] }

def adjustment (off : Nat) (f : Frag) : Nat :=
  clampScroll off (contentHeight f).toNat f.h.toNat

theorem ScrollerSizeChange_values :
    adjustment 300 (scrollerBox 100 400) = 300 ∧ adjustment 300 (scrollerBox 200 400) = 200 := by decide

theorem ScrollContentSizeChange_values :
    adjustment 300 (scrollerBox 100 400) = 300 ∧ adjustment 300 (scrollerBox 100 300) = 200 := by decide

/-! ### RelayoutOnScrollEnd (line 266)
    `#cb {position:relative; width:300px; height:300px}` holds `#scroller` (300x300, scroll) with
    `#anchor {margin-top:100px; width:50px; height:50px}`; `#anchored` has `position-area: bottom`. -/
def reCb : Frag :=
  layoutRoot 300 { width := .px 300, height := some 300, children :=
    [ { id := 2, newBfc := true, width := .px 300, height := some 300,
        children := [ { id := 3, mt := 100, width := .px 50, height := some 50 },
                      { id := 4, height := some 1000 } ] } ] }

def reAnchorBottom : Int :=
  let a := (reCb.kid 0).kid 0
  a.y + a.h - reCb.y

def reHeight (scroll : Nat) : Int :=
  bottomAreaHeight reCb.h.toNat (edgeInCb reAnchorBottom [scroll])

theorem RelayoutOnScrollEnd_values : reHeight 0 = 150 ∧ reHeight 50 = 200 := by decide

/-! ### ScrollableOverflowDuringAndAfterScroll (line 392)
    `#scroller1` (200x200, relative, scroll) holds a 100px block, `#scroller2` (100x100, scroll) with
    `#anchor {height:20px}` after 230px, a 100px block, and `#positioned` (100x100,
    `left: anchor(left); top: anchor(bottom)`). Layout reads the scroller2 offset of the last scroll
    end: compositor scrolling in progress leaves the applied offset unchanged. -/
def so1 : Frag :=
  layoutRoot 200 { newBfc := true, width := .px 200, height := some 200, children :=
    [ { id := 2, height := some 100 },
      { id := 3, newBfc := true, width := .px 100, height := some 100, children :=
          [ { id := 4, height := some 230 }, { id := 5, height := some 20 }, { id := 6, height := some 230 } ] },
      { id := 7, height := some 100 } ] }

def so1AnchorBottom : Int :=
  let s2 := so1.kid 1
  let a := s2.kid 1
  a.y + a.h - so1.y

/-- `scrollHeight` of `#scroller1` when `#scroller2` has applied (last scroll end) offset `off`. -/
def so1ScrollHeight (off : Nat) : Int :=
  let top := edgeInCb so1AnchorBottom [off]
  scrollHeight (contentHeight so1) [top + 100]

theorem ScrollableOverflow_values :
    so1ScrollHeight 0 = 450 ∧ so1ScrollHeight 50 = 400 ∧ so1ScrollHeight 100 = 350 := by decide

end TestsAnchor
end ChromiumLayout
