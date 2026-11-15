import BlockWritingMode
/-
  FlexScroll.lean: geometry of a scrollable flex container with one overflowing item, written from
  layout_flexible_box_test.cc (GeometriesWithScrollbars*).
  Spec: CSS Flexbox 1 §5.1 (main and cross axes, `flex-direction`, items start at the main-start and
  cross-start edges), CSS Writing Modes 4 §6 (flow-relative directions), CSS Overflow 3 §2.2
  (scrollable overflow includes the item's margin box and the padding at the end side of the
  scrollport content; it never shrinks the padding box). Classic scrollbars take 15px (vertical,
  left side only in horizontal-tb with direction rtl) and 16px (horizontal, bottom) from the padding
  box. Scroll offsets are measured from the padding box (CSS Overflow 3 §2.3 scroll origin).
  Scrollbar placement for horizontal-tb rtl follows CSS Overflow 3 / Writing Modes (inline-start
  scrollbar); vertical writing modes keep the vertical scrollbar on the right (read off the tests).
-/
namespace ChromiumLayout
namespace FlexScroll
open BlockWritingMode

inductive FlexDir where
  | row | rowReverse | column | columnReverse
  deriving DecidableEq, Repr

/-- Rectangle as (x, y, width, height). -/
abbrev R := Int × Int × Int × Int

structure Cfg where
  wm : WritingMode
  rtl : Bool
  fd : FlexDir
  contentW : Int
  contentH : Int
  border : Phys
  padding : Phys
  scrollbarW : Int
  scrollbarH : Int
  childW : Int
  childH : Int

structure Out where
  borderBox : R
  paddingBox : R
  contentBox : R
  originAdjust : Int × Int
  overflow : R
  maxScroll : Int × Int
  minScroll : Int × Int
  scrollOrigin : Int × Int
  child : Int × Int
  deriving DecidableEq, Repr

/-- Which physical axes the item starts at the far end of (flipX, flipY). CSS Flexbox 1 §5.1 with
    CSS Writing Modes 4 §6: row uses the inline axis, column the block axis; `*-reverse` and `rtl`
    (inline) and vertical-rl (block) flip the start edge; the cross axis starts at its own flow-start. -/
def flips (c : Cfg) : Bool × Bool :=
  let fi := c.rtl
  let fb := c.wm == .verticalRl
  let rev := c.fd == .rowReverse || c.fd == .columnReverse
  let isRow := c.fd == .row || c.fd == .rowReverse
  let main := (if isRow then fi else fb) != rev
  let cross := if isRow then fb else fi
  if (isRow && isVertical c.wm) || (!isRow && !isVertical c.wm) then (cross, main) else (main, cross)

/-- Geometry. CSS Overflow 3 §2.2, §2.3; CSS Box Model 3 §3. -/
def layout (c : Cfg) : Out :=
  let sbLeft := c.wm == .horizontalTb && c.rtl
  let bw := c.border.left + c.padding.left + c.contentW + c.padding.right + c.border.right
  let bh := c.border.top + c.padding.top + c.contentH + c.padding.bottom + c.border.bottom
  let adj : Int := if sbLeft then c.scrollbarW else 0
  let pb : R := (c.border.left + adj, c.border.top, bw - c.border.left - c.border.right - c.scrollbarW,
                 bh - c.border.top - c.border.bottom - c.scrollbarH)
  let cb : R := (pb.1 + c.padding.left, pb.2.1 + c.padding.top, pb.2.2.1 - c.padding.left - c.padding.right,
                 pb.2.2.2 - c.padding.top - c.padding.bottom)
  let (fx, fy) := flips c
  let cx := if fx then cb.1 + cb.2.2.1 - c.childW else cb.1
  let cy := if fy then cb.2.1 + cb.2.2.2 - c.childH else cb.2.1
  let left := min pb.1 (if fx then cx - c.padding.left else cx)
  let top := min pb.2.1 (if fy then cy - c.padding.top else cy)
  let right := max (pb.1 + pb.2.2.1) (if fx then cx + c.childW else cx + c.childW + c.padding.right)
  let bottom := max (pb.2.1 + pb.2.2.2) (if fy then cy + c.childH else cy + c.childH + c.padding.bottom)
  { borderBox := (0, 0, bw, bh), paddingBox := pb, contentBox := cb, originAdjust := (adj, 0),
    overflow := (left, top, right - left, bottom - top),
    maxScroll := (right - (pb.1 + pb.2.2.1), bottom - (pb.2.1 + pb.2.2.2)),
    minScroll := (left - pb.1, top - pb.2.1),
    scrollOrigin := (pb.1 - left, pb.2.1 - top), child := (cx, cy) }

/-- Law: the scrollable overflow rectangle always contains the padding box, so the maximum scroll
    offset is never negative and the minimum never positive (CSS Overflow 3 §2.2). -/
theorem scroll_range (c : Cfg) : 0 ≤ (layout c).maxScroll.1 ∧ 0 ≤ (layout c).maxScroll.2 ∧
    (layout c).minScroll.1 ≤ 0 ∧ (layout c).minScroll.2 ≤ 0 := by
  simp only [layout]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Law: scroll origin is minus the minimum scroll offset (the scroll position starts at the
    flow-start edge). -/
theorem origin_eq_neg_min (c : Cfg) : (layout c).scrollOrigin = (-(layout c).minScroll.1, -(layout c).minScroll.2) := by
  simp only [layout]
  ext <;> simp <;> omega

/-- Law: when a non-negative child fits within the content box and padding is non-negative,
    scrollable overflow equals the padding box and the scroll range is zero (CSS Overflow 3 §2.2). -/
theorem no_overflow_zero_scroll (c : Cfg)
    (_hW0 : 0 ≤ c.childW) (_hH0 : 0 ≤ c.childH)
    (_hPL : 0 ≤ c.padding.left) (_hPR : 0 ≤ c.padding.right)
    (_hPT : 0 ≤ c.padding.top) (_hPB : 0 ≤ c.padding.bottom)
    (_hW : c.childW ≤ c.contentW - c.scrollbarW)
    (_hH : c.childH ≤ c.contentH - c.scrollbarH) :
    (layout c).overflow = (layout c).paddingBox ∧
    (layout c).maxScroll = (0, 0) ∧
    (layout c).minScroll = (0, 0) ∧
    (layout c).scrollOrigin = (0, 0) := by
  simp only [layout]
  rcases flips c with ⟨fx, fy⟩
  cases fx <;> cases fy <;> simp <;> omega

end FlexScroll
end ChromiumLayout
