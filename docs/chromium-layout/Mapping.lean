/-
  Mapping.lean: coordinate mapping between a box and its ancestors, written from
  map_coordinates_test.cc and visual_rect_mapping_test.cc (pin 36c121be), not from the C++.

  Module owned by the "mapping" lane. It imports the block lane's `BlockFlow` (box tree and
  fragments), `BlockRelative` (relative insets) unchanged. Lengths are whole pixels (`Int`).

  Section 1/2 content: points in physical border-box coordinates, one `Hop` per containing-block
  step, relative positioning (CSS 2.1 §9.4.3) and the inline-level convention.
-/
import BlockFlow
import BlockRelative
import BlockAbsolute
import ColumnLayout
import BlockWritingMode

namespace ChromiumLayout
namespace Mapping
open BlockFlow

/-- A point (or offset) in physical coordinates of some box's border box, y growing downward.
    CSS Writing Modes 3 §6.2 (physical dimensions are the coordinate space of mapping). -/
structure Pt where
  x : Int
  y : Int
  deriving DecidableEq, Repr

/-- A hop is the position of a child's border-box origin in its containing block's border-box
    coordinates (CSS 2.1 §8.1 box model, §10.1 containing block). -/
abbrev Hop := Pt

/-- Child-local point to the containing block's coordinates. -/
def Pt.up (h p : Pt) : Pt := ⟨p.x + h.x, p.y + h.y⟩

/-- Containing-block point to the child's local coordinates. -/
def Pt.down (h p : Pt) : Pt := ⟨p.x - h.x, p.y - h.y⟩

/-- Map through a chain of hops listed leaf first (`LocalToAncestorPoint`). -/
def mapUp (hs : List Hop) (p : Pt) : Pt := hs.foldl (fun q h => h.up q) p

/-- Map from the ancestor down the same chain (`AncestorToLocalPoint`). -/
def mapDown (hs : List Hop) (p : Pt) : Pt := hs.foldr (fun h q => h.down q) p

abbrev WM := BlockWritingMode.WritingMode

/-- A rectangle in physical coordinates of a container's border box. -/
structure PRect where
  x : Int
  y : Int
  w : Int
  h : Int
  deriving DecidableEq, Repr

/-- A rectangle in flow-relative coordinates of a container: inline-start offset, block-start
    offset, inline size, block size (CSS Writing Modes 3 §6.1 abstract dimensions). -/
structure LRect where
  i : Int
  b : Int
  isz : Int
  bsz : Int
  deriving DecidableEq, Repr

/-- Logical to physical rectangle inside a container whose physical width (its border-box width,
    which is its block size in a vertical mode) is `cw`: CSS Writing Modes 3 §6.4
    abstract-to-physical mappings; in `vertical-rl` the block axis runs from the right edge. -/
def LRect.toPhys (wm : WM) (cw : Int) (r : LRect) : PRect :=
  match wm with
  | .horizontalTb => ⟨r.i, r.b, r.isz, r.bsz⟩
  | .verticalLr => ⟨r.b, r.i, r.bsz, r.isz⟩
  | .verticalRl => ⟨cw - r.b - r.bsz, r.i, r.bsz, r.isz⟩

/-- Physical to logical rectangle (CSS Writing Modes 3 §6.4, the other direction). -/
def PRect.toLogical (wm : WM) (cw : Int) (p : PRect) : LRect :=
  match wm with
  | .horizontalTb => ⟨p.x, p.y, p.w, p.h⟩
  | .verticalLr => ⟨p.y, p.x, p.h, p.w⟩
  | .verticalRl => ⟨p.y, cw - p.x - p.w, p.h, p.w⟩

/-- Position of a child fragment's origin in its parent fragment (both in the one coordinate
    system `layoutRoot` uses). -/
def offIn (p c : Frag) : Pt := ⟨c.x - p.x, c.y - p.y⟩

/-- Where an empty inline box starts in a container of physical width `cw`: the block-start edge,
    the left edge in a horizontal or `vertical-lr` mode and the right edge in `vertical-rl`. -/
def inlineOrigin (wm : WM) (cw : Int) : Pt :=
  let q := (LRect.mk 0 0 0 0).toPhys wm cw
  ⟨q.x, q.y⟩

/-- Offset of an out-of-flow box on one axis, in its DOM parent's border-box coordinates
    (CSS 2.1 §10.3.7, §10.6.4; CSS Position 3 §3): a given inset is measured from the containing
    block's padding-box start (`cbB` is that start in the parent's coordinates), an `auto` inset
    keeps the static position `st`; the start margin is added either way. -/
def oofAxis (cbB st : Int) (inset : BlockAbsolute.InsetVal) (m : BlockAbsolute.MarginVal) : Int :=
  (BlockAbsolute.computeOof 0 inset .auto m .auto .auto 0).insetStart +
    match inset with | .px _ => cbB | .auto => st

/-- The containing block of an out-of-flow box (CSS 2.1 §10.1): a box, whose padding box starts
    inside its border, or an inline box, which starts at its static origin and which a relative offset shifts as a whole. -/
inductive CB where
  | box (b : BF) (scroll : Pt := ⟨0, 0⟩)
  | inline (static : Pt) (rel : Option BlockRelative.Insets := none)

/-- Padding-box origin in the border-box (box, moved by the scroll offset of its content: CSSOM View
    §13 `scrollLeft`/`scrollTop`, CSS Overflow 3 §2.2) or the relative shift (inline). -/
def CB.origin : CB → Pt
  | .box b s => ⟨b.bl - s.x, b.bt - s.y⟩
  | .inline st r => ⟨st.x + (r.map (·.left)).getD 0, st.y + (r.map (·.top)).getD 0⟩

/-- Content-box origin of a box inside its border box. -/
def contentOrigin (b : BF) : Pt := ⟨b.bl + b.pl, b.bt + b.pt⟩

/-- Multi-column container geometry, content box `w` by `h`, `column-fill: auto`
    (CSS Multi-column 1 §3 used column width, §6 column-fill, §5.1 column-gap): columns of height
    `h` are filled in turn, each `colW` wide and a gap apart. -/
structure Cols where
  count : Nat
  gap : Nat
  w : Nat
  h : Nat
  rtl : Bool := false

def Cols.colW (c : Cols) : Nat := ColumnWidth.usedWidth c.count 0 c.gap c.w

/-- Column holding flow-thread block offset `fy` (content above the first column stays in it). -/
def Cols.index (c : Cols) (fy : Int) : Nat := (fy / c.h).toNat

/-- Physical position in the content box of a block at flow-thread offset `(fx, fy)` with border-box
    width `cw`: shifted to its column; in a right-to-left container the columns run from the
    right and the extent is mirrored in the content width (CSS Multi-column 1 §3.1, CSS Writing
    Modes 3 §2.1). -/
def Cols.place (c : Cols) (fx : Int) (cw : Nat) (fy : Int) : Pt :=
  let k := c.index fy
  let s := (ColumnLayout.columnInlineOffset k c.colW c.gap : Int) + fx
  ⟨if c.rtl then c.w - s - cw else s, fy - k * c.h⟩

/-- A step of the DOM-parent chain. A block contributes its fragment offset in its parent plus
    its relative-position insets (CSS 2.1 §9.4.3: the box is shifted by `left`/`top` after normal
    flow). An inline-level object (text, inline box) holds its geometry in the coordinate space
    of its container and contributes no offset, whatever its relative offset. An out-of-flow box
    (`position:absolute` or `fixed`) sits in the padding box of its containing block, `k` steps
    above its DOM parent (`cb`: where the padding box starts); `static` is where it would sit in
    flow (the offset of a zero-size marker laid out in its place). -/
inductive Node where
  | block (parent child : Frag) (rel : Option BlockRelative.Insets := none)
  | inline (rel : Option BlockRelative.Insets := none)
  | oof (k : Nat) (cb : CB) (static : Pt) (top left : BlockAbsolute.InsetVal)
      (mt ml : BlockAbsolute.MarginVal)
  | inlineIn (container : BF)
  | boxInInline (wm : WM) (cw isz bsz : Int) (rel : Option BlockRelative.Insets)
  | scrolled (s : Pt) (n : Node)
  | flow (wm : WM) (parent child : Frag)
  | col (container : BF) (cs : Cols) (flow child : Frag) (rel : Option BlockRelative.Insets := none)

/-- The hop of a node, given the hops of the ancestors above it. -/
def Node.hop (up : List Hop) : Node → Hop
  | .block p c r => ⟨(offIn p c).x + (r.map (·.left)).getD 0, (offIn p c).y + (r.map (·.top)).getD 0⟩
  | .inline _ => ⟨0, 0⟩
  | .inlineIn c => contentOrigin c
  | .boxInInline wm cw isz bsz r =>
      let q := (LRect.mk 0 0 isz bsz).toPhys wm cw
      ⟨q.x + (r.map (·.left)).getD 0, q.y + (r.map (·.top)).getD 0⟩
  | .scrolled s n => ⟨(n.hop up).x - s.x, (n.hop up).y - s.y⟩
  | .flow wm p c =>
      let q := (LRect.mk (offIn p c).x (offIn p c).y c.w c.h).toPhys wm p.h
      ⟨q.x, q.y⟩
  | .col c cs f ch r =>
      let q := cs.place (offIn f ch).x ch.w (offIn f ch).y
      ⟨(contentOrigin c).x + q.x + (r.map (·.left)).getD 0, (contentOrigin c).y + q.y + (r.map (·.top)).getD 0⟩
  | .oof k b st t l mt ml =>
      let o := mapUp (up.take k) ⟨0, 0⟩
      ⟨oofAxis (b.origin.x - o.x) st.x l ml, oofAxis (b.origin.y - o.y) st.y t mt⟩

/-- The same containing block with its scroll offset ignored (`kIgnoreScrollOffset`). -/
def CB.ignoreScroll : CB → CB
  | .box b _ => .box b ⟨0, 0⟩
  | c => c

/-- The same node with every scroll offset ignored: a scroll container's offset is not
    subtracted (`MapCoordinatesMode::kIgnoreScrollOffset`). -/
def Node.ignoreScroll : Node → Node
  | .scrolled _ n => n.ignoreScroll
  | .oof k cb st t l mt ml => .oof k cb.ignoreScroll st t l mt ml
  | n => n

/-- Hops of a leaf-first node chain. -/
def hops : List Node → List Hop
  | [] => []
  | n :: rest => n.hop (hops rest) :: hops rest

/-- Map from step `i` to step `j` of a chain (step 0 is the leaf): `LocalToAncestorPoint`. -/
def mapRange (ns : List Node) (i j : Nat) (p : Pt) : Pt := mapUp (((hops ns).take j).drop i) p

/-- The inverse direction: `AncestorToLocalPoint`. -/
def mapRangeDown (ns : List Node) (i j : Nat) (p : Pt) : Pt := mapDown (((hops ns).take j).drop i) p

/-! ## General laws -/

theorem up_down (h p : Pt) : h.down (h.up p) = p := by
  simp [Pt.up, Pt.down]

theorem down_up (h p : Pt) : h.up (h.down p) = p := by
  simp [Pt.up, Pt.down]

/-- Mapping through A then through B equals mapping through the concatenated chain, so mapping to
    an intermediate ancestor and onward equals mapping to the far ancestor directly. -/
theorem mapUp_append (a b : List Hop) (p : Pt) : mapUp (a ++ b) p = mapUp b (mapUp a p) := by
  simp [mapUp, List.foldl_append]

/-- Same for the downward direction. -/
theorem mapDown_append (a b : List Hop) (p : Pt) : mapDown (a ++ b) p = mapDown a (mapDown b p) := by
  simp [mapDown, List.foldr_append]

/-- Mapping a point to an ancestor and back returns it. -/
theorem mapDown_mapUp (hs : List Hop) (p : Pt) : mapDown hs (mapUp hs p) = p := by
  induction hs generalizing p with
  | nil => rfl
  | cons h t ih =>
      simp only [mapUp, mapDown, List.foldl_cons, List.foldr_cons] at *
      rw [ih, up_down]

/-- Mapping a point from the ancestor and back returns it. -/
theorem mapUp_mapDown (hs : List Hop) (p : Pt) : mapUp hs (mapDown hs p) = p := by
  induction hs generalizing p with
  | nil => rfl
  | cons h t ih =>
      simp only [mapUp, mapDown, List.foldl_cons, List.foldr_cons] at *
      rw [down_up]
      exact ih p

/-- Mapping is a translation: the image of a point is the point plus the summed hop offsets. -/
theorem mapUp_eq_add (hs : List Hop) (p : Pt) :
    mapUp hs p = ⟨p.x + (hs.map (·.x)).sum, p.y + (hs.map (·.y)).sum⟩ := by
  induction hs generalizing p with
  | nil => simp [mapUp]
  | cons h t ih =>
      have := ih (h.up p)
      simp only [mapUp, List.foldl_cons] at this ⊢
      rw [this]
      simp [Pt.up, List.map_cons, List.sum_cons]
      omega

/-- An inline-level node ignores its relative offset (the offset is already part of the
    container-space geometry it carries). -/
theorem inline_ignores_rel (r r' : Option BlockRelative.Insets) (up : List Hop) :
    (Node.inline r).hop up = (Node.inline r').hop up := rfl

/-- A relatively positioned block moves by exactly its resolved `left`/`top` on top of its
    in-flow offset. -/
theorem block_rel_offset (p c : Frag) (i : BlockRelative.Insets) (up : List Hop) :
    (Node.block p c (some i)).hop up = ⟨(offIn p c).x + i.left, (offIn p c).y + i.top⟩ := rfl

/-- A scroll container's offset moves everything mapped through it by exactly that offset. -/
theorem scrolled_hop (s : Pt) (n : Node) (up : List Hop) :
    (Node.scrolled s n).hop up = ⟨(n.hop up).x - s.x, (n.hop up).y - s.y⟩ := rfl

/-- Ignoring scroll removes the offset. -/
theorem ignoreScroll_scrolled (s : Pt) (n : Node) : (Node.scrolled s n).ignoreScroll = n.ignoreScroll := rfl

/-- Ignoring scroll twice is ignoring it once. -/
theorem ignoreScroll_idem (n : Node) : n.ignoreScroll.ignoreScroll = n.ignoreScroll := by
  induction n with
  | scrolled s n ih => simpa [Node.ignoreScroll] using ih
  | oof k cb st t l mt ml => cases cb <;> simp [Node.ignoreScroll, CB.ignoreScroll]
  | _ => rfl

/-- A slice `[i, k)` splits at any `j` between. -/
theorem slice_split {α : Type} (l : List α) (i j k : Nat) (hij : i ≤ j) (hjk : j ≤ k) :
    (l.take k).drop i = (l.take j).drop i ++ (l.take k).drop j := by
  conv => lhs; rw [← List.take_append_drop (j - i) ((l.take k).drop i)]
  rw [List.take_drop, List.drop_drop, List.take_take]
  have h1 : i + (j - i) = j := by omega
  have h2 : min j k = j := by omega
  rw [h1, h2]

/-- Mapping the range `[i, j)` and then `[j, k)` equals mapping `[i, k)` directly. -/
theorem mapRange_trans (ns : List Node) (i j k : Nat) (hij : i ≤ j) (hjk : j ≤ k) (p : Pt) :
    mapRange ns j k (mapRange ns i j p) = mapRange ns i k p := by
  unfold mapRange
  rw [← mapUp_append, ← slice_split _ i j k hij hjk]

/-- Mapping a range down undoes mapping it up. -/
theorem mapRangeDown_mapRange (ns : List Node) (i j : Nat) (p : Pt) :
    mapRangeDown ns i j (mapRange ns i j p) = p := mapDown_mapUp _ _

/-- An axis of an out-of-flow box with a given inset lands at the containing block's padding-box
    start plus the inset plus the start margin. -/
theorem oofAxis_px (cbB st a : Int) (m : BlockAbsolute.MarginVal) :
    oofAxis cbB st (.px a) m
      = cbB + a + (match m with | .auto => 0 | .px v => v) := by
  cases m <;> simp [oofAxis, BlockAbsolute.computeOof] <;> omega

/-- With an `auto` inset the box keeps its static position plus its start margin, whatever the
    containing block. -/
theorem oofAxis_auto (cbB cbB' st : Int) (m : BlockAbsolute.MarginVal) :
    oofAxis cbB st .auto m = oofAxis cbB' st .auto m := rfl

/-- An out-of-flow box with given insets, mapped through its DOM parent chain to its containing
    block, lands at the containing block's border origin plus padding offset: the position in the
    containing block does not depend on the intermediate ancestors. -/
theorem oof_to_cb (k : Nat) (b : CB) (st : Pt) (t l : Int) (mt ml : BlockAbsolute.MarginVal)
    (up : List Hop) (p : Pt) :
    mapUp (Node.hop up (.oof k b st (.px t) (.px l) mt ml) :: up.take k) p
      = ⟨p.x + b.origin.x + l + (match ml with | .auto => 0 | .px v => v),
         p.y + b.origin.y + t + (match mt with | .auto => 0 | .px v => v)⟩ := by
  have h : Node.hop up (.oof k b st (.px t) (.px l) mt ml)
      = ⟨(b.origin.x - (mapUp (up.take k) ⟨0, 0⟩).x) + l + (match ml with | .auto => 0 | .px v => v),
         (b.origin.y - (mapUp (up.take k) ⟨0, 0⟩).y) + t + (match mt with | .auto => 0 | .px v => v)⟩ := by
    simp only [Node.hop, oofAxis_px]
  rw [h]
  show mapUp (up.take k) _ = _
  rw [mapUp_eq_add]
  rw [mapUp_eq_add (up.take k) ⟨0, 0⟩]
  simp only [Pt.up, Pt.mk.injEq]
  constructor <;> omega

/-- The block offset inside a column is the flow offset modulo the column height. -/
theorem Cols.place_y (c : Cols) (fx : Int) (cw : Nat) (fy : Int) (h0 : 0 ≤ fy) (hh : 0 < c.h) :
    (c.place fx cw fy).y = fy % c.h := by
  have h1 : ((fy / (c.h : Int)).toNat : Int) = fy / c.h :=
    Int.toNat_of_nonneg (Int.ediv_nonneg h0 (by omega))
  simp only [Cols.place, Cols.index]
  rw [h1, Int.emod_def, Int.mul_comm]

/-- A flow offset is recovered from its column index and the offset inside the column. -/
theorem Cols.place_recover (c : Cols) (fx : Int) (cw : Nat) (fy : Int) (h0 : 0 ≤ fy) (hh : 0 < c.h) :
    fy = (c.place fx cw fy).y + (c.index fy : Int) * c.h := by
  have h1 : ((fy / (c.h : Int)).toNat : Int) = fy / c.h :=
    Int.toNat_of_nonneg (Int.ediv_nonneg h0 (by omega))
  simp only [Cols.place, Cols.index]
  rw [h1]
  omega

/-- Offsets inside a column stay within the column height. -/
theorem Cols.place_y_lt (c : Cols) (fx : Int) (cw : Nat) (fy : Int) (h0 : 0 ≤ fy) (hh : 0 < c.h) :
    0 ≤ (c.place fx cw fy).y ∧ (c.place fx cw fy).y < c.h := by
  rw [Cols.place_y c fx cw fy h0 hh]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- An out-of-flow box whose containing block is `k` steps up lands at the containing block's
    padding-box origin plus inset plus margin, whatever the scroll offsets of the ancestors on the
    way (a fixed box under a scrolled page stays where it is). -/
theorem mapRange_oof (k : Nat) (cb : CB) (st : Pt) (t l : Int) (mt ml : BlockAbsolute.MarginVal)
    (rest : List Node) (p : Pt) :
    mapRange (Node.oof k cb st (.px t) (.px l) mt ml :: rest) 0 (k + 1) p
      = ⟨p.x + cb.origin.x + l + (match ml with | .auto => 0 | .px v => v),
         p.y + cb.origin.y + t + (match mt with | .auto => 0 | .px v => v)⟩ := by
  unfold mapRange
  have : ((hops (Node.oof k cb st (.px t) (.px l) mt ml :: rest)).take (k + 1))
      = Node.hop (hops rest) (.oof k cb st (.px t) (.px l) mt ml) :: (hops rest).take k := rfl
  rw [this, List.drop_zero]
  exact oof_to_cb k cb st t l mt ml (hops rest) p

/-- Physical-to-logical undoes logical-to-physical, in every writing mode. -/
theorem toLogical_toPhys (wm : WM) (cw : Int) (r : LRect) : (r.toPhys wm cw).toLogical wm cw = r := by
  cases wm <;> cases r <;> simp [LRect.toPhys, PRect.toLogical] <;> omega

/-- And the other way round. -/
theorem toPhys_toLogical (wm : WM) (cw : Int) (p : PRect) : (p.toLogical wm cw).toPhys wm cw = p := by
  cases wm <;> cases p <;> simp [LRect.toPhys, PRect.toLogical] <;> omega

/-- The area of a rectangle does not depend on the writing mode. -/
theorem toPhys_area (wm : WM) (cw : Int) (r : LRect) :
    (r.toPhys wm cw).w * (r.toPhys wm cw).h = r.isz * r.bsz := by
  cases wm <;> simp [LRect.toPhys, Int.mul_comm]

/-- A child that lies inside its container along both axes lies inside it physically too, in every
    writing mode (`cw`, `ch`: the container's physical width and height; `bext`, `iext`: its extent
    along the block and inline axes). -/
theorem toPhys_inside (wm : WM) (cw ch bext iext : Int) (r : LRect)
    (hext : (wm = .horizontalTb ∧ bext = ch ∧ iext = cw) ∨ (wm ≠ .horizontalTb ∧ bext = cw ∧ iext = ch))
    (h0 : 0 ≤ r.b) (h1 : 0 ≤ r.i) (hb : r.b + r.bsz ≤ bext) (hi : r.i + r.isz ≤ iext) :
    0 ≤ (r.toPhys wm cw).x ∧ (r.toPhys wm cw).x + (r.toPhys wm cw).w ≤ cw ∧
    0 ≤ (r.toPhys wm cw).y ∧ (r.toPhys wm cw).y + (r.toPhys wm cw).h ≤ ch := by
  cases wm <;> simp [LRect.toPhys] at hext ⊢ <;> omega

/-- In a horizontal container a flowed child is placed exactly as a plain block. -/
theorem flow_horizontalTb (p c : Frag) (up : List Hop) :
    (Node.flow .horizontalTb p c).hop up = (Node.block p c).hop up := by
  simp [Node.hop, LRect.toPhys, offIn]

/-! ## Visual rectangles (section 6) -/

def PRect.translate (r : PRect) (p : Pt) : PRect := ⟨r.x + p.x, r.y + p.y, r.w, r.h⟩

/-- Intersection of two rectangles; empty (zero extent) when they do not overlap. -/
def PRect.inter (a b : PRect) : PRect :=
  let x := max a.x b.x
  let y := max a.y b.y
  ⟨x, y, max 0 (min (a.x + a.w) (b.x + b.w) - x), max 0 (min (a.y + a.h) (b.y + b.h) - y)⟩

/-- Bounding box of two rectangles. -/
def PRect.union (a b : PRect) : PRect :=
  let x := min a.x b.x
  let y := min a.y b.y
  ⟨x, y, max (a.x + a.w) (b.x + b.w) - x, max (a.y + a.h) (b.y + b.h) - y⟩

def PRect.isEmpty (r : PRect) : Bool := r.w ≤ 0 || r.h ≤ 0

/-- `r` lies inside `a` (an empty `r` lies inside everything). -/
def PRect.Within (r a : PRect) : Prop :=
  r.w ≤ 0 ∨ r.h ≤ 0 ∨ (a.x ≤ r.x ∧ r.x + r.w ≤ a.x + a.w ∧ a.y ≤ r.y ∧ r.y + r.h ≤ a.y + a.h)

/-- What clips the descendants of a box: `overflow` other than `visible` and `contain: paint` clip to
    the padding box (CSS Overflow 3 §3.1 overflow clip edge, CSS Containment 2 §3.3 paint
    containment), and `clip: rect(top, right, bottom, left)` on a positioned box clips to that
    rectangle relative to the border box (CSS Masking 1 §6.1 the clip property). -/
structure ClipStyle where
  overflow : Bool := false
  containPaint : Bool := false
  css : Option (Int × Int × Int × Int) := none

def ClipStyle.rect (st : ClipStyle) (pad : PRect) : Option PRect :=
  let a := if st.overflow || st.containPaint then some pad else none
  let c := st.css.map (fun (t, r, b, l) => PRect.mk l t (r - l) (b - t))
  match a, c with
  | some a, some c => some (a.inter c)
  | a, none => a
  | none, c => c

/-- Padding box of a box with physical borders, inside its physical border box `p`. -/
def paddingBox (b : BF) (p : PRect) : PRect :=
  ⟨b.bl, b.bt, p.w - b.bl - b.br, p.h - b.bt - b.bb⟩

/-- Physical border box of a fragment in its own coordinates, in writing mode `wm`. -/
def physBox (wm : WM) (f : Frag) : PRect := (LRect.mk 0 0 f.w f.h).toPhys wm f.h

/-- A box given by CSS physical `width` and `height`, as the logical box `BlockFlow` lays out:
    in a vertical writing mode the CSS width is the block size (CSS Writing Modes 3 §7.1). -/
def BF.ofPhys (wm : WM) (w h : Option Nat) (b : BF) : BF :=
  match wm with
  | .horizontalTb => { b with width := (w.map .px).getD b.width, height := h }
  | _ => { b with width := (h.map .px).getD b.width, height := w }

/-- Visual overflow of a box: its border box and its box shadows, offset by `(dx, dy)` and grown by
    `spread` (CSS Backgrounds 3 §7.1; blur is not modelled). -/
def visualOverflow (border : PRect) (shadows : List (Int × Int × Int)) : PRect :=
  shadows.foldl (fun acc (dx, dy, sp) =>
    acc.union ⟨border.x + dx - sp, border.y + dy - sp, border.w + 2 * sp, border.h + 2 * sp⟩) border

/-- Per-object data of a visual-rect step: position, scroll position, scroll origin of the
    contents space (nonzero for a flipped scroller), and the clip of its descendants. -/
structure VP where
  scroll : Pt := ⟨0, 0⟩
  origin : Pt := ⟨0, 0⟩
  clip : Option PRect := none

/-- Rectangle leaving a container: moved by its scroll position, then clipped to its clip. With
    `skip`, clips are ignored (`kSkipAncestorAndViewportClips`). -/
def leave (skip : Bool) (o : VP) (r : PRect) : PRect :=
  let r1 := r.translate ⟨-o.scroll.x, -o.scroll.y⟩
  match o.clip with
  | some c => if skip then r1 else r1.inter c
  | none => r1

/-- `MapToVisualRectInAncestorSpace`: hops and properties of the objects from the target up to the
    child of the destination (leaf first); `d` is the destination's scroll origin. -/
def mapV (skip : Bool) (d : Pt) : List (Hop × VP) → PRect → PRect
  | [], r => r
  | [(h, _)], r => (r.translate h).translate ⟨-d.x, -d.y⟩
  | (h, _) :: (h', o') :: rest, r => mapV skip d ((h', o') :: rest) (leave skip o' (r.translate h))

/-- Hops and properties of a chain of nodes. -/
def vchain (ns : List Node) (ps : List VP) : List (Hop × VP) := (hops ns).zip ps

/-- The intersection lies inside both operands. -/
theorem inter_within_left (a b : PRect) : (a.inter b).Within a := by
  unfold PRect.inter PRect.Within; dsimp only; omega

theorem inter_within_right (a b : PRect) : (a.inter b).Within b := by
  unfold PRect.inter PRect.Within; dsimp only; omega

theorem within_trans (r a b : PRect) (h : r.Within a) (h' : a.Within b) : r.Within b := by
  unfold PRect.Within at *; omega

theorem translate_within (r a : PRect) (p : Pt) (h : r.Within a) : (r.translate p).Within (a.translate p) := by
  unfold PRect.translate PRect.Within at *; dsimp only; omega

/-- A box lies inside its visual overflow (`visualOverflow` only grows it). -/
theorem union_left (a b : PRect) : a.Within (a.union b) := by
  unfold PRect.union PRect.Within; dsimp only; omega

theorem leave_within (o : VP) (r r' : PRect) (h : r.Within r') : (leave false o r).Within (leave true o r') := by
  unfold leave
  have h1 := translate_within r r' ⟨-o.scroll.x, -o.scroll.y⟩ h
  cases hc : o.clip with
  | none => simpa using h1
  | some c =>
      simp only [Bool.false_eq_true, ite_false, ite_true]
      exact within_trans _ _ _ (inter_within_left _ _) h1

/-- A visual rectangle is never larger than the unclipped one: mapping with the clips of the
    ancestors leaves a rectangle inside what mapping without them gives
    (`kSkipAncestorAndViewportClips`), whatever the chain. -/
theorem mapV_within (d : Pt) (os : List (Hop × VP)) (r r' : PRect) (h : r.Within r') :
    (mapV false d os r).Within (mapV true d os r') := by
  induction os generalizing r r' with
  | nil => simpa [mapV] using h
  | cons x t ih =>
      cases t with
      | nil =>
          simp only [mapV]
          exact translate_within _ _ _ (translate_within _ _ _ h)
      | cons y rest =>
          simp only [mapV]
          exact ih _ _ (leave_within _ _ _ (translate_within _ _ _ h))

theorem translate_empty (r : PRect) (p : Pt) (h : r.isEmpty = true) : (r.translate p).isEmpty = true := by
  unfold PRect.translate PRect.isEmpty at *
  simp only [Bool.or_eq_true, decide_eq_true_eq] at *
  exact h

theorem leave_empty (skip : Bool) (o : VP) (r : PRect) (h : r.isEmpty = true) : (leave skip o r).isEmpty = true := by
  unfold leave
  have h1 := translate_empty r ⟨-o.scroll.x, -o.scroll.y⟩ h
  cases hc : o.clip with
  | none => simpa using h1
  | some c =>
      cases skip
      · simp only [Bool.false_eq_true, ite_false]
        unfold PRect.isEmpty PRect.inter PRect.translate at *
        simp only [Bool.or_eq_true, decide_eq_true_eq] at *
        omega
      · simpa using h1

/-- An empty rectangle stays empty along any chain. -/
theorem mapV_empty (skip : Bool) (d : Pt) (os : List (Hop × VP)) (r : PRect) (h : r.isEmpty = true) :
    (mapV skip d os r).isEmpty = true := by
  induction os generalizing r with
  | nil => simpa [mapV] using h
  | cons x t ih =>
      cases t with
      | nil => simp only [mapV]; exact translate_empty _ _ (translate_empty _ _ h)
      | cons y rest => simp only [mapV]; exact ih _ (leave_empty _ _ _ (translate_empty _ _ h))


/-- The scroll and clip data of a box: its scroll position and origin, and the clip its
    `ClipStyle` imposes on its descendants, in the box's physical coordinates. -/
def VP.ofBox (wm : WM) (b : BF) (f : Frag) (st : ClipStyle) (scroll : Pt := ⟨0, 0⟩)
    (origin : Pt := ⟨0, 0⟩) : VP :=
  { scroll := scroll, origin := origin, clip := st.rect (paddingBox b (physBox wm f)) }

/-- Shrink-to-fit inline size of an `auto`-width box (CSS 2.1 §10.3.7 absolutely positioned,
    §10.3.5 floats): its max-content width. -/
def shrinkWrap (b : BF) : BF :=
  match b.width with
  | .auto => { b with width := .px (maxContent fuel b - b.hpad) }
  | _ => b

end Mapping
end ChromiumLayout
