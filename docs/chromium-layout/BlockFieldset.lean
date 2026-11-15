import BlockWritingMode
/-
  BlockFieldset.lean: fieldset and rendered legend layout, written from
  forms/fieldset_layout_algorithm_test.cc. Owned by the block lane.
  Spec: HTML Living Standard §15.3.13 "The fieldset and legend elements" (rendering): the rendered
  legend sits in the block-start border, and the fieldset's content goes in an anonymous
  fieldset content box below it. Where the HTML spec leaves details open (centering, which
  legend margins count), the rules below are read off the tests and are Chromium-specific.
-/
namespace ChromiumLayout
namespace BlockFieldset
open BlockWritingMode

/-- Rendered legend as physical width, height and physical margins. HTML §15.3.13. -/
structure Legend where
  width : Nat
  height : Nat
  margins : Phys := ⟨0, 0, 0, 0⟩

/-- The single in-flow child of the anonymous content box, with its block size.
    CSS 2.1 §10.5 (percentage heights), CSS Positioned Layout 3 §2 (absolute fills padding box). -/
inductive Child where
  | none | fixed (bs : Nat) (is : Option Nat := none) | percent (p : Nat) | absFill

/-- Fieldset input: writing mode, physical border and padding, content-box inline size, optional
    block size and max block size (flow-relative), optional legend, child. -/
structure Fieldset where
  wm : WritingMode := .horizontalTb
  border : Phys
  padding : Phys
  inlineSize : Nat
  height : Option Nat := none
  maxHeight : Option Nat := none
  legend : Option Legend := none
  child : Child := .none

abbrev Rect := Nat × Nat × Nat × Nat

structure Result where
  size : Nat × Nat
  legend : Option Rect
  anon : Rect
  child : Option Rect

/-- Physical rect of a flow-relative box (inline offset, block offset, inline size, block size)
    inside a container of physical width `cw`. CSS Writing Modes 4 §6.2. -/
def place (wm : WritingMode) (cw i b is bs : Nat) : Rect :=
  let (x, y) := flowToPhysicalOffset wm cw bs b i
  if isVertical wm then (x, y, bs, is) else (x, y, is, bs)

/-- Block extent the legend takes: border-box block size plus its block-end margin; its
    block-start margin is ignored (`LegendOrthogonalWritingMode`, `VerticalLr`, `VerticalRl`). -/
def legendExtent (wm : WritingMode) (l : Legend) : Nat :=
  flowBlockSize wm l.width l.height + (flowMargins wm l.margins).blockEnd

/-- Block offset of the anonymous content box: below the legend if it is taller than the
    block-start border, else at the border edge. HTML §15.3.13; `Legend`, `SmallLegendLargeBorder`. -/
def anonTop (f : Fieldset) : Nat :=
  let bs := (toLogical f.wm f.border).blockStart
  match f.legend with
  | none => bs
  | some l => if bs < legendExtent f.wm l then legendExtent f.wm l else bs

/-- Legend block offset: 0 if it overflows the border, otherwise centred in the border. -/
def legendY (f : Fieldset) (l : Legend) : Nat :=
  let bs := (toLogical f.wm f.border).blockStart
  if bs < legendExtent f.wm l then 0 else (bs - flowBlockSize f.wm l.width l.height) / 2

/-- Fieldset layout: border-box block size grows to enclose the legend and anonymous box padding
    (`ZeroHeight`, `ZeroMaxHeight`, `FieldsetPaddingWithLegend`); percentage children resolve
    against the anonymous box content height (`PercentageHeightChild`). -/
def layout (f : Fieldset) : Result :=
  let b := toLogical f.wm f.border
  let p := toLogical f.wm f.padding
  let padI := p.inlineStart + p.inlineEnd
  let padB := p.blockStart + p.blockEnd
  let top := anonTop f
  let c := match f.child with | .fixed n _ => n | _ => 0
  let cbs0 := match f.height with | some h => h | none => c + (top - b.blockStart)
  let cbs := match f.maxHeight with | some m => min cbs0 m | none => cbs0
  let bsz := max (b.blockStart + b.blockEnd + padB + cbs) (top + padB + b.blockEnd)
  let isz := f.inlineSize + b.inlineStart + b.inlineEnd + padI
  let cw := if isVertical f.wm then bsz else isz
  let anonB := bsz - top - b.blockEnd
  let acw := if isVertical f.wm then anonB else f.inlineSize + padI
  { size := if isVertical f.wm then (bsz, isz) else (isz, bsz)
    legend := f.legend.map fun l =>
      place f.wm cw (b.inlineStart + p.inlineStart + (flowMargins f.wm l.margins).inlineStart)
        (legendY f l) (flowInlineSize f.wm l.width l.height) (flowBlockSize f.wm l.width l.height)
    anon := place f.wm cw b.inlineStart top (f.inlineSize + padI) anonB
    child := match f.child with
      | .none => none
      | .fixed n i => some (place f.wm acw p.inlineStart p.blockStart (i.getD f.inlineSize) n)
      | .percent q => some (place f.wm acw p.inlineStart p.blockStart f.inlineSize ((anonB - padB) * q / 100))
      | .absFill => some (place f.wm acw 0 0 (f.inlineSize + padI) anonB) }

/-- Arithmetic core of `legend_above_anon`. -/
theorem aux (a b c : Nat) :
    (if a < b + c then 0 else (a - b) / 2) + b ≤ if a < b + c then b + c else a := by
  by_cases h : a < b + c <;> simp [h] <;> omega

/-- Law: the legend never overlaps the anonymous content box in the block axis. HTML §15.3.13. -/
theorem legend_above_anon (f : Fieldset) (l : Legend) (h : f.legend = some l) :
    legendY f l + flowBlockSize f.wm l.width l.height ≤ anonTop f := by
  unfold legendY anonTop legendExtent
  simp only [toLogical, h]
  cases f.wm <;> simp only [flowBlockSize, flowMargins] <;> exact aux _ _ _

/-- Min/max inline size: border + padding plus the larger of the legend's margin box and the
    content, for both min and max (`MinMax`). Sizes are (min, max). -/
def minMax (chrome : Nat) (legend content : Nat × Nat) : Nat × Nat :=
  (chrome + max legend.1 content.1, chrome + max legend.2 content.2)

/-- One fragment of a fragmented fieldset (CSS Fragmentation 3 §3.1, HTML §15.3.13). -/
structure Frag where
  size : Nat × Nat
  legend : Option Rect := none
  anon : Option Rect := none
  child : Option Rect := none
  deriving DecidableEq, Repr

/-- Remaining fragments of the anonymous content box, its in-flow child, and the block-end border.
    CSS Fragmentation 3 §3.1, §3.3. -/
def bodyFrags (isz anonW bStart pInl childW fragH : Nat) (hasChild : Bool) :
    Nat → Nat → Nat → Nat → Nat → Nat → List Frag
  | 0, _, _, _, _, _ => []
  | fuel + 1, anonY, remAnon, remPadTop, remChild, remBorderEnd =>
    let avail := fragH - anonY
    let aSlice := min remAnon avail
    let cSlice := min remChild (avail - remPadTop)
    let remAnon' := remAnon - aSlice
    let remChild' := remChild - cSlice
    let remPadTop' := remPadTop - min remPadTop avail
    let placeBorder := remAnon' == 0 && anonY + aSlice + remBorderEnd ≤ fragH
    let bEndHere := if placeBorder then remBorderEnd else 0
    let remBorderEnd' := if placeBorder then 0 else remBorderEnd
    let frag : Frag := {
      size := (isz, anonY + aSlice + bEndHere)
      anon := some (bStart, anonY, anonW, aSlice)
      child := if hasChild && (remChild > 0 || cSlice > 0) then
                 some (pInl, remPadTop, childW, cSlice)
               else none
    }
    if remAnon' == 0 && remChild' == 0 then
      if remBorderEnd' == 0 then [frag]
      else [frag, { size := (isz, remBorderEnd') }]
    else
      frag :: bodyFrags isz anonW bStart pInl childW fragH hasChild
        fuel 0 remAnon' remPadTop' remChild' remBorderEnd'

/-- Fragment a horizontal-tb fieldset across fragmentainers of block size `fragH`.
    Borders and the rendered legend are monolithic; if `anonTop f` reaches `fragH` (unless there is
    no legend and the anonymous box is empty), the anonymous content box starts in the next
    fragmentainer. CSS Fragmentation 3 §3.1, HTML §15.3.13. -/
def fragment (fragH : Nat) (f : Fieldset) : List Frag :=
  let b := toLogical f.wm f.border
  let p := toLogical f.wm f.padding
  let padI := p.inlineStart + p.inlineEnd
  let padB := p.blockStart + p.blockEnd
  let top := anonTop f
  let isz := f.inlineSize + b.inlineStart + b.inlineEnd + padI
  let anonW := f.inlineSize + padI
  let (hasChild, childH, childW) := match f.child with
    | .fixed n w => (true, n, w.getD f.inlineSize)
    | _ => (false, 0, f.inlineSize)
  let ownAnonB := padB + match f.height with
    | some h => h - (top - b.blockStart)
    | none => childH
  let legRect := f.legend.map fun l =>
    (b.inlineStart + p.inlineStart + (flowMargins f.wm l.margins).inlineStart,
     legendY f l, l.width, l.height)
  let fuel := ownAnonB + childH + 4
  if top < fragH || (f.legend.isNone && top == fragH && ownAnonB == 0) then
    match bodyFrags isz anonW b.inlineStart p.inlineStart childW fragH hasChild
            fuel top ownAnonB p.blockStart childH b.blockEnd with
    | [] => []
    | first :: rest => { first with legend := legRect } :: rest
  else
    { size := (isz, top), legend := legRect } ::
      bodyFrags isz anonW b.inlineStart p.inlineStart childW fragH hasChild
        fuel 0 ownAnonB p.blockStart childH b.blockEnd

/-- Law: when a legend is present and `anonTop f` reaches or exceeds `fragH`, the first fragment
    contains only the header of block size `anonTop f` with no anonymous content box. -/
theorem fragment_tall_header (fragH : Nat) (f : Fieldset) (l : Legend)
    (hl : f.legend = some l) (ht : fragH ≤ anonTop f) :
    ∃ r rest, fragment fragH f = r :: rest ∧ r.size.2 = anonTop f ∧ r.anon = none := by
  have hlt : ¬ (anonTop f < fragH) := Nat.not_lt.mpr ht
  simp [fragment, hl, hlt]

end BlockFieldset
end ChromiumLayout
