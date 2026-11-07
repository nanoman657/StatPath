/-
  BlockLength.lean: CSS length resolution, content contributions, fragment sizes and the aspect
  ratio, written from length_utils_test.cc (pin 36c121be). Owned by the block lane.

  Units are plain whole numbers (px); the aspect-ratio saturation vector uses raw `LayoutUnit`
  (1/64 px). `none` for an optional size means *indefinite*; for a maximum it means "no limit"
  (`LayoutUnit::Max()`).
-/
namespace ChromiumLayout
namespace BlockLength

/-- Horizontal margin: `auto` or a signed pixel length (needed by `TestAutoMargins`, and by
    `BlockFlow.BF`). -/
inductive MLen where
  | auto
  | px (n : Int)

/-- A CSS size property value (length_utils_test.cc: `TestResolveInlineLength`,
    `TestComputeContentContribution`, `TestComputeInlineSizeForFragment`,
    `TestComputeBlockSizeForFragment`). `calc a b` is `calc(a px + b%)`. -/
inductive L where
  | auto
  | px (n : Nat)
  | pct (n : Nat)
  | stretch
  | minContent
  | maxContent
  | fitContent
  | calc (a b : Int)

/-- `box-sizing`. -/
inductive Sizing where
  | contentBox
  | borderBox

/-- Border-box min-content and max-content sizes (`MinMaxSizes`). -/
structure MinMax where
  min : Nat
  max : Nat
  deriving DecidableEq, Repr

/-- Value of a length against an available size (`avail`, none when indefinite) and the box's
    min/max-content sizes: `none` for `auto` or an indefinite percentage
    (`TestResolveInlineLength`, `TestResolveBlockLength`, `TestIndefiniteResolveInlineLength`). -/
def resolveLen (avail : Option Nat) (sizes : Option MinMax) : L → Option Nat
  | .auto => none
  | .px n => some n
  | .pct p => avail.map (fun a => a * p / 100)
  | .stretch => avail
  | .minContent => sizes.map (·.min)
  | .maxContent => sizes.map (·.max)
  | .fitContent =>
      match sizes, avail with
      | some s, some a => some (Nat.min (Nat.max s.min a) s.max)
      | _, _ => none
  | .calc a b => avail.map (fun av => (a + (av : Int) * b / 100).toNat)

/-- Border-box value of a specified length: `content-box` adds border+padding, `border-box`
    never goes below border+padding; intrinsic keywords and `stretch` are already border-box
    (`TestComputeInlineSizeForFragment` tests 10-16, `TestComputeBlockSizeForFragment` 10-13). -/
def toBorderBox (sz : Sizing) (bp : Nat) (l : L) (v : Nat) : Nat :=
  match l with
  | .minContent | .maxContent | .fitContent | .stretch => v
  | _ => match sz with
         | .contentBox => v + bp
         | .borderBox => Nat.max v bp

/-- `ResolveMaxInlineLength` (`TestIndefiniteResolveInlineLength`): `none` = `LayoutUnit::Max()`;
    an indefinite percentage or `stretch` is unlimited. -/
def resolveMax (avail : Option Nat) (sizes : Option MinMax) (l : L) : Option Nat :=
  resolveLen avail sizes l

/-- `ResolveMinInlineLength` (`TestIndefiniteResolveInlineLength`): `auto` / indefinite is 0. -/
def resolveMin (avail : Option Nat) (sizes : Option MinMax) (l : L) : Nat :=
  (resolveLen avail sizes l).getD 0

/-- Clamp a border-box size by min/max lengths; the minimum wins over the maximum
    (`TestComputeContentContribution` test8: min-width 80, max-width 35 gives 80). -/
def clampSize (sz : Sizing) (bp : Nat) (avail : Option Nat) (sizes : Option MinMax)
    (minL maxL : L) (v : Nat) : Nat :=
  let v1 := match resolveLen avail sizes maxL with
    | some m => Nat.min v (toBorderBox sz bp maxL m)
    | none => v
  match resolveLen avail sizes minL with
  | some m => Nat.max v1 (toBorderBox sz bp minL m)
  | none => v1

/-- `ComputeMinAndMaxContentContribution` (`TestComputeContentContribution`): percentages,
    `stretch` and `calc` with a percentage are cyclic and use the content sizes; definite and
    keyword widths replace them; min/max-width clamp. `sizes` are the box's border-box
    min/max-content sizes. -/
def contribution (sz : Sizing) (bp : Nat) (width minL maxL : L) (sizes : MinMax) : MinMax :=
  let base : MinMax :=
    match width with
    | .px n => let v := toBorderBox sz bp width n; ⟨v, v⟩
    | .minContent => ⟨sizes.min, sizes.min⟩
    | .maxContent => ⟨sizes.max, sizes.max⟩
    | _ => sizes
  ⟨clampSize sz bp none (some sizes) minL maxL base.min,
   clampSize sz bp none (some sizes) minL maxL base.max⟩

/-- `ComputeInlineSizeForFragment` (`TestComputeInlineSizeForFragment`): `avail` is the available
    inline size, `fixedInline` the space's fixed inline size flag, `marginInline` the inline margin
    sum (stretch fills `avail - margins`, never below border+padding). -/
def inlineSizeForFragment (avail : Nat) (fixedInline : Bool) (sz : Sizing) (bp marginInline : Nat)
    (width minL maxL : L) (sizes : MinMax) : Nat :=
  if fixedInline then avail
  else
    let stretchSz := Nat.max (avail - marginInline) bp
    let base : Nat :=
      match width with
      | .auto | .stretch => stretchSz
      | .fitContent => Nat.min (Nat.max sizes.min (avail - marginInline)) sizes.max
      | l => toBorderBox sz bp l ((resolveLen (some avail) (some sizes) l).getD 0)
    clampSize sz bp (some avail) (some sizes) minL maxL base

/-- `ComputeBlockSizeForFragment` (`TestComputeBlockSizeForFragment`, `TestIndefinitePercentages`):
    `none` is `kIndefiniteSize`. `content` is the border-box intrinsic block size; `ratio` is
    `(w, h)` of `aspect-ratio`, applied to the border box for `border-box` and to the content box
    (plus block border+padding) for `content-box` against the border-box inline size `inlineBB`. -/
def blockSizeForFragment (availBlock : Option Nat) (fixedBlock : Bool) (sz : Sizing)
    (bpBlock bpInline marginBlock : Nat) (height minL maxL : L) (ratio : Option (Nat × Nat))
    (content inlineBB : Option Nat) : Option Nat :=
  if fixedBlock then availBlock
  else
    let base : Option Nat :=
      match height with
      | .auto =>
          match ratio, inlineBB with
          | some (rw, rh), some i =>
              some (match sz with
                | .borderBox => i * rh / rw
                | .contentBox => (i - bpInline) * rh / rw + bpBlock)
          | _, _ => content
      | .stretch => availBlock.map (fun a => Nat.max (a - marginBlock) bpBlock)
      | l =>
          match resolveLen availBlock none l with
          | some v => some (toBorderBox sz bpBlock l v)
          | none => content
    base.map (clampSize sz bpBlock availBlock none minL maxL)

/-- Auto-margin resolution (`ResolveInlineAutoMargins`, `TestAutoMargins`): leftover space is
    split between `auto` margins and never made negative. -/
def autoMargins (avail inl : Nat) (l r : MLen) : Int × Int :=
  let rem : Int := (avail : Int) - (inl : Int)
  match l, r with
  | .auto, .auto => let r0 := max rem 0; (r0 / 2, r0 - r0 / 2)
  | .auto, .px rr => (max (rem - rr) 0, rr)
  | .px ll, .auto => (ll, max (rem - ll) 0)
  | .px ll, .px rr => (ll, rr)

/-- A margin or padding length: auto, pixels or a percentage of the containing block's inline size
    (`TestMargins`, `TestPadding`). -/
inductive Edge where
  | auto
  | px (n : Nat)
  | pct (n : Nat)

/-- `ComputePhysicalMargins`/`ComputePadding` edge resolution: percentages resolve against the
    available inline size, `auto` is 0 (`TestMargins`, `TestPadding`). -/
def resolveEdge (availInline : Nat) : Edge → Nat
  | .auto => 0
  | .px n => n
  | .pct p => availInline * p / 100

/-- Largest `LayoutUnit` raw value (`2^31 - 1`), `LayoutUnit::Max()` (`AspectRatio`). -/
def luMax : Nat := 2147483647

/-- `InlineSizeFromAspectRatio` for `border-box` and no border/padding, in raw `LayoutUnit`
    (1/64 px): block size times `w / h`, floored and saturated (`AspectRatio`). -/
def inlineFromAspectRatio (rw rh blockRaw : Nat) : Nat :=
  Nat.min luMax (blockRaw * rw / rh)

/-- The aspect-ratio result never exceeds `LayoutUnit::Max()` (last vector of `AspectRatio`). -/
theorem inlineFromAspectRatio_le_max (rw rh b : Nat) : inlineFromAspectRatio rw rh b ≤ luMax := by
  unfold inlineFromAspectRatio; exact Nat.min_le_left _ _

/-- A 1:1 ratio is the identity below saturation (first vector of `AspectRatio`). -/
theorem inlineFromAspectRatio_one (r b : Nat) (hr : 0 < r) (hb : b ≤ luMax) :
    inlineFromAspectRatio r r b = b := by
  unfold inlineFromAspectRatio
  rw [Nat.mul_div_cancel _ hr]
  exact Nat.min_eq_right hb

/-- The min wins over the max when they conflict (`TestComputeContentContribution` test8, and the
    block-size analogue): clamping never returns less than the minimum. -/
theorem clampSize_ge_min (sz : Sizing) (bp : Nat) (avail : Option Nat) (sizes : Option MinMax)
    (minL maxL : L) (v m : Nat) (h : resolveLen avail sizes minL = some m) :
    toBorderBox sz bp minL m ≤ clampSize sz bp avail sizes minL maxL v := by
  unfold clampSize
  simp only [h]
  exact Nat.le_max_right _ _

end BlockLength
end ChromiumLayout
