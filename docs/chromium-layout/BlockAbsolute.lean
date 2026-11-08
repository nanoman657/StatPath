/-
  BlockAbsolute.lean: 1D absolute positioning constraints resolution (CSS 2.1 §10.3.7, §10.6.4),
  written from absolute_utils_test.cc (`AbsoluteUtilsTest.Horizontal`, `AbsoluteUtilsTest.Vertical`,
  `AbsoluteUtilsTest.CenterStaticPosition`, `AbsoluteUtilsTest.MinMax`). Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockAbsolute

inductive InsetVal where
  | auto
  | px (n : Int)
  deriving DecidableEq, Repr

inductive MarginVal where
  | auto
  | px (n : Int)
  deriving DecidableEq, Repr

inductive SizeVal where
  | auto
  | px (n : Nat)
  deriving DecidableEq, Repr

structure OofResult where
  size : Nat
  insetStart : Int
  insetEnd : Int
  deriving DecidableEq, Repr

/-- Compute 1D out-of-flow dimensions and insets (CSS 2.1 §10.3.7, §10.6.4). -/
def computeOof (containerSize : Nat) (startInset endInset : InsetVal)
    (startMargin endMargin : MarginVal) (sz : SizeVal) (contentSize : Nat)
    (isRtl : Bool := false) (allowNegativeSplit : Bool := false) : OofResult :=
  let c : Int := (containerSize : Int)
  match startInset, sz, endInset with
  | .auto, .auto, .auto =>
      let s := contentSize
      let mS := match startMargin with | .px m1 => m1 | .auto => 0
      if isRtl then
        ⟨s, mS, c - s - mS⟩
      else
        ⟨s, mS, c - s - mS⟩
  | .px sI, .px sSz, .px eI =>
      let free := c - sI - (sSz : Int) - eI
      let (mS, mE) := match startMargin, endMargin with
        | .auto, .auto =>
            if free < 0 && !allowNegativeSplit then
              if isRtl then (free, 0) else (0, free)
            else
              (free / 2, free - free / 2)
        | .px m1, .auto => (m1, free - m1)
        | .auto, .px m2 => (free - m2, m2)
        | .px m1, .px m2 => (m1, m2)
      ⟨sSz, sI + mS, eI + mE⟩
  | .auto, .auto, .px eI =>
      let s := contentSize
      let mS := match startMargin with | .auto => 0 | .px m => m
      let mE := match endMargin with | .auto => 0 | .px m => m
      let sI := c - eI - (s : Int) - mS - mE
      ⟨s, sI + mS, eI + mE⟩
  | .auto, .px sSz, .auto =>
      let mS := match startMargin with | .auto => 0 | .px m => m
      let mE := match endMargin with | .auto => 0 | .px m => m
      let eI := c - (sSz : Int) - mS - mE
      ⟨sSz, mS, mE + eI⟩
  | .px sI, .auto, .auto =>
      let s := contentSize
      let mS := match startMargin with | .auto => 0 | .px m => m
      let mE := match endMargin with | .auto => 0 | .px m => m
      let eI := c - sI - (s : Int) - mS - mE
      ⟨s, sI + mS, eI + mE⟩
  | .auto, .px sSz, .px eI =>
      let mS := match startMargin with | .auto => 0 | .px m => m
      let mE := match endMargin with | .auto => 0 | .px m => m
      let sI := c - eI - (sSz : Int) - mS - mE
      ⟨sSz, sI + mS, eI + mE⟩
  | .px sI, .px sSz, .auto =>
      let mS := match startMargin with | .auto => 0 | .px m => m
      let mE := match endMargin with | .auto => 0 | .px m => m
      let eI := c - sI - (sSz : Int) - mS - mE
      ⟨sSz, sI + mS, eI + mE⟩
  | .px sI, .auto, .px eI =>
      let mS := match startMargin with | .auto => 0 | .px m => m
      let mE := match endMargin with | .auto => 0 | .px m => m
      let s := (c - sI - eI - mS - mE).toNat
      ⟨s, sI + mS, eI + mE⟩

/-- Clamp size by min and max values (`MinMax`). -/
def clamp (minVal maxVal sz : Nat) : Nat :=
  Nat.min maxVal (Nat.max minVal sz)

/-- Clamping always stays within [minVal, maxVal] when minVal ≤ maxVal. -/
theorem clamp_bounds (minVal maxVal sz : Nat) (h : minVal ≤ maxVal) :
    minVal ≤ clamp minVal maxVal sz ∧ clamp minVal maxVal sz ≤ maxVal := by
  unfold clamp
  simp only [Nat.min_def, Nat.max_def]
  split <;> split <;> omega

inductive StaticPositionAlignment where
  | start
  | center
  | endEdge
  deriving DecidableEq, Repr

/-- Compute 1D out-of-flow dimensions with static position alignment and min/max clamping. -/
def computeOofExtended (containerSize : Nat) (startInset endInset : InsetVal)
    (startMargin endMargin : MarginVal) (sz : SizeVal) (contentSize : Nat)
    (staticOffset : Option Int := none)
    (staticAlign : StaticPositionAlignment := .start)
    (minSize : Option Nat := none) (maxSize : Option Nat := none)
    (isRtl : Bool := false) (allowNegativeSplit : Bool := false) : OofResult :=
  let initial := computeOof containerSize startInset endInset startMargin endMargin sz contentSize isRtl allowNegativeSplit
  let clampedSize := match minSize, maxSize with
    | some mn, some mx => clamp mn mx initial.size
    | some mn, none => Nat.max mn initial.size
    | none, some mx => Nat.min mx initial.size
    | none, none => initial.size
  let (finalStart, finalEnd) :=
    match startInset, endInset, staticOffset with
    | .auto, .auto, some pos =>
        match staticAlign with
        | .center =>
            let sI := pos - (clampedSize : Int) / 2
            let eI := (containerSize : Int) - sI - (clampedSize : Int)
            (sI, eI)
        | _ => (initial.insetStart, initial.insetEnd)
    | _, _, _ =>
        (initial.insetStart, (containerSize : Int) - initial.insetStart - (clampedSize : Int))
  ⟨clampedSize, finalStart, finalEnd⟩

inductive PositionType where
  | static
  | relative
  | absolute
  | fixed
  deriving DecidableEq, Repr

structure OofDescendant where
  id : Nat := 0
  posType : PositionType := .absolute
  top : InsetVal := .auto
  left : InsetVal := .auto
  width : SizeVal := .auto
  height : SizeVal := .auto
  staticTop : Int := 0
  staticLeft : Int := 0
  deriving DecidableEq, Repr

/-- Resolve 2D final offset of an out-of-flow descendant (CSS 2.1 §9.3.1). -/
def resolveOofOffset (cbTop cbLeft : Int) (desc : OofDescendant) : Int × Int :=
  let y := match desc.top with
    | .px n => n
    | .auto => cbTop + desc.staticTop
  let x := match desc.left with
    | .px n => n
    | .auto => cbLeft + desc.staticLeft
  (x, y)

/-- Explicit insets override static positions in out-of-flow offset resolution. -/
theorem explicit_inset_overrides_static (cbTop cbLeft topVal staticTop : Int) :
    let desc : OofDescendant := { posType := .fixed, top := .px topVal, staticTop := staticTop }
    (resolveOofOffset cbTop cbLeft desc).2 = topVal := by
  rfl

/-- Auto insets use static position relative to containing block. -/
theorem auto_inset_uses_static (cbTop cbLeft staticTop : Int) :
    let desc : OofDescendant := { posType := .fixed, top := .auto, staticTop := staticTop }
    (resolveOofOffset cbTop cbLeft desc).2 = cbTop + staticTop := by
  rfl

end BlockAbsolute
end ChromiumLayout
