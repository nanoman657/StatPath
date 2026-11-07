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

end BlockAbsolute
end ChromiumLayout
