/-
  MappingTransform.lean: 2D transforms for coordinate mapping, written from
  map_coordinates_test.cc and visual_rect_mapping_test.cc (pin 36c121be), not from the C++.

  Module owned by the "mapping" lane. Matrices are integer matrices with a common positive
  denominator, so composition and inverse stay exact (no floating point, no `Rat`: the kernel does
  not evaluate it). Rotations by angles other than multiples of 90 degrees need irrational entries
  and are not modelled (rows depending on them are blocked in MANIFEST-mapping.md).
-/
import Mapping

namespace ChromiumLayout
namespace Mapping

/-- A rational point `(x / den, y / den)`. -/
structure RPt where
  x : Int
  y : Int
  den : Nat := 1
  deriving DecidableEq, Repr

/-- Equality of the rational points (cross-multiplied). -/
def RPt.Eq (p q : RPt) : Prop := p.x * q.den = q.x * p.den ∧ p.y * q.den = q.y * p.den

/-- The integer point a rational point equals, when it is one. -/
def RPt.toPt (p : RPt) : Pt := ⟨p.x / p.den, p.y / p.den⟩

def RPt.ofPt (p : Pt) : RPt := ⟨p.x, p.y, 1⟩

/-- A 2D affine map `(x, y) ↦ ((a x + c y + e) / den, (b x + d y + f) / den)`, the matrix
    `[[a c e], [b d f], [0 0 1]]` of CSS Transforms 1 §3 / §18 divided by `den`. -/
structure Aff where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  den : Nat := 1
  deriving DecidableEq, Repr

def Aff.map (A : Aff) (p : RPt) : RPt :=
  ⟨A.a * p.x + A.c * p.y + A.e * p.den, A.b * p.x + A.d * p.y + A.f * p.den, A.den * p.den⟩

/-- `A.comp B` applies `B` first (matrix product, CSS Transforms 1 §8). -/
def Aff.comp (A B : Aff) : Aff :=
  ⟨A.a * B.a + A.c * B.b, A.b * B.a + A.d * B.b, A.a * B.c + A.c * B.d, A.b * B.c + A.d * B.d,
   A.a * B.e + A.c * B.f + A.e * B.den, A.b * B.e + A.d * B.f + A.f * B.den, A.den * B.den⟩

def Aff.translate (t : Pt) : Aff := ⟨1, 0, 0, 1, t.x, t.y, 1⟩

/-- `scale(n/d, m/d)`-style scaling: numerators `sx`, `sy` over `den` (CSS Transforms 1 §13.2). -/
def Aff.scale (sx sy : Int) (den : Nat := 1) : Aff := ⟨sx, 0, 0, sy, 0, 0, den⟩

def Aff.det (A : Aff) : Int := A.a * A.d - A.c * A.b

/-- Inverse of an invertible map (adjugate over determinant, sign folded into the entries). -/
def Aff.inv (A : Aff) : Aff :=
  let s : Int := if A.det < 0 then -1 else 1
  ⟨s * A.den * A.d, -(s * A.den * A.b), -(s * A.den * A.c), s * A.den * A.a,
   -(s * (A.d * A.e - A.c * A.f)), -(s * (A.a * A.f - A.b * A.e)), A.det.natAbs⟩

/-- A transform with its `transform-origin` `o` (in the box's own coordinates): translate to the
    origin, apply, translate back (CSS Transforms 1 §6 transform-origin, §8 the transform
    property). -/
def Aff.about (o : Pt) (A : Aff) : Aff :=
  (Aff.translate o).comp (A.comp (Aff.translate ⟨-o.x, -o.y⟩))

/-! ## General laws -/

/-- Mapping through `A.comp B` is mapping through `B`, then `A`. -/
theorem map_comp (A B : Aff) (p : RPt) : (A.comp B).map p = A.map (B.map p) := by
  simp only [Aff.comp, Aff.map, RPt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · push_cast; grind
  · push_cast; grind
  · exact Nat.mul_assoc _ _ _

/-- A translation moves a point by its offset. -/
theorem map_translate (t : Pt) (p : Pt) : ((Aff.translate t).map (RPt.ofPt p)).toPt = ⟨p.x + t.x, p.y + t.y⟩ := by
  simp [Aff.translate, Aff.map, RPt.ofPt, RPt.toPt]

/-- An invertible map and its inverse undo each other (up to rational equality). -/
theorem inv_map (A : Aff) (p : RPt) :
    (A.inv.map (A.map p)).Eq p := by
  unfold RPt.Eq Aff.inv Aff.map
  dsimp only
  by_cases hneg : A.det < 0
  · have hn : ((A.det.natAbs : Nat) : Int) = -A.det := by omega
    simp only [hneg, ite_true]
    push_cast
    rw [hn]
    unfold Aff.det
    constructor <;> grind
  · have hn : ((A.det.natAbs : Nat) : Int) = A.det := by omega
    simp only [hneg, ite_false]
    push_cast
    rw [hn]
    unfold Aff.det
    constructor <;> grind

def Aff.id : Aff := ⟨1, 0, 0, 1, 0, 0, 1⟩

/-- `IsIdentity` (the matrix maps every point to itself). -/
def Aff.isId (A : Aff) : Bool :=
  A.a == A.den && A.d == A.den && A.b == 0 && A.c == 0 && A.e == 0 && A.f == 0

/-- `IsIdentityOrTranslation`. -/
def Aff.isTranslation (A : Aff) : Bool :=
  A.a == A.den && A.d == A.den && A.b == 0 && A.c == 0

/-- The step of a chain: the hop into the parent, after the box's own transform about its
    origin. -/
def stepAff (h : Hop) (x : Option (Pt × Aff)) : Aff :=
  match x with
  | none => Aff.translate h
  | some (o, A) => (Aff.translate h).comp (Aff.about o A)

/-- Affine steps of a node chain with the optional transform (origin, matrix) of each box. -/
def affChain (ns : List Node) (xs : List (Option (Pt × Aff))) : List Aff :=
  List.zipWith stepAff (hops ns) xs

/-- Map a rational point from step `i` to step `j` of a chain. -/
def mapA (affs : List Aff) (i j : Nat) (p : RPt) : RPt :=
  (((affs.take j).drop i).foldl (fun q a => a.map q) p)

/-- The inverse direction: from step `j` back down to step `i`. -/
def mapADown (affs : List Aff) (i j : Nat) (p : RPt) : RPt :=
  (((affs.take j).drop i).foldr (fun a q => a.inv.map q) p)

/-- The matrix of a whole chain (`LocalToAbsoluteTransform`). -/
def composeAll (affs : List Aff) : Aff := affs.foldl (fun A a => a.comp A) Aff.id

/-- Does `p` equal `q` as rational points, with positive denominators? -/
theorem RPt.Eq.trans' {p q r : RPt} (h1 : p.Eq q) (h2 : q.Eq r) (hq : 0 < q.den) : p.Eq r := by
  unfold RPt.Eq at *
  have hq' : (q.den : Int) ≠ 0 := by omega
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  constructor
  · apply Int.eq_of_mul_eq_mul_right hq'
    calc p.x * ↑r.den * ↑q.den = (p.x * ↑q.den) * ↑r.den := by rw [Int.mul_right_comm]
      _ = (q.x * ↑p.den) * ↑r.den := by rw [a1]
      _ = (q.x * ↑r.den) * ↑p.den := by rw [Int.mul_right_comm]
      _ = (r.x * ↑q.den) * ↑p.den := by rw [b1]
      _ = r.x * ↑p.den * ↑q.den := by rw [Int.mul_right_comm]
  · apply Int.eq_of_mul_eq_mul_right hq'
    calc p.y * ↑r.den * ↑q.den = (p.y * ↑q.den) * ↑r.den := by rw [Int.mul_right_comm]
      _ = (q.y * ↑p.den) * ↑r.den := by rw [a2]
      _ = (q.y * ↑r.den) * ↑p.den := by rw [Int.mul_right_comm]
      _ = (r.y * ↑q.den) * ↑p.den := by rw [b2]
      _ = r.y * ↑p.den * ↑q.den := by rw [Int.mul_right_comm]

theorem Aff.map_eq (A : Aff) {p q : RPt} (h : p.Eq q) : (A.map p).Eq (A.map q) := by
  unfold RPt.Eq Aff.map at *
  dsimp only
  obtain ⟨h1, h2⟩ := h
  push_cast
  constructor <;> grind

theorem Aff.map_den_pos (A : Aff) (p : RPt) (ha : 0 < A.den) (hp : 0 < p.den) : 0 < (A.map p).den := by
  simp only [Aff.map]; exact Nat.mul_pos ha hp

theorem Aff.inv_den_pos (A : Aff) (h : A.det ≠ 0) : 0 < A.inv.den := by
  simp only [Aff.inv]; omega

theorem mapADown_mapA_list (l : List Aff) (hv : ∀ a ∈ l, 0 < a.den ∧ a.det ≠ 0) :
    ∀ (p : RPt), 0 < p.den → (l.foldr (fun a q => a.inv.map q) (l.foldl (fun q a => a.map q) p)).Eq p := by
  induction l with
  | nil => intro p _; exact ⟨rfl, rfl⟩
  | cons a t ih =>
      intro p hp
      simp only [List.foldl_cons, List.foldr_cons]
      have ha := hv a (by simp)
      have hap : 0 < (a.map p).den := Aff.map_den_pos a p ha.1 hp
      have h1 := ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) (a.map p) hap
      have h2 := Aff.map_eq a.inv h1
      have h3 := inv_map a p
      have hinv : 0 < (a.inv.map (a.map p)).den :=
        Aff.map_den_pos a.inv (a.map p) (Aff.inv_den_pos a ha.2) hap
      exact RPt.Eq.trans' h2 h3 hinv

/-- Mapping a point up a chain of invertible steps and down again returns it, whatever the
    transforms on the way. -/
theorem mapADown_mapA (affs : List Aff) (i j : Nat)
    (hv : ∀ a ∈ affs, 0 < a.den ∧ a.det ≠ 0) (p : RPt) (hp : 0 < p.den) :
    (mapADown affs i j (mapA affs i j p)).Eq p :=
  mapADown_mapA_list _ (fun a ha => hv a (List.mem_of_mem_take (List.mem_of_mem_drop ha))) p hp

/-- The matrix of a chain maps a point as the steps do one after the other. -/
theorem composeAll_map (affs : List Aff) (p : RPt) :
    (composeAll affs).map p = affs.foldl (fun q a => a.map q) p := by
  have key : ∀ (l : List Aff) (acc : Aff),
      (l.foldl (fun A a => a.comp A) acc).map p = l.foldl (fun q a => a.map q) (acc.map p) := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons a t ih => intro acc; simp only [List.foldl_cons]; rw [ih, map_comp]
  have := key affs Aff.id
  simpa [composeAll, Aff.map, Aff.id] using this

/-- The initial `transform-origin` `50% 50%` of a box of border-box size `f` (CSS Transforms 1 §6). -/
def Aff.center (f : BlockFlow.Frag) : Pt := ⟨(f.w : Int) / 2, f.h / 2⟩

/-! ## Which ancestor contains a fixed-position box -/

/-- Properties that make a box the containing block of fixed (and absolute) descendants: a
    `transform` other than `none` (CSS Transforms 1 §2), `will-change: transform` (CSS Will Change
    1 §3) and `contain: paint` (CSS Containment 2 §3.3). -/
structure BoxStyle where
  transform : Bool := false
  willChange : Bool := false
  containPaint : Bool := false

def BoxStyle.formsCB (s : BoxStyle) : Bool := s.transform || s.willChange || s.containPaint

/-- Steps from a fixed box's parent up to its containing block: the index of the first ancestor
    (parent first) that forms one, else all the way to the viewport. -/
def cbSteps (ss : List BoxStyle) : Nat := ss.findIdx BoxStyle.formsCB

theorem cbSteps_le (ss : List BoxStyle) : cbSteps ss ≤ ss.length := List.findIdx_le_length

theorem cbSteps_before (ss : List BoxStyle) (i : Nat) (hi : i < cbSteps ss) (h : i < ss.length) :
    (ss[i]).formsCB = false := by
  have := List.not_of_lt_findIdx hi
  simpa using this

theorem cbSteps_forms (ss : List BoxStyle) (h : cbSteps ss < ss.length) :
    (ss[cbSteps ss]).formsCB = true := by
  unfold cbSteps
  exact List.findIdx_getElem

/-! ## SVG viewBox (SVG 2 §8.2) -/

/-- The transform from SVG user space to the viewport box for `viewBox="vx vy vw vh"` in a `pw × ph`
    viewport with the initial `preserveAspectRatio="xMidYMid meet"` (SVG 2 §8.2, the algorithm for
    the viewBox transform): uniform scale `min(pw / vw, ph / vh)`, the viewBox centred in the
    viewport. The scale is the fraction `num / den`. -/
def viewBoxAff (vx vy vw vh : Int) (pw ph : Nat) : Aff :=
  let num : Int := if (pw : Int) * vh ≤ (ph : Int) * vw then pw else ph
  let den : Int := if (pw : Int) * vh ≤ (ph : Int) * vw then vw else vh
  ⟨2 * num, 0, 0, 2 * num, pw * den - vw * num - 2 * vx * num, ph * den - vh * num - 2 * vy * num,
   (2 * den).toNat⟩

/-- The viewBox transform scales both axes alike (the aspect ratio is preserved). -/
theorem viewBoxAff_uniform (vx vy vw vh : Int) (pw ph : Nat) :
    (viewBoxAff vx vy vw vh pw ph).a = (viewBoxAff vx vy vw vh pw ph).d := by
  simp only [viewBoxAff]

/-- The centre of the viewBox lands on the centre of the viewport (`xMidYMid`). -/
theorem viewBoxAff_center (vx vy vw vh : Int) (pw ph : Nat) (hw : 0 < vw) (hh : 0 < vh) :
    ((viewBoxAff vx vy vw vh pw ph).map ⟨2 * vx + vw, 2 * vy + vh, 2⟩).Eq ⟨pw, ph, 2⟩ := by
  unfold RPt.Eq Aff.map viewBoxAff
  dsimp only
  by_cases hc : (pw : Int) * vh ≤ (ph : Int) * vw
  · have h2 : (((2 * vw).toNat : Nat) : Int) = 2 * vw := Int.toNat_of_nonneg (by omega)
    simp only [hc, ite_true]
    push_cast
    rw [h2]
    constructor <;> grind
  · have h2 : (((2 * vh).toNat : Nat) : Int) = 2 * vh := Int.toNat_of_nonneg (by omega)
    simp only [hc, ite_false]
    push_cast
    rw [h2]
    constructor <;> grind

/-! ## Drawable elements in a canvas -/

/-- A step toward a canvas: an ordinary hop, or a drawable element, which is drawn into the canvas
    by its own canvas transform only (its position among ancestors does not enter). -/
inductive CN where
  | plain (h : Hop)
  | drawable (t : Pt)

/-- Offset of a chain of steps up to the canvas: it stops at the first drawable element. -/
def canvasShift : List CN → Pt
  | [] => ⟨0, 0⟩
  | .drawable t :: _ => t
  | .plain h :: rest => ⟨h.x + (canvasShift rest).x, h.y + (canvasShift rest).y⟩

/-- A rectangle mapped to the canvas: moved by the chain's offset (the visual-rect counterpart of
    the point map). -/
def mapCanvas (l : List CN) (r : PRect) : PRect := r.translate (canvasShift l)

theorem canvasShift_drawable (t : Pt) (rest : List CN) : canvasShift (.drawable t :: rest) = t := rfl

/-- Ancestors beyond the first drawable element do not matter. -/
theorem canvasShift_append (l r : List CN) (h : ∃ t, CN.drawable t ∈ l) : canvasShift (l ++ r) = canvasShift l := by
  induction l with
  | nil => obtain ⟨t, ht⟩ := h; simp at ht
  | cons x xs ih =>
      cases x with
      | drawable t => rfl
      | plain h' =>
          obtain ⟨t, ht⟩ := h
          have : ∃ t, CN.drawable t ∈ xs := ⟨t, by simpa using ht⟩
          simp [canvasShift, ih this]

/-! ## Rotations (CSS Transforms 1 §13.1 rotate()) -/

/-- Fixed-point scale of the trigonometric values (10^15). -/
def trigScale : Int := 1000000000000000

/-- Angle in degrees reduced to `[-180, 180]`. -/
def reduceDeg (d : Int) : Int := if d % 360 > 180 then d % 360 - 360 else d % 360

/-- Maclaurin series with twelve terms in fixed point: terms `t_{k+1} = -t_k x² / ((2k+1+o)(2k+2+o))`,
    starting from `first`; `x` is the angle in radians times `trigScale`. -/
def series (x first : Int) (o : Nat) : Int :=
  ((List.range 12).foldl (fun (ts : Int × Int) k =>
    let t := -(ts.1 * x * x / (trigScale * trigScale)) / ((2 * k + 1 + o : Nat) * (2 * k + 2 + o : Nat))
    (t, ts.2 + t)) (first, first)).2

/-- Angle in radians times `trigScale` (π ≈ 3.141592653589793). -/
def radS (deg : Int) : Int := reduceDeg deg * 3141592653589793 / 180

def sinS (deg : Int) : Int := series (radS deg) (radS deg) 1
def cosS (deg : Int) : Int := series (radS deg) trigScale 0

/-- `rotate(deg)`: the matrix `[[cos -sin], [sin cos]]` of CSS Transforms 1 §13.1, with `cos` and
    `sin` as fixed-point integers over `trigScale` (accurate to about 1e-12). -/
def rotation (deg : Int) : Aff := ⟨cosS deg, sinS deg, -sinS deg, cosS deg, 0, 0, trigScale.toNat⟩

/-- Is `p` within `tn / td` of the point `(x / d, y / d)` on both axes? -/
def RPt.near (p : RPt) (x y : Int) (d : Nat) (tn td : Nat) : Bool :=
  (p.x * d - x * p.den).natAbs * td ≤ tn * p.den * d && (p.y * d - y * p.den).natAbs * td ≤ tn * p.den * d

/-- A full turn changes nothing. -/
theorem rotation_period (d : Int) : rotation (d + 360) = rotation d := by
  have h : reduceDeg (d + 360) = reduceDeg d := by
    unfold reduceDeg; omega
  simp only [rotation, sinS, cosS, radS, h]

/-- Rotating by zero degrees is the identity (the matrix is `trigScale` times the identity over
    `trigScale`). -/
theorem rotation_zero : rotation 0 = Aff.scale trigScale trigScale trigScale.toNat := by decide

end Mapping
end ChromiumLayout
