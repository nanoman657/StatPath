/-
  MappingTransform3.lean: 3D transforms and perspective for coordinate mapping, written from
  map_coordinates_test.cc (pin 36c121be), not from the C++.

  Module owned by the "mapping" lane. Matrices are 4x4 integer matrices acting on homogeneous
  coordinates, so a matrix is only meaningful up to a common factor and a perspective divide is the
  exact ratio of two integers (`project`).
-/
import MappingTransform

namespace ChromiumLayout
namespace Mapping

/-- A 4x4 matrix `m row col` (indices 0..3) acting on column vectors `(x, y, z, w)`. -/
abbrev Mat := Nat → Nat → Int
abbrev Vec := Nat → Int

def Mat.comp (A B : Mat) : Mat := fun i j => (List.range 4).foldl (fun s k => s + A i k * B k j) 0

def Mat.apply (A : Mat) (v : Vec) : Vec := fun i => (List.range 4).foldl (fun s k => s + A i k * v k) 0

def Mat.id : Mat := fun i j => if i = j then 1 else 0

/-- `translate3d(x, y, z)` (CSS Transforms 2 §13). -/
def Mat.translate3 (x y z : Int) : Mat := fun i j =>
  if i = j then 1 else if j = 3 then (if i = 0 then x else if i = 1 then y else if i = 2 then z else 0) else 0

/-- `rotateY(deg)`: `x' = cos x + sin z`, `z' = -sin x + cos z`, scaled by `trigScale`. -/
def Mat.rotY (deg : Int) : Mat := fun i j =>
  if i = 0 ∧ j = 0 then cosS deg else if i = 0 ∧ j = 2 then sinS deg
  else if i = 2 ∧ j = 0 then -sinS deg else if i = 2 ∧ j = 2 then cosS deg
  else if i = j then trigScale else 0

/-- `perspective(d)` (CSS Transforms 2 §13): `w' = 1 - z / d`, scaled by `d`. -/
def Mat.persp (d : Int) : Mat := fun i j =>
  if i = 3 ∧ j = 2 then -1 else if i = j then d else 0

/-- Flattening into the plane (CSS Transforms 2 §9, `transform-style: flat`): depth is dropped,
    the `w` row (perspective) is kept. -/
def Mat.flatten (A : Mat) : Mat := fun i j =>
  if i = 2 ∨ j = 2 then (if i = j then 1 else 0) else A i j

/-- Matrix about an origin `(ox, oy)` (CSS Transforms 1 §6). -/
def Mat.about (ox oy : Int) (T : Mat) : Mat :=
  (Mat.translate3 ox oy 0).comp (T.comp (Mat.translate3 (-ox) (-oy) 0))

/-- Perspective with its origin `(px, py)`: applies to the children of the box. -/
def Mat.perspAt (d px py : Int) : Mat := Mat.about px py (Mat.persp d)

/-- The point `(x, y)` of the plane `z = 0` as a vector. -/
def Vec.plane (x y : Int) : Vec := fun i => if i = 0 then x else if i = 1 then y else if i = 3 then 1 else 0

/-- Projection onto the plane: the exact ratio `(x / w, y / w)` (a positive `w`). -/
def Vec.project (v : Vec) : RPt := ⟨v 0, v 1, (v 3).toNat⟩

/-- A box in a 3D chain: its `transform-origin`, transform, `transform-style: preserve-3d`
    (whether it keeps its children in 3D) and `perspective` (distance, origin) for its children. -/
structure Box3 where
  origin : Pt := ⟨0, 0⟩
  xf : Mat := Mat.id
  preserve : Bool := false
  persp : Option (Int × Pt) := none

/-- The matrix from a leaf to the end of a chain of `(box, offset in parent)` steps (leaf first):
    each step applies the box's transform and its offset; the parent's perspective is applied, and
    the result is flattened unless the parent preserves 3D (CSS Transforms 2 §9, §13). -/
def chain3 : List (Box3 × Pt) → Mat → Mat
  | [], acc => acc
  | [(b, off)], acc => (Mat.translate3 off.x off.y 0).comp ((Mat.about b.origin.x b.origin.y b.xf).comp acc)
  | (b, off) :: (p, o') :: rest, acc =>
      let a1 := (Mat.translate3 off.x off.y 0).comp ((Mat.about b.origin.x b.origin.y b.xf).comp acc)
      let a2 := match p.persp with
        | some (d, po) => (Mat.perspAt d po.x po.y).comp a1
        | none => a1
      chain3 ((p, o') :: rest) (if p.preserve then a2 else Mat.flatten a2)

/-- Mapping through a product is mapping step by step. -/
theorem apply_comp (A B : Mat) (v : Vec) (i : Nat) : (A.comp B).apply v i = A.apply (B.apply v) i := by
  simp only [Mat.comp, Mat.apply, List.range, List.range.loop, List.foldl]
  grind

/-- Flattening leaves depth alone. -/
theorem flatten_z (A : Mat) (v : Vec) : (Mat.flatten A).apply v 2 = v 2 := by
  simp only [Mat.apply, Mat.flatten, List.range, List.range.loop, List.foldl]
  grind

/-- A flattened chain gives every point of the plane a depth of zero relative to it: points of the
    plane stay in the plane. -/
theorem flatten_plane (A : Mat) (x y : Int) : (Mat.flatten A).apply (Vec.plane x y) 2 = 0 := by
  rw [flatten_z]; rfl

/-- Without a transform and perspective a chain is a pure offset. -/
theorem chain3_nil (acc : Mat) : chain3 [] acc = acc := rfl

end Mapping
end ChromiumLayout
