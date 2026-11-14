/-
  BlockDiffuser.lean: spreading a LayoutUnit total over n buckets, written from
  geometry/layout_unit_diffuser_test.cc. Owned by the block lane.
  No CSS spec text fixes this: CSS leaves sub-pixel rounding of distributed space to the browser
  (CSS Values 4 §10 "rounding"); the rule is read off the tests (round-half-up of the running
  proportional share, in raw 1/64 units).
-/
namespace ChromiumLayout
namespace BlockDiffuser

/-- Share of `t` (raw units) for bucket `k` of `n`; 0 once the `n` buckets are used up. -/
def share (t n k : Nat) : Nat :=
  if k < n then (2 * t * (k + 1) + n) / (2 * n) - (2 * t * k + n) / (2 * n) else 0

/-- Total handed out by the first `m` buckets. -/
def given (t n : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => given t n m + share t n m

/-- Law: the first `m ≤ n` buckets hand out exactly the rounded running share, so nothing is lost
    or created (`ThreeBuckets`, `FourBuckets`, `SevenBuckets`). -/
theorem given_eq (t n : Nat) (hn : 0 < n) (m : Nat) (hm : m ≤ n) :
    given t n m = (2 * t * m + n) / (2 * n) := by
  induction m with
  | zero => simp [given]; exact (Nat.div_eq_of_lt (by omega)).symm
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 : (2 * t * m + n) / (2 * n) ≤ (2 * t * (m + 1) + n) / (2 * n) :=
      Nat.div_le_div_right (by rw [Nat.mul_succ]; omega)
    simp only [given, share, h1, show m < n by omega, ite_true]
    omega

/-- The whole total is handed out by `n` buckets. -/
theorem given_all (t n : Nat) (hn : 0 < n) : given t n n = t := by
  rw [given_eq t n hn n (Nat.le_refl n)]
  have e1 : t * (2 * n) = 2 * t * n := by simp [Nat.mul_comm, Nat.mul_left_comm]
  have e2 : (t + 1) * (2 * n) = 2 * t * n + 2 * n := by
    rw [Nat.add_mul, e1, Nat.one_mul]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

end BlockDiffuser
end ChromiumLayout
