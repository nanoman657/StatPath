/-
  BlockFragmentation.lean: block fragmentation of an already laid-out `BlockFlow` tree into
  fragmentainer slices, written from block_layout_algorithm_test.cc (NoFragmentation,
  SimpleFragmentation, InnerChildrenFragmentation, InnerFormattingContextChildrenFragmentation,
  InnerChildrenFragmentationSmallHeight). Owned by the block lane (new `Block*.lean`).

  The tests say: a box is cut at every multiple of the fragmentainer block size F; fragment `k`
  of a box covers its border box intersected with slice `k`, a child's offset is measured from
  the start of the parent's fragment, and a break token exists exactly while some part of the
  subtree lies beyond the slice. Unbreakable content and forced breaks are not modelled.
-/
import BlockFlow

namespace ChromiumLayout
namespace BlockFlow

/-- Size of fragment `k` of a border box `[y, y + h)` in fragmentainers of size `F`
    (`SimpleFragmentation`: 300 in F=200 gives 200 then 100). -/
def sliceSize (F : Nat) (y : Int) (h : Nat) (k : Nat) : Nat :=
  (min (y + h) (((k + 1) * F : Nat) : Int) - max y ((k * F : Nat) : Int)).toNat

/-- Block offset of a box's fragment `k` from the start of its parent's fragment `k`
    (`InnerChildrenFragmentation`: child2 at 40 in the second fragment). -/
def sliceOffset (F : Nat) (parentY childY : Int) (k : Nat) : Int :=
  max childY ((k * F : Nat) : Int) - max parentY ((k * F : Nat) : Int)

/-- Lowest block-end edge in a subtree; fragmentation continues while it lies beyond the slice
    (`InnerChildrenFragmentationSmallHeight`: a 70px container still continues because its
    overflowing child does). Fuel bounds the depth. -/
def extent : Nat → Frag → Int
  | 0, f => f.y + f.h
  | d + 1, f => f.kids.foldl (fun m c => max m (extent d c)) (f.y + f.h)

/-- Whether fragment `k` of the subtree has a break token (`GetBreakToken()`). -/
def hasBreakToken (F : Nat) (f : Frag) (k : Nat) : Bool :=
  decide ((((k + 1) * F : Nat) : Int) < extent fuel f)

/-- Whether a child contributes a fragment to slice `k`. -/
def inSlice (F : Nat) (c : Frag) (k : Nat) : Bool :=
  decide (c.y < (((k + 1) * F : Nat) : Int) ∧ (((k * F : Nat) : Int) < c.y + c.h))

/-- Fragment sizes over the first `n` slices add up (helper for conservation). -/
def sliceTotal (F : Nat) (y : Int) (h : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sliceTotal F y h n + sliceSize F y h n

/-- Consumed block size up to fragmentainer k (`break_token->ConsumedBlockSize()`,
    `fragmentation_test.cc: ConsumedBlockSizeOverflowInflow`). -/
def consumedBlockSize (F : Nat) (k : Nat) : Nat :=
  (k + 1) * F

/-- Consumed block size increases by fragmentainer size with each fragment. -/
theorem consumedBlockSize_step (F k : Nat) :
    consumedBlockSize F (k + 1) = consumedBlockSize F k + F := by
  unfold consumedBlockSize
  rw [Nat.succ_mul]

/-- Closed form of the first `n` slice sizes: the clamped extent of `[y, y+h)` in `[0, nF)`. -/
theorem sliceTotal_eq (F : Nat) (y : Int) (h : Nat) (hy : 0 ≤ y) (n : Nat) :
    (sliceTotal F y h n : Int) = min (y + h) ((n * F : Nat) : Int) - min y ((n * F : Nat) : Int) := by
  induction n with
  | zero => simp [sliceTotal]; omega
  | succ n ih =>
      have e : ((n + 1) * F : Nat) = n * F + F := by rw [Nat.succ_mul]
      simp only [sliceTotal, sliceSize, e]
      omega

/-- Fragmentation conserves block size: once the slices cover the whole box, the fragment sizes
    sum to the box's border-box block size (`SimpleFragmentation`: 200 + 100 = 300;
    `InnerChildrenFragmentation`: 180 + 20 = 200). -/
theorem fragmentation_conserves_size (F : Nat) (y : Int) (h : Nat) (hy : 0 ≤ y) (n : Nat)
    (hcover : y + h ≤ ((n * F : Nat) : Int)) :
    sliceTotal F y h n = h := by
  have := sliceTotal_eq F y h hy n
  omega

/-- Number of fragmentainer slices needed to hold content of height `h` in fragmentainers of size `F`.
    CSS Fragmentation Level 3 §2. -/
def sliceCount (F : Nat) (h : Nat) : Nat :=
  if F = 0 then 0
  else if h = 0 then 1
  else (h + F - 1) / F

/-- Law: Non-empty content in positive fragmentainer always requires at least one slice.
    CSS Fragmentation Level 3 §2. -/
theorem sliceCount_pos (F h : Nat) (hF : 0 < F) :
    1 ≤ sliceCount F h := by
  dsimp [sliceCount]
  split
  · omega
  · split
    · omega
    · have hle : F ≤ h + F - 1 := by omega
      have hdiv : F / F ≤ (h + F - 1) / F := Nat.div_le_div_right hle
      rw [Nat.div_self hF] at hdiv
      exact hdiv

end BlockFlow
end ChromiumLayout
