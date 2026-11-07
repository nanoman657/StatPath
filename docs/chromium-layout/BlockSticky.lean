/-
  BlockSticky.lean: sticky fragment propagation to single-axis and multi-axis scroll containers,
  written from physical_fragment_test.cc (`StickyFragmentPropagationTest.StickyAxisEnabled`,
  `StickyFragmentPropagationTest.StickyAxisDisabled`). Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockSticky

/-- Physical axes (None, Horizontal, Vertical, Both). -/
inductive Axis where
  | none
  | horizontal
  | vertical
  | both
  deriving DecidableEq, Repr

/-- Whether an axis set contains horizontal. -/
def hasHorizontal : Axis → Bool
  | .horizontal | .both => true
  | _ => false

/-- Whether an axis set contains vertical. -/
def hasVertical : Axis → Bool
  | .vertical | .both => true
  | _ => false

/-- Combine horizontal and vertical boolean flags into an Axis value. -/
def combineAxes (h v : Bool) : Axis :=
  match h, v with
  | true, true => .both
  | true, false => .horizontal
  | false, true => .vertical
  | false, false => .none

/-- Result of sticky propagation to a scroller: consumed axes and pending axes. -/
structure StickyPropagation where
  consumed : Axis
  pending : Axis
  deriving DecidableEq, Repr

/-- Single-axis sticky propagation (`StickyAxisEnabled`): a scroller consumes axes it can scroll,
    leaving unscrollable sticky axes pending to propagate to ancestor scrollers. -/
def propagateSingleAxis (scrollerAxes elemAxes : Axis) : StickyPropagation :=
  let cH := hasHorizontal scrollerAxes && hasHorizontal elemAxes
  let cV := hasVertical scrollerAxes && hasVertical elemAxes
  let pH := (!hasHorizontal scrollerAxes) && hasHorizontal elemAxes
  let pV := (!hasVertical scrollerAxes) && hasVertical elemAxes
  ⟨combineAxes cH cV, combineAxes pH pV⟩

/-- Legacy sticky propagation (`StickyAxisDisabled`): any scroller consumes all axes. -/
def propagateLegacy (_ : Axis) : StickyPropagation :=
  ⟨.both, .none⟩

/-- Single-axis propagation partitions element axes into consumed and pending. -/
theorem propagation_disjoint (s e : Axis) :
    let p := propagateSingleAxis s e
    ((hasHorizontal p.consumed && hasHorizontal p.pending) = false) ∧
    ((hasVertical p.consumed && hasVertical p.pending) = false) := by
  cases s <;> cases e <;> decide

end BlockSticky
end ChromiumLayout
