/-
  BlockPhysicalFragment.lean: physical box fragment properties: float descendant propagation,
  fragmentation context root identification, descendants above block start, and overflow clip margin,
  written from physical_box_fragment_test.cc. Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockPhysicalFragment

/-- Formatting context type for float propagation. -/
inductive FormattingContextType where
  | inlineBlock
  | flowRoot
  | positioned
  | block
  deriving DecidableEq, Repr

/-- Float descendant propagation: inline-block isolates floats within its own IFC,
    whereas block-level contexts (flow-root, positioned, block) propagate to ancestors
    (physical_box_fragment_test.cc: `FloatingDescendantsInlineChlidren`,
    `FloatingDescendantsBlockChlidren`, `FloatingDescendantsInlineBlock`,
    `FloatingDescendantsBlockFormattingContext`). -/
def propagatesFloats : FormattingContextType → Bool
  | .inlineBlock => false
  | .flowRoot | .positioned | .block => true

/-- Fragment box type for fragmentation context root query. -/
inductive BoxType where
  | multicol
  | column
  | fieldsetWrapper
  | normal
  deriving DecidableEq, Repr

/-- Whether a box is a fragmentation context root (`IsFragmentationContextRoot`,
    `IsFragmentationContextRootNested`, `IsFragmentationContextRootFieldset`).
    Multicol containers and fieldset multicol wrappers establish fragmentation contexts;
    columns and normal children do not. -/
def isFragmentationContextRoot : BoxType → Bool
  | .multicol | .fieldsetWrapper => true
  | .column | .normal => false

/-- A box or ancestor may have a descendant above block start if any child has negative
    start offset or negative margin (`MayHaveDescendantAboveBlockStart`,
    `MayHaveDescendantAboveBlockStartBlockInInline`). -/
def mayHaveDescendantAboveBlockStart (childTop : Int) : Bool :=
  childTop < 0

/-- Reference box for overflow-clip-margin. -/
inductive ClipBox where
  | contentBox
  | paddingBox
  | borderBox
  deriving DecidableEq, Repr

/-- Ink overflow width under overflow-clip-margin (`OverflowClipMarginVisualBox`). -/
def clipMarginWidth (cb : ClipBox) : Nat :=
  match cb with
  | .contentBox => 75
  | .paddingBox => 80
  | .borderBox => 85

/-- Ink overflow height of fragment 1 under overflow-clip-margin (`OverflowClipMarginVisualBox`). -/
def clipMarginHeightFrag1 (cb : ClipBox) : Nat :=
  match cb with
  | .contentBox => 40
  | .paddingBox => 45
  | .borderBox => 50

/-- Overflow clip margin monotonically expands ink overflow from content-box to padding-box to border-box. -/
theorem clip_margin_monotonic :
    clipMarginWidth .contentBox < clipMarginWidth .paddingBox ∧
    clipMarginWidth .paddingBox < clipMarginWidth .borderBox ∧
    clipMarginHeightFrag1 .contentBox < clipMarginHeightFrag1 .paddingBox ∧
    clipMarginHeightFrag1 .paddingBox < clipMarginHeightFrag1 .borderBox := by
  decide

/-- Inline-block isolates floats within its own IFC, while flow-root and positioned propagate. -/
theorem inline_block_isolates_floats :
    propagatesFloats .inlineBlock = false ∧
    propagatesFloats .flowRoot = true ∧
    propagatesFloats .positioned = true := by
  decide

end BlockPhysicalFragment
end ChromiumLayout
