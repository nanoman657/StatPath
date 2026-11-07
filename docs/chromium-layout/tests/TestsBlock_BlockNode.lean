/-
  Vectors transcribed from block_node_test.cc.
-/
import BlockNode

namespace ChromiumLayout
namespace TestsBlock
open BlockNode

/-- `IsFloatingForOutOfFlowFloating` (line 16): `float:left; position:absolute` is not floating. -/
theorem IsFloatingForOutOfFlowFloating_vectors :
    isFloating .left .absolute = false ∧ isFloating .left .fixed = false ∧
    isFloating .left .static = true := by decide

/-- `ChildInlineAndBlock` (31): `Hello!<div></div>`: two block children, then none. -/
theorem ChildInlineAndBlock_vectors :
    childNodes [.text, .block] = [.block, .block] := by decide

/-- `ChildBlockAndInline` (45): `<div></div>Hello!`. -/
theorem ChildBlockAndInline_vectors :
    childNodes [.block, .text] = [.block, .block] := by decide

/-- `ChildFloatBeforeBlock` (59): `<float></float><div></div>`: two block children. -/
theorem ChildFloatBeforeBlock_vectors :
    childNodes [.float, .block] = [.block, .block] := by decide

/-- `ChildFloatBeforeInline` (76): `<float></float>Hello!`: one inline child. -/
theorem ChildFloatBeforeInline_vectors :
    childNodes [.float, .text] = [.inline] := by decide

/-- `ChildFloatAfterInline` (91): `Hello<float></float>`: one inline child. -/
theorem ChildFloatAfterInline_vectors :
    childNodes [.text, .float] = [.inline] := by decide

/-- `ChildFloatOnly` (106): a lone float is one block child. -/
theorem ChildFloatOnly_vectors : childNodes [.float] = [.block] := by decide

/-- `ChildFloatWithSpaces` (121): a float between whitespace is one block child (whitespace
    generates no item). -/
theorem ChildFloatWithSpaces_vectors : childNodes [.float] = [.block] := by decide

/-- `ChildOofBeforeInline` (138): `<oof></oof>Hello!`: one inline child. -/
theorem ChildOofBeforeInline_vectors : childNodes [.oof, .text] = [.inline] := by decide

/-- `ChildOofAfterInline` (153): `Hello!<oof></oof>`: one inline child. -/
theorem ChildOofAfterInline_vectors : childNodes [.text, .oof] = [.inline] := by decide

end TestsBlock
end ChromiumLayout
