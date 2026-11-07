/-
  docs/chromium-layout/tests/TestsInline_InlineNode.lean

  Test vectors and theorems transcribed from:
  `third_party/blink/renderer/core/layout/inline/inline_node_test.cc`

  Note: All tests in `inline_node_test.cc` are classified as either:
  - `internal`: asserting C++ layout invalidation flags (NeedsCollectInlines, SetText, etc.)
  - `blocked: model lacks CollectInlines tree traversal`: requiring DOM/HTML box tree parsing.
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout.TestsInline

-- All tests in inline_node_test.cc are classified as internal or blocked.

end ChromiumLayout.TestsInline
