/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineLineBox
import InlineShaping

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-!
# Tests for Inline Layout & Formatting Contexts

Corresponds to:
- `core/layout/inline_layout_test.cc`
- `core/layout/inline/inline_layout_algorithm_test.cc`
-/

/-! ### BlockWithSingleTextNode (`inline_layout_test.cc:32`) -/
theorem inlineLayout_blockWithSingleTextNode :
    (collectInlines [.text "Hello ", .openTag "strong", .text "World", .closeTag, .text "!"]).text = "Hello World!" := by
  decide

/-! ### BlockWithTextAndAtomicInline (`inline_layout_test.cc:59`) -/
theorem inlineLayout_blockWithTextAndAtomicInline :
    (collectInlines [.text "Hello ", .atomicInline 10, .text "."]).text = "Hello \uFFFC." := by
  decide

/-! ### Types (`inline/inline_layout_algorithm_test.cc:97`) -/
theorem inlineLayout_emptyLineBoxTypes :
    isLineBoxEmpty [.text "normal"] = false ∧
    isLineBoxEmpty [.openTag "span", .closeTag] = true := by
  decide

/-! ### MAYBE_VerticalAlignBottomReplaced (`inline/inline_layout_algorithm_test.cc:431`) -/
theorem inlineLayout_verticalAlignBottomReplaced :
    let r := layoutReplacedLineBox 10 96 .bottom
    r.lineHeight = 96 ∧ r.itemTopOffset = 0 := by
  decide

end ChromiumLayout.TestsInline
