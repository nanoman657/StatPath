/-
  docs/chromium-layout/tests/TestsInline_LineInfo.lean

  Formalized layout tests for LineInfo
  (`third_party/blink/renderer/core/layout/inline/line_info_test.cc`).

  Covers:
  - InflowEndOffset (`inline/line_info_test.cc:23`)
-/
import LayoutTypes
import InlineRuby

namespace ChromiumLayout

/-! ## 1. Inflow End Offset (`inline/line_info_test.cc:23`) -/

/-- Test `LineInfoTest, InflowEndOffset` (`inline/line_info_test.cc:23`).
    InflowEndOffset returns the end offset of text in the ruby base (7 == "abc" (3) + kOpenRubyColumn (1) + "def" (3)),
    excluding annotation text ("rt"). -/
theorem lineInfo_inflowEndOffset :
    let results : List LineResultItem := [
      .text 0 3,
      .openRubyColumn 3 4,
      .rubyColumn 4 7 9
    ]
    lineInflowEndOffset 0 results = 7 := by
  decide

end ChromiumLayout
