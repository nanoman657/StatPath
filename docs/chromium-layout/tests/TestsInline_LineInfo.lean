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
    InflowEndOffset returns the end offset of text in the ruby base (7 == "abc" + kOpenRubyColumn + "def"),
    excluding annotation text ("rt") per CSS Ruby 1 §3.1. -/
theorem lineInfo_inflowEndOffset :
    let textPrefix := "abc"
    let rubyBase := "def"
    let rubyAnno := "rt"
    let off0 := 0
    let off1 := off0 + textPrefix.length
    let offOpen := off1 + 1
    let offBaseEnd := offOpen + rubyBase.length
    let offAnnoEnd := offBaseEnd + rubyAnno.length
    let results : List LineResultItem := [
      .text off0 off1,
      .openRubyColumn off1 offOpen,
      .rubyColumn offOpen offBaseEnd offAnnoEnd
    ]
    lineInflowEndOffset off0 results = 7 := by
  decide

end ChromiumLayout
