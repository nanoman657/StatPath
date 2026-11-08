/-
  docs/chromium-layout/tests/TestsInline_LayoutBR.lean

  Formalized layout test for LayoutBR
  (`third_party/blink/renderer/core/layout/layout_br_test.cc`).

  Covers:
  - TextMethods (`layout_br_test.cc:14`)
-/
import LayoutTypes
import LayoutInline
import InlineOffsetMapping

namespace ChromiumLayout

/-! ## 1. TextMethods (`layout_br_test.cc:14`) -/

/-- Test `LayoutBRTest, TextMethods` (`layout_br_test.cc:14`).
    A `<br>` layout object has a single non-collapsed line-break unit with resolved length 1. -/
theorem layoutBR_textMethods :
    let units := layoutBRUnits
    (units.length = 1) ∧
    ((units.headD {}).unitType = .identity) ∧
    ((units.headD {}).textEnd - (units.headD {}).textStart = 1) ∧
    (getSnapCodeWithUnits units ['\n'] 0 = "BC-") ∧
    (getSnapCodeWithUnits units ['\n'] 1 = "--A") := by
  decide

end ChromiumLayout
