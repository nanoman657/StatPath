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
    A `<br>` layout object has a single non-collapsed line-break unit with resolved length 1,
    derived from the DOM input `[DomNode.br 0]`. -/
theorem layoutBR_textMethods :
    let nodes := [DomNode.br 0]
    let units := buildDomOffsetMapping nodes
    (units = [{ nodeId := 0, unitType := .identity, domStart := 0, domEnd := 1, textStart := 0, textEnd := 1 }]) ∧
    (domNodeSnapCode units nodes[0]! 0 = "BC-") ∧
    (domNodeSnapCode units nodes[0]! 1 = "--A") := by
  decide

end ChromiumLayout
