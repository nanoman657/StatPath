/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineLineWidths

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-!
# Tests for Line Widths and Float Exclusion Precomputation

Transcribed from `inline/line_widths_test.cc`.
-/

/-- Helper returning the widths for each line of an optional LineWidths. -/
def getLineWidthsList (optLw : Option LineWidths) (count : Nat) : List Nat :=
  match optLw with
  | none => []
  | some lw => (List.range count).map lw.get

/-! ### Test 1: LineWidthsDataTest.Data (`inline/line_widths_test.cc:175`) -/
theorem lineWidthsDataTest_data :
    -- Case 0: No floats
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.text "0123 5678"]) 2 = [100, 100] ∧
    -- Case 1: Inflow tags, no floats
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.text "0123 ", .openTag true, .text "5", .closeTag, .text "678"]) 2 = [100, 100] ∧
    -- Case 2: Single left float
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .text "0123 5678"]) 2 = [70, 100] ∧
    -- Case 3: Single right float
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .text "0123 5678"]) 2 = [70, 100] ∧
    -- Case 4: Non-leading float
    computeLineWidths (100 * 4) (10 * 4) [.text "0123 5678", .floating (30 * 4) (10 * 4)] = none ∧
    -- Case 5: Float fits leading (lh: 15px, float h: 11px)
    getLineWidthsList (computeLineWidths (100 * 4) (15 * 4) [.floating (30 * 4) (11 * 4), .text "0123 5678"]) 2 = [70, 100] ∧
    -- Case 6: Float taller than one line (lh: 10px, float h: 11px)
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (11 * 4), .text "0123 5678"]) 3 = [70, 70, 100] ∧
    -- Case 7: Float taller than one line with line-height (lh: 15px, float h: 16px)
    getLineWidthsList (computeLineWidths (100 * 4) (15 * 4) [.floating (30 * 4) (16 * 4), .text "0123 5678"]) 3 = [70, 70, 100] ∧
    -- Case 8: Fractional float height 46.25px with line-height 23px (185 quanta / 92 quanta)
    getLineWidthsList (computeLineWidths (100 * 4) (23 * 4) [.floating (30 * 4) 185, .text "0123 5678"]) 4 = [70, 70, 70, 100] ∧
    -- Case 9: Multiple floats forming single exclusion (total float width 60px)
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .floating (30 * 4) (10 * 4), .text "0123 5678"]) 2 = [40, 100] ∧
    -- Case 10: Multiple floats forming stepped exclusions (h1: 20px, h2: 10px)
    computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (20 * 4), .floating (30 * 4) (10 * 4), .text "0123 5678"] = none ∧
    -- Case 11: Non-baseline vertical-align
    computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .text "0123 5678 ", .openTag false, .text "0", .closeTag, .text "123 5678"] = none ∧
    -- Case 12: Multiple fonts fitting the strut
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .text "0123 5678 ", .text "0123" true, .text " 5678"]) 2 = [70, 100] ∧
    -- Case 13: Multiple fonts exceeding the strut
    computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .text "0123 5678 ", .text "0123" false, .text " 5678"] = none ∧
    -- Case 14: Atomic inlines without floats
    getLineWidthsList (computeLineWidths (100 * 4) (10 * 4) [.text "0123 ", .atomicInline, .text " 5678"]) 2 = [100, 100] ∧
    -- Case 15: Atomic inlines with leading floats
    computeLineWidths (100 * 4) (10 * 4) [.floating (30 * 4) (10 * 4), .text "0123 ", .atomicInline, .text " 5678"] = none := by
  decide

end ChromiumLayout.TestsInline
