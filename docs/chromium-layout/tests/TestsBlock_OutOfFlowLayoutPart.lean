import BlockAbsolute

namespace TestsBlock

open ChromiumLayout.BlockAbsolute

-- out_of_flow_layout_part_test.cc:46: FixedInsideAbs
-- #abs is at top:49, left:0. #pad has height:50.
-- fixed1 has no explicit top/left; static position top is #abs.top + #pad.height = 99.
-- fixed2 has top:9, left:7.
def fixedInsideAbs_fixed1 : OofDescendant :=
  { posType := .fixed, top := .auto, width := .px 50, staticTop := 50 }

def fixedInsideAbs_fixed2 : OofDescendant :=
  { posType := .fixed, top := .px 9, left := .px 7 }

theorem FixedInsideAbs_offsets :
    -- fixed1 top is static: #abs.top (49) + #pad.height (50) = 99
    (resolveOofOffset 49 0 fixedInsideAbs_fixed1).2 = 99 ∧
    -- fixed2 top is positioned: #fixed2.top = 9, left = 7
    (resolveOofOffset 49 0 fixedInsideAbs_fixed2).2 = 9 ∧
    (resolveOofOffset 49 0 fixedInsideAbs_fixed2).1 = 7 := by
  decide

end TestsBlock
