import OutOfFlowCB

namespace TestsBlock

open ChromiumLayout.OutOfFlowCB

-- out_of_flow_layout_part_test.cc:46: FixedInsideAbs
-- #abs has top: 49, #pad has height: 50 -> fixed1 static top is 49 + 50 = 99
-- #fixed2 has top: 9
-- Neither #abs nor #rel has layout containment: containing block is viewport (none)
def FixedInsideAbs_cb : Option Nat := fixedContainingBlock [false, false]
def FixedInsideAbs_fixed1_top : Nat := 49 + 50
def FixedInsideAbs_fixed2_top : Nat := 9

theorem FixedInsideAbs_vectors :
    FixedInsideAbs_cb = none ∧
    FixedInsideAbs_fixed1_top = 99 ∧
    FixedInsideAbs_fixed2_top = 9 := by
  decide

end TestsBlock
