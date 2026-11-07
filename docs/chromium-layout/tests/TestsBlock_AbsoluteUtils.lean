import BlockAbsolute

namespace TestsBlock

open ChromiumLayout.BlockAbsolute

-- absolute_utils_test.cc:150: Horizontal
theorem Horizontal_vectors :
    -- All auto => width is content 116, start is 0
    (computeOof 200 .auto .auto .auto .auto .auto 116).size = 116 ∧
    (computeOof 200 .auto .auto .auto .auto .auto 116).insetStart = 0 ∧
    -- All auto + RTL
    (computeOof 200 .auto .auto .auto .auto .auto 116 true).insetEnd = 84 ∧
    -- left 5, right 13, width 160: margins auto split 11
    (computeOof 200 (.px 5) (.px 13) .auto .auto (.px 160) 116).insetStart = 16 ∧
    (computeOof 200 (.px 5) (.px 13) .auto .auto (.px 160) 116).insetEnd = 24 ∧
    -- Overconstrained LTR: width 200
    (computeOof 200 (.px 5) (.px 13) .auto .auto (.px 200) 116).insetStart = 5 ∧
    (computeOof 200 (.px 5) (.px 13) .auto .auto (.px 200) 116).insetEnd = -5 ∧
    -- Overconstrained RTL: width 200
    (computeOof 200 (.px 5) (.px 13) .auto .auto (.px 200) 116 true).insetStart = -13 ∧
    (computeOof 200 (.px 5) (.px 13) .auto .auto (.px 200) 116 true).insetEnd = 13 ∧
    -- Rule 1: left and width auto
    (computeOof 200 .auto (.px 13) (.px 7) (.px 15) .auto 116).size = 116 ∧
    -- Rule 2: left and right auto
    (computeOof 200 .auto .auto (.px 7) (.px 15) (.px 160) 116).insetStart = 7 ∧
    (computeOof 200 .auto .auto (.px 7) (.px 15) (.px 160) 116).insetEnd = 33 ∧
    -- Rule 3: width and right auto
    (computeOof 200 (.px 5) .auto (.px 7) (.px 15) .auto 116).size = 116 ∧
    (computeOof 200 (.px 5) .auto (.px 7) (.px 15) .auto 116).insetEnd = 72 ∧
    -- Rule 4: left is auto
    (computeOof 200 .auto (.px 13) (.px 7) (.px 15) (.px 160) 116).insetStart = 12 ∧
    -- Rule 5: right is auto
    (computeOof 200 (.px 5) .auto (.px 7) (.px 15) (.px 160) 116).insetEnd = 28 ∧
    -- Rule 6: width is auto
    (computeOof 200 (.px 5) (.px 13) (.px 7) (.px 15) .auto 116).size = 160 := by
  decide

-- absolute_utils_test.cc:315: Vertical
theorem Vertical_vectors :
    -- All auto: height 60, start 0
    (computeOof 300 .auto .auto .auto .auto .auto 60).size = 60 ∧
    (computeOof 300 .auto .auto .auto .auto .auto 60).insetStart = 0 ∧
    -- top 5, bottom 13, height 260
    (computeOof 300 (.px 5) (.px 13) .auto .auto (.px 260) 60).insetStart = 16 ∧
    (computeOof 300 (.px 5) (.px 13) .auto .auto (.px 260) 60).insetEnd = 24 ∧
    -- top 5, bottom 13, height 300, negative auto margins split
    (computeOof 300 (.px 5) (.px 13) .auto .auto (.px 300) 60 false true).insetStart = -4 ∧
    (computeOof 300 (.px 5) (.px 13) .auto .auto (.px 300) 60 false true).insetEnd = 4 ∧
    -- Rule 1: top and height auto
    (computeOof 300 .auto (.px 13) (.px 7) (.px 15) .auto 60).size = 60 ∧
    -- Rule 2: top and bottom auto
    (computeOof 300 .auto .auto (.px 7) (.px 15) (.px 260) 60).insetStart = 7 ∧
    (computeOof 300 .auto .auto (.px 7) (.px 15) (.px 260) 60).insetEnd = 33 ∧
    -- Rule 3: height and bottom auto
    (computeOof 300 (.px 5) .auto (.px 7) (.px 15) .auto 60).size = 60 ∧
    -- Rule 4: top auto
    (computeOof 300 .auto (.px 13) (.px 7) (.px 15) (.px 260) 60).insetStart = 12 ∧
    -- Rule 5: bottom auto
    (computeOof 300 (.px 5) .auto (.px 7) (.px 15) (.px 260) 60).size = 260 := by
  decide

end TestsBlock
