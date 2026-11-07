import BlockLength
import BlockWritingMode
import ColumnWidth

namespace TestsBlock

open ChromiumLayout.BlockLength
open ChromiumLayout.BlockWritingMode
open ChromiumLayout.ColumnWidth

-- length_utils_test.cc:120: TestResolveInlineLength
theorem TestResolveInlineLength_vectors :
    resolveLen (some 200) none (.pct 30) = some 60 ∧
    resolveLen (some 200) none (.px 150) = some 150 ∧
    resolveLen (some 200) none .stretch = some 200 ∧
    resolveLen (some 200) (some ⟨30, 40⟩) .minContent = some 30 ∧
    resolveLen (some 200) (some ⟨30, 40⟩) .maxContent = some 40 ∧
    resolveLen (some 200) (some ⟨30, 40⟩) .fitContent = some 40 ∧
    resolveLen (some 200) (some ⟨30, 800⟩) .fitContent = some 200 := by
  decide

-- length_utils_test.cc:144: TestIndefiniteResolveInlineLength
theorem TestIndefiniteResolveInlineLength_vectors :
    resolveMin none none .auto = 0 ∧
    resolveMax none none (.pct 30) = none ∧
    resolveMax none none .stretch = none := by
  decide

-- length_utils_test.cc:155: TestResolveBlockLength
theorem TestResolveBlockLength_vectors :
    resolveLen (some 300) none (.pct 30) = some 90 ∧
    resolveLen (some 300) none (.px 150) = some 150 ∧
    resolveLen (some 300) none .stretch = some 300 := by
  decide

-- length_utils_test.cc:161: TestComputeContentContribution
theorem TestComputeContentContribution_vectors :
    contribution .contentBox 0 (.pct 30) .auto .auto ⟨30, 40⟩ = ⟨30, 40⟩ ∧
    contribution .contentBox 0 .stretch .auto .auto ⟨30, 40⟩ = ⟨30, 40⟩ ∧
    contribution .contentBox 0 (.px 150) .auto .auto ⟨30, 40⟩ = ⟨150, 150⟩ ∧
    contribution .contentBox 0 .auto .auto .auto ⟨30, 40⟩ = ⟨30, 40⟩ ∧
    contribution .contentBox 400 .auto .auto .auto ⟨430, 440⟩ = ⟨430, 440⟩ ∧
    contribution .contentBox 0 (.calc 100 10) .auto .auto ⟨30, 40⟩ = ⟨30, 40⟩ ∧
    contribution .contentBox 0 .auto .auto (.px 35) ⟨30, 40⟩ = ⟨30, 35⟩ ∧
    contribution .contentBox 0 .auto (.px 80) (.px 35) ⟨30, 40⟩ = ⟨80, 80⟩ ∧
    contribution .contentBox 50 (.px 100) .auto .auto ⟨80, 90⟩ = ⟨150, 150⟩ ∧
    contribution .borderBox 50 (.px 100) .auto .auto ⟨80, 90⟩ = ⟨100, 100⟩ ∧
    contribution .borderBox 400 (.px 100) .auto .auto ⟨430, 440⟩ = ⟨400, 400⟩ ∧
    contribution .borderBox 400 .minContent .auto .auto ⟨430, 440⟩ = ⟨430, 430⟩ ∧
    contribution .borderBox 400 (.px 100) .auto .maxContent ⟨430, 440⟩ = ⟨400, 400⟩ ∧
    contribution .borderBox 0 (.px 100) .auto .maxContent ⟨30, 40⟩ = ⟨40, 40⟩ := by
  decide

-- length_utils_test.cc:270: TestComputeInlineSizeForFragment
theorem TestComputeInlineSizeForFragment_vectors :
    inlineSizeForFragment 200 false .contentBox 0 0 (.pct 30) .auto .auto ⟨30, 40⟩ = 60 ∧
    inlineSizeForFragment 200 false .contentBox 0 0 .stretch .auto .auto ⟨30, 40⟩ = 200 ∧
    inlineSizeForFragment 200 false .contentBox 0 0 (.px 150) .auto .auto ⟨30, 40⟩ = 150 ∧
    inlineSizeForFragment 200 false .contentBox 0 0 .auto .auto .auto ⟨30, 40⟩ = 200 ∧
    inlineSizeForFragment 200 false .contentBox 0 0 (.calc 100 (-10)) .auto .auto ⟨30, 40⟩ = 80 ∧
    inlineSizeForFragment 120 true .contentBox 0 0 (.px 150) .auto .auto ⟨30, 40⟩ = 120 ∧
    inlineSizeForFragment 200 false .contentBox 0 0 (.px 200) .auto (.pct 80) ⟨30, 40⟩ = 160 ∧
    inlineSizeForFragment 200 false .contentBox 0 0 (.px 100) (.pct 80) (.pct 80) ⟨30, 40⟩ = 160 ∧
    inlineSizeForFragment 200 false .contentBox 0 20 .auto .auto .auto ⟨30, 40⟩ = 180 ∧
    inlineSizeForFragment 200 false .contentBox 50 20 (.px 100) .auto .auto ⟨30, 40⟩ = 150 ∧
    inlineSizeForFragment 200 false .borderBox 50 20 (.px 100) .auto .auto ⟨30, 40⟩ = 100 ∧
    inlineSizeForFragment 200 false .borderBox 400 20 (.px 100) .auto .auto ⟨30, 40⟩ = 400 ∧
    inlineSizeForFragment 200 false .borderBox 400 20 .stretch .auto .auto ⟨30, 40⟩ = 400 ∧
    inlineSizeForFragment 120 false .borderBox 400 20 .minContent .auto .auto ⟨430, 440⟩ = 430 ∧
    inlineSizeForFragment 120 false .borderBox 400 20 (.px 100) .auto .maxContent ⟨430, 440⟩ = 400 ∧
    inlineSizeForFragment 120 false .borderBox 0 20 (.px 100) .auto .maxContent ⟨30, 40⟩ = 40 := by
  decide

-- length_utils_test.cc:355: TestComputeBlockSizeForFragment
theorem TestComputeBlockSizeForFragment_vectors :
    blockSizeForFragment (some 300) false .contentBox 0 0 0 (.pct 30) .auto .auto none none none = some 90 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 .stretch .auto .auto none none none = some 300 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 (.px 150) .auto .auto none none none = some 150 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 .auto .auto .auto none (some 0) none = some 0 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 .auto .auto .auto none (some 120) none = some 120 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 (.calc 100 (-10)) .auto .auto none none none = some 70 ∧
    blockSizeForFragment (some 200) true .contentBox 0 0 0 (.px 150) .auto .auto none none none = some 200 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 (.px 300) .auto (.pct 80) none none none = some 240 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 (.px 100) (.pct 80) (.pct 80) none none none = some 240 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 20 .stretch .auto .auto none none none = some 280 ∧
    blockSizeForFragment (some 300) false .contentBox 50 0 0 (.px 100) .auto .auto none none none = some 150 ∧
    blockSizeForFragment (some 300) false .borderBox 50 0 0 (.px 100) .auto .auto none none none = some 100 ∧
    blockSizeForFragment (some 300) false .borderBox 400 0 0 (.px 100) .auto .auto none none none = some 400 ∧
    blockSizeForFragment (some 300) false .borderBox 400 0 0 .stretch .auto .auto none none none = some 400 ∧
    blockSizeForFragment (some 300) false .contentBox 0 0 0 .auto .auto .auto (some (2, 1)) (some 0) (some 100) = some 50 ∧
    blockSizeForFragment (some 300) false .contentBox 20 10 0 .auto .auto .auto (some (2, 1)) (some 20) (some 100) = some 65 ∧
    blockSizeForFragment (some 300) false .borderBox 20 10 0 .auto .auto .auto (some (2, 1)) (some 20) (some 100) = some 50 := by
  decide

-- length_utils_test.cc:443: TestIndefinitePercentages
theorem TestIndefinitePercentages_vectors :
    blockSizeForFragment none false .contentBox 0 0 0 (.pct 20) (.px 20) .auto none none none = none ∧
    blockSizeForFragment none false .contentBox 0 0 0 (.pct 20) (.px 20) .auto none (some 10) none = some 20 ∧
    blockSizeForFragment none false .contentBox 0 0 0 (.pct 20) (.px 20) .auto none (some 120) none = some 120 := by
  decide

-- length_utils_test.cc:475: TestMargins
theorem TestMargins_vectors :
    resolveEdge 200 (.pct 10) = 20 ∧
    resolveEdge 200 (.px 52) = 52 ∧
    resolveEdge 200 .auto = 0 ∧
    resolveEdge 200 (.pct 11) = 22 := by
  decide

-- length_utils_test.cc:493: TestBorders
theorem TestBorders_vectors :
    toLogical .verticalLr ⟨1, 2, 3, 4⟩ = ⟨1, 3, 4, 2⟩ := rfl

-- length_utils_test.cc:514: TestPadding
theorem TestPadding_vectors :
    let phys : Phys := ⟨resolveEdge 200 (.pct 10), resolveEdge 200 (.px 52),
                         resolveEdge 200 .auto, resolveEdge 200 (.pct 11)⟩
    toLogical .verticalRl phys = ⟨20, 0, 52, 22⟩ := rfl

-- length_utils_test.cc:534: TestAutoMargins
theorem TestAutoMargins_vectors :
    autoMargins 200 150 .auto .auto = (25, 25) ∧
    autoMargins 200 150 (.px 0) .auto = (0, 50) ∧
    autoMargins 200 150 .auto (.px 0) = (50, 0) ∧
    autoMargins 200 150 .auto (.px 5000) = (0, 5000) := by
  decide

-- length_utils_test.cc:612: TestColumnWidthAndCount
theorem TestColumnWidthAndCount_vectors :
    usedWidth 0 100 0 300 = 100 ∧ usedCount 0 100 0 300 = 3 ∧
    usedWidth 0 101 0 300 = 150 ∧ usedCount 0 101 0 300 = 2 ∧
    usedWidth 0 151 0 300 = 300 ∧ usedCount 0 151 0 300 = 1 ∧
    usedWidth 0 1000 0 300 = 300 ∧ usedCount 0 1000 0 300 = 1 ∧
    usedWidth 0 100 10 320 = 100 ∧ usedCount 0 100 10 320 = 3 ∧
    usedWidth 0 101 10 310 = 150 ∧ usedCount 0 101 10 310 = 2 ∧
    usedWidth 0 151 10 300 = 300 ∧ usedCount 0 151 10 300 = 1 ∧
    usedWidth 0 1000 10 300 = 300 ∧ usedCount 0 1000 10 300 = 1 ∧
    usedWidth 4 0 0 500 = 125 ∧ usedCount 4 0 0 500 = 4 ∧
    usedWidth 4 100 0 500 = 125 ∧ usedCount 4 100 0 500 = 4 ∧
    usedWidth 6 100 0 500 = 100 ∧ usedCount 6 100 0 500 = 5 ∧
    usedWidth 0 100 0 500 = 100 ∧ usedCount 0 100 0 500 = 5 ∧
    usedWidth 4 0 10 530 = 125 ∧ usedCount 4 0 10 530 = 4 ∧
    usedWidth 4 100 10 530 = 125 ∧ usedCount 4 100 10 530 = 4 ∧
    usedWidth 6 100 10 540 = 100 ∧ usedCount 6 100 10 540 = 5 ∧
    usedWidth 0 100 10 540 = 100 ∧ usedCount 0 100 10 540 = 5 ∧
    usedWidth 3 0 10 10 = 0 ∧ usedCount 3 0 10 10 = 3 := by
  decide

-- length_utils_test.cc:657: AspectRatio: raw LayoutUnit values (1/64 px)
def rawLU (px : Nat) : Nat := px * 64

theorem AspectRatio_vectors :
    inlineFromAspectRatio (rawLU 8000) (rawLU 8000) (rawLU 8000) = rawLU 8000 ∧
    inlineFromAspectRatio (rawLU 1) (rawLU 10000) (rawLU 10000) = rawLU 1 ∧
    inlineFromAspectRatio (rawLU 1) (rawLU 1000000) (rawLU 4000000) = rawLU 4 ∧
    inlineFromAspectRatio (rawLU 3) (rawLU 5000000) (rawLU 5) = 0 ∧
    inlineFromAspectRatio (rawLU 20000000) (rawLU 10000000) (rawLU 4000000) = rawLU 8000000 ∧
    inlineFromAspectRatio (rawLU 10000) (rawLU 1) (rawLU 10000) = luMax := by
  decide

end TestsBlock
