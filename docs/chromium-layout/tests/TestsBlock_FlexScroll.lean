import FlexScroll

namespace TestsBlock

open ChromiumLayout.BlockWritingMode ChromiumLayout.FlexScroll

-- CommonStyle(): #flex-box 400x300, padding 10px 20px 30px 40px, border 20px 30px 40px 50px,
-- scrollbar 15 x 16, child 2000 x 1000 (flex: none).
private def cfg (wm : WritingMode) (rtl : Bool) (fd : FlexDir) : Cfg :=
  { wm, rtl, fd, contentW := 400, contentH := 300, border := ⟨20, 30, 40, 50⟩, padding := ⟨10, 20, 30, 40⟩,
    scrollbarW := 15, scrollbarH := 16, childW := 2000, childH := 1000 }

private def bb : R := (0, 0, 540, 400)
-- Expected shapes (overflow rect, max, min, origin, child). The padding and content boxes are
-- (50,20,445,324) and (90,30,385,284), or (65,20,..) and (105,30,..) with the scrollbar on the left.
private def A : Out := ⟨bb, (50, 20, 445, 324), (90, 30, 385, 284), (0, 0), (50, 20, 2060, 1040), (1615, 716), (0, 0), (0, 0), (90, 30)⟩
private def B : Out := ⟨bb, (50, 20, 445, 324), (90, 30, 385, 284), (0, 0), (-1565, 20, 2060, 1040), (0, 716), (-1615, 0), (1615, 0), (-1525, 30)⟩
private def C : Out := ⟨bb, (50, 20, 445, 324), (90, 30, 385, 284), (0, 0), (50, -696, 2060, 1040), (1615, 0), (0, -716), (0, 716), (90, -686)⟩
private def D : Out := ⟨bb, (50, 20, 445, 324), (90, 30, 385, 284), (0, 0), (-1565, -696, 2060, 1040), (0, 0), (-1615, -716), (1615, 716), (-1525, -686)⟩
private def L1 : Out := ⟨bb, (65, 20, 445, 324), (105, 30, 385, 284), (15, 0), (-1550, 20, 2060, 1040), (0, 716), (-1615, 0), (1615, 0), (-1510, 30)⟩
private def L2 : Out := ⟨bb, (65, 20, 445, 324), (105, 30, 385, 284), (15, 0), (65, 20, 2060, 1040), (1615, 716), (0, 0), (0, 0), (105, 30)⟩

-- layout_flexible_box_test.cc:96 RowHTB, :123 RowVLR, :151 RowVRL
theorem FlexScroll_row : layout (cfg .horizontalTb false .row) = A ∧ layout (cfg .verticalLr false .row) = A ∧
    layout (cfg .verticalRl false .row) = B := by decide +kernel
-- :160 RowReverseHTB, :229 RowReverseVRL (:200 RowReverseVLR is a held-out row: not transcribed)
theorem FlexScroll_rowReverse : layout (cfg .horizontalTb false .rowReverse) = B ∧
    layout (cfg .verticalRl false .rowReverse) = D := by decide +kernel
-- :238 ColumnHTB, :247 ColumnVLR, :256 ColumnVRL
theorem FlexScroll_column : layout (cfg .horizontalTb false .column) = A ∧ layout (cfg .verticalLr false .column) = A ∧
    layout (cfg .verticalRl false .column) = B := by decide +kernel
-- :292 ColumnReverseVLR, :315 ColumnReverseVRL (:269 ColumnReverseHTB is a held-out row: not transcribed)
theorem FlexScroll_columnReverse : layout (cfg .verticalLr false .columnReverse) = B ∧ layout (cfg .verticalRl false .columnReverse) = A := by decide +kernel
-- :357 RTLRowHTB, :366 RTLRowVLR, :375 RTLRowVRL
theorem FlexScroll_rtlRow : layout (cfg .horizontalTb true .row) = L1 ∧ layout (cfg .verticalLr true .row) = C ∧
    layout (cfg .verticalRl true .row) = D := by decide +kernel
-- :384 RTLRowReverseHTB, :409 RTLRowReverseVLR, :418 RTLRowReverseVRL
theorem FlexScroll_rtlRowReverse : layout (cfg .horizontalTb true .rowReverse) = L2 ∧
    layout (cfg .verticalLr true .rowReverse) = A ∧ layout (cfg .verticalRl true .rowReverse) = B := by decide +kernel

end TestsBlock
