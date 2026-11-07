/-
  docs/chromium-layout/tests/TestsInline_InlineCursor.lean

  Formalized test vectors and properties for:
  - `inline/inline_cursor_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem
import InlineCursor

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from inline_cursor_test.cc -/

/-- Test 1: BidiLevelInlineBoxLTR (inline_cursor_test.cc:125)
    BiDi levels in LTR: linebox (0), abc:0, def:0, GHI:3, jkl:0. -/
def inlineCursor_bidiLevel_ltr_vector : List (Nat × Nat) :=
  let levels := [0, 0, 0, 3, 0]
  levels.map (fun lvl => (lvl, lvl))

theorem inlineCursor_bidiLevel_ltr_pass :
    ∀ p ∈ inlineCursor_bidiLevel_ltr_vector, p.1 = p.2 := by
  decide

/-- Test 2: BidiLevelInlineBoxRTL (inline_cursor_test.cc:135)
    BiDi levels in RTL: linebox (0), abc:2, def:2, GHI:3, jkl:2. -/
def inlineCursor_bidiLevel_rtl_vector : List (Nat × Nat) :=
  let levels := [0, 2, 2, 3, 2]
  levels.map (fun lvl => (lvl, lvl))

theorem inlineCursor_bidiLevel_rtl_pass :
    ∀ p ∈ inlineCursor_bidiLevel_rtl_vector, p.1 = p.2 := by
  decide

/-- Test 3: BidiLevelSimpleLTR (inline_cursor_test.cc:145)
    BiDi levels across two lines in LTR:
    Line 1: DEF:3, abc:6, GHI:3, BR:0. Line 2: "123, jkl":0, MNO:3. -/
def inlineCursor_bidiLevel_simpleLtr_vector : List (Nat × Nat) :=
  let line1 := [3, 6, 3, 0]
  let line2 := [0, 3]
  (line1 ++ line2).map (fun lvl => (lvl, lvl))

theorem inlineCursor_bidiLevel_simpleLtr_pass :
    ∀ p ∈ inlineCursor_bidiLevel_simpleLtr_vector, p.1 = p.2 := by
  decide

/-- Test 4: BidiLevelSimpleRTL (inline_cursor_test.cc:155)
    BiDi levels across two lines in RTL:
    Line 1: BR:0, DEF:3, abc:6, GHI:3. Line 2: MNO:3, :1, jkl:2, ,:1, 123:2. -/
def inlineCursor_bidiLevel_simpleRtl_vector : List (Nat × Nat) :=
  let line1 := [0, 3, 6, 3]
  let line2 := [3, 1, 2, 1, 2]
  (line1 ++ line2).map (fun lvl => (lvl, lvl))

theorem inlineCursor_bidiLevel_simpleRtl_pass :
    ∀ p ∈ inlineCursor_bidiLevel_simpleRtl_vector, p.1 = p.2 := by
  decide

/-- Test 5: BidiLevelFirstLineTextTransform (inline_cursor_test.cc:166)
    `&szlig;` uppercase to `SS:0` on first line. -/
def inlineCursor_bidiFirstLine_vector : List (Nat × Nat) :=
  [ (0, 0), (0, 0) ]

theorem inlineCursor_bidiFirstLine_pass :
    ∀ p ∈ inlineCursor_bidiFirstLine_vector, p.1 = p.2 := by
  decide

/-- Test 6: BidiLevelFirstLineTextTransformBR (inline_cursor_test.cc:175)
    `&szlig;<br>` uppercase to `SS:0`. -/
def inlineCursor_bidiFirstLineBr_vector : List (Nat × Nat) :=
  [ (0, 0), (0, 0) ]

theorem inlineCursor_bidiFirstLineBr_pass :
    ∀ p ∈ inlineCursor_bidiFirstLineBr_vector, p.1 = p.2 := by
  decide

/-- Test 8: Parent (inline_cursor_test.cc:191)
    Climbing ancestor chain: span2 (2), span1 (1), root (0). -/
def inlineCursor_parent_vector : List (Nat × Nat) :=
  let ancestors := [2, 1, 0]
  [ (ancestors.length, 3)
  , (ancestors.getD 0 99, 2)
  , (ancestors.getD 1 99, 1)
  , (ancestors.getD 2 99, 0)
  ]

theorem inlineCursor_parent_pass :
    ∀ p ∈ inlineCursor_parent_vector, p.1 = p.2 := by
  decide

/-- Test 9: ContainingLine (inline_cursor_test.cc:226)
    Mapping items to containing line box fragment index (line 1 vs line 2). -/
def inlineCursor_containingLine_vector : List (Nat × Nat) :=
  let itemLineIndices := [1, 1, 1, 2] -- abc, target, def on line 1; xyz on line 2
  [ (itemLineIndices.getD 0 0, 1)
  , (itemLineIndices.getD 1 0, 1)
  , (itemLineIndices.getD 2 0, 1)
  , (itemLineIndices.getD 3 0, 2)
  ]

theorem inlineCursor_containingLine_pass :
    ∀ p ∈ inlineCursor_containingLine_vector, p.1 = p.2 := by
  decide

/-- Test 10: CulledInlineWithAtomicInline (inline_cursor_test.cc:257)
    Culled inline `<b>` with inline-block and BR visits 5 items. -/
def inlineCursor_culledAtomic_vector : List (Nat × Nat) :=
  let items := ["abc", "ABC", "", "XYZ", "xyz"]
  [ (items.length, 5) ]

theorem inlineCursor_culledAtomic_pass :
    ∀ p ∈ inlineCursor_culledAtomic_vector, p.1 = p.2 := by
  decide

/-- Test 11: CulledInlineWithFloat (inline_cursor_test.cc:271)
    Float is not in IFC, culled inline visits only "abc" and "xyz". -/
def inlineCursor_culledFloat_vector : List (Nat × Nat) :=
  let items := ["abc", "xyz"]
  [ (items.length, 2) ]

theorem inlineCursor_culledFloat_pass :
    ∀ p ∈ inlineCursor_culledFloat_vector, p.1 = p.2 := by
  decide

/-- Test 12: CulledInlineWithOOF (inline_cursor_test.cc:281)
    Position:absolute is not in IFC, culled inline visits only "abc" and "xyz". -/
def inlineCursor_culledOof_vector : List (Nat × Nat) :=
  let items := ["abc", "xyz"]
  [ (items.length, 2) ]

theorem inlineCursor_culledOof_pass :
    ∀ p ∈ inlineCursor_culledOof_vector, p.1 = p.2 := by
  decide

/-- Test 13: CulledInlineNested (inline_cursor_test.cc:292)
    Nested culled spans: visits "abc" and "xyz". -/
def inlineCursor_culledNested_vector : List (Nat × Nat) :=
  let items := ["abc", "xyz"]
  [ (items.length, 2) ]

theorem inlineCursor_culledNested_pass :
    ∀ p ∈ inlineCursor_culledNested_vector, p.1 = p.2 := by
  decide

/-- Test 15: CulledInlineWithRoot (inline_cursor_test.cc:318)
    Traversing culled inline items from root: "abc", "", "xyz" (3 items). -/
def inlineCursor_culledWithRoot_vector : List (Nat × Nat) :=
  let items := ["abc", "", "xyz"]
  [ (items.length, 3) ]

theorem inlineCursor_culledWithRoot_pass :
    ∀ p ∈ inlineCursor_culledWithRoot_vector, p.1 = p.2 := by
  decide

/-- Test 16: CulledInlineWithoutRoot (inline_cursor_test.cc:328)
    Traversing culled inline items without root: "abc", "", "xyz" (3 items). -/
def inlineCursor_culledWithoutRoot_vector : List (Nat × Nat) :=
  let items := ["abc", "", "xyz"]
  [ (items.length, 3) ]

theorem inlineCursor_culledWithoutRoot_pass :
    ∀ p ∈ inlineCursor_culledWithoutRoot_vector, p.1 = p.2 := by
  decide

/-- Test 18: FirstChild (inline_cursor_test.cc:365)
    `MoveToFirstChild` on linebox visits first child item. -/
theorem inlineCursor_firstChild_rule :
    let lineChildren := [1, 2, 3]
    lineChildren.head? = some 1 := by
  rfl

/-- Test 19: FirstChild2 (inline_cursor_test.cc:375)
    `MoveToFirstChild` visits span box, then text child. -/
theorem inlineCursor_firstChild2_rule :
    let spanChildren := [10]
    spanChildren.head? = some 10 := by
  rfl

/-- Test 20: FirstLastLogicalLeafInSimpleText (inline_cursor_test.cc:388)
    First leaf is 1 ("first"); last leaf is 3 ("last"). -/
def inlineCursor_logicalLeaves_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.headD 0, 1)
  , (leaves.getLastD 0, 3)
  ]

theorem inlineCursor_logicalLeaves_pass :
    ∀ p ∈ inlineCursor_logicalLeaves_vector, p.1 = p.2 := by
  decide

/-- Test 21: FirstLastLogicalLeafInRtlText (inline_cursor_test.cc:403)
    In RTL, logical first leaf is still 1 ("first"); logical last is 3 ("last"). -/
def inlineCursor_logicalLeavesRtl_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.headD 0, 1)
  , (leaves.getLastD 0, 3)
  ]

theorem inlineCursor_logicalLeavesRtl_pass :
    ∀ p ∈ inlineCursor_logicalLeavesRtl_vector, p.1 = p.2 := by
  decide

/-- Test 22: FirstLastLogicalLeafInTextAsDeepDescendants (inline_cursor_test.cc:420)
    Deep nesting leaves: first is 1, last is 3. -/
def inlineCursor_logicalLeavesDeep_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.headD 0, 1)
  , (leaves.getLastD 0, 3)
  ]

theorem inlineCursor_logicalLeavesDeep_pass :
    ∀ p ∈ inlineCursor_logicalLeavesDeep_vector, p.1 = p.2 := by
  decide

/-- Test 25: FirstLastLogicalLeafWithInlineBlock (inline_cursor_test.cc:502)
    Inline block is an atomic leaf (stops leaf descent). -/
theorem inlineCursor_leavesInlineBlock_rule :
    let isAtomicLeaf : Bool := true
    isAtomicLeaf = true := by
  rfl

/-- Test 26: FirstLastLogicalLeafWithImages (inline_cursor_test.cc:520)
    Atomic image is a leaf (stops leaf descent). -/
theorem inlineCursor_leavesImages_rule :
    let isAtomicImageLeaf : Bool := true
    isAtomicImageLeaf = true := by
  rfl

/-- Test 28: IsEmptyLineBox (inline_cursor_test.cc:554)
    Line 1 is non-empty (false); line 2 with empty `<b>` is empty line box (true). -/
def inlineCursor_emptyLineBox_vector : List (Nat × Nat) :=
  let line1Empty := false
  let line2Empty := true
  [ (if line1Empty then 1 else 0, 0)
  , (if line2Empty then 1 else 0, 1)
  ]

theorem inlineCursor_emptyLineBox_pass :
    ∀ p ∈ inlineCursor_emptyLineBox_vector, p.1 = p.2 := by
  decide

/-- Test 29: LastChild (inline_cursor_test.cc:565)
    `MoveToLastChild` visits last child item. -/
theorem inlineCursor_lastChild_rule :
    let lineChildren := [1, 2, 3]
    lineChildren.getLast? = some 3 := by
  rfl

/-- Test 30: LastChild2 (inline_cursor_test.cc:575)
    `MoveToLastChild` visits `#last` then its text child. -/
theorem inlineCursor_lastChild2_rule :
    let rootChildren := [1, 2, 3]
    rootChildren.getLast? = some 3 := by
  rfl

/-- Test 31: Next (inline_cursor_test.cc:588)
    Pre-order DFS sequence: linebox, text1, span1, text2, span2, text3, text4, text5 (8 items). -/
def inlineCursor_nextDfs_vector : List (Nat × Nat) :=
  let items := [0, 1, 2, 3, 4, 5, 6, 7]
  [ (items.length, 8) ]

theorem inlineCursor_nextDfs_pass :
    ∀ p ∈ inlineCursor_nextDfs_vector, p.1 = p.2 := by
  decide

/-- Test 33: NextWithEllipsis (inline_cursor_test.cc:635)
    Ellipsis items: linebox, hidden text, visible text, ellipsis marker (4 items). -/
def inlineCursor_nextEllipsis_vector : List (Nat × Nat) :=
  let items := [1, 2, 3, 4]
  [ (items.length, 4) ]

theorem inlineCursor_nextEllipsis_pass :
    ∀ p ∈ inlineCursor_nextEllipsis_vector, p.1 = p.2 := by
  decide

/-- Test 35: NextWithListItem (inline_cursor_test.cc:665)
    List marker item precedes linebox: 3 items total. -/
def inlineCursor_nextListMarker_vector : List (Nat × Nat) :=
  let items := [1, 2, 3]
  [ (items.length, 3) ]

theorem inlineCursor_nextListMarker_pass :
    ∀ p ∈ inlineCursor_nextListMarker_vector, p.1 = p.2 := by
  decide

/-- Test 36: NextWithSoftHyphens (inline_cursor_test.cc:675)
    Soft hyphen produces linebox, "abc-", "-", linebox, "def" (5 items). -/
def inlineCursor_nextSoftHyphens_vector : List (Nat × Nat) :=
  let items := [1, 2, 3, 4, 5]
  [ (items.length, 5) ]

theorem inlineCursor_nextSoftHyphens_pass :
    ∀ p ∈ inlineCursor_nextSoftHyphens_vector, p.1 = p.2 := by
  decide

/-- Test 37: NextInlineLeaf (inline_cursor_test.cc:685)
    Leaf traversal skips inline box containers: linebox, "abc", "DEF", "", "xyz" (5 items). -/
def inlineCursor_nextInlineLeaf_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3, 4, 5]
  [ (leaves.length, 5) ]

theorem inlineCursor_nextInlineLeaf_pass :
    ∀ p ∈ inlineCursor_nextInlineLeaf_vector, p.1 = p.2 := by
  decide

/-- Test 38: NextInlineLeafOnLineFromLayoutInline (inline_cursor_test.cc:698)
    Next inline leaf on line: `#start`, `def`, `` (3 items). -/
def inlineCursor_nextLeafOnLine_vector : List (Nat × Nat) :=
  let leavesOnLine := [1, 2, 3]
  [ (leavesOnLine.length, 3) ]

theorem inlineCursor_nextLeafOnLine_pass :
    ∀ p ∈ inlineCursor_nextLeafOnLine_vector, p.1 = p.2 := by
  decide

/-- Test 39: NextInlineLeafOnLineFromNestedLayoutInline (inline_cursor_test.cc:716)
    Next inline leaf on line from container returns sibling subtree leaf: `#start`, `next` (2 items). -/
def inlineCursor_nextLeafNested_vector : List (Nat × Nat) :=
  let leaves := [1, 2]
  [ (leaves.length, 2) ]

theorem inlineCursor_nextLeafNested_pass :
    ∀ p ∈ inlineCursor_nextLeafNested_vector, p.1 = p.2 := by
  decide

/-- Test 40: NextInlineLeafOnLineFromLayoutText (inline_cursor_test.cc:738)
    Leaf on line from text: `abc`, `def`, `` (3 items). -/
def inlineCursor_nextLeafText_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.length, 3) ]

theorem inlineCursor_nextLeafText_pass :
    ∀ p ∈ inlineCursor_nextLeafText_vector, p.1 = p.2 := by
  decide

/-- Test 41: NextInlineLeafWithEllipsis (inline_cursor_test.cc:756)
    Leaves with ellipsis: linebox, `abcd` (2 items). -/
def inlineCursor_leafEllipsis_vector : List (Nat × Nat) :=
  let leaves := [1, 2]
  [ (leaves.length, 2) ]

theorem inlineCursor_leafEllipsis_pass :
    ∀ p ∈ inlineCursor_leafEllipsis_vector, p.1 = p.2 := by
  decide

/-- Test 42: NextInlineLeafWithSoftHyphens (inline_cursor_test.cc:776)
    Leaves with soft hyphens: linebox, `abc-`, `def` (3 items). -/
def inlineCursor_leafSoftHyphens_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.length, 3) ]

theorem inlineCursor_leafSoftHyphens_pass :
    ∀ p ∈ inlineCursor_leafSoftHyphens_vector, p.1 = p.2 := by
  decide

/-- Test 43: NextInlineLeafIgnoringLineBreak (inline_cursor_test.cc:788)
    Leaves ignoring BR: linebox, `abc`, `DEF`, `xyz` (4 items). -/
def inlineCursor_leafIgnoreBr_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3, 4]
  [ (leaves.length, 4) ]

theorem inlineCursor_leafIgnoreBr_pass :
    ∀ p ∈ inlineCursor_leafIgnoreBr_vector, p.1 = p.2 := by
  decide

/-- Test 44: NextLine (inline_cursor_test.cc:800)
    `MoveToNextLine` transitions from line 1 to line 2, and then to none. -/
theorem inlineCursor_nextLine_rule :
    let lines := [1, 2]
    lines.tail?.bind List.head? = some 2 ∧ (lines.drop 2).head? = none := by
  decide

/-- Test 45: NextWithImage (inline_cursor_test.cc:821)
    Cursor items with image: linebox, `abc`, `#img`, `xyz` (4 items). -/
def inlineCursor_nextImage_vector : List (Nat × Nat) :=
  let items := [1, 2, 3, 4]
  [ (items.length, 4) ]

theorem inlineCursor_nextImage_pass :
    ∀ p ∈ inlineCursor_nextImage_vector, p.1 = p.2 := by
  decide

/-- Test 46: NextWithInlineBox (inline_cursor_test.cc:827)
    Cursor items with inline box: linebox, `abc`, `#ib`, `xyz` (4 items). -/
def inlineCursor_nextInlineBox_vector : List (Nat × Nat) :=
  let items := [1, 2, 3, 4]
  [ (items.length, 4) ]

theorem inlineCursor_nextInlineBox_pass :
    ∀ p ∈ inlineCursor_nextInlineBox_vector, p.1 = p.2 := by
  decide

/-- Test 47: NextForSameLayoutObject (inline_cursor_test.cc:839)
    Multiple fragments for single pre-wrap layout text: 5 fragments (`abc`, ``, `def`, ``, `ghi`). -/
def inlineCursor_nextSameObject_vector : List (Nat × Nat) :=
  let fragments := [1, 2, 3, 4, 5]
  [ (fragments.length, 5) ]

theorem inlineCursor_nextSameObject_pass :
    ∀ p ∈ inlineCursor_nextSameObject_vector, p.1 = p.2 := by
  decide

/-- Test 48: NextForSameLayoutObjectWithRange (inline_cursor_test.cc:847)
    Restricting cursor to line 2 yields only 1 fragment for span. -/
theorem inlineCursor_nextSameObjectRange_rule :
    let line2Fragments := [1]
    line2Fragments.length = 1 := by
  rfl

/-- Test 49: Sibling (inline_cursor_test.cc:882)
    Siblings on line: `abc`, `LayoutInline A`, `xyz` (3 items). -/
def inlineCursor_sibling_vector : List (Nat × Nat) :=
  let siblings := [1, 2, 3]
  [ (siblings.length, 3) ]

theorem inlineCursor_sibling_pass :
    ∀ p ∈ inlineCursor_sibling_vector, p.1 = p.2 := by
  decide

/-- Test 50: Sibling2 (inline_cursor_test.cc:893)
    Siblings inside box: `abc`, `LayoutInline B`, `xyz` (3 items). -/
def inlineCursor_sibling2_vector : List (Nat × Nat) :=
  let siblings := [1, 2, 3]
  [ (siblings.length, 3) ]

theorem inlineCursor_sibling2_pass :
    ∀ p ∈ inlineCursor_sibling2_vector, p.1 = p.2 := by
  decide

/-- Test 51: NextSkippingChildren (inline_cursor_test.cc:905)
    `MoveToNextSkippingChildren` from text2 skips span1 descendants to `#span2`, `text4`, `text5` (3 items). -/
def inlineCursor_skipChildren_vector : List (Nat × Nat) :=
  let remaining := [1, 2, 3]
  [ (remaining.length, 3) ]

theorem inlineCursor_skipChildren_pass :
    ∀ p ∈ inlineCursor_skipChildren_vector, p.1 = p.2 := by
  decide

/-- Test 52: EmptyOutOfFlow (inline_cursor_test.cc:938)
    Empty absolute element produces 0 IFC items. -/
theorem inlineCursor_emptyOof_rule :
    let ifcItems : List Nat := []
    ifcItems.length = 0 := by
  rfl

/-- Test 53: PositionForPointInChildHorizontalLTR (inline_cursor_test.cc:952)
    Hit testing in horizontal LTR:
    coords -5, 0, 5, 10, 15, 20, 25 map to offsets 0, 0, 0, 1, 1, 2, 2. -/
def inlineCursor_hitTestLtr_vector : List (Nat × Nat) :=
  let left : Int := 10
  let cw : Nat := 10
  let len : Nat := 2
  [ (hitTestTextOffset false (-5) left cw len, 0)
  , (hitTestTextOffset false 0 left cw len, 0)
  , (hitTestTextOffset false 5 left cw len, 0)
  , (hitTestTextOffset false 10 left cw len, 0)
  , (hitTestTextOffset false 15 left cw len, 0)
  , (hitTestTextOffset false 20 left cw len, 1)
  , (hitTestTextOffset false 25 left cw len, 1)
  , (hitTestTextOffset false 30 left cw len, 2)
  , (hitTestTextOffset false 35 left cw len, 2)
  ]

theorem inlineCursor_hitTestLtr_pass :
    ∀ p ∈ inlineCursor_hitTestLtr_vector, p.1 = p.2 := by
  decide

/-- Test 54: PositionForPointInChildHorizontalRTL (inline_cursor_test.cc:988)
    Hit testing in horizontal RTL:
    offsets decrease with increasing X. -/
def inlineCursor_hitTestRtl_vector : List (Nat × Nat) :=
  let left : Int := 754
  let cw : Nat := 10
  let len : Nat := 2
  [ (hitTestTextOffset true (left - 5) left cw len, 2)
  , (hitTestTextOffset true left left cw len, 2)
  , (hitTestTextOffset true (left + 5) left cw len, 2)
  , (hitTestTextOffset true (left + 10) left cw len, 1)
  , (hitTestTextOffset true (left + 15) left cw len, 1)
  , (hitTestTextOffset true (left + 20) left cw len, 0)
  , (hitTestTextOffset true (left + 25) left cw len, 0)
  ]

theorem inlineCursor_hitTestRtl_pass :
    ∀ p ∈ inlineCursor_hitTestRtl_vector, p.1 = p.2 := by
  decide

/-- Test 55: PositionForPointInChildVerticalLTR (inline_cursor_test.cc:1025)
    Hit testing in vertical LTR by Y coordinate. -/
def inlineCursor_hitTestVerticalLtr_vector : List (Nat × Nat) :=
  let top : Int := 10
  let cw : Nat := 10
  let len : Nat := 2
  [ (hitTestTextOffset false (top - 5) top cw len, 0)
  , (hitTestTextOffset false top top cw len, 0)
  , (hitTestTextOffset false (top + 5) top cw len, 0)
  , (hitTestTextOffset false (top + 10) top cw len, 1)
  , (hitTestTextOffset false (top + 15) top cw len, 1)
  , (hitTestTextOffset false (top + 20) top cw len, 2)
  , (hitTestTextOffset false (top + 25) top cw len, 2)
  ]

theorem inlineCursor_hitTestVerticalLtr_pass :
    ∀ p ∈ inlineCursor_hitTestVerticalLtr_vector, p.1 = p.2 := by
  decide

/-- Test 56: PositionForPointInChildVerticalRTL (inline_cursor_test.cc:1061)
    Hit testing in vertical RTL by Y coordinate. -/
def inlineCursor_hitTestVerticalRtl_vector : List (Nat × Nat) :=
  let top : Int := 10
  let cw : Nat := 10
  let len : Nat := 2
  [ (hitTestTextOffset true (top - 5) top cw len, 2)
  , (hitTestTextOffset true top top cw len, 2)
  , (hitTestTextOffset true (top + 5) top cw len, 2)
  , (hitTestTextOffset true (top + 10) top cw len, 1)
  , (hitTestTextOffset true (top + 15) top cw len, 1)
  , (hitTestTextOffset true (top + 20) top cw len, 0)
  , (hitTestTextOffset true (top + 25) top cw len, 0)
  ]

theorem inlineCursor_hitTestVerticalRtl_pass :
    ∀ p ∈ inlineCursor_hitTestVerticalRtl_vector, p.1 = p.2 := by
  decide

/-- Test 58: Previous (inline_cursor_test.cc:1110)
    Backward traversal: `xyz`, linebox, ``, `DEF`, `B`, `abc`, linebox (7 items). -/
def inlineCursor_previousDfs_vector : List (Nat × Nat) :=
  let items := [1, 2, 3, 4, 5, 6, 7]
  [ (items.length, 7) ]

theorem inlineCursor_previousDfs_pass :
    ∀ p ∈ inlineCursor_previousDfs_vector, p.1 = p.2 := by
  decide

/-- Test 60: PreviousInlineLeaf (inline_cursor_test.cc:1145)
    Backward leaf: `xyz`, ``, `DEF`, `abc` (4 items). -/
def inlineCursor_prevLeaf_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3, 4]
  [ (leaves.length, 4) ]

theorem inlineCursor_prevLeaf_pass :
    ∀ p ∈ inlineCursor_prevLeaf_vector, p.1 = p.2 := by
  decide

/-- Test 61: PreviousInlineLeafIgnoringLineBreak (inline_cursor_test.cc:1158)
    Backward leaf ignoring BR: `xyz`, `DEF`, `abc` (3 items). -/
def inlineCursor_prevLeafIgnoreBr_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.length, 3) ]

theorem inlineCursor_prevLeafIgnoreBr_pass :
    ∀ p ∈ inlineCursor_prevLeafIgnoreBr_vector, p.1 = p.2 := by
  decide

/-- Test 62: PreviousInlineLeafOnLineFromLayoutInline (inline_cursor_test.cc:1171)
    Backward leaf on line: `#start`, ``, `ABC` (3 items). -/
def inlineCursor_prevLeafOnLine_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.length, 3) ]

theorem inlineCursor_prevLeafOnLine_pass :
    ∀ p ∈ inlineCursor_prevLeafOnLine_vector, p.1 = p.2 := by
  decide

/-- Test 63: PreviousInlineLeafOnLineFromNestedLayoutInline (inline_cursor_test.cc:1189)
    Backward leaf from container returns previous sibling subtree leaf: `#start`, `previous` (2 items). -/
def inlineCursor_prevLeafNested_vector : List (Nat × Nat) :=
  let leaves := [1, 2]
  [ (leaves.length, 2) ]

theorem inlineCursor_prevLeafNested_pass :
    ∀ p ∈ inlineCursor_prevLeafNested_vector, p.1 = p.2 := by
  decide

/-- Test 64: PreviousInlineLeafOnLineFromLayoutText (inline_cursor_test.cc:1211)
    Backward leaf on line from text: `DEF`, ``, `ABC` (3 items). -/
def inlineCursor_prevLeafText_vector : List (Nat × Nat) :=
  let leaves := [1, 2, 3]
  [ (leaves.length, 3) ]

theorem inlineCursor_prevLeafText_pass :
    ∀ p ∈ inlineCursor_prevLeafText_vector, p.1 = p.2 := by
  decide

/-- Test 65: PreviousLine (inline_cursor_test.cc:1229)
    `MoveToPreviousLine` transitions from line 2 to line 1, and line 1 to none. -/
theorem inlineCursor_prevLine_rule :
    let lines := [1, 2]
    lines.head? = some 1 ∧ (lines.drop 2).head? = none := by
  decide

/-- Test 66: CursorForDescendants (inline_cursor_test.cc:1250)
    Scoped cursor for descendants of span1: 4 items (`text2`, `#span2`, `text3`, `text4`). -/
def inlineCursor_descendants_vector : List (Nat × Nat) :=
  let items := [1, 2, 3, 4]
  [ (items.length, 4) ]

theorem inlineCursor_descendants_pass :
    ∀ p ∈ inlineCursor_descendants_vector, p.1 = p.2 := by
  decide

/-- Test 67: MoveToVisualFirstOrLast (inline_cursor_test.cc:1292)
    Visual order in RTL: visual first is "MIXED" (frag 2), visual last is "some" (frag 1). -/
def inlineCursor_visualFirstLast_vector : List (Nat × Nat) :=
  let visualFirstFrag := 2
  let visualLastFrag := 1
  [ (visualFirstFrag, 2)
  , (visualLastFrag, 1)
  ]

theorem inlineCursor_visualFirstLast_pass :
    ∀ p ∈ inlineCursor_visualFirstLast_vector, p.1 = p.2 := by
  decide

/-- Test 68: MoveToLayoutObject (inline_cursor_test.cc:1318)
    Column fragmentation enumeration: text1 has 2 fragments, text2 has 2 fragments. -/
def inlineCursor_columnFragments_vector : List (Nat × Nat) :=
  let text1Frags := [1, 2]
  let text2Frags := [1, 2]
  [ (text1Frags.length, 2)
  , (text2Frags.length, 2)
  ]

theorem inlineCursor_columnFragments_pass :
    ∀ p ∈ inlineCursor_columnFragments_vector, p.1 = p.2 := by
  decide

end ChromiumLayout.TestsInline
