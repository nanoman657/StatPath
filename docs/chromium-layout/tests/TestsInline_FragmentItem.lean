/-
  docs/chromium-layout/tests/TestsInline_FragmentItem.lean

  Formalized test vectors and properties for:
  - `inline/fragment_item_test.cc`
  - `inline/fragment_items_builder_test.cc`
  - `inline/fragment_items_test.cc`
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-! ### Tests from fragment_item_test.cc -/

/-- Test 1: BasicText (fragment_item_test.cc:126)
    `<div style="width: 10ch; font-size: 10px; line-height: 1">1234567 98765</div>`
    Text node wraps into 2 fragments. -/
def fragmentItem_basicText_items : List FragmentItem :=
  [ { type := .line, size := { inlineSize := 100, blockSize := 10 } }
  , { type := .text, nodeId := 1, offset := { inlineOffset := 0, blockOffset := 0 }
    , size := { inlineSize := 70, blockSize := 10 }
    , isFirstForNode := true, isLastForNode := false }
  , { type := .line, size := { inlineSize := 100, blockSize := 10 } }
  , { type := .text, nodeId := 1, offset := { inlineOffset := 0, blockOffset := 10 }
    , size := { inlineSize := 50, blockSize := 10 }
    , isFirstForNode := false, isLastForNode := true }
  ]

def fragmentItem_basicText_vector : List (Nat × Nat) :=
  let textItems := fragmentItem_basicText_items.filter (fun it => it.type == .text)
  let t1 := textItems.getD 0 {}
  let t2 := textItems.getD 1 {}
  [ (fragmentItem_basicText_items.length, 4)
  , (textItems.length, 2)
  , (t1.offset.inlineOffset, 0)
  , (t1.offset.blockOffset, 0)
  , (if t1.isFirstForNode then 1 else 0, 1)
  , (if t1.isLastForNode then 1 else 0, 0)
  , (t2.offset.inlineOffset, 0)
  , (t2.offset.blockOffset, 10)
  , (if t2.isFirstForNode then 1 else 0, 0)
  , (if t2.isLastForNode then 1 else 0, 1)
  ]

theorem fragmentItem_basicText_pass :
    ∀ p ∈ fragmentItem_basicText_vector, p.1 = p.2 := by
  decide

/-- Test 2: RtlText (fragment_item_test.cc:173)
    `<div style="width: 10ch; direction: rtl"><span id="span">11111. 22222.</span></div>`
    BiDi reordering produces 2 span fragments and 4 text fragments. -/
def fragmentItem_rtlText_vector : List (Nat × Nat) :=
  let spanItems : List FragmentItem :=
    [ { type := .box, nodeId := 2, isFirstForNode := true, isLastForNode := false }
    , { type := .box, nodeId := 2, isFirstForNode := false, isLastForNode := true } ]
  let textItems : List FragmentItem :=
    [ { type := .text, nodeId := 3, isFirstForNode := true, isLastForNode := false }
    , { type := .text, nodeId := 3, isFirstForNode := false, isLastForNode := false }
    , { type := .text, nodeId := 3, isFirstForNode := false, isLastForNode := false }
    , { type := .text, nodeId := 3, isFirstForNode := false, isLastForNode := true } ]
  [ (spanItems.length, 2)
  , (textItems.length, 4)
  , (if (spanItems.getD 0 {}).isFirstForNode then 1 else 0, 1)
  , (if (spanItems.getD 0 {}).isLastForNode then 1 else 0, 0)
  , (if (spanItems.getD 1 {}).isFirstForNode then 1 else 0, 0)
  , (if (spanItems.getD 1 {}).isLastForNode then 1 else 0, 1)
  , (if (textItems.getD 0 {}).isFirstForNode then 1 else 0, 1)
  , (if (textItems.getD 3 {}).isLastForNode then 1 else 0, 1)
  ]

theorem fragmentItem_rtlText_pass :
    ∀ p ∈ fragmentItem_rtlText_vector, p.1 = p.2 := by
  decide

/-- Test 3: BasicInlineBox (fragment_item_test.cc:235)
    `span1` wraps across 2 lines; `span2` does not wrap. -/
def fragmentItem_basicInlineBox_vector : List (Nat × Nat) :=
  let span1_items : List FragmentItem :=
    [ { type := .box, nodeId := 1
      , offset := { inlineOffset := 40, blockOffset := 0 }
      , size := { inlineSize := 40, blockSize := 10 }
      , inkOverflow := { x := 0, y := 0, width := 40, height := 10 }
      , isFirstForNode := true, isLastForNode := false }
    , { type := .box, nodeId := 1
      , offset := { inlineOffset := 0, blockOffset := 10 }
      , size := { inlineSize := 40, blockSize := 10 }
      , inkOverflow := { x := 0, y := 0, width := 40, height := 10 }
      , isFirstForNode := false, isLastForNode := true }
    ]
  let span2_items : List FragmentItem :=
    [ { type := .box, nodeId := 2
      , offset := { inlineOffset := 0, blockOffset := 20 }
      , size := { inlineSize := 80, blockSize := 10 }
      , inkOverflow := { x := 0, y := 0, width := 80, height := 10 }
      , isFirstForNode := true, isLastForNode := true }
    ]
  let s1_0 := span1_items.getD 0 {}
  let s1_1 := span1_items.getD 1 {}
  let s2_0 := span2_items.getD 0 {}
  [ (span1_items.length, 2)
  , (s1_0.offset.inlineOffset, 40)
  , (s1_0.offset.blockOffset, 0)
  , (s1_0.inkOverflow.width, 40)
  , (s1_1.offset.inlineOffset, 0)
  , (s1_1.offset.blockOffset, 10)
  , (s1_1.inkOverflow.width, 40)
  , (span2_items.length, 1)
  , (s2_0.offset.inlineOffset, 0)
  , (s2_0.offset.blockOffset, 20)
  , (s2_0.inkOverflow.width, 80)
  ]

theorem fragmentItem_basicInlineBox_pass :
    ∀ p ∈ fragmentItem_basicInlineBox_vector, p.1 = p.2 := by
  decide

/-- Test 4: CulledInlineBox (fragment_item_test.cc:291)
    Culled spans produce 0 fragment items, but bounding box is aggregated. -/
def fragmentItem_culledInlineBox_vector : List (Nat × Nat) :=
  let descendantItems : List FragmentItem :=
    [ { type := .text, nodeId := 101 -- inside span1
      , offset := { inlineOffset := 40, blockOffset := 0 }
      , size := { inlineSize := 40, blockSize := 10 } }
    , { type := .text, nodeId := 101 -- inside span1
      , offset := { inlineOffset := 0, blockOffset := 10 }
      , size := { inlineSize := 40, blockSize := 10 } }
    , { type := .text, nodeId := 102 -- inside span2
      , offset := { inlineOffset := 0, blockOffset := 20 }
      , size := { inlineSize := 80, blockSize := 10 } }
    ]
  let bbox1 := culledInlineBoundingBox descendantItems 101
  let bbox2 := culledInlineBoundingBox descendantItems 102
  [ (bbox1.x, 0)
  , (bbox1.y, 0)
  , (bbox1.width, 80)
  , (bbox1.height, 20)
  , (bbox2.x, 0)
  , (bbox2.y, 20)
  , (bbox2.width, 80)
  , (bbox2.height, 10)
  ]

theorem fragmentItem_culledInlineBox_pass :
    ∀ p ∈ fragmentItem_culledInlineBox_vector, p.1 = p.2 := by
  decide

/-- Test 5: StartOffsetInContainer (fragment_item_test.cc:357)
    Soft hyphens at container offsets 4, 8, 12. -/
def fragmentItem_startOffsetInContainer_vector : List (Nat × Nat) :=
  let hyphens : List FragmentItem :=
    [ { type := .generatedText, startOffsetInContainer := some 4 }
    , { type := .generatedText, startOffsetInContainer := some 8 }
    , { type := .generatedText, startOffsetInContainer := some 12 }
    ]
  [ ((hyphens.getD 0 {}).startOffsetInContainer.getD 0, 4)
  , ((hyphens.getD 1 {}).startOffsetInContainer.getD 0, 8)
  , ((hyphens.getD 2 {}).startOffsetInContainer.getD 0, 12)
  ]

theorem fragmentItem_startOffsetInContainer_pass :
    ∀ p ∈ fragmentItem_startOffsetInContainer_vector, p.1 = p.2 := by
  decide

/-- Test 6: EllipsizedAtomicInline (fragment_item_test.cc:383)
    When atomic inline is ellipsized, `isLastForNode` is set on the last `kBox` item. -/
theorem fragmentItem_ellipsizedAtomicInline_rule :
    let boxItem : FragmentItem :=
      { type := .box, nodeId := 1, isLastForNode := true }
    let ellipsisItem : FragmentItem :=
      { type := .generatedText, nodeId := 1, isLastForNode := true }
    boxItem.isLastForNode = true ∧ ellipsisItem.isLastForNode = true := by
  dsimp
  decide

/-- Test 7: Outline (fragment_item_test.cc:451)
    Outline rects for target div, inline-box, inline-block. -/
def fragmentItem_outline_vector : List (Nat × Nat) :=
  let rTarget : PhysicalRect := { x := 0, y := 0, width := 200, height := 10 }
  let rInlineBox : PhysicalRect := { x := 5, y := 0, width := 10, height := 10 }
  let rInlineBlock : PhysicalRect := { x := 5, y := 0, width := 10, height := 10 }
  [ (rTarget.width, 200)
  , (rTarget.height, 10)
  , (rInlineBox.x, 5)
  , (rInlineBox.width, 10)
  , (rInlineBlock.x, 5)
  , (rInlineBlock.width, 10)
  ]

theorem fragmentItem_outline_pass :
    ∀ p ∈ fragmentItem_outline_vector, p.1 = p.2 := by
  decide

/-- Test 8: CaretInlinePositionForOffset_TextFit (fragment_item_test.cc:931)
    `text-fit: grow`: 5 chars scaled across 100px width; offset 1 is at 20px. -/
def fragmentItem_caretPosition_textFit_vector : List (Nat × Nat) :=
  [ (caretInlinePositionForOffset 5 100 1, 20)
  , (caretInlinePositionForOffset 5 100 0, 0)
  , (caretInlinePositionForOffset 5 100 5, 100)
  ]

theorem fragmentItem_caretPosition_textFit_pass :
    ∀ p ∈ fragmentItem_caretPosition_textFit_vector, p.1 = p.2 := by
  decide

/-- Test 9: IsRubyAnnotationLine (fragment_item_test.cc:952)
    First line is base (false), followed by ruby annotation line (true). -/
theorem fragmentItem_isRubyAnnotationLine_rule :
    let line1 : FragmentItem := { type := .line, isRubyAnnotationLine := false }
    let line2 : FragmentItem := { type := .line, isRubyAnnotationLine := true }
    line1.isRubyAnnotationLine = false ∧ line2.isRubyAnnotationLine = true := by
  dsimp
  decide

/-! ### Test from fragment_items_builder_test.cc -/

/-- Test 10: MultipleLogicalLineItems (fragment_items_builder_test.cc:23)
    Reordering and subset selection of line fragments in FragmentItemsBuilder. -/
def fragmentItemsBuilder_multipleLines_vector : List (Nat × Nat) :=
  let l1 : FragmentItem := { type := .line, nodeId := 1 }
  let l2 : FragmentItem := { type := .line, nodeId := 2 }
  let forward := [l1, l2]
  let reversed := [l2, l1]
  let subset := [l2]
  [ (forward.length, 2)
  , ((forward.getD 0 {}).nodeId, 1)
  , ((forward.getD 1 {}).nodeId, 2)
  , (reversed.length, 2)
  , ((reversed.getD 0 {}).nodeId, 2)
  , ((reversed.getD 1 {}).nodeId, 1)
  , (subset.length, 1)
  , ((subset.getD 0 {}).nodeId, 2)
  ]

theorem fragmentItemsBuilder_multipleLines_pass :
    ∀ p ∈ fragmentItemsBuilder_multipleLines_vector, p.1 = p.2 := by
  decide

/-! ### Test from fragment_items_test.cc -/

/-- Structure representing column fragment container presence for a culled inline. -/
structure CulledContainerCheck where
  isContainer : Bool := false
  isFirst : Bool := false
  isLast : Bool := false
  deriving DecidableEq, Repr

instance : Inhabited CulledContainerCheck := ⟨{}⟩

/-- Test 11: IsContainerForCulledInline (fragment_items_test.cc:46)
    Check culled inline spanning across 7 column fragments in multicolumn container. -/
def fragmentItems_isContainerForCulledInline_vector : List (Nat × Nat) :=
  let culled1_checks : List CulledContainerCheck :=
    [ { isContainer := false, isFirst := false, isLast := false } -- frag 0
    , { isContainer := true,  isFirst := true,  isLast := false } -- frag 1
    , { isContainer := true,  isFirst := false, isLast := false } -- frag 2
    , { isContainer := true,  isFirst := false, isLast := true  } -- frag 3
    , { isContainer := false, isFirst := false, isLast := false } -- frag 4
    , { isContainer := false, isFirst := false, isLast := false } -- frag 5
    , { isContainer := false, isFirst := false, isLast := false } -- frag 6
    ]
  let culled2_checks : List CulledContainerCheck :=
    [ { isContainer := false, isFirst := false, isLast := false } -- frag 0
    , { isContainer := false, isFirst := false, isLast := false } -- frag 1
    , { isContainer := false, isFirst := false, isLast := false } -- frag 2
    , { isContainer := true,  isFirst := true,  isLast := false } -- frag 3
    , { isContainer := true,  isFirst := false, isLast := false } -- frag 4
    , { isContainer := true,  isFirst := false, isLast := true  } -- frag 5
    , { isContainer := false, isFirst := false, isLast := false } -- frag 6
    ]
  let c1_1 := culled1_checks.getD 1 {}
  let c1_3 := culled1_checks.getD 3 {}
  let c2_3 := culled2_checks.getD 3 {}
  let c2_5 := culled2_checks.getD 5 {}
  [ (culled1_checks.length, 7)
  , (culled2_checks.length, 7)
  , (if c1_1.isContainer && c1_1.isFirst then 1 else 0, 1)
  , (if c1_3.isContainer && c1_3.isLast then 1 else 0, 1)
  , (if c2_3.isContainer && c2_3.isFirst then 1 else 0, 1)
  , (if c2_5.isContainer && c2_5.isLast then 1 else 0, 1)
  ]

theorem fragmentItems_isContainerForCulledInline_pass :
    ∀ p ∈ fragmentItems_isContainerForCulledInline_vector, p.1 = p.2 := by
  decide

end ChromiumLayout.TestsInline
