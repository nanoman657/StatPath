/-
  BlockNode.lean: layout-input-node tree facts, written from block_node_test.cc,
  block_child_iterator_test.cc and layout_block_flow_test.cc. Owned by the block lane.
  The models are as small as the tests: they pin exactly the cases the tests state.
-/
namespace ChromiumLayout
namespace BlockNode

/-- Positioning scheme (`position`), needed by `IsFloatingForOutOfFlowFloating` at
    block_node_test.cc:16. -/
inductive Position where
  | static | relative | absolute | fixed
  deriving DecidableEq

/-- `float` value (block_node_test.cc:16). -/
inductive Float where
  | none | left | right
  deriving DecidableEq

/-- `BlockNode::IsFloating()`: a floated box is a float only if it is not absolutely or fixed
    positioned (block_node_test.cc:16 `IsFloatingForOutOfFlowFloating`: `float:left; position:absolute` is not
    floating). -/
def isFloating (f : Float) (p : Position) : Bool :=
  f != .none && p != .absolute && p != .fixed

/-- Kind of a DOM child as the block_node_test.cc fixtures write them: text/inline-level content,
    in-flow block, float, out-of-flow positioned. (Whitespace-only text between blocks does not
    generate a child, as in `ChildFloatWithSpaces`.) -/
inductive Item where
  | text | block | float | oof
  deriving DecidableEq

/-- Kind of a `LayoutInputNode` child. -/
inductive NodeKind where
  | inline | block
  deriving DecidableEq

/-- `BlockNode::FirstChild()/NextSibling()` sequence (block_node_test.cc: `ChildInlineAndBlock`,
    `ChildBlockAndInline`, `ChildFloatBeforeBlock`, `ChildFloatBeforeInline`,
    `ChildFloatAfterInline`, `ChildFloatOnly`, `ChildFloatWithSpaces`, `ChildOofBeforeInline`,
    `ChildOofAfterInline`): inline content with no block sibling is one inline node and floats /
    out-of-flow boxes are not children of it; otherwise every block or float is a block node and a
    maximal run of text is one anonymous block node. Out-of-flow boxes in block mode are not
    produced as children (no test covers that case). -/
def childNodes (items : List Item) : List NodeKind :=
  let hasText := items.any (· == Item.text)
  let hasBlock := items.any (· == Item.block)
  if hasText && !hasBlock then [NodeKind.inline]
  else
    (items.foldl
      (fun (acc : List NodeKind × Bool) it =>
        match it with
        | Item.text => if acc.2 then acc else (acc.1 ++ [NodeKind.block], true)
        | Item.block => (acc.1 ++ [NodeKind.block], false)
        | Item.float => (acc.1 ++ [NodeKind.block], false)
        | Item.oof => acc)
      ([], false)).1

/-- A multicol container needs an anonymous block wrapper exactly when all its children are
    inline-level (layout_block_flow_test.cc:109 `AnonymousContainer`, :165 `NoAnonymousContainer`);
    with `columns:auto` there is no wrapper. -/
def needsAnonymousWrapper (multicol : Bool) (items : List Item) : Bool :=
  multicol && items.all (· == Item.text)

/-- `LayoutObject::IsInsideMulticol()` (layout_block_flow_test.cc:38 `IsInsideMulticol`): some
    proper ancestor is a multicol container. `ancestorsColumns` lists, for the proper ancestors,
    whether each has `columns` other than `auto`. -/
def isInsideMulticol (ancestorsColumns : List Bool) : Bool := ancestorsColumns.any id

/-- Entry of `BlockChildIterator`: a child (by sibling index) and whether it comes with a break
    token (block_child_iterator_test.cc). -/
structure Entry where
  child : Nat
  hasToken : Bool
  deriving DecidableEq

/-- `BlockChildIterator::NextChild` sequence over children `children` (strictly increasing sibling
    indices), child break tokens `toks` (strictly increasing) and the parent token's
    `HasSeenAllChildren` flag (block_child_iterator_test.cc: `NullFirstChild`, `NoBreakToken`,
    `BreakTokens`, `SeenAllChildren`). A child with a token is returned with it; children before
    the last token without a token are finished and skipped; children after the last token are
    returned fresh unless all children were seen. -/
def iterate (children toks : List Nat) (seenAll : Bool) : List Entry :=
  match toks.getLast? with
  | none => if seenAll then [] else children.map (fun c => ⟨c, false⟩)
  | some last =>
      children.filterMap (fun c =>
        if toks.contains c then some ⟨c, true⟩
        else if last < c && !seenAll then some ⟨c, false⟩ else none)

/-- `BlockChildIterator` resolves its next child lazily from the live sibling list, so a sibling
    removed during iteration is skipped (block_child_iterator_test.cc:177
    `DeleteNodeWhileIteration`). -/
def nextChild (live : List Nat) (prev : Option Nat) : Option Nat :=
  match prev with
  | none => live.head?
  | some p => live.find? (fun c => p < c)

/-- Every entry the iterator returns is one of the children (block_child_iterator_test.cc). -/
theorem iterate_mem (children toks : List Nat) (seenAll : Bool) :
    ∀ e ∈ iterate children toks seenAll, e.child ∈ children := by
  intro e he
  unfold iterate at he
  split at he
  · split at he
    · simp at he
    · simp only [List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      exact hc
  · rename_i last _
    simp only [List.mem_filterMap] at he
    obtain ⟨c, hc, h⟩ := he
    split at h
    · cases h; exact hc
    · split at h
      · cases h; exact hc
      · cases h

end BlockNode
end ChromiumLayout
