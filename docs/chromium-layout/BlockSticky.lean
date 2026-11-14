/-
  BlockSticky.lean: CSS Positioned Layout Level 3 sticky positioning algorithm,
  written from CSS Positioned Layout Module Level 3 §2.3 (Sticky positioning)
  and checked against layout_box_model_object_test.cc (StickyPositionNested,
  StickyPositionChildHasLargerTop, StickyPositionParentHasLargerTop,
  StickyPositionChildPushingOutsideParent, StickyPositionTripleNestedDiv).
  Owned by the block lane (Block*).
-/
import BlockOverflow

namespace ChromiumLayout
namespace BlockSticky

open BlockOverflow

/-- Specification of a sticky box constraint in the block axis. CSS Positioned Layout 3 §2.3. -/
structure StickyConstraint where
  top : Option Nat := none
  inFlowTop : Nat := 0
  height : Nat := 0
  cbHeight : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- 1D constraint interval (top, height). CSS Positioned Layout 3 §2.3. -/
structure StickyInterval where
  top : Nat := 0
  height : Nat := 0
  deriving Inhabited, DecidableEq, Repr

/-- Compute scroller-relative containing block interval from container geometry.
    CSS Positioned Layout Module Level 3 §2.3. -/
def containingBlockInterval (containerTop containerPadding containerBorder containerHeight : Nat)
    (isBorderBox : Bool) : StickyInterval :=
  let cbTop := containerTop + containerBorder + containerPadding
  let bpTotal := 2 * (containerBorder + containerPadding)
  let cbHeight := if isBorderBox then containerHeight - bpTotal else containerHeight
  ⟨cbTop, cbHeight⟩

/-- Compute scroller-relative sticky box interval.
    CSS Positioned Layout Module Level 3 §2.3. -/
def stickyBoxInterval (cbTop offsetInCb stickyHeight : Nat) : StickyInterval :=
  ⟨cbTop + offsetInCb, stickyHeight⟩

/-- Compute the sticky offset along the block axis given scroll offset and ancestor shifts.
    CSS Positioned Layout Module Level 3 §2.3:
    The sticky box shifts to remain at `top` relative to the scroll container,
    constrained to never push outside its containing block (`cbHeight - height`). -/
def computeStickyOffset (c : StickyConstraint) (scrollPos : Nat) (ancestorShift : Nat) : Nat :=
  match c.top with
  | none => 0
  | some topInset =>
      let targetPos := scrollPos + topInset
      let startPos := c.inFlowTop + ancestorShift
      if targetPos ≤ startPos then 0
      else
        let desiredShift := targetPos - startPos
        let maxShift := if c.cbHeight ≥ c.height then c.cbHeight - c.height else 0
        Nat.min desiredShift maxShift

/-- Law: Sticky offset is always bounded by the containing block headroom (cbHeight - height).
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_offset_le_max_shift (c : StickyConstraint) (scrollPos ancShift : Nat)
    (hcb : c.cbHeight ≥ c.height) :
    computeStickyOffset c scrollPos ancShift ≤ c.cbHeight - c.height := by
  dsimp [computeStickyOffset]
  split
  · omega
  · split
    · omega
    · apply Nat.min_le_right

/-- Law: If no top inset is specified, sticky offset is 0.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_offset_none (c : StickyConstraint) (h : c.top = none) (scrollPos ancShift : Nat) :
    computeStickyOffset c scrollPos ancShift = 0 := by
  dsimp [computeStickyOffset]
  rw [h]

/-- Law: If target position is at or before starting position, sticky offset is 0.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_offset_unscrolled (c : StickyConstraint) (topInset : Nat) (h : c.top = some topInset)
    (scrollPos ancShift : Nat) (hunscrolled : scrollPos + topInset ≤ c.inFlowTop + ancShift) :
    computeStickyOffset c scrollPos ancShift = 0 := by
  dsimp [computeStickyOffset]
  rw [h]
  have hcond : scrollPos + topInset ≤ c.inFlowTop + ancShift := hunscrolled
  simp [hcond]

/-- Law: Sticky box start is always at or after containing block start.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem sticky_box_ge_cb_top (cbTop off h : Nat) :
    (stickyBoxInterval cbTop off h).top ≥ cbTop := by
  dsimp [stickyBoxInterval]
  omega

/-- Law: Containing block top is monotonic with container top offset.
    CSS Positioned Layout Module Level 3 §2.3. -/
theorem cb_interval_top_monotone (t1 t2 p b h : Nat) (isBb : Bool) (ht : t1 ≤ t2) :
    (containingBlockInterval t1 p b h isBb).top ≤ (containingBlockInterval t2 p b h isBb).top := by
  dsimp [containingBlockInterval]
  omega

/-- Physical axes for sticky positioning and scroll container scrolling.
    CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3. -/
inductive PhysicalAxes where
  | none
  | horizontal
  | vertical
  | both
  deriving Inhabited, DecidableEq, Repr

/-- Consumed and pending axes for a sticky descendant in a scroll container fragment.
    CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3. -/
structure StickyAxes where
  consumed : PhysicalAxes := .none
  pending : PhysicalAxes := .none
  deriving Inhabited, DecidableEq, Repr

/-- Whether an axis set includes horizontal. -/
def hasHorizontal : PhysicalAxes → Bool
  | .horizontal | .both => true
  | _ => false

/-- Whether an axis set includes vertical. -/
def hasVertical : PhysicalAxes → Bool
  | .vertical | .both => true
  | _ => false

/-- Intersect two axis sets. -/
def intersectAxes (a b : PhysicalAxes) : PhysicalAxes :=
  match hasHorizontal a && hasHorizontal b, hasVertical a && hasVertical b with
  | true, true => .both
  | true, false => .horizontal
  | false, true => .vertical
  | false, false => .none

/-- Subtract axis set `sub` from `a` (axes in `a` not in `sub`). -/
def diffAxes (a sub : PhysicalAxes) : PhysicalAxes :=
  match hasHorizontal a && !hasHorizontal sub, hasVertical a && !hasVertical sub with
  | true, true => .both
  | true, false => .horizontal
  | false, true => .vertical
  | false, false => .none

/-- A sticky descendant element with its identifier and requested sticky axes.
    CSS Positioned Layout 3 §2.3. -/
structure StickyItem where
  id : String
  axes : PhysicalAxes
  deriving Inhabited, DecidableEq, Repr

/-- Entry in a scroll container's sticky descendants table. -/
structure StickyDescendantEntry where
  id : String
  axes : StickyAxes
  deriving Inhabited, DecidableEq, Repr

/-- Resolve sticky descendants for a scroll container given its scrolling axes.
    CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3. -/
def resolveStickyDescendants (scrollerAxes : PhysicalAxes) (items : List StickyItem) :
    List StickyDescendantEntry :=
  items.map (fun it =>
    let consumed := intersectAxes it.axes scrollerAxes
    let pending := diffAxes it.axes scrollerAxes
    ⟨it.id, ⟨consumed, pending⟩⟩)

/-- Propagate pending sticky descendants from an inner scroller to an outer scroller.
    CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3. -/
def propagatePendingSticky (innerEntries : List StickyDescendantEntry) : List StickyItem :=
  innerEntries.filterMap (fun e =>
    if e.axes.pending ≠ .none then
      some ⟨e.id, e.axes.pending⟩
    else
      none)

/-- Law: Subtracting an axis set from itself yields no pending axes.
    CSS Positioned Layout 3 §2.3. -/
theorem diff_axes_self (a : PhysicalAxes) : diffAxes a a = .none := by
  cases a <;> rfl

/-- Law: Intersecting with both axes is the identity.
    CSS Positioned Layout 3 §2.3. -/
theorem intersect_axes_both (a : PhysicalAxes) : intersectAxes a .both = a := by
  cases a <;> rfl

/-- Law: Intersecting physical axes is commutative.
    CSS Positioned Layout 3 §2.3. -/
theorem intersect_axes_comm (a b : PhysicalAxes) : intersectAxes a b = intersectAxes b a := by
  cases a <;> cases b <;> rfl

/-- Law: Resolving an empty list of sticky items yields no sticky descendants.
    CSS Positioned Layout 3 §2.3. -/
theorem resolve_sticky_descendants_empty (ax : PhysicalAxes) :
    resolveStickyDescendants ax [] = [] := rfl

/-- Law: Propagating an empty list of sticky entries yields no pending items.
    CSS Positioned Layout 3 §2.3. -/
theorem propagate_pending_sticky_empty :
    propagatePendingSticky [] = [] := rfl

/-- A node in the box tree with its sticky status and containing block hierarchy.
    CSS Positioned Layout 3 §2.3, CSS 2.1 §10.1. -/
structure StickyNode where
  id : String
  isSticky : Bool := false
  isAnchored : Bool := false
  isScroller : Bool := false
  containingBlockId : Option String := none
  parentId : Option String := none
  deriving Inhabited, DecidableEq, Repr

/-- Find nearest sticky-box shifting ancestor: the first anchored sticky ancestor in the parent chain
    before reaching the containing block or scroller.
    CSS Positioned Layout 3 §2.3. -/
def findNearestStickyBoxShiftingAncestor (nodes : List StickyNode) (startId : String) : Option String :=
  let rec walk (fuel : Nat) (curId : String) : Option String :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match nodes.find? (fun n => n.id == curId) with
      | none => none
      | some n =>
        match n.parentId with
        | none => none
        | some pid =>
          match nodes.find? (fun p => p.id == pid) with
          | none => none
          | some parentNode =>
            if parentNode.isScroller then none
            else if parentNode.isSticky && parentNode.isAnchored then some parentNode.id
            else walk fuel parentNode.id
  walk nodes.length startId

/-- Find nearest containing-block shifting ancestor: the first anchored sticky element in the ancestor
    chain starting from the containing block (inclusive) up to the ancestor scroll container (exclusive).
    CSS Positioned Layout 3 §2.3. -/
def findNearestContainingBlockShiftingAncestor (nodes : List StickyNode) (startId : String) : Option String :=
  let startNode := nodes.find? (fun n => n.id == startId)
  match startNode with
  | none => none
  | some node =>
    match node.containingBlockId with
    | none => none
    | some cbId =>
      let rec walk (fuel : Nat) (curId : String) : Option String :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match nodes.find? (fun n => n.id == curId) with
          | none => none
          | some n =>
            if n.isScroller then none
            else if n.isSticky && n.isAnchored then some n.id
            else
              match n.parentId with
              | none => none
              | some pid => walk fuel pid
      walk nodes.length cbId

/-- Law: Finding nearest sticky-box shifting ancestor in an empty node list yields none.
    CSS Positioned Layout 3 §2.3. -/
theorem find_nearest_sticky_box_empty (id : String) :
    findNearestStickyBoxShiftingAncestor [] id = none := rfl

/-- Law: Finding nearest containing-block shifting ancestor in an empty node list yields none.
    CSS Positioned Layout 3 §2.3. -/
theorem find_nearest_containing_block_empty (id : String) :
    findNearestContainingBlockShiftingAncestor [] id = none := rfl

/-- Whether an overflow value establishes a scroll container.
    CSS Overflow Module Level 3 §3 Scrollable Overflow. -/
def isScrollContainer (ox oy : OverflowValue) : Bool :=
  ox != .visible || oy != .visible

/-- Find the containing scroll container for a sticky box: the nearest ancestor establishing
    a scroll container, defaulting to the root view.
    CSS Positioned Layout Module Level 3 §2.3, CSS Overflow Module Level 3 §3. -/
def findContainingScrollContainer (ancestorOverflows : List (String × OverflowValue × OverflowValue))
    (rootId : String) : String :=
  match ancestorOverflows.find? (fun (_, ox, oy) => isScrollContainer ox oy) with
  | some (id, _, _) => id
  | none => rootId

/-- Law: If no ancestor establishes a scroll container, the containing scroll container is the root view.
    CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3. -/
theorem find_containing_scroll_container_empty (rootId : String) :
    findContainingScrollContainer [] rootId = rootId := rfl

/-- Law: Visible overflow on all ancestors falls through to the root view.
    CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3. -/
theorem find_containing_scroll_container_visible (ancId rootId : String) :
    findContainingScrollContainer [(ancId, .visible, .visible)] rootId = rootId := rfl

end BlockSticky
end ChromiumLayout
