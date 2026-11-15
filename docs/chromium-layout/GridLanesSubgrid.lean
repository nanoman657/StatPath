/-
  GridLanesSubgrid.lean: Subgrid axis resolution, orthogonal writing-mode mapping,
  nested subgrid item collection, auto-placed propagation, RTL span translation,
  virtual item span expansion, and placement cache invalidation for `display: grid-lanes`.
  Spec: CSS Grid Layout Module Level 2 §2.1–§2.4 (Subgrids) and
  CSS Grid Layout Module Level 3 (Grid Lanes / Masonry layout).
-/

namespace ChromiumLayout
namespace GridLanesSubgrid

/-- Grid track axis (`columns` or `rows`). CSS Grid 2 §2.1. -/
inductive Axis where
  | cols
  | rows
  deriving DecidableEq, Repr

/-- `grid-lanes-direction` value (`column`, `row`, or `normal`). CSS Grid 3. -/
inductive Dir where
  | col
  | row
  | normal
  deriving DecidableEq, Repr

/-- Resolve the grid-lanes track sizing axis from `grid-lanes-direction` and whether
    explicit column/row templates are defined (`normal` resolves to `rows` iff
    `grid-template-rows` is set and `grid-template-columns` is `none`).
    Required by `GridLanesDirectionChangeMarksPlacementDirty`,
    `ResolvedGridAxisFlipMarksPlacementDirty`. -/
def resolveAxis (d : Dir) (hasCols hasRows : Bool) : Axis :=
  match d with
  | .col => .cols
  | .row => .rows
  | .normal => if !hasCols && hasRows then .rows else .cols

/-- Whether changing `grid-lanes-direction`, template definitions, or `grid-lanes-pack`
    marks cached grid-lanes placement dirty.
    Required by `GridLanesDirectionChangeMarksPlacementDirty`,
    `GridLanesPackChangeMarksPlacementDirty`, `ResolvedGridAxisFlipMarksPlacementDirty`. -/
def placementDirty (d1 d2 : Dir) (c1 r1 c2 r2 : Bool) (pack1 pack2 : Bool) : Bool :=
  d1 != d2 || resolveAxis d1 c1 r1 != resolveAxis d2 c2 r2 || pack1 != pack2

/-- Whether a subgrid child subgrids the parent's column axis after accounting for
    writing-mode orthogonality (`parallel`) and, if the child is itself `display: grid-lanes`,
    its own track sizing axis (`ownAxis`). CSS Grid 2 §2.1, CSS Writing Modes 4 §7.1.
    Required by `AppendSubgriddedItemsColumns`, `OrthogonalAppendSubgriddedItemsColumns`,
    `GridLanesSubgridIgnoresNonGridAxis`, `OrthogonalGridLanesSubgridMapsGridAxis`. -/
def hasSubCols (subCols subRows parallel : Bool) (ownAxis : Option Axis := none) : Bool :=
  let effCols := subCols && ownAxis != some .rows
  let effRows := subRows && ownAxis != some .cols
  if parallel then effCols else effRows

/-- Whether a subgrid child subgrids the parent's row axis after accounting for
    writing-mode orthogonality (`parallel`) and `ownAxis`. CSS Grid 2 §2.1.
    Required by `AppendSubgriddedItemsRows`, `OrthogonalAppendSubgriddedItemsRows`,
    `AppendRowSubgriddedGridLanesItems`. -/
def hasSubRows (subCols subRows parallel : Bool) (ownAxis : Option Axis := none) : Bool :=
  let effCols := subCols && ownAxis != some .rows
  let effRows := subRows && ownAxis != some .cols
  if parallel then effRows else effCols

/-- `(mustConsiderCols, mustConsiderRows, isSubgrid)` for a child of a `grid-lanes`
    container whose track sizing axis is `parentAxis`. Only the parent's active
    `grid-lanes` axis participates in track sizing.
    Required by `AppendSubgriddedItemsColumns`, `AppendSubgriddedItemsRows`,
    `SubgridRowsIgnoredInColumnGridLanes`, `SubgridColumnsIgnoredInRowGridLanes`,
    `OrthogonalAppendSubgriddedItemsColumns`, `OrthogonalAppendSubgriddedItemsRows`,
    `OrthogonalSubgridColumnsIgnoredInColumnGridLanes`,
    `OrthogonalSubgridRowsIgnoredInRowGridLanes`. -/
def subgridFlags (parentAxis : Axis) (subCols subRows parallel : Bool)
    (ownAxis : Option Axis := none) : Bool × Bool × Bool :=
  let sc := hasSubCols subCols subRows parallel ownAxis
  let sr := hasSubRows subCols subRows parallel ownAxis
  let c := parentAxis == .cols && sc
  let r := parentAxis == .rows && sr
  (c, r, c || r)

/-- Counts `(includeSubgriddedCount, subgriddedToParentCount)` for a `grid-lanes`
    container with `directCount` direct items, where one child is a subgrid with
    `subChildCount` items and flags `(subCols, subRows, parallel, ownAxis)`. -/
def singleSubgridCounts (parentAxis : Axis) (directCount subChildCount : Nat)
    (subCols subRows parallel : Bool) (ownAxis : Option Axis := none) : Nat × Nat :=
  let (_, _, active) := subgridFlags parentAxis subCols subRows parallel ownAxis
  let sub := if active then subChildCount else 0
  (directCount + sub, sub)

/-- A node in a nested grid/subgrid tree: `(id, subgridsParentCols, subgridsParentRows, children)`. -/
inductive Node where
  | mk (id : Nat) (subCols subRows : Bool) (children : List Node)
  deriving Repr

/-- Direct child IDs of a node. -/
def directIds : Node → List Nat
  | .mk _ _ _ cs => cs.map fun | .mk i _ _ _ => i

/-- Collect descendant item IDs subgridded to an ancestor that owns standalone tracks on
    `(ownsCols, ownsRows)` (breadth-first across nesting levels). CSS Grid 2 §2.4.
    Required by `IncludeSubgriddedItemsIncludesNestedDescendants`,
    `ItemsSubgriddedToParentExcludesDirectItems`. -/
def collectSubgridded (fuel : Nat) (ownsCols ownsRows : Bool) (cs : List Node) : List Nat :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    let activeChildren := cs.filter fun
      | .mk _ sc sr _ => (ownsCols && sc) || (ownsRows && sr)
    let levelIds := activeChildren.flatMap directIds
    let nextNodes := activeChildren.flatMap fun
      | .mk _ sc sr gcs =>
        gcs.map fun
          | .mk i gsc gsr ggcs => .mk i (sc && gsc) (sr && gsr) ggcs
    levelIds ++ collectSubgridded fuel' ownsCols ownsRows nextNodes

/-- `(directIds, includeSubgriddedIds, subgriddedToParentIds)` for a grid/subgrid node
    that establishes standalone tracks on `(ownsCols, ownsRows)`. -/
def nodeItemLists (ownsCols ownsRows : Bool) (n : Node) : List Nat × List Nat × List Nat :=
  match n with
  | .mk _ _ _ cs =>
    let d := directIds n
    let s := collectSubgridded (cs.length + 2) ownsCols ownsRows cs
    (d, d ++ s, s)

/-- Number of subgrid nodes in a sizing tree (1 for root + active subgrid descendants).
    Required by `AppendColumnSubgriddedGridLanesItems`, `AppendRowSubgriddedGridLanesItems`,
    `GridLanesSubgridIgnoresNonGridAxis`, `OrthogonalGridLanesSubgridMapsGridAxis`,
    `BuildsNestedGridLanesSubgrids`. -/
def sizingTreeSize (parentAxis : Axis) (levels : List (Bool × Bool × Bool × Option Axis)) : Nat :=
  let rec go : List (Bool × Bool × Bool × Option Axis) → Nat
    | [] => 1
    | (sc, sr, par, own) :: rest =>
      if (subgridFlags parentAxis sc sr par own).2.2 then 1 + go rest else 1
  go levels

/-- Whether an item inside a subgrid is marked `is_auto_placed` in the root `grid-lanes`
    sizing tree: if the parent subgrid is auto-placed, all its descendants are auto-placed
    because the subgrid's own root position is unresolved; if the parent subgrid has a
    definite root position, its placement algorithm resolves all its direct children to
    definite spans unless the child is itself an unplaced subgrid before placement.
    Required by `AutoPlacedSubgriddedItemsAreAutoPlaced`,
    `DefiniteSubgridChildrenAreExplicitlyPlaced`,
    `NestedSubgridInAutoPlacedSubgridIsAutoPlaced`,
    `ExplicitlyPlacedNestedSubgridInAutoPlacedSubgridIsAutoPlaced`,
    `NestedSubgridUnderExplicitOuterSubgridIsNotAutoPlaced`,
    `DeepNestedAutoPlacedSubgridsAreAllAutoPlaced`,
    `AllChildrenOfAutoPlacedSubgridAreAutoPlaced`. -/
def childAutoPlaced (parentAutoPlaced : Bool) (resolvedBySubgridPlacement : Bool) : Bool :=
  parentAutoPlaced || !resolvedBySubgridPlacement

/-- Propagate `is_auto_placed` down a chain of nested subgrids where the root subgrid has
    `rootAutoPlaced`. Once a subgrid is auto-placed, every nested subgrid inside it is
    also auto-placed regardless of whether its local placement is explicit. -/
def chainAutoPlaced (rootAutoPlaced : Bool) (depth : Nat) : List Bool :=
  List.replicate depth rootAutoPlaced

/-- Translate a child's 0-based local span `(cStart, cEnd)` into a definite parent subgrid
    spanning `[sStart, sEnd)`. When `oppositeDir` is true (e.g., RTL subgrid in LTR root),
    track positions are reversed within `[sStart, sEnd)`. CSS Grid 2 §2.3.
    Required by `OppositeDirectionSubgridReversesChildSpans`,
    `DefiniteSubgridsAtDifferentPositionsProduceSeparateVirtualItems`,
    `DefiniteSubgridAutoPlacedChildProducesDefiniteVirtualItem`. -/
def translateSpan (sStart sEnd cStart cEnd : Nat) (oppositeDir : Bool) : Nat × Nat :=
  if oppositeDir then (sEnd - cEnd, sEnd - cStart) else (sStart + cStart, sStart + cEnd)

/-- Expand items `(optStart, spanLen, maxContentContrib)` in a `numTracks`-track `grid-lanes`
    container into virtual items `(startLine, endLine, maxContentContrib)`, expanding
    auto-placed (`none`) items across every valid track start `0 .. numTracks - spanLen`
    and deduplicating spans by taking the maximum contribution. CSS Grid 3.
    Required by `DefiniteSubgridsAtDifferentPositionsProduceSeparateVirtualItems`,
    `AutoPlacedSubgridChildrenAreAutoPlacedForVirtualItems`,
    `DefiniteSubgridAutoPlacedChildProducesDefiniteVirtualItem`. -/
def expandVirtualItems (numTracks : Nat)
    (items : List (Option Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  let raw : List (Nat × Nat × Nat) := items.flatMap fun (optS, len, c) =>
    match optS with
    | some s => [(s, s + len, c)]
    | none => (List.range (numTracks + 1 - len)).map fun s => (s, s + len, c)
  raw.foldl (fun acc (s, e, c) =>
    if acc.any (fun (s', e', _) => s' == s && e' == e) then
      acc.map (fun (s', e', c') => if s' == s && e' == e then (s', e', max c' c) else (s', e', c'))
    else
      acc ++ [(s, e, c)]) []

/-- Law: translating a child span into a parent subgrid preserves the span length in both
    normal and opposite (RTL) directions (CSS Grid 2 §2.3). -/
theorem translateSpan_length (sStart sEnd cStart cEnd : Nat) (rev : Bool)
    (h1 : cStart ≤ cEnd) (h2 : cEnd ≤ sEnd) :
    (translateSpan sStart sEnd cStart cEnd rev).2 -
      (translateSpan sStart sEnd cStart cEnd rev).1 = cEnd - cStart := by
  cases rev <;> simp [translateSpan] <;> omega

/-- Law: every item inside an auto-placed subgrid is marked auto-placed regardless of its
    local placement within the subgrid (CSS Grid 2 §2.4, CSS Grid 3). -/
theorem childAutoPlaced_of_parentAuto (resolved : Bool) :
    childAutoPlaced true resolved = true := by
  rfl

/-- Law: an orthogonal writing mode swaps the subgridded column and row axes relative to
    the parent grid (CSS Grid 2 §2.1, CSS Writing Modes 4 §7.1). -/
theorem orthogonal_swaps_axes (subC subR : Bool) :
    hasSubCols subC subR false none = hasSubRows subC subR true none ∧
    hasSubRows subC subR false none = hasSubCols subC subR true none := by
  simp [hasSubCols, hasSubRows]

end GridLanesSubgrid
end ChromiumLayout
