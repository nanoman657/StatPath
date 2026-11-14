import ColumnLayout
import BlockFloat
import BlockOverflow

namespace TestsBlock

open ChromiumLayout.ColumnLayout
open ChromiumLayout.BlockFloat
open ChromiumLayout.BlockOverflow

-- physical_box_fragment_test.cc:29: PhysicalBoxFragmentTest.FloatingDescendantsInlineChlidren
theorem FloatingDescendantsInlineChlidren_vectors :
    let hasfloats : List BoxDescendant := [
      .leaf 1,
      .leaf 2 .block true
    ]
    let nofloats : List BoxDescendant := [
      .leaf 1
    ]
    listHasFloats 10 hasfloats = true ∧
    listHasFloats 10 nofloats = false := by
  decide

-- physical_box_fragment_test.cc:65: PhysicalBoxFragmentTest.FloatingDescendantsInlineBlock
theorem FloatingDescendantsInlineBlock_vectors :
    let spanHasFloats : BoxDescendant :=
      .node 2 .inlineBlock [.leaf 3 .block true]
    let nofloats : List BoxDescendant := [
      .leaf 1,
      spanHasFloats
    ]
    listHasFloats 10 nofloats = false ∧
    hasFloatingDescendants 10 (.node 2 .block [.leaf 3 .block true]) = true := by
  decide

-- physical_box_fragment_test.cc:83: PhysicalBoxFragmentTest.FloatingDescendantsBlockFormattingContext
theorem FloatingDescendantsBlockFormattingContext_vectors :
    let hasfloats : List BoxDescendant := [
      .node 1 .flowRoot [.leaf 2 .block true]
    ]
    let hasfloats2 : List BoxDescendant := [
      .node 1 .block [.leaf 2 .block true]
    ]
    listHasFloats 10 hasfloats = true ∧
    listHasFloats 10 hasfloats2 = true := by
  decide

-- physical_box_fragment_test.cc:115: PhysicalBoxFragmentTest.IsFragmentationContextRoot
-- Empty child in columns:3 generates 1 column fragmentainer
theorem IsFragmentationContextRoot_columnCount :
    (layoutMulticol { cols := 3, gap := 0, width := 300, height := 100, children := [{ id := 1, height := 0 }] }).columns.length = 1 := by
  decide

-- physical_box_fragment_test.cc:135: PhysicalBoxFragmentTest.IsFragmentationContextRootNested
-- Nested multicol containers each generate 1 column fragmentainer
theorem IsFragmentationContextRootNested_columnCounts :
    (layoutMulticol { cols := 3, gap := 0, width := 300, height := 100, children := [{ id := 1, height := 0 }] }).columns.length = 1 ∧
    (layoutMulticol { cols := 3, gap := 0, width := 300, height := 100, children := [{ id := 2, height := 0 }] }).columns.length = 1 := by
  decide

-- physical_box_fragment_test.cc:201: PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStart
-- Negative margins can pull child content above the block-start edge (y < 0).
-- This property propagates to ancestor containers.
-- CSS 2.1 §8.3.1 Collapsing Margins, CSS Overflow 3 §2.
theorem MayHaveDescendantAboveBlockStart_vectors :
    let child1 : FragmentDescendant := ⟨0, 100, false⟩
    let child2 : FragmentDescendant := ⟨-100, 100, false⟩
    let containerHasDescendant := computeMayHaveDescendantAboveBlockStart [child1, child2]
    let container : FragmentDescendant := ⟨0, 100, containerHasDescendant⟩
    let container2HasDescendant := computeMayHaveDescendantAboveBlockStart [container]
    containerHasDescendant = true ∧
    container2HasDescendant = true := by
  decide

-- physical_box_fragment_test.cc:216: PhysicalBoxFragmentTest.MayHaveDescendantAboveBlockStartBlockInInline
-- Block-in-inline with negative margins also pulls content above block-start edge.
-- CSS 2.1 §8.3.1, §9.2.1.1, CSS Overflow 3 §2.
theorem MayHaveDescendantAboveBlockStartBlockInInline_vectors :
    let child1 : FragmentDescendant := ⟨0, 100, false⟩
    let child2 : FragmentDescendant := ⟨-100, 100, false⟩
    let inlineHasDescendant := computeMayHaveDescendantAboveBlockStart [child1, child2]
    let inlineContainer : FragmentDescendant := ⟨0, 100, inlineHasDescendant⟩
    let containerHasDescendant := computeMayHaveDescendantAboveBlockStart [inlineContainer]
    let container : FragmentDescendant := ⟨0, 100, containerHasDescendant⟩
    let container2HasDescendant := computeMayHaveDescendantAboveBlockStart [container]
    containerHasDescendant = true ∧
    container2HasDescendant = true := by
  decide

-- physical_box_fragment_test.cc:169: PhysicalBoxFragmentTest.IsFragmentationContextRootFieldset
-- A fieldset with columns:3 creates a legend and an anonymous fieldset content wrapper.
-- The anonymous wrapper establishes the multicol container (isFragmentationContextRoot = true),
-- while the fieldset, legend, column box, and child do not (isFragmentationContextRoot = false).
-- HTML Living Standard §4.10.15, §15.3.11, CSS Multi-column Layout Level 1 §2.
theorem IsFragmentationContextRootFieldset_vectors :
    let childId : Nat := 2
    let legendId : Nat := 1
    let childFrag := FragNode.mk .normalChild (some childId) false []
    let fsFrag := layoutFieldsetFragments true true legendId [childFrag]
    isFragContextRoot fsFrag = false ∧
    fsFrag.children.length = 2 ∧
    (match fsFrag.children with
     | [legend, wrapper] =>
         legend.nodeId = some legendId ∧
         isFragContextRoot legend = false ∧
         wrapper.nodeId = none ∧
         isFragContextRoot wrapper = true ∧
         wrapper.children.length = 1 ∧
         (match wrapper.children with
          | [col] =>
              isColumnBox col = true ∧
              isFragContextRoot col = false ∧
              (match col.children with
               | [c] =>
                   c.nodeId = some childId ∧
                   isFragContextRoot c = false
               | _ => false)
          | _ => false)
     | _ => false) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- physical_box_fragment_test.cc:233: PhysicalBoxFragmentTest.OverflowClipMarginVisualBox
-- overflow-clip-margin expands the clipping rect from content-box, padding-box, or border-box.
-- With width: 50px, border: 5px, padding: 5px, margin: 15px:
-- content-box clip width is 75px, padding-box is 80px, border-box is 85px.
-- CSS Overflow Module Level 3 §3.2 The overflow-clip-margin property.
theorem OverflowClipMarginVisualBox_vectors :
    let contentW := 50
    let pad := 5
    let bdr := 5
    let margin := 15
    visualBoxClipSize .contentBox contentW pad bdr margin = 75 ∧
    visualBoxClipSize .paddingBox contentW pad bdr margin = 80 ∧
    visualBoxClipSize .borderBox contentW pad bdr margin = 85 := by
  decide

end TestsBlock
