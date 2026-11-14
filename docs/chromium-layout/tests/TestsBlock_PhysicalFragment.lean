import BlockFlow
import BlockSticky
import BlockAbsolute
import ColumnLayout

namespace ChromiumLayout
namespace TestsBlock

open BlockFlow BlockSticky BlockAbsolute ColumnLayout

-- physical_fragment_test.cc:84: StickyFragmentPropagationTest.StickyAxisEnabled
-- Single-axis scroll container (overflow-y: scroll; overflow-x: clip) consumes vertical sticky
-- and marks horizontal sticky pending. Ancestor scroller (overflow: scroll) consumes pending horizontal.
-- CSS Positioned Layout 3 §2.3, CSS Overflow 3 §3.
theorem StickyAxisEnabled_vectors :
    let innerItems : List StickyItem := [
      ⟨"sticky-y", .vertical⟩,
      ⟨"sticky-x", .horizontal⟩,
      ⟨"sticky-both", .both⟩
    ]
    let innerDescendants := resolveStickyDescendants .vertical innerItems
    let outerItems := propagatePendingSticky innerDescendants
    let outerDescendants := resolveStickyDescendants .both outerItems
    -- inner checks:
    innerDescendants.length = 3 ∧
    innerDescendants[0]!.axes = ⟨.vertical, .none⟩ ∧
    innerDescendants[1]!.axes = ⟨.none, .horizontal⟩ ∧
    innerDescendants[2]!.axes = ⟨.vertical, .horizontal⟩ ∧
    -- outer checks:
    outerDescendants.length = 2 ∧
    outerDescendants[0]!.axes = ⟨.horizontal, .none⟩ ∧
    outerDescendants[1]!.axes = ⟨.horizontal, .none⟩ := by
  decide

-- physical_fragment_test.cc:134: DumpFragmentTreeBasic
-- Input: HTML/body with <div id="block"></div>
def basicDoc : BF := htmlBody [{ id := 2 }]

theorem DumpFragmentTreeBasic_vectors :
    let f := layoutRoot 800 basicDoc
    let body := f.kid 0
    let block := body.kid 0
    body.w = 784 ∧ body.h = 0 ∧
    block.w = 784 ∧ block.h = 0 ∧
    f.relX body = 8 ∧ f.relY body = 8 ∧
    body.relX block = 0 ∧ body.relY block = 0 := by
  decide

-- physical_fragment_test.cc:149: DumpFragmentTreeWithAbspos
-- LayoutView is the containing block of an absolutely positioned descendant when no positioned ancestor exists.
-- CSS 2.1 §10.1, CSS Positioned Layout 3 §2.1, §2.2.
theorem DumpFragmentTreeWithAbspos_vectors :
    let bodyBf : BF := { id := 1, mt := 8, mb := 8, ml := .px 8, mr := .px 8, children := [] }
    let htmlBf : BF := { id := 0, newBfc := true, children := [bodyBf] }
    let htmlFrag := layoutRoot 800 htmlBf
    let bodyFrag := htmlFrag.kid 0
    let absCandidate : OofCandidate := { id := 2, w := 0, h := 0, left := none, top := none, staticX := 8, staticY := 8 }
    -- BODY is static, so candidate propagates up
    let (bodyResolved, p1) := resolveOofContainer .static bodyFrag [absCandidate]
    -- HTML is static, so candidate propagates up
    let (htmlResolved, p2) := resolveOofContainer .static { htmlFrag with kids := [bodyResolved] } p1
    -- Document root (LayoutView / ICB) consumes candidate
    let docFrag := layoutDocument 800 600 htmlResolved p2
    let docHtml := docFrag.kid 0
    let docAbs := docFrag.kid 1
    docFrag.w = 800 ∧ docFrag.h = 600 ∧
    docFrag.kids.length = 2 ∧
    docHtml.w = 800 ∧
    docFrag.relX docHtml = 0 ∧ docFrag.relY docHtml = 0 ∧
    let docBody := docHtml.kid 0
    docBody.w = 784 ∧ docBody.h = 0 ∧
    docHtml.relX docBody = 8 ∧ docHtml.relY docBody = 8 ∧
    docBody.kids.length = 0 ∧
    docAbs.id = 2 ∧ docAbs.w = 0 ∧ docAbs.h = 0 ∧
    docFrag.relX docAbs = 8 ∧ docFrag.relY docAbs = 8 := by
  decide

-- physical_fragment_test.cc:165: DumpFragmentTreeWithAbsposInRelpos
-- An NG object with position:relative is the containing block of an absolutely positioned descendant.
-- CSS 2.1 §10.1, CSS Positioned Layout 3 §2.1.
theorem DumpFragmentTreeWithAbsposInRelpos_vectors :
    let relBf : BF := { id := 2, children := [] }
    let bodyBf : BF := { id := 1, mt := 8, mb := 8, ml := .px 8, mr := .px 8, children := [relBf] }
    let htmlBf : BF := { id := 0, newBfc := true, children := [bodyBf] }
    let htmlFrag := layoutRoot 800 htmlBf
    let bodyFrag := htmlFrag.kid 0
    let relFrag := bodyFrag.kid 0
    let absCandidate : OofCandidate := { id := 3, w := 0, h := 0, left := some 10, top := some 20, staticX := 0, staticY := 0 }
    -- DIV#rel is relative, so it consumes candidate abs
    let (relResolved, pRel) := resolveOofContainer .relative relFrag [absCandidate]
    -- BODY is static, pRel is empty
    let (bodyResolved, pBody) := resolveOofContainer .static { bodyFrag with kids := [relResolved] } pRel
    -- HTML is static, pBody is empty
    let (htmlResolved, pHtml) := resolveOofContainer .static { htmlFrag with kids := [bodyResolved] } pBody
    -- Document root (LayoutView / ICB) has no remaining candidates
    let docFrag := layoutDocument 800 600 htmlResolved pHtml
    let docHtml := docFrag.kid 0
    let docBody := docHtml.kid 0
    let docRel := docBody.kid 0
    let docAbs := docRel.kid 0
    docFrag.w = 800 ∧ docFrag.h = 600 ∧
    docFrag.kids.length = 1 ∧
    docHtml.w = 800 ∧
    docFrag.relX docHtml = 0 ∧ docFrag.relY docHtml = 0 ∧
    docBody.w = 784 ∧ docBody.h = 0 ∧
    docHtml.relX docBody = 8 ∧ docHtml.relY docBody = 8 ∧
    docRel.id = 2 ∧ docRel.w = 784 ∧ docRel.h = 0 ∧
    docBody.relX docRel = 0 ∧ docBody.relY docRel = 0 ∧
    docRel.kids.length = 1 ∧
    docAbs.id = 3 ∧ docAbs.w = 0 ∧ docAbs.h = 0 ∧
    docRel.relX docAbs = 10 ∧ docRel.relY docAbs = 20 := by
  decide

-- physical_fragment_test.cc:213: DumpFragmentTreeWithTargetInsideColumn
-- Multicolumn fragmentation splits a 150px child across 3 balanced columns of width 100px, height 50px, gap 10px.
-- CSS Multi-column Layout Level 1 §3.4, §4, CSS Fragmentation Level 3 §2.
theorem DumpFragmentTreeWithTargetInsideColumn_vectors :
    let mc : Multicol := { cols := 3, gap := 10, width := 320, height := 50, children := [{ id := 2, height := 150 }] }
    let res := layoutMulticol mc
    res.colWidth = 100 ∧
    res.columns.length = 3 ∧
    (match res.columns with
     | [col0, col1, col2] =>
         col0.relX = 0 ∧ col0.w = 100 ∧ col0.h = 50 ∧
         col1.relX = 110 ∧ col1.w = 100 ∧ col1.h = 50 ∧
         col2.relX = 220 ∧ col2.w = 100 ∧ col2.h = 50 ∧
         col0.slices = [⟨2, 0, 0, 100, 50⟩] ∧
         col1.slices = [⟨2, 0, 0, 100, 50⟩] ∧
         col2.slices = [⟨2, 0, 0, 100, 50⟩]
     | _ => false) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end TestsBlock
end ChromiumLayout
