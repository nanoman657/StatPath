/-
  docs/chromium-layout/InlineCaret.lean

  Formal model for Blink InlineCaretPosition and caret resolution
  (`third_party/blink/renderer/core/layout/inline/inline_caret_position.h`,
   `hyphen_result.h`).

  Owns: TextAffinity, InlineCaretPositionType, InlineCaretPosition,
  caret resolution rules, and HyphenResult glyph rotation.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 1. Hyphen Glyph Orientation -/

inductive GlyphRotation where
  | regular
  | rotateCanvasUpright
  deriving DecidableEq, Repr

/-- Hyphen glyph rotation for horizontal vs vertical writing modes
    (`inline/hyphen_result.cc:25-60`). -/
def hyphenGlyphRotation (isVertical : Bool) (isUpright : Bool) : GlyphRotation :=
  if !isVertical then .regular
  else if isUpright then .rotateCanvasUpright
  else .regular

/-! ## 2. Inline Caret Position -/

inductive TextAffinity where
  | upstream
  | downstream
  deriving DecidableEq, Repr

inductive InlineCaretPositionType where
  | beforeBox
  | afterBox
  | atTextOffset
  deriving DecidableEq, Repr

/-- `InlineCaretPosition` (`inline/inline_caret_position.h:35-120`). -/
structure InlineCaretPosition where
  fragmentId : Nat := 0
  positionType : InlineCaretPositionType := .atTextOffset
  textOffset : Option Nat := none
  deriving DecidableEq, Repr

/-- Caret resolution at soft wrap boundary between two consecutive fragments
    (`inline/inline_caret_position.cc:350-420`).
    `upstream` affinity binds to the end of `frag1`;
    `downstream` affinity binds to the start of `frag2`. -/
def resolveSoftWrapCaret (frag1 frag2 : Nat) (wrapOffset : Nat) (affinity : TextAffinity) :
    InlineCaretPosition :=
  match affinity with
  | .upstream => { fragmentId := frag1, positionType := .atTextOffset, textOffset := some wrapOffset }
  | .downstream => { fragmentId := frag2, positionType := .atTextOffset, textOffset := some wrapOffset }

/-- CSS Inline 3 §2 & Blink ComputeInlineCaretPosition:
    Caret resolution at soft wrap boundary between two consecutive atomic inline boxes (e.g. images).
    - Upstream affinity binds to the end of the first box (afterBox).
    - Downstream affinity binds to the start of the second box (beforeBox). -/
def resolveSoftWrapBoxCaret (box1 box2 : Nat) (affinity : TextAffinity) : InlineCaretPosition :=
  match affinity with
  | .upstream => { fragmentId := box1, positionType := .afterBox, textOffset := none }
  | .downstream => { fragmentId := box2, positionType := .beforeBox, textOffset := none }

/-- Caret resolution at text offset within a single fragment
    (`inline/inline_caret_position.cc:280-340`). -/
def resolveTextCaret (fragId : Nat) (offset : Nat) : InlineCaretPosition :=
  { fragmentId := fragId, positionType := .atTextOffset, textOffset := some offset }

/-! ## 3. Spec-First Inline Caret Model (CSS Inline 3 §2, CSS Text 3 §5, §5.3) -/

/-- CSS Inline 3 §2 & CSS Text 3 §5: Document item input representing text and inline elements. -/
inductive CaretDocItem where
  | text (content : String)
  | softWrapText (line1 line2 : String)
  | softHyphenText (before after : String)
  | forcedBreakText (line1 line2 : String)
  | emptyLineText (before after : String)
  | span (id : String) (isCulled : Bool) (content : String)
  | atomicImage (id : String)
  deriving DecidableEq, Repr

/-- CSS Inline 3 §2: A layout fragment generated from inline elements. -/
structure CaretFragment where
  id : Nat := 0
  elementId : String := ""
  startOffset : Nat := 0
  endOffset : Nat := 0
  isBox : Bool := false
  isCulled : Bool := false
  isAtomic : Bool := false
  isLineBreak : Bool := false
  isEmptyLine : Bool := false
  isSoftHyphen : Bool := false
  hasSoftWrapToNext : Bool := false
  deriving DecidableEq, Repr

/-- CSS Text 3 §5 & CSS Inline 3 §2: Partition input document into layout fragments. -/
def buildCaretFragments : CaretDocItem → List CaretFragment
  | .text s =>
    [{ id := 0, startOffset := 0, endOffset := s.length }]
  | .softWrapText l1 l2 =>
    [{ id := 0, startOffset := 0, endOffset := l1.length, hasSoftWrapToNext := true },
     { id := 1, startOffset := l1.length, endOffset := l1.length + l2.length }]
  | .softHyphenText b a =>
    let h := b.length + 1
    [{ id := 0, startOffset := 0, endOffset := h, isSoftHyphen := true, hasSoftWrapToNext := true },
     { id := 1, startOffset := h, endOffset := h + a.length }]
  | .forcedBreakText l1 l2 =>
    let b := l1.length
    [{ id := 0, startOffset := 0, endOffset := b },
     { id := 1, startOffset := b, endOffset := b + 1, isLineBreak := true },
     { id := 2, startOffset := b + 1, endOffset := b + 1 + l2.length }]
  | .emptyLineText b a =>
    let b1 := b.length
    [{ id := 0, startOffset := 0, endOffset := b1 },
     { id := 1, startOffset := b1, endOffset := b1 + 1, isLineBreak := true },
     { id := 2, startOffset := b1 + 1, endOffset := b1 + 2, isLineBreak := true, isEmptyLine := true },
     { id := 3, startOffset := b1 + 2, endOffset := b1 + 2 + a.length }]
  | .span id true content =>
    [{ id := 0, elementId := id, startOffset := 0, endOffset := content.length, isCulled := true }]
  | .span id false content =>
    [{ id := 0, elementId := id, startOffset := 0, endOffset := content.length, isBox := true },
     { id := 1, elementId := id, startOffset := 0, endOffset := content.length }]
  | .atomicImage id =>
    [{ id := 0, elementId := id, startOffset := 0, endOffset := 1, isBox := true, isAtomic := true }]

/-- CSS Inline 3 §2: Query for caret position by character offset or after a node. -/
inductive CaretQuery where
  | atOffset (offset : Nat)
  | afterNode (nodeId : String)
  deriving DecidableEq, Repr

/-- CSS Text 3 §5 & CSS Inline 3 §2: Compute inline caret position from layout fragments and query. -/
def computeCaretPosition (frags : List CaretFragment) (q : CaretQuery) (affinity : TextAffinity) : InlineCaretPosition :=
  match q with
  | .afterNode nid =>
    match frags.find? (fun f => f.elementId == nid && f.isBox) with
    | some boxFrag => { fragmentId := boxFrag.id, positionType := .afterBox, textOffset := none }
    | none =>
      match frags.find? (fun f => f.elementId == nid && ¬f.isBox) with
      | some textFrag => { fragmentId := textFrag.id, positionType := .atTextOffset, textOffset := some textFrag.endOffset }
      | none => { fragmentId := 0, positionType := .afterBox, textOffset := none }
  | .atOffset off =>
    match frags.find? (fun f => f.isAtomic) with
    | some atom =>
      if off == atom.startOffset then
        { fragmentId := atom.id, positionType := .beforeBox, textOffset := none }
      else
        { fragmentId := atom.id, positionType := .afterBox, textOffset := none }
    | none =>
      match frags.find? (fun f => f.hasSoftWrapToNext && f.endOffset == off) with
      | some f1 =>
        if f1.isSoftHyphen then
          { fragmentId := f1.id, positionType := .atTextOffset, textOffset := some off }
        else
          match affinity with
          | .upstream => { fragmentId := f1.id, positionType := .atTextOffset, textOffset := some off }
          | .downstream =>
            match frags.find? (fun f => f.id == f1.id + 1) with
            | some f2 => { fragmentId := f2.id, positionType := .atTextOffset, textOffset := some off }
            | none => { fragmentId := f1.id, positionType := .atTextOffset, textOffset := some off }
      | none =>
        let validFrags := frags.filter (fun f => ¬f.isLineBreak ∨ f.isEmptyLine)
        let candidate :=
          if affinity == .downstream then
            match validFrags.find? (fun f => f.startOffset == off) with
            | some f => some f
            | none => validFrags.find? (fun f => f.startOffset ≤ off ∧ off ≤ f.endOffset)
          else
            match validFrags.find? (fun f => f.startOffset ≤ off ∧ off ≤ f.endOffset) with
            | some f => some f
            | none => validFrags.find? (fun f => f.startOffset == off)
        match candidate with
        | some f => { fragmentId := f.id, positionType := .atTextOffset, textOffset := some off }
        | none => { fragmentId := 0, positionType := .atTextOffset, textOffset := some off }

/-! ## 4. General Laws for Inline Caret Position -/

/-- Theorem: Upstream and downstream caret positions at a wrap boundary between distinct
    fragments always target distinct fragments. -/
theorem caret_wrap_affinity_targets_distinct (frag1 frag2 : Nat) (offset : Nat)
    (hDistinct : frag1 ≠ frag2) :
    (resolveSoftWrapCaret frag1 frag2 offset .upstream).fragmentId ≠
    (resolveSoftWrapCaret frag1 frag2 offset .downstream).fragmentId := by
  dsimp [resolveSoftWrapCaret]
  exact hDistinct

/-- Theorem: Hyphen glyph rotation is always regular in horizontal mode regardless of upright flag. -/
theorem hyphen_horizontal_always_regular (isUpright : Bool) :
    hyphenGlyphRotation false isUpright = .regular := by
  dsimp [hyphenGlyphRotation]

/-- CSS Inline 3 §2 Law: Upstream caret at box wrap boundary targets the first box with afterBox. -/
theorem soft_wrap_box_upstream (b1 b2 : Nat) :
    resolveSoftWrapBoxCaret b1 b2 .upstream = { fragmentId := b1, positionType := .afterBox, textOffset := none } := by
  rfl

/-- CSS Inline 3 §2 Law: Downstream caret at box wrap boundary targets the second box with beforeBox. -/
theorem soft_wrap_box_downstream (b1 b2 : Nat) :
    resolveSoftWrapBoxCaret b1 b2 .downstream = { fragmentId := b2, positionType := .beforeBox, textOffset := none } := by
  rfl

/-- CSS Inline 3 §2 Law: Upstream and downstream box carets at distinct boxes target distinct fragments. -/
theorem soft_wrap_box_distinct (b1 b2 : Nat) (h : b1 ≠ b2) :
    (resolveSoftWrapBoxCaret b1 b2 .upstream).fragmentId ≠
    (resolveSoftWrapBoxCaret b1 b2 .downstream).fragmentId := by
  dsimp [resolveSoftWrapBoxCaret]
  exact h

/-- CSS Text 3 §5 Law: Soft line wrap boundary resolves upstream to previous line fragment and downstream to next line fragment. -/
theorem soft_wrap_affinity_law (s1 s2 : String) :
    let frags := buildCaretFragments (.softWrapText s1 s2)
    (computeCaretPosition frags (.atOffset s1.length) .upstream =
      { fragmentId := 0, positionType := .atTextOffset, textOffset := some s1.length }) ∧
    (computeCaretPosition frags (.atOffset s1.length) .downstream =
      { fragmentId := 1, positionType := .atTextOffset, textOffset := some s1.length }) := by
  dsimp [buildCaretFragments, computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Caret after a culled span resolves to text fragment at text offset. -/
theorem culled_span_caret_law (id : String) (txt : String) :
    let frags := buildCaretFragments (.span id true txt)
    computeCaretPosition frags (.afterNode id) .downstream =
      { fragmentId := 0, positionType := .atTextOffset, textOffset := some txt.length } := by
  dsimp [buildCaretFragments, computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Caret after a non-culled span resolves to afterBox on the box fragment. -/
theorem non_culled_span_caret_law (id : String) (txt : String) :
    let frags := buildCaretFragments (.span id false txt)
    computeCaretPosition frags (.afterNode id) .downstream =
      { fragmentId := 0, positionType := .afterBox, textOffset := none } := by
  dsimp [buildCaretFragments, computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Atomic inline image resolves offset 0 to beforeBox and offset 1 to afterBox. -/
theorem atomic_image_caret_law (id : String) :
    let frags := buildCaretFragments (.atomicImage id)
    (computeCaretPosition frags (.atOffset 0) .downstream =
      { fragmentId := 0, positionType := .beforeBox, textOffset := none }) ∧
    (computeCaretPosition frags (.atOffset 1) .downstream =
      { fragmentId := 0, positionType := .afterBox, textOffset := none }) := by
  dsimp [buildCaretFragments, computeCaretPosition]
  simp

end ChromiumLayout
