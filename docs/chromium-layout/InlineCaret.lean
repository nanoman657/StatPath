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
import InlineBreakCandidate

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
    (`inline/inline_caret_position.cc:350-420`). -/
def resolveSoftWrapCaret (frag1 frag2 : Nat) (wrapOffset : Nat) (affinity : TextAffinity) :
    InlineCaretPosition :=
  match affinity with
  | .upstream => { fragmentId := frag1, positionType := .atTextOffset, textOffset := some wrapOffset }
  | .downstream => { fragmentId := frag2, positionType := .atTextOffset, textOffset := some wrapOffset }

/-- CSS Inline 3 §2 & Blink ComputeInlineCaretPosition:
    Caret resolution at soft wrap boundary between two consecutive atomic inline boxes. -/
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
  | span (id : String) (isCulled : Bool) (content : String)
  | br
  | image (id : String)
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
  hasTrailingSpace : Bool := false
  deriving DecidableEq, Repr

/-- CSS Text 3 §5: Find break opportunities using LineBreaker candidates. -/
def findBreakOpportunity (s : String) : Option (Nat × Bool × Bool) :=
  let cands := computeLineBreakCandidates [⟨0, .text s⟩]
  match cands.find? (fun c => c.isHyphenated || c.endOffset.textOffset < c.offset.textOffset) with
  | some c => some (if c.isHyphenated then c.offset.textOffset else c.endOffset.textOffset, c.isHyphenated, ¬c.isHyphenated)
  | none => none

/-- Fuel-bounded fragment builder reusing LineBreaker break opportunities and available width. -/
def buildCaretFragmentsAux (items : List CaretDocItem) (avail : Option Nat) (nextId : Nat) (offset : Nat) (lineOff : Nat) (prevBr : Bool) : List CaretFragment :=
  match items with
  | [] => []
  | .image id :: rest =>
    let fits := match avail with | some w => decide (lineOff + 1 ≤ w) | none => true
    let wrap := !fits ∨ (!rest.isEmpty ∧ avail.isSome)
    let f : CaretFragment := { id := nextId, elementId := id, isBox := true, isAtomic := true,
                               startOffset := offset, endOffset := offset + 1, hasSoftWrapToNext := wrap }
    f :: buildCaretFragmentsAux rest avail (nextId + 1) (offset + 1) (if fits then lineOff + 1 else 1) false
  | .br :: rest =>
    let f : CaretFragment := { id := nextId, isLineBreak := true, isEmptyLine := prevBr,
                               startOffset := offset, endOffset := offset + 1 }
    f :: buildCaretFragmentsAux rest avail (nextId + 1) (offset + 1) 0 true
  | .span id isCulled content :: rest =>
    let fits := match avail with | some w => decide (lineOff + content.length ≤ w) | none => true
    let wrap := !fits ∨ (!rest.isEmpty ∧ avail.isSome)
    let nOff := offset + content.length
    let nLine := if fits then lineOff + content.length else content.length
    if isCulled then
      let f : CaretFragment := { id := nextId, elementId := id, isCulled := true,
                                 startOffset := offset, endOffset := nOff, hasSoftWrapToNext := wrap }
      f :: buildCaretFragmentsAux rest avail (nextId + 1) nOff nLine false
    else
      let fBox : CaretFragment := { id := nextId, elementId := id, isBox := true,
                                    startOffset := offset, endOffset := nOff }
      let fTxt : CaretFragment := { id := nextId + 1, elementId := id,
                                    startOffset := offset, endOffset := nOff, hasSoftWrapToNext := wrap }
      fBox :: fTxt :: buildCaretFragmentsAux rest avail (nextId + 2) nOff nLine false
  | .text s :: rest =>
    match avail with
    | some w =>
      match findBreakOpportunity s with
      | some (bOff, isHyphen, isSpace) =>
        let off2 := if isSpace then bOff + 1 else bOff
        let f1 : CaretFragment := { id := nextId, startOffset := offset, endOffset := offset + bOff,
                                    isSoftHyphen := isHyphen, hasSoftWrapToNext := true, hasTrailingSpace := isSpace }
        let f2 : CaretFragment := { id := nextId + 1, startOffset := offset + off2, endOffset := offset + s.length }
        f1 :: f2 :: buildCaretFragmentsAux rest avail (nextId + 2) (offset + s.length) (s.length - off2) false
      | none =>
        if s.length > w then
          let f1 : CaretFragment := { id := nextId, startOffset := offset, endOffset := offset + w, hasSoftWrapToNext := true }
          let f2 : CaretFragment := { id := nextId + 1, startOffset := offset + w, endOffset := offset + s.length }
          f1 :: f2 :: buildCaretFragmentsAux rest avail (nextId + 2) (offset + s.length) (s.length - w) false
        else
          let f : CaretFragment := { id := nextId, startOffset := offset, endOffset := offset + s.length }
          f :: buildCaretFragmentsAux rest avail (nextId + 1) (offset + s.length) (lineOff + s.length) false
    | none =>
      let f : CaretFragment := { id := nextId, startOffset := offset, endOffset := offset + s.length }
      f :: buildCaretFragmentsAux rest avail (nextId + 1) (offset + s.length) (lineOff + s.length) false

/-- CSS Text 3 §5 & CSS Inline 3 §2: Partition input document items into layout fragments. -/
def buildCaretFragments (items : List CaretDocItem) (availWidth : Option Nat := none) : List CaretFragment :=
  buildCaretFragmentsAux items availWidth 0 0 0 false

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
    | some b => { fragmentId := b.id, positionType := .afterBox, textOffset := none }
    | none =>
      let t := frags.find? (fun f => f.elementId == nid && ¬f.isBox)
      { fragmentId := t.map (·.id) |>.getD 0, positionType := if t.isSome then .atTextOffset else .afterBox,
        textOffset := t.map (·.endOffset) }
  | .atOffset off =>
    match frags.find? (fun f => f.isAtomic && (f.startOffset == off || f.endOffset == off)) with
    | some atom =>
      if off == atom.startOffset then { fragmentId := atom.id, positionType := .beforeBox, textOffset := none }
      else
        let nextAtom := frags.find? (fun f => f.id == atom.id + 1 && f.isAtomic)
        if nextAtom.isSome ∧ affinity == .downstream
        then { fragmentId := atom.id + 1, positionType := .beforeBox, textOffset := none }
        else { fragmentId := atom.id, positionType := .afterBox, textOffset := none }
    | none =>
      match frags.find? (fun f => f.hasSoftWrapToNext) with
      | some f1 =>
        if f1.isSoftHyphen ∧ off == f1.endOffset then
          { fragmentId := f1.id, positionType := .atTextOffset, textOffset := some off }
        else if (f1.hasTrailingSpace ∧ off == f1.endOffset + 1) ∨ off == f1.endOffset then
          if affinity == .upstream then
            { fragmentId := f1.id, positionType := .atTextOffset, textOffset := some f1.endOffset }
          else
            let f2 := frags.find? (fun f => f.id > f1.id && ¬f.isBox)
            { fragmentId := f2.map (·.id) |>.getD (f1.id + 1), positionType := .atTextOffset,
              textOffset := some (if f1.hasTrailingSpace then f1.endOffset + 1 else off) }
        else fallback frags off affinity
      | none => fallback frags off affinity
where
  fallback frags off aff :=
    let valid := frags.filter (fun f => ¬f.isLineBreak ∨ f.isEmptyLine)
    let target := if aff == .downstream
      then valid.find? (fun f => f.startOffset == off) <|> valid.find? (fun f => f.startOffset ≤ off ∧ off ≤ f.endOffset)
      else valid.find? (fun f => f.startOffset ≤ off ∧ off ≤ f.endOffset) <|> valid.find? (fun f => f.startOffset == off)
    { fragmentId := target.map (·.id) |>.getD 0, positionType := .atTextOffset, textOffset := some off }

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

/-- CSS Text 3 §5 Law: Soft line wrap boundary without space resolves upstream to previous line fragment and downstream to next line fragment. -/
theorem soft_wrap_affinity_law (s : String) (w : Nat) (_h : w > 0) :
    let frags : List CaretFragment := [
      { id := 0, startOffset := 0, endOffset := w, hasSoftWrapToNext := true },
      { id := 1, startOffset := w, endOffset := s.length }
    ]
    (computeCaretPosition frags (.atOffset w) .upstream =
      { fragmentId := 0, positionType := .atTextOffset, textOffset := some w }) ∧
    (computeCaretPosition frags (.atOffset w) .downstream =
      { fragmentId := 1, positionType := .atTextOffset, textOffset := some w }) := by
  dsimp [computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Caret after a culled span resolves to text fragment at text offset. -/
theorem culled_span_caret_law (id : String) (txt : String) :
    let frags := buildCaretFragments [.span id true txt]
    computeCaretPosition frags (.afterNode id) .downstream =
      { fragmentId := 0, positionType := .atTextOffset, textOffset := some txt.length } := by
  dsimp [buildCaretFragments, buildCaretFragmentsAux, computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Caret after a non-culled span resolves to afterBox on the box fragment. -/
theorem non_culled_span_caret_law (id : String) (txt : String) :
    let frags := buildCaretFragments [.span id false txt]
    computeCaretPosition frags (.afterNode id) .downstream =
      { fragmentId := 0, positionType := .afterBox, textOffset := none } := by
  dsimp [buildCaretFragments, buildCaretFragmentsAux, computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Atomic inline image resolves offset 0 to beforeBox and offset 1 to afterBox. -/
theorem atomic_image_caret_law (id : String) :
    let frags := buildCaretFragments [.image id]
    (computeCaretPosition frags (.atOffset 0) .downstream =
      { fragmentId := 0, positionType := .beforeBox, textOffset := none }) ∧
    (computeCaretPosition frags (.atOffset 1) .downstream =
      { fragmentId := 0, positionType := .afterBox, textOffset := none }) := by
  dsimp [buildCaretFragments, buildCaretFragmentsAux, computeCaretPosition]
  simp

/-- CSS Inline 3 §2 Law: Multi-column text fragment without break opportunities maps offset to identity text offset. -/
theorem multicol_fragment_caret_offset (fragId startOff endOff off : Nat) (hRange : startOff ≤ off ∧ off ≤ endOff) :
    let frags : List CaretFragment := [{ id := fragId, startOffset := startOff, endOffset := endOff }]
    (computeCaretPosition frags (.atOffset off) .downstream).textOffset = some off := by
  dsimp [computeCaretPosition, computeCaretPosition.fallback]
  simp [hRange.1, hRange.2]

end ChromiumLayout
