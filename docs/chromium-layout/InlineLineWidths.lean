/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import LayoutTypes

/-!
# CSS 2.1 §9.5, §10.8 & CSS Inline 3 §3: Line Widths and Float Exclusion Precomputation

Formalizes:
- CSS 2.1 §9.5: Floats and Line Box Shortening
- CSS 2.1 §10.8: Line Height Calculations: The 'Strut' and Baseline Alignment
- CSS Inline 3 §3: Line Heights and Baseline Alignment
- `third_party/blink/renderer/core/layout/inline/line_widths.h`
- `third_party/blink/renderer/core/layout/inline/line_widths.cc`

Owns:
- `SimpleInlineItem`
- `LineWidths`
- `LineWidths.get`
- `ceilDiv`
- `quantaToPx`
- `computeLineWidths`
-/

namespace ChromiumLayout

/-! ## 1. Core Model Definitions -/

/-- Exact quarter-pixel conversion: quanta to integer pixels (quanta / 4). -/
def quantaToPx (q : Nat) : Nat := q / 4

/-- Integer ceiling division `ceil(a / b)`. When b is 0, returns 0. -/
def ceilDiv (a b : Nat) : Nat :=
  if b == 0 then 0 else (a + b - 1) / b

/-- Simplified inline items for precomputing line width budgets before layout. -/
inductive SimpleInlineItem where
  | text (str : String) (fitsStrut : Bool := true)
  | openTag (isBaselineAlign : Bool := true)
  | closeTag
  | floating (widthQuanta : Nat) (heightQuanta : Nat)
  | atomicInline
  deriving DecidableEq, Repr, Inhabited

/-- Precomputed line widths (`Blink::LineWidths`).
    Maintains a default line width and an excluded width for the initial lines affected by a float exclusion. -/
structure LineWidths where
  defaultWidth : Nat
  excludedWidth : Nat := defaultWidth
  numExcludedLines : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- CSS 2.1 §9.5: Returns the width of a line at 0-based index. -/
def LineWidths.get (lw : LineWidths) (index : Nat) : Nat :=
  if index < lw.numExcludedLines then lw.excludedWidth else lw.defaultWidth

/-- State tracker for item scanning in LineWidths::Set. -/
structure ItemScanState where
  seenInflow : Bool := false
  hasNonLeadingFloat : Bool := false
  hasInvalidAlign : Bool := false
  hasUnfitStrut : Bool := false
  hasAtomicInline : Bool := false
  leadingFloats : List (Nat × Nat) := []
  deriving DecidableEq, Repr

/-- Fold step scanning items. -/
def scanItemStep (st : ItemScanState) (item : SimpleInlineItem) : ItemScanState :=
  match item with
  | .openTag isBaseline =>
    if ¬ isBaseline then
      { st with hasInvalidAlign := true }
    else
      st
  | .closeTag =>
    st
  | .text str fitsStrut =>
    if ¬ fitsStrut then
      { st with hasUnfitStrut := true }
    else if str != "" then
      { st with seenInflow := true }
    else
      st
  | .atomicInline =>
    { st with seenInflow := true, hasAtomicInline := true }
  | .floating w h =>
    if st.seenInflow then
      { st with hasNonLeadingFloat := true }
    else
      { st with leadingFloats := st.leadingFloats ++ [(w, h)] }

/-- CSS 2.1 §9.5, §10.8 & Blink LineWidths::Set:
    Precompute line widths for simple inline nodes without full layout.
    Returns `none` if the node has non-leading floats, non-baseline vertical-align,
    text exceeding the line strut, atomic inlines with floats, or stepped multi-float exclusions. -/
def computeLineWidths (containerWidthQuanta : Nat) (lineHeightQuanta : Nat) (items : List SimpleInlineItem) : Option LineWidths :=
  let st := items.foldl scanItemStep {}
  if st.hasInvalidAlign ∨ st.hasUnfitStrut ∨ st.hasNonLeadingFloat then
    none
  else
    match st.leadingFloats with
    | [] =>
      let defW := quantaToPx containerWidthQuanta
      some { defaultWidth := defW, excludedWidth := defW, numExcludedLines := 0 }
    | [(fw, fh)] =>
      if st.hasAtomicInline then
        none
      else
        let defW := quantaToPx containerWidthQuanta
        let exW := quantaToPx (if fw ≥ containerWidthQuanta then 0 else containerWidthQuanta - fw)
        let numLines := ceilDiv fh lineHeightQuanta
        some { defaultWidth := defW, excludedWidth := exW, numExcludedLines := numLines }
    | (fw0, fh0) :: rest =>
      if st.hasAtomicInline then
        none
      else if rest.all (fun (_, h) => h == fh0) then
        let defW := quantaToPx containerWidthQuanta
        let totalFw := fw0 + rest.foldl (fun acc (w, _) => acc + w) 0
        let exW := quantaToPx (if totalFw ≥ containerWidthQuanta then 0 else containerWidthQuanta - totalFw)
        let numLines := ceilDiv fh0 lineHeightQuanta
        some { defaultWidth := defW, excludedWidth := exW, numExcludedLines := numLines }
      else
        -- Stepped exclusions cannot be computed without full layout
        none

/-! ## 2. General Laws (CSS 2.1 §9.5 & §10.8) -/

/-- CSS 2.1 §9.5 Law: Any line beyond the exclusion region has the default container width. -/
theorem lineWidths_get_ge_excluded (lw : LineWidths) (i : Nat) (h : i ≥ lw.numExcludedLines) :
    lw.get i = lw.defaultWidth := by
  unfold LineWidths.get
  split
  · rename_i hlt
    omega
  · rfl

/-- CSS 2.1 §9.5 Law: Any line within the exclusion region has the excluded width. -/
theorem lineWidths_get_lt_excluded (lw : LineWidths) (i : Nat) (h : i < lw.numExcludedLines) :
    lw.get i = lw.excludedWidth := by
  unfold LineWidths.get
  split
  · rfl
  · rename_i hge
    omega

/-- Ceiling division by zero is safely zero. -/
theorem lineWidths_ceilDiv_zero (a : Nat) :
    ceilDiv a 0 = 0 := by
  rfl

/-- CSS 2.1 §9.5 Law: When there are no items, there are zero excluded lines and the container uses the default width. -/
theorem lineWidths_no_items_numExcluded_zero (w : Nat) (lh : Nat) :
    computeLineWidths w lh [] =
      some { defaultWidth := quantaToPx w, excludedWidth := quantaToPx w, numExcludedLines := 0 } := by
  rfl

/-- CSS 2.1 §9.5 Law: A float appearing after an in-flow atomic inline is non-leading and fails precomputation. -/
theorem lineWidths_non_leading_float_fails (w : Nat) (lh : Nat) (fw fh : Nat) :
    computeLineWidths w lh [SimpleInlineItem.atomicInline, SimpleInlineItem.floating fw fh] = none := by
  rfl

/-- CSS 2.1 §9.5 Law: An atomic inline following a leading float cannot be precomputed without layout. -/
theorem lineWidths_atomic_with_leading_float_fails (w : Nat) (lh : Nat) (fw fh : Nat) :
    computeLineWidths w lh [SimpleInlineItem.floating fw fh, SimpleInlineItem.atomicInline] = none := by
  rfl

/-- CSS 2.1 §10.8 Law: Non-baseline vertical alignment fails precomputation. -/
theorem lineWidths_non_baseline_align_fails (w : Nat) (lh : Nat) :
    computeLineWidths w lh [SimpleInlineItem.openTag false] = none := by
  rfl

/-- CSS 2.1 §10.8 Law: Text that exceeds the strut metrics fails precomputation. -/
theorem lineWidths_unfit_strut_fails (w : Nat) (lh : Nat) (s : String) :
    computeLineWidths w lh [SimpleInlineItem.text s false] = none := by
  rfl

end ChromiumLayout
