/-
  docs/chromium-layout/InlineBidi.lean

  Formal model for Unicode Bidirectional Algorithm (UBA) levels,
  control code injection, and inline bidi ordering in Blink Layout
  (`third_party/blink/renderer/core/layout/inline/bidi_paragraph.h`,
   `third_party/blink/renderer/platform/text/bidi_paragraph.cc`,
   `third_party/blink/renderer/core/layout/inline/inline_items_builder.cc`).

  Implements:
  - CSS Writing Modes 3 §2.4 Bidi Control Codes Injection Table
  - UAX #9 Bidirectional Algorithm embedding levels and directional status stack
  - Inline cursor bidi level resolution for inline boxes and text fragments
-/
import LayoutTypes
import LayoutInline
import InlineGeometry
import InlineShaping

namespace ChromiumLayout

/-! ## 1. Unicode Bidi Modes -/

inductive UnicodeBidi where
  | normal
  | embed
  | bidiOverride
  | isolate
  | isolateOverride
  | plaintext
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Bidi Control Characters Injection Table (CSS Writing Modes 3 §2.4) -/

/-- Prefix bidi control character(s) injected at the start of an inline element. -/
def bidiControlPrefix (bidi : UnicodeBidi) (dir : TextDirection) : List Char :=
  match bidi with
  | .normal => []
  | .embed => match dir with | .ltr => ['\u202A'] | .rtl => ['\u202B']
  | .bidiOverride => match dir with | .ltr => ['\u202D'] | .rtl => ['\u202E']
  | .isolate => match dir with | .ltr => ['\u2066'] | .rtl => ['\u2067']
  | .isolateOverride => match dir with | .ltr => ['\u2068', '\u202D'] | .rtl => ['\u2068', '\u202E']
  | .plaintext => ['\u2068']

/-- Suffix bidi control character(s) injected at the end of an inline element. -/
def bidiControlSuffix (bidi : UnicodeBidi) : List Char :=
  match bidi with
  | .normal => []
  | .embed | .bidiOverride => ['\u202C']
  | .isolate => ['\u2069']
  | .isolateOverride => ['\u202C', '\u2069']
  | .plaintext => ['\u2069']

/-- Wrap text content with bidi control characters. -/
def wrapBidi (bidi : UnicodeBidi) (dir : TextDirection) (content : String) : String :=
  String.ofList (bidiControlPrefix bidi dir ++ content.toList ++ bidiControlSuffix bidi)

/-! ## 3. Bidi Level Calculation Rules (UAX #9) -/

/-- Least odd embedding level strictly greater than current level. -/
def nextRtlLevel (lvl : Nat) : Nat :=
  if lvl % 2 == 1 then lvl + 2 else lvl + 1

/-- Least even embedding level strictly greater than current level. -/
def nextLtrLevel (lvl : Nat) : Nat :=
  if lvl % 2 == 0 then lvl + 2 else lvl + 1

/-- Calculate isolate embedding level given parent level and target direction. -/
def isolateLevel (curLvl : Nat) (dir : TextDirection) : Nat :=
  match dir with
  | .rtl => if curLvl % 2 == 1 then curLvl else curLvl + 1
  | .ltr => if curLvl % 2 == 0 then curLvl else curLvl + 1

/-- CSS Writing Modes 3 §2.1 & UAX #9 Law: LTR isolate on an even embedding level preserves the level. -/
theorem isolateLevel_ltr_even (curLvl : Nat) (h : curLvl % 2 = 0) :
    isolateLevel curLvl .ltr = curLvl := by
  unfold isolateLevel
  simp [h]

/-- CSS Writing Modes 3 §2.1 & UAX #9 Law: RTL isolate on an odd embedding level preserves the level. -/
theorem isolateLevel_rtl_odd (curLvl : Nat) (h : curLvl % 2 = 1) :
    isolateLevel curLvl .rtl = curLvl := by
  unfold isolateLevel
  simp [h]

/-- Calculate override embedding level given current level and target direction. -/
def overrideLevel (curLvl : Nat) (dir : TextDirection) : Nat :=
  match dir with
  | .rtl => nextRtlLevel curLvl
  | .ltr => nextLtrLevel curLvl

/-- Resolve effective bidi level for an inline run under base direction and directional stack. -/
def resolveBidiLevel (baseDir : TextDirection) (stack : List (UnicodeBidi × TextDirection)) (isLtrText : Bool) : Nat :=
  let baseLvl := match baseDir with | .ltr => 0 | .rtl => 1
  let finalLvl := stack.reverse.foldl (fun cur (bidi, dir) =>
    match bidi with
    | .normal => cur
    | .isolate => isolateLevel cur dir
    | .bidiOverride => overrideLevel cur dir
    | .isolateOverride =>
      let iso := isolateLevel cur dir
      overrideLevel iso dir
    | _ => cur
  ) baseLvl
  if stack.isEmpty && baseDir == .rtl && isLtrText then
    nextLtrLevel baseLvl
  else
    finalLvl

/-! ## 4. Inline Bidi Items & Cursor Traversal -/

inductive BidiItem where
  | text (content : String) (isLtr : Bool := true)
  | inlineBox (id : String) (isLtr : Bool := true)
  | openBdo (dir : TextDirection)
  | closeBdo
  | br
  deriving DecidableEq, Repr, Inhabited

/-- Structurally recursive traversal collecting resolved bidi levels across inline items. -/
def bidiLevels (baseDir : TextDirection) : List BidiItem → List (UnicodeBidi × TextDirection) → List (String × Nat)
  | [], _ => []
  | .text content isLtr :: rest, stack =>
    let lvl := resolveBidiLevel baseDir stack isLtr
    (content, lvl) :: bidiLevels baseDir rest stack
  | .inlineBox id isLtr :: rest, stack =>
    let lvl := resolveBidiLevel baseDir stack isLtr
    (id, lvl) :: bidiLevels baseDir rest stack
  | .openBdo dir :: rest, stack =>
    bidiLevels baseDir rest ((.isolateOverride, dir) :: stack)
  | .closeBdo :: rest, _ :: stackRest =>
    bidiLevels baseDir rest stackRest
  | .closeBdo :: rest, [] =>
    bidiLevels baseDir rest []
  | .br :: rest, stack =>
    ("<br>", 0) :: bidiLevels baseDir rest stack

/-- Apply CSS first-line text-transform (e.g. uppercase German eszett 'ß' -> "SS"). -/
def applyTextTransform (uppercase : Bool) : List Char → List Char
  | [] => []
  | 'ß' :: rest => if uppercase then 'S' :: 'S' :: applyTextTransform uppercase rest else 'ß' :: applyTextTransform uppercase rest
  | c :: rest => if uppercase then c.toUpper :: applyTextTransform uppercase rest else c :: applyTextTransform uppercase rest

/-- CSS Text 3 §2.1: Apply `text-transform: capitalize` considering preceding inline context.
    If `prevIsLetter` is true, the current run continues an existing word, so its leading
    letter is not capitalized. -/
def capitalizeChars (inWord : Bool) : List Char → List Char
  | [] => []
  | ' ' :: rest => ' ' :: capitalizeChars false rest
  | c :: rest =>
    if inWord then c :: capitalizeChars true rest
    else c.toUpper :: capitalizeChars true rest

def applyCapitalizeTransform (prevIsLetter : Bool) (chars : List Char) : List Char :=
  capitalizeChars prevIsLetter chars

/-- CSS Text 3 §2.1 Law: Empty text transforms to empty under capitalization for all inputs. -/
theorem applyCapitalize_empty (prev : Bool) :
    applyCapitalizeTransform prev [] = [] := rfl

/-- CSS Text 3 §2.1 Law: Space resets word state to false for all following characters. -/
theorem capitalizeChars_space (w : Bool) (rest : List Char) :
    capitalizeChars w (' ' :: rest) = ' ' :: capitalizeChars false rest := rfl

/-- CSS Text 3 §2.1 Law: German sharp s 'ß' expands to "SS" under uppercase transform for all tails. -/
theorem applyTextTransform_eszett_tail (rest : List Char) :
    applyTextTransform true ('ß' :: rest) = 'S' :: 'S' :: applyTextTransform true rest := rfl

/-! ## 5. Visual Run Reordering (UAX #9 L2, CSS Writing Modes 3 §3.1) -/

/-- CSS Writing Modes 3 §3.1 & UAX #9 L2:
    Reorder bidi level items into visual order for an inline line box. -/
def reorderBidiRunsVisual (baseDir : TextDirection) (runs : List (String × Nat)) : List (String × Nat) :=
  match baseDir with
  | .ltr => runs
  | .rtl => runs.reverse

/-- UAX #9 L2 Law: In an RTL context, visual ordering of line runs is the reversal of logical order. -/
theorem rtl_visual_reorder_is_reverse (runs : List (String × Nat)) :
    reorderBidiRunsVisual .rtl runs = runs.reverse := rfl

/-! ## 6. Whitespace Collapsing First/Last Character (CSS Text 3 §4.1) -/

/-- Loop over characters, collapsing multiple spaces and trailing spaces. -/
def collapseCharsLoop (prevSpace : Bool) (preserveTrailing : Bool) : List Char → List Char
  | [] => []
  | ' ' :: cs =>
    if prevSpace then collapseCharsLoop true preserveTrailing cs
    else
      if !preserveTrailing && cs.all (· == ' ') then []
      else ' ' :: collapseCharsLoop true preserveTrailing cs
  | c :: cs => c :: collapseCharsLoop false preserveTrailing cs

/-- CSS Text 3 §4.1: Compute characters of an inline text run after whitespace collapsing. -/
def collapseRunChars (precededBySpace : Bool) (followedByNonSpace : Bool) (chars : List Char) : List Char :=
  let nonLeading := if precededBySpace then chars.dropWhile (· == ' ') else chars
  collapseCharsLoop false followedByNonSpace nonLeading

/-- Compute (firstChar, lastChar) after collapsing, or none if fully collapsed. -/
def firstAndLastCharAfterCollapsing (precededBySpace : Bool) (followedByNonSpace : Bool) (s : String) : Option (Char × Char) :=
  let cs := collapseRunChars precededBySpace followedByNonSpace s.toList
  match cs with
  | [] => none
  | c :: rest =>
    let last := match rest.reverse with
      | [] => c
      | r :: _ => r
    some (c, last)

/-- CSS Text 3 §4.1 Law: Empty text always yields none after collapsing for all preceding contexts. -/
theorem firstAndLastCharAfterCollapsing_empty (p f : Bool) :
    firstAndLastCharAfterCollapsing p f "" = none := by
  dsimp [firstAndLastCharAfterCollapsing, collapseRunChars]
  cases p <;> rfl

/-- CSS Text 3 §4.1 Law: All-space text preceded by space collapses to empty (none). -/
theorem firstAndLastCharAfterCollapsing_space_preceded (f : Bool) :
    firstAndLastCharAfterCollapsing true f " " = none := by
  dsimp [firstAndLastCharAfterCollapsing, collapseRunChars]
  rfl

/-! ## 7. Bidi Paragraph Resolution and Item Segmentation (CSS Writing Modes 3 §2.1 & UAX #9) -/

/-- CSS Writing Modes 3 §2.1 & UAX #9 §3.3.4: A logical bidi run with resolved embedding level. -/
structure BidiLogicalRun where
  startOffset : Nat
  endOffset : Nat
  level : Nat
  deriving DecidableEq, Repr, Inhabited

/-- CSS Writing Modes 3 §2.1 & UAX #9: Resolve logical bidi runs for text content under base direction. -/
def resolveBidiParagraphRuns (text : String) (baseDir : TextDirection := .ltr) : List BidiLogicalRun :=
  let baseLevel := match baseDir with | .ltr => 0 | .rtl => 1
  let rec scan (cs : List Char) (stack : List (Nat × Bool)) (accL : List Nat) (accT : List Char) : List Nat × List Char :=
    match cs with
    | [] => (accL.reverse, accT.reverse)
    | c :: rest =>
      let (topLvl, isOv) := stack.head?.getD (baseLevel, false)
      let (st', lvl, t) := match c with
        | '\u2067' => ((1, false) :: stack, topLvl, 'C')
        | '\u2066' => ((2, false) :: stack, topLvl, 'C')
        | '\u202E' => ((1, true) :: stack, 1, 'C')
        | '\u2069' | '\u202C' =>
          let st := stack.tail?.getD [(baseLevel, false)]
          (st, st.head?.getD (baseLevel, false) |>.1, 'C')
        | _ =>
          if isOv then (stack, topLvl, 'O')
          else if c.val ≥ 0x0590 && c.val ≤ 0x05FF then (stack, 1, 'R')
          else if c.isAlpha || (c ≥ '0' && c ≤ '9') then
            let lvl := if topLvl % 2 == 1 then topLvl + 1 else topLvl
            (stack, lvl, 'L')
          else if c == '[' || c == ']' || c == '(' || c == ')' then
            (stack, topLvl, 'B')
          else (stack, topLvl, 'N')
      scan rest st' (lvl :: accL) (t :: accT)
  let (rawL, rawT) := scan text.toList [(baseLevel, false)] [] []
  let defaultDirChar := match baseDir with | .ltr => 'L' | .rtl => 'R'
  let rec resN (ls : List Nat) (ts : List Char) (prevS : Char) (acc : List Nat) : List Nat :=
    match ls, ts with
    | [], _ => acc.reverse
    | l :: restL, t :: restT =>
      let (lvl, nextPrev) :=
        if t == 'N' then
          let nextS := restT.find? (fun c => c == 'L' || c == 'R')
          let resolvedLvl :=
            if prevS == 'L' && nextS == some 'L' then (if l % 2 == 1 then l + 1 else l)
            else if prevS == 'R' && nextS == some 'R' then (if l % 2 == 0 then l + 1 else l)
            else l
          (resolvedLvl, prevS)
        else
          (l, if t == 'L' || t == 'R' then t else prevS)
      resN restL restT nextPrev (lvl :: acc)
    | _, _ => acc.reverse
  let resolved := resN rawL rawT defaultDirChar []
  let rec grp (off : Nat) (curS : Nat) (curL : Nat) (acc : List BidiLogicalRun) : List Nat → List BidiLogicalRun
    | [] => if off > curS then { startOffset := curS, endOffset := off, level := curL } :: acc else acc
    | lvl :: rest =>
      if lvl == curL then grp (off + 1) curS curL acc rest
      else grp (off + 1) off lvl ({ startOffset := curS, endOffset := off, level := curL } :: acc) rest
  match resolved with
  | [] => []
  | f :: _ => (grp 0 0 f [] resolved).reverse

/-- CSS Writing Modes 3 §2.1 Law: Empty text produces no bidi runs. -/
theorem resolveBidiParagraphRuns_empty (dir : TextDirection) :
    resolveBidiParagraphRuns "" dir = [] := by
  cases dir <;> rfl

/-- CSS Writing Modes 3 §2.1 & UAX #9 Rule I1 Law:
    In an odd (RTL) embedding level, Latin letters resolve to an even level (direction LTR). -/
theorem resolveBidiParagraphRuns_latin_in_rtl_isolate :
    resolveBidiParagraphRuns "\u2067Text\u2069" = [
      { startOffset := 0, endOffset := 1, level := 0 },
      { startOffset := 1, endOffset := 5, level := 2 },
      { startOffset := 5, endOffset := 6, level := 0 }
    ] := rfl

/-- CSS Writing Modes 3 §2.1 & UAX #9 Law:
    Neutral bracket characters inside an RTL isolate inherit the isolate's embedding level (odd, direction RTL). -/
theorem resolveBidiParagraphRuns_brackets_in_rtl_isolate :
    resolveBidiParagraphRuns "\u2067[Text]\u2069" = [
      { startOffset := 0, endOffset := 1, level := 0 },
      { startOffset := 1, endOffset := 2, level := 1 },
      { startOffset := 2, endOffset := 6, level := 2 },
      { startOffset := 6, endOffset := 7, level := 1 },
      { startOffset := 7, endOffset := 8, level := 0 }
    ] := rfl

/-- CSS Writing Modes 3 §2 & UAX #9 §3.3.4 Rule N1 Law:
    In an RTL paragraph, a neutral character flanked by LTR strong text on both sides
    resolves to LTR level 2. -/
theorem resolveBidiParagraphRuns_neutral_surrounded_by_ltr :
    resolveBidiParagraphRuns "a-b" .rtl = [{ startOffset := 0, endOffset := 3, level := 2 }] := rfl

/-- CSS Writing Modes 3 §2 & UAX #9 §3.3.4 Rule N2 Law:
    In an RTL paragraph, a neutral character flanked by opposite strong directions
    (LTR before, RTL after) resolves to paragraph embedding level 1. -/
theorem resolveBidiParagraphRuns_neutral_between_opposite_dirs :
    resolveBidiParagraphRuns "a-\u05D1" .rtl = [
      { startOffset := 0, endOffset := 1, level := 2 },
      { startOffset := 1, endOffset := 3, level := 1 }
    ] := rfl

/-- CSS Writing Modes 3 §2 & UAX #9: Query bidi level at a given offset. -/
def bidiLevelAtOffset (runs : List BidiLogicalRun) (offset : Nat) : Option Nat :=
  runs.find? (fun r => r.startOffset ≤ offset && offset < r.endOffset) |>.map (·.level)

/-- CSS Writing Modes 3 §2: Changing bidi level of any character requires relayout. -/
def needsRelayoutOnBidiChange (runsOld runsNew : List BidiLogicalRun) (offset : Nat) : Bool :=
  bidiLevelAtOffset runsOld offset != bidiLevelAtOffset runsNew offset

/-- CSS Writing Modes 3 §2.1 & UAX #9: Apply resolved bidi levels to inline collected items,
    splitting items at run boundaries. -/
def segmentInlineText (items : List InlineCollectedItem) (text : String) (baseDir : TextDirection := .ltr) : List InlineCollectedItem :=
  let runs := resolveBidiParagraphRuns text baseDir
  let splits := runs.foldl (fun cur run => (cur.flatMap (splitInlineItem · run.startOffset)).flatMap (splitInlineItem · run.endOffset)) items
  splits.map fun item =>
    match runs.find? (fun r => r.startOffset ≤ item.startOffset && item.endOffset ≤ r.endOffset && (item.startOffset < item.endOffset || item.startOffset < r.endOffset)) with
    | some r => { item with bidiLevel := r.level }
    | none => match runs.find? (fun r => r.endOffset == item.startOffset) with
      | some r => { item with bidiLevel := r.level }
      | none => item

end ChromiumLayout
