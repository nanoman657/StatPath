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

end ChromiumLayout
