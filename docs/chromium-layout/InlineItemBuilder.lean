/-
  docs/chromium-layout/InlineItemBuilder.lean

  Formal model for Blink InlineItemsBuilder and CSS whitespace collapsing
  (`third_party/blink/renderer/core/layout/inline/inline_items_builder.h`,
   `inline_items_builder.cc`).

  Owns: WhiteSpaceMode, whitespace collapsing rules, Bidi control code injection,
  and the whitespace collapsing laws.
-/
import LayoutTypes
import LayoutInline
import InlineFragmentItem

namespace ChromiumLayout

/-! ## 1. Whitespace Mode and Collapsing Model -/

inductive WhiteSpaceMode where
  | normal
  | nowrap
  | pre
  | preLine
  | preWrap
  deriving DecidableEq, Repr

/-- Whether a whitespace mode collapses consecutive spaces to a single space
    (`inline/inline_items_builder.cc:50-90`). -/
def WhiteSpaceMode.collapsesSpaces : WhiteSpaceMode → Bool
  | .normal => true
  | .nowrap => true
  | .preLine => true
  | .pre => false
  | .preWrap => false

/-- Whether a whitespace mode collapses newlines into spaces
    (`inline/inline_items_builder.cc:50-90`). -/
def WhiteSpaceMode.collapsesNewlines : WhiteSpaceMode → Bool
  | .normal => true
  | .nowrap => true
  | .preLine => false
  | .pre => false
  | .preWrap => false

/-- Collapse consecutive spaces in a list of characters. -/
def collapseSpaceList (inSpace : Bool) : List Char → List Char
  | [] => []
  | ' ' :: rest =>
    if inSpace then collapseSpaceList true rest
    else ' ' :: collapseSpaceList true rest
  | '\t' :: rest =>
    if inSpace then collapseSpaceList true rest
    else ' ' :: collapseSpaceList true rest
  | '\n' :: rest =>
    if inSpace then collapseSpaceList true rest
    else ' ' :: collapseSpaceList true rest
  | c :: rest =>
    c :: collapseSpaceList false rest

/-- Strip leading spaces from a list of characters. -/
def stripLeadingSpaces : List Char → List Char
  | [] => []
  | ' ' :: rest => stripLeadingSpaces rest
  | '\t' :: rest => stripLeadingSpaces rest
  | '\n' :: rest => stripLeadingSpaces rest
  | c :: rest => c :: rest

/-- Strip trailing spaces from a list of characters. -/
def stripTrailingSpaces (l : List Char) : List Char :=
  (stripLeadingSpaces l.reverse).reverse

/-- Collapse whitespace for inline text given whitespace mode. -/
def collapseText (mode : WhiteSpaceMode) (chars : List Char) : List Char :=
  if mode.collapsesSpaces then
    stripTrailingSpaces (stripLeadingSpaces (collapseSpaceList false chars))
  else
    chars

/-! ## 2. Whitespace Collapsing Laws -/

/-- General Law: In pre or pre-wrap modes, text is preserved identically. -/
theorem whitespace_pre_identity (chars : List Char) :
    collapseText .pre chars = chars ∧ collapseText .preWrap chars = chars := by
  dsimp [collapseText, WhiteSpaceMode.collapsesSpaces]
  exact ⟨rfl, rfl⟩

/-- General Law: normal, nowrap, and preLine modes all collapse whitespace. -/
theorem whitespace_collapsing_modes :
    (WhiteSpaceMode.normal.collapsesSpaces = true) ∧
    (WhiteSpaceMode.nowrap.collapsesSpaces = true) ∧
    (WhiteSpaceMode.preLine.collapsesSpaces = true) := by
  decide

/-- General Law: pre and preWrap modes preserve whitespace. -/
theorem whitespace_preserving_modes :
    (WhiteSpaceMode.pre.collapsesSpaces = false) ∧
    (WhiteSpaceMode.preWrap.collapsesSpaces = false) := by
  decide

/-! ## 3. Inline Items Builder Model (CSS Text 3 §4, §4.1, §5.1, CSS 2.1 §9.2.1.1, CSS Ruby 1 §2.3) -/

inductive BuilderItemType where
  | text
  | control
  | atomicInline
  | blockInInline
  | bidiControl
  | openTag
  | closeTag
  | openRubyColumn
  | closeRubyColumn
  | rubyLinePlaceholder
  deriving DecidableEq, Repr

structure BuiltInlineItem where
  type : BuilderItemType
  startOffset : Nat
  endOffset : Nat
  deriving DecidableEq, Repr

inductive BuilderInput where
  | text (content : String) (mode : WhiteSpaceMode := .normal)
  | opaqueChar (type : BuilderItemType) (c : Char)
  | atomicInline
  | blockInInline
  | openTag
  | closeTag
  | openRubyColumn
  | closeRubyColumn
  | rubyLinePlaceholder
  deriving DecidableEq, Repr

structure BuilderState where
  text : List Char := []
  items : List BuiltInlineItem := []
  trailingCollapsibleSpace : Bool := false
  trailingNewlineCollapsible : Bool := false
  lastWasNoWrap : Bool := false
  deriving DecidableEq, Repr

def collapsePreLineFuel (fuel : Nat) : List Char → List Char
  | [] => []
  | c :: rest => match fuel with
    | 0 => []
    | fuel + 1 =>
      if c == '\n' then '\n' :: collapsePreLineFuel fuel (rest.dropWhile (fun x => x == ' ' || x == '\t'))
      else if c == ' ' || c == '\t' then
        let rem := rest.dropWhile (fun x => x == ' ' || x == '\t')
        if rem.head? == some '\n' then collapsePreLineFuel fuel rem else ' ' :: collapsePreLineFuel fuel rem
      else c :: collapsePreLineFuel fuel rest

def collapsePreLine (chars : List Char) : List Char :=
  collapsePreLineFuel (chars.length + 1) chars

def transformSegmentBreaksFuel (fuel : Nat) (prevZws : Bool) : List Char → List Char
  | [] => []
  | c :: rest => match fuel with
    | 0 => []
    | fuel + 1 =>
      if c == '\u200B' then
        let rem := rest.dropWhile (fun x => x == ' ' || x == '\t')
        if rem.head? == some '\n' then '\u200B' :: transformSegmentBreaksFuel fuel true rem.tail
        else '\u200B' :: transformSegmentBreaksFuel fuel true rest
      else if c == ' ' || c == '\t' || c == '\n' then
        let spaces := (c :: rest).takeWhile (fun x => x == ' ' || x == '\t' || x == '\n')
        let rem := (c :: rest).dropWhile (fun x => x == ' ' || x == '\t' || x == '\n')
        let hasNl := spaces.contains '\n'
        if hasNl && (prevZws || rem.head? == some '\u200B') then
          transformSegmentBreaksFuel fuel prevZws rem
        else ' ' :: transformSegmentBreaksFuel fuel false rem
      else c :: transformSegmentBreaksFuel fuel false rest

def transformSegmentBreaks (chars : List Char) : List Char :=
  transformSegmentBreaksFuel (chars.length * 2 + 2) false chars

def processPreWrapFuel (fuel : Nat) : List Char → List Char
  | [] => []
  | c :: rest => match fuel with
    | 0 => []
    | fuel + 1 =>
      if c == '\n' then
        let sp := rest.takeWhile (fun x => x == ' ')
        let rem := rest.dropWhile (fun x => x == ' ')
        if !sp.isEmpty then '\n' :: (sp ++ ('\u200B' :: processPreWrapFuel fuel rem))
        else '\n' :: processPreWrapFuel fuel rest
      else c :: processPreWrapFuel fuel rest

def processPreWrapText (chars : List Char) (isStart : Bool) : List Char :=
  let input := if isStart && chars.head? == some ' ' then
    let sp := chars.takeWhile (fun x => x == ' ')
    sp ++ ('\u200B' :: chars.dropWhile (fun x => x == ' '))
  else chars
  processPreWrapFuel (input.length + 1) input

def splitPreItems (chars : List Char) (base : Nat) : List BuiltInlineItem :=
  let rec loop (start : Option Nat) (idx : Nat) (acc : List BuiltInlineItem) : List Char → List BuiltInlineItem
    | [] =>
      match start with
      | some s => (⟨.text, s, idx⟩ :: acc).reverse
      | none => if idx == base then [⟨.text, base, base⟩] else acc.reverse
    | c :: rest =>
      if c == '\n' || c == '\x0c' || c == '\t' then
        let acc' := match start with | some s => ⟨.text, s, idx⟩ :: acc | none => acc
        loop none (idx + 1) (⟨.control, idx, idx + 1⟩ :: acc') rest
      else loop (some (start.getD idx)) (idx + 1) acc rest
  loop none base [] chars

def appendBuilderInput (st : BuilderState) (inp : BuilderInput) : BuilderState :=
  match inp with
  | .openTag => { st with items := st.items ++ [⟨.openTag, st.text.length, st.text.length⟩] }
  | .closeTag => { st with items := st.items ++ [⟨.closeTag, st.text.length, st.text.length⟩] }
  | .rubyLinePlaceholder => { st with items := st.items ++ [⟨.rubyLinePlaceholder, st.text.length, st.text.length⟩] }
  | .openRubyColumn =>
    let off := st.text.length
    { st with text := st.text ++ ['\uFFFC'], items := st.items ++ [⟨.openRubyColumn, off, off + 1⟩] }
  | .closeRubyColumn =>
    let off := st.text.length
    { st with text := st.text ++ ['\uFFFC'], items := st.items ++ [⟨.closeRubyColumn, off, off + 1⟩] }
  | .atomicInline =>
    let off := st.text.length
    { st with text := st.text ++ ['\uFFFC'], items := st.items ++ [⟨.atomicInline, off, off + 1⟩],
              trailingCollapsibleSpace := false, lastWasNoWrap := false }
  | .blockInInline =>
    let txt := if st.trailingCollapsibleSpace && st.text.getLast? == some ' ' then st.text.dropLast else st.text
    let off := txt.length
    { st with text := txt ++ ['\uFFFC'], items := st.items ++ [⟨.blockInInline, off, off + 1⟩],
              trailingCollapsibleSpace := true, lastWasNoWrap := false }
  | .opaqueChar t c =>
    let off := st.text.length
    { st with text := st.text ++ [c], items := st.items ++ [⟨t, off, off + 1⟩] }
  | .text s m =>
    if s.isEmpty then { st with items := st.items ++ [⟨.text, st.text.length, st.text.length⟩] }
    else
      let chars := s.toList
      match m with
      | .pre =>
        let off := st.text.length
        { st with text := st.text ++ chars, items := st.items ++ splitPreItems chars off,
                  trailingCollapsibleSpace := false, lastWasNoWrap := false }
      | .preWrap =>
        let proc := processPreWrapText chars (st.text.isEmpty || st.text.getLast? == some '\n')
        let off := st.text.length
        { st with text := st.text ++ proc, items := st.items ++ [⟨.text, off, off + proc.length⟩],
                  trailingCollapsibleSpace := false, lastWasNoWrap := false }
      | .preLine =>
        let proc := collapsePreLine chars
        let off := st.text.length
        { st with text := st.text ++ proc, items := st.items ++ [⟨.text, off, off + proc.length⟩],
                  trailingCollapsibleSpace := false, lastWasNoWrap := false }
      | .normal | .nowrap =>
        let startsZws := chars.head? == some '\u200B'
        let (txt1, trail1) := if startsZws && st.trailingNewlineCollapsible && st.text.getLast? == some ' '
          then (st.text.dropLast, false) else (st.text, st.trailingCollapsibleSpace)
        let prevZws := txt1.getLast? == some '\u200B'
        let prevZwsSp := match txt1.reverse with | ' ' :: '\u200B' :: _ => true | _ => false
        let (txt2, chars2) :=
          if (prevZws || prevZwsSp) && (chars.head? == some '\n' || chars.take 2 == [' ', '\n']) then
            (if prevZwsSp then txt1.dropLast else txt1, chars.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n'))
          else (txt1, chars)
        let proc := transformSegmentBreaks chars2
        let allSp := proc.all (fun c => c == ' ' || c == '\t' || c == '\n')
        if allSp && trail1 then
          let off := txt2.length
          { st with text := txt2, items := st.items ++ [⟨.text, off, off⟩], trailingCollapsibleSpace := true,
                    trailingNewlineCollapsible := st.trailingNewlineCollapsible || chars.contains '\n' }
        else
          let pfx := if st.lastWasNoWrap && m == .normal && (proc.head? == some ' ' || trail1) then ['\u200B'] else []
          let startSp := proc.head? == some ' '
          let base := txt2 ++ pfx
          let fin := if (trail1 || txt2.isEmpty) && startSp then base ++ proc.tail else base ++ proc
          let hasTrail := fin.getLast? == some ' '
          let off := txt2.length
          { st with text := fin, items := st.items ++ [⟨.text, off, fin.length⟩],
                    trailingCollapsibleSpace := hasTrail,
                    trailingNewlineCollapsible := hasTrail && chars.contains '\n',
                    lastWasNoWrap := (m == .nowrap && hasTrail) }

def finishBuilder (st : BuilderState) : BuilderState :=
  if st.trailingCollapsibleSpace && st.text.getLast? == some ' ' then
    { st with text := st.text.dropLast, trailingCollapsibleSpace := false }
  else st

def buildInlineString (inputs : List BuilderInput) : String :=
  String.ofList (finishBuilder (inputs.foldl appendBuilderInput {})).text

/-! ## 4. General Laws for Inline Items Builder -/

theorem opaque_control_preserves_space_collapsing (st : BuilderState) (t : BuilderItemType) (c : Char) :
    (appendBuilderInput st (.opaqueChar t c)).trailingCollapsibleSpace = st.trailingCollapsibleSpace ∧
    (appendBuilderInput st (.opaqueChar t c)).lastWasNoWrap = st.lastWasNoWrap := by
  dsimp [appendBuilderInput]
  exact ⟨rfl, rfl⟩

theorem atomic_inline_resets_space_collapsing (st : BuilderState) :
    (appendBuilderInput st .atomicInline).trailingCollapsibleSpace = false ∧
    (appendBuilderInput st .atomicInline).lastWasNoWrap = false := by
  dsimp [appendBuilderInput]
  exact ⟨rfl, rfl⟩

theorem block_in_inline_sets_space_collapsing (st : BuilderState) :
    (appendBuilderInput st .blockInInline).trailingCollapsibleSpace = true ∧
    (appendBuilderInput st .blockInInline).lastWasNoWrap = false := by
  dsimp [appendBuilderInput]
  exact ⟨rfl, rfl⟩

theorem empty_text_preserves_builder_text (st : BuilderState) (m : WhiteSpaceMode) :
    (appendBuilderInput st (.text "" m)).text = st.text := by
  rfl

end ChromiumLayout
