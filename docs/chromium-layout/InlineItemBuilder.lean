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

-- CSS Text 3 §4.1 White Space Processing
/-- CSS Text 3 §4.1: Determine whether inline text undergoes any character or length modification
    under whitespace collapsing. When the collapsed text is identical in length and characters
    to the source text, the layout engine shares the source DOM string buffer directly. -/
def canShareInlineTextContent (mode : WhiteSpaceMode) (chars : List Char) : Bool :=
  collapseText mode chars == chars

/-- CSS Text 3 §4.1 Law: In pre mode, any text preserves all characters and its sharing predicate
    evaluates to equality with the source characters. -/
theorem canShareInlineTextContent_pre (chars : List Char) :
    canShareInlineTextContent .pre chars = (chars == chars) := rfl

/-- CSS Text 3 §4.1 Law: In pre-wrap mode, any text preserves all characters and its sharing predicate
    evaluates to equality with the source characters. -/
theorem canShareInlineTextContent_preWrap (chars : List Char) :
    canShareInlineTextContent .preWrap chars = (chars == chars) := rfl

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

/-- CSS Text 3 §5.1 Law:
    Leading preserved space sequences in pre-wrap generate a break opportunity (zero-width space). -/
theorem processPreWrapText_leading_space_break_opportunity :
    processPreWrapText [' ', 'a'] true = [' ', '\u200B', 'a'] := rfl

/-- CSS Text 3 §5.1 Law:
    Preserved spaces not at line start do not generate a break opportunity. -/
theorem processPreWrapText_midline_space_no_break_opportunity :
    processPreWrapText [' ', 'a'] false = [' ', 'a'] := rfl

theorem empty_text_preserves_builder_text (st : BuilderState) (m : WhiteSpaceMode) :
    (appendBuilderInput st (.text "" m)).text = st.text := by
  rfl

/-! ## 5. DOM CharacterData Mutations and Incremental Invalidation
    (DOM Standard §5.3, CSS Text 3 §4.1, CSS 2.1 §9.2.2) -/

/-- DOM CharacterData mutation operations (DOM Standard §5.3, CSS Text 3 §4.1). -/
inductive CharacterDataMutation where
  | append (data : String)
  | delete (offset : Nat) (count : Nat)
  | insert (offset : Nat) (data : String)
  | replace (offset : Nat) (count : Nat) (data : String)
  | set (data : String)
  deriving DecidableEq, Repr

/-- Apply a DOM CharacterData mutation to an input string (DOM Standard §5.3). -/
def applyCharacterDataMutation (s : String) : CharacterDataMutation → String
  | .append data => s ++ data
  | .delete offset count =>
    let chars := s.toList
    String.ofList (chars.take offset ++ chars.drop (offset + count))
  | .insert offset data =>
    let chars := s.toList
    String.ofList (chars.take offset ++ data.toList ++ chars.drop offset)
  | .replace offset count data =>
    let chars := s.toList
    String.ofList (chars.take offset ++ data.toList ++ chars.drop (offset + count))
  | .set data => data

/-- CSS 2.1 §9.2.2 & CSS Text 3 §4.1: Whether a DOM text node generates an inline LayoutObject.
    An empty text node produces no layout object. -/
def textLayoutObjectNeeded (text : String) : Bool :=
  text != ""

/-- CSS Text 3 §4.1 & Blink incremental layout invalidation:
    `setData` invalidates the entire inline node collection, requiring full recollection.
    Incremental mutations (`append`, `delete`, `insert`, `replace`) can relocate items. -/
def mutationNeedsCollectInlines : CharacterDataMutation → Bool
  | .set _ => true
  | _ => false

/-- Invalidation status for incremental text mutations (Blink layout_text_test.cc:1528). -/
structure TextMutationInvalidation where
  needsCollectInlines : Bool
  forceReattachLayoutTree : Bool := false
  deriving DecidableEq, Repr

/-- Compute layout invalidation for DOM text changes
    (CSS Text 3 §4.1 & Blink layout_text_test.cc:1528, 1612). -/
def computeTextMutationInvalidation (op : CharacterDataMutation) (isFirstLetterBoundaryChange : Bool := false) :
    TextMutationInvalidation :=
  { needsCollectInlines := mutationNeedsCollectInlines op,
    forceReattachLayoutTree := isFirstLetterBoundaryChange }

/-- Layout text item representation for Blink `GetItemsAsString`
    (CSS Text 3 §4.1 & Blink layout_text_test.cc:104). -/
structure LayoutTextItem where
  isTarget : Bool
  text : String
  shapeStart : Nat
  shapeLength : Nat
  numGlyphs : Option Nat := none
  snappedWidth : Option Nat := none
  hasShapeResult : Bool := true
  deriving DecidableEq, Repr

/-- Format an inline text item as a string matching Blink `GetItemsAsString`
    (CSS Text 3 §4.1 & Blink layout_text_test.cc:104). -/
def formatLayoutTextItem (item : LayoutTextItem) : String :=
  let pfx := if item.isTarget then "*" else ""
  let shapeStr :=
    if !item.hasShapeResult then ""
    else
      let glyphStr := match item.numGlyphs with | some g => s!" #glyphs={g}" | none => ""
      let widthStr := match item.snappedWidth with | some w => s!" width={w}" | none => ""
      s!", ShapeResult={item.shapeStart}+{item.shapeLength}{glyphStr}{widthStr}"
  s!"{pfx}{'{'}'{item.text}'{shapeStr}{'}'}\n"

/-- Format a list of inline text items as a string matching Blink `GetItemsAsString`. -/
def formatLayoutTextItems (items : List LayoutTextItem) : String :=
  String.join (items.map formatLayoutTextItem)

/-- CSS Text 3 §4.1.1 Phase I: Collapsing and Transformation & DOM Standard §5.3:
    Mutate a single text node and collapse whitespace. -/
def mutateAndCollapseText (mode : WhiteSpaceMode) (text : String) (op : CharacterDataMutation) : String :=
  String.ofList (collapseText mode (applyCharacterDataMutation text op).toList)

/-! ## 6. General Laws for DOM CharacterData Mutations and Invalidation -/

/-- General Law (DOM Standard §5.3):
    Appending data to string `s` yields `s ++ data`. -/
theorem applyCharacterDataMutation_append (s data : String) :
    applyCharacterDataMutation s (.append data) = s ++ data := rfl

/-- General Law (DOM Standard §5.3):
    Setting data overrides string `s` with `data`. -/
theorem applyCharacterDataMutation_set (s data : String) :
    applyCharacterDataMutation s (.set data) = data := rfl

/-- General Law (CSS 2.1 §9.2.2 & CSS Text 3 §4.1):
    Empty text node does not generate a LayoutObject. -/
theorem textLayoutObjectNeeded_empty :
    textLayoutObjectNeeded "" = false := rfl

/-- General Law (CSS Text 3 §4.1):
    `setData` always sets `needsCollectInlines` for full recollection. -/
theorem mutationNeedsCollectInlines_set (data : String) :
    mutationNeedsCollectInlines (.set data) = true := rfl

/-- General Law (CSS Text 3 §4.1):
    Incremental append does not trigger full recollection. -/
theorem mutationNeedsCollectInlines_append (data : String) :
    mutationNeedsCollectInlines (.append data) = false := rfl

/-- General Law (CSS Text 3 §4.1):
    Incremental delete does not trigger full recollection. -/
theorem mutationNeedsCollectInlines_delete (off cnt : Nat) :
    mutationNeedsCollectInlines (.delete off cnt) = false := rfl

/-- General Law (CSS Text 3 §4.1):
    Incremental insert does not trigger full recollection. -/
theorem mutationNeedsCollectInlines_insert (off : Nat) (data : String) :
    mutationNeedsCollectInlines (.insert off data) = false := rfl

/-- General Law (CSS Text 3 §4.1):
    Incremental replace does not trigger full recollection. -/
theorem mutationNeedsCollectInlines_replace (off cnt : Nat) (data : String) :
    mutationNeedsCollectInlines (.replace off cnt data) = false := rfl

/-- General Law:
    First letter boundary change forces reattachment of the layout tree. -/
theorem computeTextMutationInvalidation_reattach (op : CharacterDataMutation) :
    (computeTextMutationInvalidation op true).forceReattachLayoutTree = true := rfl

-- CSS Writing Modes 3 §2.4 Bidi Embedding Breaks
/-- CSS Writing Modes 3 §2.4: Decompose pre-formatted visual bidi text containing forced line breaks
    into layout inline items, popping and restoring bidi controls across each newline. -/
def buildVisualBidiTextItems (off : Nat) : List String → List BuiltInlineItem
  | [] => []
  | [s] => [⟨.text, off, off + s.length⟩]
  | s :: rest =>
    let e := off + s.length
    ⟨.text, off, e⟩ :: ⟨.bidiControl, e, e + 1⟩ :: ⟨.control, e + 1, e + 2⟩ :: ⟨.bidiControl, e + 2, e + 3⟩ ::
      buildVisualBidiTextItems (e + 3) rest

/-- CSS Writing Modes 3 §2.4 Law: Two text segments separated by a forced newline produce
    5 inline items: [text, bidiControl, control, bidiControl, text]. -/
theorem buildVisualBidiTextItems_two_segments (off : Nat) (s1 s2 : String) :
    (buildVisualBidiTextItems off [s1, s2]).map (·.type) =
      [.text, .bidiControl, .control, .bidiControl, .text] := by
  dsimp [buildVisualBidiTextItems]
  rfl

-- CSS Text 3 §2.1 Full-width Transform & CSS Text 3 §4.1 White Space Processing
/-- CSS Text 3 §2.1: Transform ASCII space to full-width ideographic space U+3000. -/
def transformFullWidthSpace (c : Char) : Char :=
  if c == ' ' then '\u3000' else c

/-- CSS Text 3 §4.1 & §2.1: Collapsed text length across adjacent inline elements with optional
    full-width transformation. Two adjacent collapsible spaces collapse into one. -/
def collapsedInlineBoundaryLength (l1 l2 : Nat) (trail lead : Bool) : Nat :=
  if trail && lead then l1 + l2 - 1 else l1 + l2

/-- CSS Text 3 §4.1 Law: Adjacent collapsible spaces across inline elements collapse into a single space. -/
theorem collapsedInlineBoundaryLength_collapse (l1 l2 : Nat) :
    collapsedInlineBoundaryLength l1 l2 true true = l1 + l2 - 1 := rfl

/-- CSS Text 3 §4.1 Law: When neither boundary has collapsible spaces, total length is preserved. -/
theorem collapsedInlineBoundaryLength_no_collapse (l1 l2 : Nat) :
    collapsedInlineBoundaryLength l1 l2 false false = l1 + l2 := rfl

-- CSS 2.1 §12.1 & CSS Lists 3 §3: Generated Content Pseudo-Elements
/-- CSS 2.1 §12.1 & CSS Lists 3 §3: LayoutText generated by CSS pseudo-elements (::before, ::after, ::marker)
    originates from stylesheet style rules and has no underlying DOM Text node.
    Its original text is empty while its rendered/transformed text is non-empty. -/
def isGeneratedPseudoText (hasDomNode : Bool) (transformedLen : Nat) : Bool :=
  !hasDomNode && transformedLen > 0

/-- CSS 2.1 §12.1 & CSS Lists 3 §3 Law: Any pseudo-element with non-zero transformed text
    and no DOM node satisfies isGeneratedPseudoText. -/
theorem isGeneratedPseudoText_pseudo (len : Nat) :
    isGeneratedPseudoText false (len + 1) = true := rfl

end ChromiumLayout
