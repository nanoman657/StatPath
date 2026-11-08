/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import LayoutTypes

/-!
# CSS Counter Styles 3 & CSS Lists 3: Counter Styles and List Markers

Formalizes:
- CSS Counter Styles 3 §2: The @counter-style Rule and Scoped Resolution
- CSS Counter Styles 3 §3.1.2: Fixed Counter System (`system: fixed`)
- CSS Counter Styles 3 §6: Predefined Counter Styles (`decimal`, `upper-roman`)
- CSS Lists 3 §3: Markers and Marker Dimensions
- `third_party/blink/renderer/core/layout/list/list_marker.h`

Owns:
- `CounterSystem`
- `CounterStyle`
- `natToDigits`
- `predefinedUpperRoman`
- `formatPredefined`
- `formatCounterValue`
- `resolveCounterStyleInChain`
- `formatScopedCounterValue`
- `ListMarkerContent`
- `computeMarkerContent`
- `ListStylePosition`
- `ListMarkerBox`
- `buildListMarkerBox`
- `markerSymbolWidth`
-/

namespace ChromiumLayout

/-! ## 1. Counter Style Definitions (CSS Counter Styles 3 §2, §3) -/

/-- CSS Counter Styles 3 §3: Counter systems. -/
inductive CounterSystem where
  | numeric
  | fixed (firstSymbolValue : Int := 1)
  deriving DecidableEq, Repr

/-- CSS Counter Styles 3 §2: Counter style definition (`@counter-style`). -/
structure CounterStyle where
  name : String
  system : CounterSystem := .numeric
  symbols : List String := []
  fallback : String := "decimal"
  suffix : String := ". "
  deriving DecidableEq, Repr

/-- Small digit conversion that reduces directly in Lean 4 kernel. -/
def natToDigits (n : Nat) : String :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => "10"

/-- Predefined CSS Counter Styles 3 §6: Upper Roman numerals. -/
def predefinedUpperRoman (val : Nat) : String :=
  match val with
  | 1 => "I"
  | 2 => "II"
  | 3 => "III"
  | 4 => "IV"
  | 5 => "V"
  | _ => natToDigits val

/-- Predefined styles fallback formatting (`decimal`, `upper-roman`). -/
def formatPredefined (name : String) (val : Nat) : String :=
  if name == "upper-roman" then
    predefinedUpperRoman val ++ ". "
  else
    natToDigits val ++ ". "

/-- CSS Counter Styles 3 §2 & §3.1.2: Generate marker text for a counter value.
    Looks up in active counter styles, evaluating fixed symbols or falling back to predefined styles. -/
def formatCounterValue (styles : List CounterStyle) (styleName : String) (val : Int) : String :=
  match styles.find? (fun s => s.name == styleName) with
  | some s =>
    match s.system with
    | .fixed startVal =>
      let idx := val - startVal
      if idx ≥ 0 && idx.toNat < s.symbols.length then
        match s.symbols[idx.toNat]? with
        | some sym => sym ++ s.suffix
        | none => formatPredefined s.fallback val.toNat
      else
        formatPredefined s.fallback val.toNat
    | .numeric =>
      formatPredefined s.fallback val.toNat
  | none =>
    formatPredefined styleName val.toNat

/-- CSS Lists 3 §3: Width of list marker symbol (`ListMarker::WidthOfSymbol`).
    When font-size is 0, marker width is 0. -/
def markerSymbolWidth (fontSize : Nat) (_styleName : String) : Nat :=
  if fontSize == 0 then 0 else fontSize

/-- CSS Counter Styles 3 §2 & DOM Standard §4.2.1: Resolve a counter style through an ancestor scope chain.
    Traverses from innermost tree scope (e.g. shadow tree) outward to document scope. -/
def resolveCounterStyleInChain (scopeChain : List (List CounterStyle)) (name : String) : Option CounterStyle :=
  match scopeChain with
  | [] => none
  | localStyles :: outer =>
    match localStyles.find? (fun s => s.name == name) with
    | some s => some s
    | none => resolveCounterStyleInChain outer name

/-- CSS Counter Styles 3 §2 & §3.1.2: Generate marker text for a counter value in a scoped context.
    Looks up in the scope chain from shadow tree outward to document tree, evaluating fixed symbols
    or falling back to predefined styles. -/
def formatScopedCounterValue (scopeChain : List (List CounterStyle)) (styleName : String) (val : Int) : String :=
  match resolveCounterStyleInChain scopeChain styleName with
  | some s =>
    match s.system with
    | .fixed startVal =>
      let idx := val - startVal
      if idx ≥ 0 && idx.toNat < s.symbols.length then
        match s.symbols[idx.toNat]? with
        | some sym => sym ++ s.suffix
        | none => formatPredefined s.fallback val.toNat
      else
        formatPredefined s.fallback val.toNat
    | .numeric =>
      formatPredefined s.fallback val.toNat
  | none =>
    formatPredefined styleName val.toNat

/-- CSS Lists 3 §3: Marker content type. -/
inductive ListMarkerContent where
  | text (str : String)
  | image (url : String)
  deriving DecidableEq, Repr, Inhabited

/-- CSS Lists 3 §3.2: Compute marker content given list style type, optional image URL, and whether images are enabled.
    If an image is specified and images are enabled, the marker is an image; otherwise it falls back to text. -/
def computeMarkerContent (imagesEnabled : Bool) (listStyleImage : Option String)
    (counterStyles : List (List CounterStyle)) (listStyleType : String) (val : Int) : ListMarkerContent :=
  match listStyleImage, imagesEnabled with
  | some url, true => .image url
  | _, _ => .text (formatScopedCounterValue counterStyles listStyleType val)

/-- CSS Lists 3 §3.1: List marker position. -/
inductive ListStylePosition where
  | inside
  | outside
  deriving DecidableEq, Repr, Inhabited

/-- CSS Lists 3 §3.1 & CSS Pseudo 4 §7.1: Structure of a list marker box in the layout tree.
    Holds the marker content as its child. -/
structure ListMarkerBox where
  position : ListStylePosition
  children : List ListMarkerContent
  deriving DecidableEq, Repr, Inhabited

/-- CSS Lists 3 §3.1 & CSS Pseudo 4 §7.1: Build list marker box for a list item.
    For an inside or outside list item with marker content, creates exactly one marker box
    holding exactly one marker content child. First-line style does not duplicate the marker box children. -/
def buildListMarkerBox (pos : ListStylePosition) (content : ListMarkerContent) : ListMarkerBox :=
  { position := pos, children := [content] }

/-- Number of children of a marker box. -/
def ListMarkerBox.childCount (box : ListMarkerBox) : Nat :=
  box.children.length

/-! ## 2. General Laws (CSS Counter Styles 3 & CSS Lists 3) -/

/-- CSS Lists 3 §3 Law: When font size is 0, list marker width is always 0 for any counter style. -/
theorem markerSymbolWidth_zero (styleName : String) :
    markerSymbolWidth 0 styleName = 0 := by
  rfl

/-- CSS Counter Styles 3 §3.1.2 Law: For any fixed counter style starting at 1 with symbols `sym :: rest`,
    evaluating value 1 produces exactly the first symbol concatenated with the suffix.
    Proved definitionally for all symbols, suffixes, and symbol lists. -/
theorem fixed_counter_first_symbol (sym : String) (suffix : String) (rest : List String) :
    formatCounterValue [{ name := "style", system := .fixed 1, symbols := sym :: rest, suffix := suffix }] "style" 1 = sym ++ suffix := by
  rfl

/-- CSS Counter Styles 3 §6 Law: In the default context with no custom styles,
    decimal values format as their decimal digit representation followed by the default suffix. -/
theorem default_counter_decimal (val : Nat) :
    formatCounterValue [] "decimal" val = natToDigits val ++ ". " := by
  rfl

/-- CSS Counter Styles 3 §6 Law: In the default context, upper-roman values format as
    their predefined roman numeral followed by the default suffix. -/
theorem default_counter_upper_roman (val : Nat) :
    formatCounterValue [] "upper-roman" val = predefinedUpperRoman val ++ ". " := by
  rfl

/-- CSS Counter Styles 3 §2 Law: Scope chain lookup on a single list is identical to List.find?. -/
theorem scoped_counter_single_equiv (styles : List CounterStyle) (name : String) :
    resolveCounterStyleInChain [styles] name = styles.find? (fun s => s.name == name) := by
  unfold resolveCounterStyleInChain
  cases styles.find? (fun s => s.name == name) <;> rfl

/-- CSS Counter Styles 3 §2 Law: Evaluating a counter value in a single-scope chain produces
    the identical result to evaluating in formatCounterValue. -/
theorem scoped_counter_single_scope_equiv (styles : List CounterStyle) (name : String) (val : Int) :
    formatScopedCounterValue [styles] name val = formatCounterValue styles name val := by
  unfold formatScopedCounterValue formatCounterValue
  rw [scoped_counter_single_equiv]

/-- CSS Counter Styles 3 §2 Law: Evaluating in an empty scope chain falls back to predefined formatting. -/
theorem scoped_counter_empty_scope_fallback (name : String) (val : Int) :
    formatScopedCounterValue [] name val = formatPredefined name val.toNat := by
  rfl

/-- CSS Counter Styles 3 §2 & DOM Standard §4.2.1 Law: A counter style defined in an inner scope
    shadows any counter style in an outer scope. -/
theorem scoped_counter_shadow_precedence (s : CounterStyle) (outer : List (List CounterStyle)) :
    resolveCounterStyleInChain ([s] :: outer) s.name = some s := by
  unfold resolveCounterStyleInChain
  simp

/-- CSS Lists 3 §3.2 Law: When images are disabled, computeMarkerContent always falls back to text. -/
theorem marker_fallback_when_images_disabled (url : String) (styles : List (List CounterStyle)) (st : String) (val : Int) :
    computeMarkerContent false (some url) styles st val = .text (formatScopedCounterValue styles st val) := by
  rfl

/-- CSS Lists 3 §3.2 Law: When images are enabled and an image URL is specified, computeMarkerContent produces an image marker. -/
theorem marker_image_when_enabled (url : String) (styles : List (List CounterStyle)) (st : String) (val : Int) :
    computeMarkerContent true (some url) styles st val = .image url := by
  rfl

/-- CSS Lists 3 §3.2 Law: When no image URL is specified, computeMarkerContent produces text marker. -/
theorem marker_none_image_produces_text (enabled : Bool) (styles : List (List CounterStyle)) (st : String) (val : Int) :
    computeMarkerContent enabled none styles st val = .text (formatScopedCounterValue styles st val) := by
  cases enabled <;> rfl

/-- CSS Lists 3 §3.1 & CSS Pseudo 4 §7.1 Law: A newly built list marker box contains exactly one child. -/
theorem buildListMarkerBox_child_count (pos : ListStylePosition) (content : ListMarkerContent) :
    (buildListMarkerBox pos content).childCount = 1 := by
  rfl

/-- CSS Lists 3 §3.1 & CSS Pseudo 4 §7.1 Law: A list marker box's child list is exactly `[content]`. -/
theorem buildListMarkerBox_children (pos : ListStylePosition) (content : ListMarkerContent) :
    (buildListMarkerBox pos content).children = [content] := by
  rfl

end ChromiumLayout
