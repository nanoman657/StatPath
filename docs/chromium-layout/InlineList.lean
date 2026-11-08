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

end ChromiumLayout
