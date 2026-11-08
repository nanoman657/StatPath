/-
Copyright 2024 The Chromium Authors
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file.
-/
import InlineList

namespace ChromiumLayout.TestsInline

open ChromiumLayout

/-!
# Tests for List Markers and Counter Styles

Corresponds to `core/layout/list/list_marker_test.cc`.
-/

def fooStyle : CounterStyle :=
  { name := "foo", system := .fixed 1, symbols := ["W", "X", "Y", "Z"] }

def barStyle : CounterStyle :=
  { name := "bar", system := .fixed 1, symbols := ["A", "B", "C"] }

def upperRomanOverride : CounterStyle :=
  { name := "upper-roman", system := .fixed 1, symbols := ["A", "B", "C"] }

def fooOverride : CounterStyle :=
  { name := "foo", system := .fixed 1, symbols := ["A", "B", "C"] }

/-! ### Test 1: AddCounterStyle (`list_marker_test.cc:71`) -/
theorem listMarker_addCounterStyle :
    formatCounterValue [fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [fooStyle] "foo" 2 = "X. " ∧
    formatCounterValue [fooStyle] "bar" 3 = "3. " ∧
    formatCounterValue [barStyle, fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [barStyle, fooStyle] "foo" 2 = "X. " ∧
    formatCounterValue [barStyle, fooStyle] "bar" 3 = "C. " := by
  decide

/-! ### Test 2: RemoveCounterStyle (`list_marker_test.cc:105`) -/
theorem listMarker_removeCounterStyle :
    formatCounterValue [fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [fooStyle] "foo" 2 = "X. " ∧
    formatCounterValue [] "decimal" 1 = "1. " ∧
    formatCounterValue [] "foo" 2 = "2. " := by
  decide

/-! ### Test 3: OverridePredefinedCounterStyle (`list_marker_test.cc:135`) -/
theorem listMarker_overridePredefinedCounterStyle :
    formatCounterValue [] "decimal" 1 = "1. " ∧
    formatCounterValue [] "upper-roman" 2 = "II. " ∧
    formatCounterValue [upperRomanOverride] "decimal" 1 = "1. " ∧
    formatCounterValue [upperRomanOverride] "upper-roman" 2 = "B. " := by
  decide

/-! ### Test 4: RemoveOverrideOfPredefinedCounterStyle (`list_marker_test.cc:160`) -/
theorem listMarker_removeOverrideOfPredefinedCounterStyle :
    formatCounterValue [upperRomanOverride] "decimal" 1 = "1. " ∧
    formatCounterValue [upperRomanOverride] "upper-roman" 2 = "B. " ∧
    formatCounterValue [] "decimal" 1 = "1. " ∧
    formatCounterValue [] "upper-roman" 2 = "II. " := by
  decide

/-! ### Test 5: OverrideSameScopeCounterStyle (`list_marker_test.cc:190`) -/
theorem listMarker_overrideSameScopeCounterStyle :
    formatCounterValue [fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [fooStyle] "foo" 2 = "X. " ∧
    formatCounterValue [fooOverride, fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [fooOverride, fooStyle] "foo" 2 = "B. " := by
  decide

/-! ### Test 6: RemoveOverrideOfSameScopeCounterStyle (`list_marker_test.cc:220`) -/
theorem listMarker_removeOverrideOfSameScopeCounterStyle :
    formatCounterValue [fooOverride, fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [fooOverride, fooStyle] "foo" 2 = "B. " ∧
    formatCounterValue [fooStyle] "decimal" 1 = "1. " ∧
    formatCounterValue [fooStyle] "foo" 2 = "X. " := by
  decide

/-! ### Test 7: WidthOfSymbolForFontSizeZero (`list_marker_test.cc:335`) -/
theorem listMarker_widthOfSymbolForFontSizeZero :
    markerSymbolWidth 0 "disc" = 0 := by
  rfl

end ChromiumLayout.TestsInline
