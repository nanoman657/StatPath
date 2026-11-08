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

def shadowFoo1Style : CounterStyle :=
  { name := "foo", system := .fixed 1, symbols := ["A", "B", "C"] }

def shadowFoo2Style : CounterStyle :=
  { name := "foo", system := .fixed 1, symbols := ["D", "E", "F"] }

/-! ### Test 0: FallbackToTextWhenImagesDisable (`list_marker_test.cc:51`) -/
theorem listMarker_fallbackToTextWhenImagesDisable :
    computeMarkerContent false (some "data:image/gif;base64,R0lGODdhCQAJAKEAAO6C7v8A/6Ag8AAAACwAAAAACQAJAAACFISPaWLhLhh4UNIQG81zswiGIlgAADs=")
      [] "decimal" 1 = .text "1. " := by
  rfl

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

/-! ### Test 8: ModifyShadowDOMWithOwnCounterStyles (`list_marker_test.cc:256`) -/
theorem listMarker_modifyShadowDOMWithOwnCounterStyles :
    -- Document root initial state
    formatScopedCounterValue [[fooStyle]] "decimal" 1 = "1. " ∧
    formatScopedCounterValue [[fooStyle]] "foo" 2 = "X. " ∧
    -- Attach shadow1: does not affect document root
    formatScopedCounterValue [[fooStyle]] "decimal" 1 = "1. " ∧
    formatScopedCounterValue [[fooStyle]] "foo" 2 = "X. " ∧
    formatScopedCounterValue [[shadowFoo1Style], [fooStyle]] "foo" 1 = "A. " ∧
    -- Attach shadow2: does not affect document root or shadow1
    formatScopedCounterValue [[fooStyle]] "decimal" 1 = "1. " ∧
    formatScopedCounterValue [[fooStyle]] "foo" 2 = "X. " ∧
    formatScopedCounterValue [[shadowFoo1Style], [fooStyle]] "foo" 1 = "A. " ∧
    formatScopedCounterValue [[shadowFoo2Style], [fooStyle]] "foo" 1 = "D. " ∧
    -- Remove shadow1: document root and shadow2 remain consistent
    formatScopedCounterValue [[fooStyle]] "decimal" 1 = "1. " ∧
    formatScopedCounterValue [[fooStyle]] "foo" 2 = "X. " ∧
    formatScopedCounterValue [[shadowFoo2Style], [fooStyle]] "foo" 1 = "D. " := by
  decide

/-! ### Test 9: InsideWithFirstLine (`layout_list_item_test.cc:37`) -/
theorem layoutListItem_insideWithFirstLine :
    let marker := buildListMarkerBox .inside (.text "• ")
    marker.position = .inside ∧
    marker.childCount = 1 ∧
    marker.children = [.text "• "] := by
  decide

end ChromiumLayout.TestsInline
