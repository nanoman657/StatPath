/-
  docs/chromium-layout/InlineShaping.lean

  Formal model for Blink Inline Node item collection, text shaping,
  and Min/Max size computation
  (`third_party/blink/renderer/core/layout/inline/inline_node.h`,
   `third_party/blink/renderer/core/layout/inline/inline_node.cc`,
   `third_party/blink/renderer/core/layout/inline/line_breaker.cc`).

  Owns:
  - Inline item classification (text, control, atomic inline, open/close tags)
  - InlineNode::CollectInlines DOM flattening and item offset attribution
  - Fixed-width font (Ahem 10px) min/max intrinsic inline sizes calculation
  - Grapheme cluster and combining mark segmentation
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout

/-! ## 1. Inline Item Types & Collection Tokens -/

inductive InlineItemType where
  | text
  | control
  | atomicInline
  | openTag
  | closeTag
  | floating
  | bidiControl
  deriving DecidableEq, Repr, Inhabited

structure InlineCollectedItem where
  itemType : InlineItemType := .text
  startOffset : Nat := 0
  endOffset : Nat := 0
  deriving DecidableEq, Repr, Inhabited

inductive InlineCollectionToken where
  | text (content : String)
  | openTag (tag : String)
  | closeTag
  | atomicInline (widthPx : Nat := 10)
  | br
  deriving DecidableEq, Repr, Inhabited

structure CollectionResult where
  text : String := ""
  items : List InlineCollectedItem := []
  deriving DecidableEq, Repr

/-! ## 2. Flattening and Item Collection (`InlineNode::CollectInlines`) -/

/-- Flatten input inline node tokens into character text and classified inline items. -/
def collectInlines (tokens : List InlineCollectionToken) : CollectionResult :=
  let rec loop (offset : Nat) (accItems : List InlineCollectedItem) (accChars : List Char) :
      List InlineCollectionToken → Nat × List InlineCollectedItem × List Char
    | [] => (offset, accItems, accChars)
    | .text s :: rest =>
      let len := s.length
      let item : InlineCollectedItem := { itemType := .text, startOffset := offset, endOffset := offset + len }
      loop (offset + len) (item :: accItems) (accChars ++ s.toList) rest
    | .openTag _ :: rest =>
      let item : InlineCollectedItem := { itemType := .openTag, startOffset := offset, endOffset := offset }
      loop offset (item :: accItems) accChars rest
    | .closeTag :: rest =>
      let item : InlineCollectedItem := { itemType := .closeTag, startOffset := offset, endOffset := offset }
      loop offset (item :: accItems) accChars rest
    | .atomicInline _ :: rest =>
      let item : InlineCollectedItem := { itemType := .atomicInline, startOffset := offset, endOffset := offset + 1 }
      loop (offset + 1) (item :: accItems) (accChars ++ ['\uFFFC']) rest
    | .br :: rest =>
      let item : InlineCollectedItem := { itemType := .control, startOffset := offset, endOffset := offset + 1 }
      loop (offset + 1) (item :: accItems) (accChars ++ ['\n']) rest
  let (_, revItems, chars) := loop 0 [] [] tokens
  { text := String.ofList chars, items := revItems.reverse }

/-! ## 3. Grapheme Cluster & Combining Mark Segmentation -/

def utf16Length (c : Char) : Nat :=
  if c.val > 0xFFFF then 2 else 1

def isCombiningMark (c : Char) : Bool :=
  c == '\u05B4' || c == '\u0343'

/-- Compute UTF-16 code unit lengths for grapheme clusters respecting combining marks. -/
def clusterUtf16Lengths (cs : List Char) : List Nat :=
  let rec loop (acc : List Nat) (prevLen : Option Nat) : List Char → List Nat
    | [] =>
      match prevLen with
      | some l => (l :: acc).reverse
      | none => acc.reverse
    | c :: rest =>
      if isCombiningMark c then
        match prevLen with
        | some l => loop acc (some (l + utf16Length c)) rest
        | none => loop (utf16Length c :: acc) none rest
      else
        match prevLen with
        | some l => loop (l :: acc) (some (utf16Length c)) rest
        | none => loop acc (some (utf16Length c)) rest
  loop [] none cs

/-- Segment text into grapheme cluster UTF-16 lengths. -/
def graphemeLengths (s : String) : List Nat :=
  clusterUtf16Lengths s.toList

/-! ## 4. Intrinsic Min/Max Size Computation (`InlineNode::ComputeMinMaxSizes`) -/

structure MinMaxSizes where
  minSize : Nat := 0
  maxSize : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Compute min/max content sizes for 10px fixed-width (Ahem) font. -/
def computeMinMaxSizesAhem (tokens : List InlineCollectionToken) : MinMaxSizes :=
  let rec toSegments (curWordLen : Nat) (words : List Nat) (totalChars : Nat) : List InlineCollectionToken → List Nat × Nat
    | [] =>
      let finalWords := if curWordLen > 0 then curWordLen :: words else words
      (finalWords, totalChars)
    | .text s :: rest =>
      let chars := s.toList
      let rec processChars (wLen : Nat) (accW : List Nat) (tot : Nat) : List Char → Nat × List Nat × Nat
        | [] => (wLen, accW, tot)
        | ' ' :: cs =>
          let nextAccW := if wLen > 0 then wLen :: accW else accW
          processChars 0 nextAccW (tot + 1) cs
        | _ :: cs =>
          processChars (wLen + 1) accW (tot + 1) cs
      let (endW, midWords, nextTot) := processChars curWordLen words totalChars chars
      toSegments endW midWords nextTot rest
    | .openTag _ :: rest =>
      toSegments curWordLen words totalChars rest
    | .closeTag :: rest =>
      toSegments curWordLen words totalChars rest
    | .atomicInline wPx :: rest =>
      let wordsAfterPrev := if curWordLen > 0 then curWordLen :: words else words
      let wordsWithAtomic := (wPx / 10) :: wordsAfterPrev
      toSegments 0 wordsWithAtomic (totalChars + (wPx / 10)) rest
    | .br :: rest =>
      let wordsAfterPrev := if curWordLen > 0 then curWordLen :: words else words
      toSegments 0 wordsAfterPrev totalChars rest
  let (wordLengths, totalCharCount) := toSegments 0 [] 0 tokens
  let maxWord := wordLengths.foldl Nat.max 0
  { minSize := maxWord * 10, maxSize := totalCharCount * 10 }

end ChromiumLayout
