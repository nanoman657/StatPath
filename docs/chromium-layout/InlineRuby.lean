/-
  docs/chromium-layout/InlineRuby.lean

  Formal model for CSS Ruby Annotation Layout Level 1 (CSS Ruby 1)
  and Blink RubyBlockPositionCalculator (`third_party/blink/renderer/core/layout/inline/ruby_utils.h`).
-/
import LayoutTypes
import LayoutInline

namespace ChromiumLayout

/-! ## 1. CSS Ruby 1 Annotation Level Types -/

/-- CSS Ruby 1 §4.1: ruby-position property (over vs under). -/
inductive RubyPosition where
  | over
  | under
  deriving DecidableEq, Repr, Inhabited

/-- CSS Ruby 1 §2.3.1: Ruby level representing base or annotation depth path.
    Base level is represented by the empty list `[]`. -/
abbrev RubyLevel := List Int

/-- CSS Ruby 1 §2.3.1: Check whether a ruby level represents the base text level. -/
def isBaseLevel (lvl : RubyLevel) : Bool :=
  lvl.isEmpty

/-- CSS Ruby 1 §2.3: A ruby column pairing base items with annotation items. -/
structure LogicalRubyColumn where
  startIndex : Nat := 0
  size : Nat := 0
  rubyPosition : RubyPosition := .over
  subColumns : List LogicalRubyColumn := []
  deriving Inhabited

/-- CSS Ruby 1 §2.3: The end index of a logical ruby column in the inline sequence. -/
def LogicalRubyColumn.endIndex (c : LogicalRubyColumn) : Nat :=
  c.startIndex + c.size

/-- CSS Ruby 1 §3.1: A line of ruby annotations at a particular ruby level. -/
structure RubyLine where
  level : RubyLevel := []
  columns : List LogicalRubyColumn := []
  deriving Inhabited

/-- CSS Ruby 1 §2.3.1: Check whether a ruby line is at the base text level. -/
def RubyLine.isBaseLevel (line : RubyLine) : Bool :=
  line.level.isEmpty

/-! ## 2. CSS Ruby 1 §2.3.1 Segment Pairing and Level Grouping -/

/-- CSS Ruby 1 §2.3.1: Check if column a encloses column b in the base inline progression. -/
def encloses (a b : LogicalRubyColumn) : Bool :=
  a.startIndex ≤ b.startIndex && b.endIndex ≤ a.endIndex

/-- CSS Ruby 1 §2.3.1: Compute the annotation depth of a column given enclosing columns on the same side. -/
def computeColumnDepth (pos : RubyPosition) (col : LogicalRubyColumn) (allCols : List LogicalRubyColumn) : Int :=
  let enclosed := allCols.filter (fun c => c.startIndex ≠ col.startIndex && encloses col c && c.rubyPosition == pos)
  let baseDepth : Int := if pos == .under then -1 else 1
  if pos == .under then
    baseDepth - (enclosed.length : Int)
  else
    baseDepth + (enclosed.length : Int)

/-- CSS Ruby 1 §3.1.2: Order depths (under annotations inner-to-outer, then over inner-to-outer). -/
def isDepthLe (d1 d2 : Int) : Bool :=
  if d1 < 0 && d2 ≥ 0 then true
  else if d1 ≥ 0 && d2 < 0 then false
  else if d1 < 0 && d2 < 0 then d2 ≤ d1
  else d1 ≤ d2

/-- CSS Ruby 1 §3.1.2: Lexicographic ordering on ruby levels. -/
def isLevelLe : RubyLevel → RubyLevel → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x ≠ y then isDepthLe x y
    else isLevelLe xs ys

/-- Insert a ruby level in sorted order. -/
def insertLevel (lvl : RubyLevel) : List RubyLevel → List RubyLevel
  | [] => [lvl]
  | x :: xs => if isLevelLe lvl x then lvl :: x :: xs else x :: insertLevel lvl xs

/-- Sort ruby levels by closing order. -/
def sortLevels : List RubyLevel → List RubyLevel
  | [] => []
  | x :: xs => insertLevel x (sortLevels xs)

/-- CSS Ruby 1 §2.3.1: Group columns sharing a parent level into lines by their computed ruby levels. -/
def groupColumnsToLines (parentLevel : RubyLevel) (cols : List LogicalRubyColumn) : List RubyLine :=
  let assignedLevels := cols.map (fun c =>
    let d := computeColumnDepth c.rubyPosition c cols
    (parentLevel ++ [d], c)
  )
  let rawLevels := assignedLevels.foldl (fun acc (lvl, _) => if acc.contains lvl then acc else acc ++ [lvl]) []
  let sortedLevels := sortLevels rawLevels
  sortedLevels.map (fun lvl =>
    let matchingCols := (assignedLevels.filter (fun (l, _) => l == lvl)).map Prod.snd
    { level := lvl, columns := matchingCols }
  )

/-- CSS Ruby 1 §3.1.2: Group a list of ruby columns into ruby lines starting from the base line. -/
def groupLines (cols : List LogicalRubyColumn) : List RubyLine :=
  let baseLine : RubyLine := { level := [], columns := [] }
  if cols.isEmpty then [baseLine]
  else
    let topLines := groupColumnsToLines [] cols
    let subLines := cols.foldl (fun acc col =>
      match col.subColumns with
      | [] => acc
      | subs =>
        let colDepth := computeColumnDepth col.rubyPosition col cols
        let colLevel := [colDepth]
        acc ++ groupColumnsToLines colLevel subs
    ) []
    baseLine :: (topLines ++ subLines)

/-! ## 3. General Laws -/

/-- General Law: LogicalRubyColumn end index is the sum of startIndex and size for all inputs. -/
theorem logicalRubyColumn_endIndex (start sz : Nat) (pos : RubyPosition) (subs : List LogicalRubyColumn) :
    (LogicalRubyColumn.mk start sz pos subs).endIndex = start + sz := by
  rfl

/-- General Law: A RubyLevel is base level if and only if it is empty for all inputs. -/
theorem rubyLevel_isBaseLevel_iff (lvl : RubyLevel) :
    isBaseLevel lvl = true ↔ lvl = [] := by
  dsimp [isBaseLevel]
  cases lvl <;> simp

/-- General Law: A RubyLine is at the base level if and only if its level is empty for all inputs. -/
theorem rubyLine_isBaseLevel_iff (line : RubyLine) :
    line.isBaseLevel = true ↔ line.level = [] := by
  dsimp [RubyLine.isBaseLevel]
  cases line.level <;> simp

end ChromiumLayout
