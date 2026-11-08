/-
  Mapping.lean: coordinate mapping between a box and its ancestors, written from
  map_coordinates_test.cc and visual_rect_mapping_test.cc (pin 36c121be), not from the C++.

  Module owned by the "mapping" lane. It imports the block lane's `BlockFlow` (box tree and
  fragments), `BlockRelative` (relative insets) unchanged. Lengths are whole pixels (`Int`).

  Section 1/2 content: points in physical border-box coordinates, one `Hop` per containing-block
  step, relative positioning (CSS 2.1 §9.4.3) and the inline-level convention.
-/
import BlockFlow
import BlockRelative

namespace ChromiumLayout
namespace Mapping
open BlockFlow

/-- A point (or offset) in physical coordinates of some box's border box, y growing downward.
    CSS Writing Modes 3 §6.2 (physical dimensions are the coordinate space of mapping). -/
structure Pt where
  x : Int
  y : Int
  deriving DecidableEq, Repr

/-- A hop is the position of a child's border-box origin in its containing block's border-box
    coordinates (CSS 2.1 §8.1 box model, §10.1 containing block). -/
abbrev Hop := Pt

/-- Child-local point to the containing block's coordinates. -/
def Pt.up (h p : Pt) : Pt := ⟨p.x + h.x, p.y + h.y⟩

/-- Containing-block point to the child's local coordinates. -/
def Pt.down (h p : Pt) : Pt := ⟨p.x - h.x, p.y - h.y⟩

/-- Map through a chain of hops listed leaf first (`LocalToAncestorPoint`). -/
def mapUp (hs : List Hop) (p : Pt) : Pt := hs.foldl (fun q h => h.up q) p

/-- Map from the ancestor down the same chain (`AncestorToLocalPoint`). -/
def mapDown (hs : List Hop) (p : Pt) : Pt := hs.foldr (fun h q => h.down q) p

/-- A step of the containing-block chain. A block contributes its fragment offset in its parent
    plus its relative-position insets (CSS 2.1 §9.4.3: the box is shifted by `left`/`top` after
    normal flow). An inline-level object (text, inline box) holds its geometry in the coordinate
    space of its container and contributes no offset, whatever its relative offset. -/
inductive Node where
  | block (parent child : Frag) (rel : Option BlockRelative.Insets := none)
  | inline (rel : Option BlockRelative.Insets := none)

def Node.hop : Node → Hop
  | .block p c r => ⟨c.x - p.x + (r.map (·.left)).getD 0, c.y - p.y + (r.map (·.top)).getD 0⟩
  | .inline _ => ⟨0, 0⟩

/-- The chain of a node list. -/
def chain (ns : List Node) : List Hop := ns.map Node.hop

/-! ## General laws -/

theorem up_down (h p : Pt) : h.down (h.up p) = p := by
  simp [Pt.up, Pt.down]

theorem down_up (h p : Pt) : h.up (h.down p) = p := by
  simp [Pt.up, Pt.down]

/-- Mapping through A then through B equals mapping through the concatenated chain, so mapping to
    an intermediate ancestor and onward equals mapping to the far ancestor directly. -/
theorem mapUp_append (a b : List Hop) (p : Pt) : mapUp (a ++ b) p = mapUp b (mapUp a p) := by
  simp [mapUp, List.foldl_append]

/-- Same for the downward direction. -/
theorem mapDown_append (a b : List Hop) (p : Pt) : mapDown (a ++ b) p = mapDown a (mapDown b p) := by
  simp [mapDown, List.foldr_append]

/-- Mapping a point to an ancestor and back returns it. -/
theorem mapDown_mapUp (hs : List Hop) (p : Pt) : mapDown hs (mapUp hs p) = p := by
  induction hs generalizing p with
  | nil => rfl
  | cons h t ih =>
      simp only [mapUp, mapDown, List.foldl_cons, List.foldr_cons] at *
      rw [ih, up_down]

/-- Mapping a point from the ancestor and back returns it. -/
theorem mapUp_mapDown (hs : List Hop) (p : Pt) : mapUp hs (mapDown hs p) = p := by
  induction hs generalizing p with
  | nil => rfl
  | cons h t ih =>
      simp only [mapUp, mapDown, List.foldl_cons, List.foldr_cons] at *
      rw [down_up]
      exact ih p

/-- Mapping is a translation: the image of a point is the point plus the summed hop offsets. -/
theorem mapUp_eq_add (hs : List Hop) (p : Pt) :
    mapUp hs p = ⟨p.x + (hs.map (·.x)).sum, p.y + (hs.map (·.y)).sum⟩ := by
  induction hs generalizing p with
  | nil => simp [mapUp]
  | cons h t ih =>
      have := ih (h.up p)
      simp only [mapUp, List.foldl_cons] at this ⊢
      rw [this]
      simp [Pt.up, List.map_cons, List.sum_cons]
      omega

/-- An inline-level node ignores its relative offset (the offset is already part of the
    container-space geometry it carries). -/
theorem inline_ignores_rel (r r' : Option BlockRelative.Insets) :
    (Node.inline r).hop = (Node.inline r').hop := rfl

/-- A relatively positioned block moves by exactly its resolved `left`/`top` on top of its
    in-flow offset. -/
theorem block_rel_offset (p c : Frag) (i : BlockRelative.Insets) :
    (Node.block p c (some i)).hop = ⟨c.x - p.x + i.left, c.y - p.y + i.top⟩ := rfl

end Mapping
end ChromiumLayout
