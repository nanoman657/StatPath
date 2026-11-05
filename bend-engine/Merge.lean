/-!
# Merge.lean: the learning-data merge of src/engine/merge.ts

This file models `bend-engine/merge.bend` function by function, with the same algorithm:
each map is a list of entries, strictly increasing by key, and a key in both maps is combined.
Lean 4.34.0, core only. Every step is proved; there are no placeholder proofs.

What is proved here, for sorted (canonical) inputs:

* lessons and XP per day: `merge a b = merge b a`, and `merge a a = a`; the XP total is
  commutative too;
* SRS cards: `merge a a = a`; `merge a b = merge b a` is false, by two counterexamples; so the
  merged learning state is not commutative either (the lessons and XP parts are).

The Bend code is a transcription of the definitions below. The correspondence is checked by
`tests/merge_bend.test.ts`, which compares the compiled Bend merge with `mergeProgress` on random
states. It is not proved here. The key order is assumed to be the order of `String.cmp`, which the
same test file checks against JavaScript's string order.
-/

namespace BendMerge

/-! ## The model -/

/-- The three-way result of a comparison: Bend's `Cmp`. -/
inductive Cmp where
  | lt
  | eq
  | gt
  deriving DecidableEq

/-- The order of two keys: merge.bend's `skey_cmp`. -/
def skeyCmp (a b : String) : Cmp :=
  if a < b then .lt else if a = b then .eq else .gt

/-- The order of two numbers: `Nat.cmp` in Bend. -/
def natCmp (a b : Nat) : Cmp :=
  if a < b then .lt else if a = b then .eq else .gt

/-- An entry of a map: a key and the value stored under it. -/
structure Entry (α : Type) where
  key : String
  val : α
  deriving DecidableEq

/-- The combined value of a key in the first map (`x`) and in the second (`y`). -/
def combOpt {α : Type} (comb : α → α → α) : Option α → Option α → Option α
  | some v, some w => some (comb v w)
  | some v, none => some v
  | none, some w => some w
  | none, none => none

/-- The value stored under `k`: that of the first entry with key `k`. -/
def lookup {α : Type} : List (Entry α) → String → Option α
  | [], _ => none
  | h :: t, k => if h.key = k then some h.val else lookup t k

/-- Strictly increasing keys. -/
def Sorted {α : Type} : List (Entry α) → Prop
  | [] => True
  | h :: t => (∀ x ∈ t, h.key < x.key) ∧ Sorted t

/-- The comparison `c` of `e` with `h` agrees with the keys. -/
def ConsOK {α : Type} : Cmp → Entry α → Entry α → Prop
  | .lt, e, h => e.key < h.key
  | .eq, e, h => e.key = h.key
  | .gt, e, h => h.key < e.key

/-- Insert `e` into `h :: t`, where `c` is the comparison of `e` with `h` and `t` is the rest after
`h`. The list comes first, as in `lins_c` of merge.bend. A key in both is combined as
`comb h.val e.val`: the first map's value first. -/
def insC {α : Type} (comb : α → α → α) : List (Entry α) → Cmp → Entry α → Entry α → List (Entry α)
  | [], .lt, e, h => [e, h]
  | [], .eq, e, h => [⟨h.key, comb h.val e.val⟩]
  | [], .gt, e, h => [h, e]
  | h2 :: t2, .lt, e, h => e :: h :: h2 :: t2
  | h2 :: t2, .eq, e, h => ⟨h.key, comb h.val e.val⟩ :: h2 :: t2
  | h2 :: t2, .gt, e, h => h :: insC comb t2 (skeyCmp e.key h2.key) e h2

/-- Insert one entry into a map: `lins` of merge.bend. -/
def ins {α : Type} (comb : α → α → α) (e : Entry α) : List (Entry α) → List (Entry α)
  | [] => [e]
  | h :: t => insC comb t (skeyCmp e.key h.key) e h

/-- Insert every entry of `xs` into `acc`: `lfold` of merge.bend. -/
def fold {α : Type} (comb : α → α → α) : List (Entry α) → List (Entry α) → List (Entry α)
  | [], acc => acc
  | h :: t, acc => fold comb t (ins comb h acc)

/-- The merge of two maps: the first map's entries, then the second's, combined per key. -/
def mergeMap {α : Type} (comb : α → α → α) (a b : List (Entry α)) : List (Entry α) :=
  fold comb b (fold comb a [])

/-- A lesson's progress: `LessonProgress` in merge.ts. -/
structure Lesson where
  crowns : Nat
  attempts : Nat
  best : Nat
  played : Nat
  deriving DecidableEq, Repr

/-- `mergeLesson`: the larger value of each field. -/
def lpMax (a b : Lesson) : Lesson :=
  ⟨max a.crowns b.crowns, max a.attempts b.attempts, max a.best b.best, max a.played b.played⟩

/-- An SRS card: `SrsCard` in merge.ts. `last` is `lastReview`; `none` is an absent one. -/
structure Card where
  id : String
  lessonId : String
  interval : Nat
  ease : Nat
  due : Nat
  lapses : Nat
  reps : Nat
  last : Option Nat
  deriving DecidableEq, Repr

/-- The review time as `mergeCard` reads it: an absent one counts as 0. -/
def lastOr0 : Option Nat → Nat
  | none => 0
  | some x => x

/-- The card that `mergeCard` keeps, given the three comparisons. A full tie keeps `a`. -/
def cardPick (cLast cReps cDue : Cmp) (a b : Card) : Card :=
  match cLast with
  | .lt => b
  | .gt => a
  | .eq =>
    match cReps with
    | .lt => b
    | .gt => a
    | .eq =>
      match cDue with
      | .lt => b
      | .gt => a
      | .eq => a

/-- `mergeCard(a, b)`: the later review, then more reps, then the later due date, else `a`. -/
def cardMerge (a b : Card) : Card :=
  cardPick (natCmp (lastOr0 a.last) (lastOr0 b.last)) (natCmp a.reps b.reps)
    (natCmp a.due b.due) a b

/-- The learning data of one copy: lessons, SRS cards and XP per day. -/
structure State where
  lessons : List (Entry Lesson)
  srs : List (Entry Card)
  xp : List (Entry Nat)

/-- The learning data of two copies merged, map by map. -/
def mergeState (a b : State) : State :=
  ⟨mergeMap lpMax a.lessons b.lessons, mergeMap cardMerge a.srs b.srs,
    mergeMap Nat.max a.xp b.xp⟩

/-- The total XP: the sum of the day values (`xsum` of merge.bend). -/
def xsum : List (Entry Nat) → Nat
  | [] => 0
  | h :: t => h.val + xsum t

/-! ## Facts about the order on keys -/

theorem lt_ne {a b : String} (h : a < b) : a ≠ b := by
  intro e
  subst e
  exact String.lt_irrefl _ h

theorem lt_ne' {a b : String} (h : a < b) : b ≠ a := by
  intro e
  subst e
  exact String.lt_irrefl _ h

theorem key_tri (a b : String) : a < b ∨ a = b ∨ b < a :=
  Std.lt_trichotomy a b

theorem skeyCmp_lt {a b : String} (h : a < b) : skeyCmp a b = .lt := by
  simp [skeyCmp, h]

theorem skeyCmp_eq {a b : String} (h : a = b) : skeyCmp a b = .eq := by
  subst h
  simp [skeyCmp, String.lt_irrefl]

theorem skeyCmp_gt {a b : String} (h : b < a) : skeyCmp a b = .gt := by
  have hn : ¬ a < b := fun hab => String.lt_asymm hab h
  have hne : ¬ a = b := fun e => lt_ne h e.symm
  simp [skeyCmp, hn, hne]

theorem skey_ok {α : Type} (e h : Entry α) : ConsOK (skeyCmp e.key h.key) e h := by
  rcases key_tri e.key h.key with h1 | h1 | h1
  · rw [skeyCmp_lt h1]
    exact h1
  · rw [skeyCmp_eq h1]
    exact h1
  · rw [skeyCmp_gt h1]
    exact h1

/-! ## Lookup -/

theorem lookup_cons_eq {α : Type} (h : Entry α) (t : List (Entry α)) {k : String}
    (hk : h.key = k) : lookup (h :: t) k = some h.val := by
  simp [lookup, hk]

theorem lookup_cons_ne {α : Type} (h : Entry α) (t : List (Entry α)) {k : String}
    (hk : h.key ≠ k) : lookup (h :: t) k = lookup t k := by
  simp [lookup, hk]

theorem lookup_none_of {α : Type} : ∀ (L : List (Entry α)) (k : String),
    (∀ y ∈ L, y.key ≠ k) → lookup L k = none
  | [], _, _ => rfl
  | h :: t, k, hL => by
    rw [lookup_cons_ne h t (hL h List.mem_cons_self)]
    exact lookup_none_of t k (fun y hy => hL y (List.mem_cons_of_mem h hy))

theorem sorted_singleton {α : Type} (e : Entry α) : Sorted [e] :=
  ⟨fun x hx => by simp at hx, trivial⟩

theorem combOpt_none_right {α : Type} (comb : α → α → α) (x : Option α) :
    combOpt comb x none = x := by
  cases x <;> rfl

theorem combOpt_none_left {α : Type} (comb : α → α → α) (y : Option α) :
    combOpt comb none y = y := by
  cases y <;> rfl

theorem combOpt_comm {α : Type} (comb : α → α → α) (hc : ∀ v w, comb v w = comb w v)
    (x y : Option α) : combOpt comb x y = combOpt comb y x := by
  cases x <;> cases y <;> simp [combOpt, hc]

theorem combOpt_self {α : Type} (comb : α → α → α) (hi : ∀ v, comb v v = v) (x : Option α) :
    combOpt comb x x = x := by
  cases x <;> simp [combOpt, hi]

/-! ## Insertion -/

/-- The keys of `insC`'s result are the keys of the list with `e` added (or combined into `h`). -/
theorem insC_mem {α : Type} (comb : α → α → α) (t : List (Entry α)) :
    ∀ (c : Cmp) (e h x : Entry α), x ∈ insC comb t c e h →
      x.key = e.key ∨ ∃ y ∈ h :: t, y.key = x.key := by
  induction t with
  | nil =>
    intro c e h x hx
    cases c
    · have hx' : x ∈ [e, h] := hx
      rcases List.mem_cons.mp hx' with hxe | hxh
      · exact Or.inl (congrArg Entry.key hxe)
      · have hxh' : x = h := List.mem_singleton.mp hxh
        exact Or.inr ⟨h, List.mem_cons_self, congrArg Entry.key hxh'.symm⟩
    · have hx' : x ∈ [⟨h.key, comb h.val e.val⟩] := hx
      have hxe : x = ⟨h.key, comb h.val e.val⟩ := List.mem_singleton.mp hx'
      exact Or.inr ⟨h, List.mem_cons_self, (congrArg Entry.key hxe).symm⟩
    · have hx' : x ∈ [h, e] := hx
      rcases List.mem_cons.mp hx' with hxh | hxe
      · have hxh' : x = h := hxh
        exact Or.inr ⟨h, List.mem_cons_self, congrArg Entry.key hxh'.symm⟩
      · exact Or.inl (congrArg Entry.key (List.mem_singleton.mp hxe))
  | cons h2 t2 ih =>
    intro c e h x hx
    cases c
    · have hx' : x ∈ e :: h :: h2 :: t2 := hx
      rcases List.mem_cons.mp hx' with hxe | hx''
      · exact Or.inl (congrArg Entry.key hxe)
      rcases List.mem_cons.mp hx'' with hxh | hx3
      · have hxh' : x = h := hxh
        exact Or.inr ⟨h, List.mem_cons_self, congrArg Entry.key hxh'.symm⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem h hx3, rfl⟩
    · have hx' : x ∈ ⟨h.key, comb h.val e.val⟩ :: h2 :: t2 := hx
      rcases List.mem_cons.mp hx' with hxe | hx3
      · exact Or.inr ⟨h, List.mem_cons_self, (congrArg Entry.key hxe).symm⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem h hx3, rfl⟩
    · have hx' : x ∈ h :: insC comb t2 (skeyCmp e.key h2.key) e h2 := hx
      rcases List.mem_cons.mp hx' with hxh | hx3
      · have hxh' : x = h := hxh
        exact Or.inr ⟨h, List.mem_cons_self, congrArg Entry.key hxh'.symm⟩
      · rcases ih (skeyCmp e.key h2.key) e h2 x hx3 with hxe | ⟨y, hy, hyx⟩
        · exact Or.inl hxe
        · exact Or.inr ⟨y, List.mem_cons_of_mem h hy, hyx⟩

/-- `insC` keeps the keys strictly increasing and gives the lookup of the inserted map. -/
theorem insC_spec {α : Type} (comb : α → α → α) (t : List (Entry α)) :
    ∀ (c : Cmp) (e h : Entry α), Sorted (h :: t) → ConsOK c e h →
      Sorted (insC comb t c e h) ∧
      ∀ k, lookup (insC comb t c e h) k =
        (if e.key = k then combOpt comb (lookup (h :: t) k) (some e.val) else lookup (h :: t) k) := by
  induction t with
  | nil =>
    intro c e h hs hc
    cases c
    · refine ⟨?_, fun k => ?_⟩
      · show Sorted [e, h]
        exact ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hc, sorted_singleton h⟩
      · show lookup [e, h] k = (if e.key = k then combOpt comb (lookup [h] k) (some e.val)
          else lookup [h] k)
        by_cases hek : e.key = k
        · have hl : lookup [h] k = none := lookup_none_of [h] k (fun y hy => by
            rw [List.mem_singleton.mp hy]
            exact fun hh => lt_ne' hc (hh.trans hek.symm))
          rw [if_pos hek, lookup_cons_eq e [h] hek, hl, combOpt_none_left]
        · rw [if_neg hek, lookup_cons_ne e [h] hek]
    · refine ⟨?_, fun k => ?_⟩
      · show Sorted [⟨h.key, comb h.val e.val⟩]
        exact sorted_singleton _
      · show lookup [⟨h.key, comb h.val e.val⟩] k = (if e.key = k then
          combOpt comb (lookup [h] k) (some e.val) else lookup [h] k)
        have hEq : e.key = h.key := hc
        by_cases hek : e.key = k
        · have hhk : h.key = k := hEq.symm.trans hek
          rw [if_pos hek, lookup_cons_eq (⟨h.key, comb h.val e.val⟩ : Entry α) [] hhk,
            lookup_cons_eq h [] hhk]
          rfl
        · have hhk : h.key ≠ k := fun hh => hek (hEq.trans hh)
          rw [if_neg hek, lookup_cons_ne (⟨h.key, comb h.val e.val⟩ : Entry α) [] hhk,
            lookup_cons_ne h [] hhk]
    · refine ⟨?_, fun k => ?_⟩
      · show Sorted [h, e]
        exact ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hc, sorted_singleton e⟩
      · show lookup [h, e] k = (if e.key = k then combOpt comb (lookup [h] k) (some e.val)
          else lookup [h] k)
        have hc' : h.key < e.key := hc
        by_cases hek : e.key = k
        · have hhk : h.key ≠ k := fun hh => lt_ne hc' (hh.trans hek.symm)
          rw [if_pos hek, lookup_cons_ne h [e] hhk, lookup_cons_eq e [] hek,
            lookup_cons_ne h [] hhk]
          rfl
        · by_cases hhk : h.key = k
          · rw [if_neg hek, lookup_cons_eq h [e] hhk, lookup_cons_eq h [] hhk]
          · rw [if_neg hek, lookup_cons_ne h [e] hhk, lookup_cons_ne e [] hek,
              lookup_cons_ne h [] hhk]
  | cons h2 t2 ih =>
    intro c e h hs hc
    have hs2 : Sorted (h2 :: t2) := hs.2
    have hlt2 : ∀ x ∈ h2 :: t2, h.key < x.key := hs.1
    cases c
    · refine ⟨?_, fun k => ?_⟩
      · show Sorted (e :: h :: h2 :: t2)
        refine ⟨fun x hx => ?_, hs⟩
        rcases List.mem_cons.mp hx with hxh | hx3
        · rw [hxh]
          exact hc
        · rcases List.mem_cons.mp hx3 with hxh2 | hx4
          · rw [hxh2]
            exact String.lt_trans hc (hlt2 h2 List.mem_cons_self)
          · exact String.lt_trans hc (hlt2 x (List.mem_cons_of_mem h2 hx4))
      · show lookup (e :: h :: h2 :: t2) k = (if e.key = k then
          combOpt comb (lookup (h :: h2 :: t2) k) (some e.val) else lookup (h :: h2 :: t2) k)
        by_cases hek : e.key = k
        · have hnone : lookup (h :: h2 :: t2) k = none := by
            apply lookup_none_of
            intro y hy
            rcases List.mem_cons.mp hy with hyh | hy3
            · rw [hyh]
              exact fun hh => lt_ne' hc (hh.trans hek.symm)
            · rcases List.mem_cons.mp hy3 with hyh2 | hy4
              · rw [hyh2]
                exact fun hh => lt_ne' (String.lt_trans hc (hlt2 h2 List.mem_cons_self))
                  (hh.trans hek.symm)
              · exact fun hh => lt_ne' (String.lt_trans hc (hlt2 y (List.mem_cons_of_mem h2 hy4)))
                  (hh.trans hek.symm)
          rw [if_pos hek, lookup_cons_eq e _ hek, hnone, combOpt_none_left]
        · rw [if_neg hek, lookup_cons_ne e _ hek]
    · have hEq : e.key = h.key := hc
      refine ⟨⟨fun x hx => hlt2 x hx, hs2⟩, fun k => ?_⟩
      show lookup (⟨h.key, comb h.val e.val⟩ :: h2 :: t2) k = (if e.key = k then
        combOpt comb (lookup (h :: h2 :: t2) k) (some e.val) else lookup (h :: h2 :: t2) k)
      by_cases hek : e.key = k
      · have hhk : h.key = k := hEq.symm.trans hek
        rw [if_pos hek, lookup_cons_eq (⟨h.key, comb h.val e.val⟩ : Entry α) (h2 :: t2) hhk,
          lookup_cons_eq h (h2 :: t2) hhk]
        rfl
      · have hhk : h.key ≠ k := fun hh => hek (hEq.trans hh)
        rw [if_neg hek, lookup_cons_ne (⟨h.key, comb h.val e.val⟩ : Entry α) (h2 :: t2) hhk,
          lookup_cons_ne h (h2 :: t2) hhk]
    · have hc' : h.key < e.key := hc
      obtain ⟨hsIH, hlkIH⟩ := ih (skeyCmp e.key h2.key) e h2 hs2 (skey_ok e h2)
      show Sorted (h :: insC comb t2 (skeyCmp e.key h2.key) e h2) ∧ ∀ k,
        lookup (h :: insC comb t2 (skeyCmp e.key h2.key) e h2) k =
          (if e.key = k then combOpt comb (lookup (h :: h2 :: t2) k) (some e.val)
            else lookup (h :: h2 :: t2) k)
      refine ⟨?_, fun k => ?_⟩
      · refine ⟨fun x hx => ?_, hsIH⟩
        rcases insC_mem comb t2 (skeyCmp e.key h2.key) e h2 x hx with hxe | ⟨y, hy, hyx⟩
        · rw [hxe]
          exact hc'
        · rw [← hyx]
          rcases List.mem_cons.mp hy with hyh | hyt
          · rw [hyh]
            exact hlt2 h2 List.mem_cons_self
          · exact hlt2 y (List.mem_cons_of_mem h2 hyt)
      · by_cases hhk : h.key = k
        · have hek : e.key ≠ k := fun hh => lt_ne hc' (hhk.trans hh.symm)
          rw [if_neg hek, lookup_cons_eq h _ hhk, lookup_cons_eq h (h2 :: t2) hhk]
        · rw [lookup_cons_ne h (insC comb t2 (skeyCmp e.key h2.key) e h2) hhk, hlkIH k,
            lookup_cons_ne h (h2 :: t2) hhk]

theorem ins_sorted {α : Type} (comb : α → α → α) (e : Entry α) (s : List (Entry α))
    (hs : Sorted s) : Sorted (ins comb e s) := by
  cases s with
  | nil => exact sorted_singleton e
  | cons h t => exact (insC_spec comb t _ e h hs (skey_ok e h)).1

theorem ins_lookup {α : Type} (comb : α → α → α) (e : Entry α) (s : List (Entry α))
    (hs : Sorted s) (k : String) :
    lookup (ins comb e s) k =
      (if e.key = k then combOpt comb (lookup s k) (some e.val) else lookup s k) := by
  cases s with
  | nil =>
    show lookup [e] k = (if e.key = k then combOpt comb none (some e.val) else none)
    by_cases hek : e.key = k
    · rw [if_pos hek, lookup_cons_eq e [] hek, combOpt_none_left]
    · rw [if_neg hek, lookup_cons_ne e [] hek]
      rfl
  | cons h t => exact (insC_spec comb t _ e h hs (skey_ok e h)).2 k

/-! ## Folds and merges -/

theorem fold_sorted {α : Type} (comb : α → α → α) : ∀ (xs acc : List (Entry α)),
    Sorted acc → Sorted (fold comb xs acc) := by
  intro xs
  induction xs with
  | nil => intro acc hacc; exact hacc
  | cons h t ih =>
    intro acc hacc
    exact ih (ins comb h acc) (ins_sorted comb h acc hacc)

theorem fold_lookup {α : Type} (comb : α → α → α) : ∀ (xs acc : List (Entry α)),
    Sorted xs → Sorted acc → ∀ k,
      lookup (fold comb xs acc) k = combOpt comb (lookup acc k) (lookup xs k) := by
  intro xs
  induction xs with
  | nil =>
    intro acc _ _ k
    show lookup acc k = combOpt comb (lookup acc k) none
    rw [combOpt_none_right]
  | cons h t ih =>
    intro acc hsx hacc k
    show lookup (fold comb t (ins comb h acc)) k = combOpt comb (lookup acc k) (lookup (h :: t) k)
    rw [ih (ins comb h acc) hsx.2 (ins_sorted comb h acc hacc) k, ins_lookup comb h acc hacc k]
    by_cases hhk : h.key = k
    · have hT : lookup t k = none := by
        apply lookup_none_of
        intro y hy
        exact fun hh => lt_ne' (hsx.1 y hy) (hh.trans hhk.symm)
      rw [if_pos hhk, hT, combOpt_none_right, lookup_cons_eq h t hhk]
    · rw [if_neg hhk, lookup_cons_ne h t hhk]

theorem mergeMap_sorted {α : Type} (comb : α → α → α) (a b : List (Entry α)) :
    Sorted (mergeMap comb a b) :=
  fold_sorted comb b _ (fold_sorted comb a [] trivial)

theorem mergeMap_lookup {α : Type} (comb : α → α → α) (a b : List (Entry α))
    (ha : Sorted a) (hb : Sorted b) (k : String) :
    lookup (mergeMap comb a b) k = combOpt comb (lookup a k) (lookup b k) := by
  unfold mergeMap
  rw [fold_lookup comb b _ hb (fold_sorted comb a [] trivial) k,
    fold_lookup comb a [] ha trivial k]
  show combOpt comb (combOpt comb none (lookup a k)) (lookup b k) = _
  rw [combOpt_none_left]

/-- Two strictly increasing maps with the same lookups are equal. -/
theorem eq_of_sorted_lookup {α : Type} : ∀ (L1 L2 : List (Entry α)), Sorted L1 → Sorted L2 →
    (∀ k, lookup L1 k = lookup L2 k) → L1 = L2
  | [], [], _, _, _ => rfl
  | [], g :: u, _, _, hL => by
    have h1 := hL g.key
    rw [lookup_cons_eq g u rfl] at h1
    exact absurd h1 (by simp [lookup])
  | h :: t, [], _, _, hL => by
    have h1 := hL h.key
    rw [lookup_cons_eq h t rfl] at h1
    exact absurd h1 (by simp [lookup])
  | h :: t, g :: u, hs1, hs2, hL => by
    have hkey : h.key = g.key := by
      rcases key_tri h.key g.key with hlt | heq | hgt
      · exfalso
        have hnone : lookup (g :: u) h.key = none := by
          apply lookup_none_of
          intro y hy
          rcases List.mem_cons.mp hy with hyg | hyu
          · rw [hyg]
            exact lt_ne' hlt
          · exact lt_ne' (String.lt_trans hlt (hs2.1 y hyu))
        have h1 := hL h.key
        rw [lookup_cons_eq h t rfl, hnone] at h1
        exact absurd h1 (by simp)
      · exact heq
      · exfalso
        have hnone : lookup (h :: t) g.key = none := by
          apply lookup_none_of
          intro y hy
          rcases List.mem_cons.mp hy with hyh | hyt
          · rw [hyh]
            exact lt_ne' hgt
          · exact lt_ne' (String.lt_trans hgt (hs1.1 y hyt))
        have h1 := hL g.key
        rw [lookup_cons_eq g u rfl, hnone] at h1
        exact absurd h1 (by simp)
    have hval : h.val = g.val := by
      have h1 := hL h.key
      rw [lookup_cons_eq h t rfl, lookup_cons_eq g u hkey.symm] at h1
      exact Option.some.inj h1
    have htail : ∀ k, lookup t k = lookup u k := by
      intro k
      by_cases hk : h.key = k
      · have hT : lookup t k = none := by
          apply lookup_none_of
          intro y hy
          exact fun e => lt_ne' (hs1.1 y hy) (e.trans hk.symm)
        have hU : lookup u k = none := by
          apply lookup_none_of
          intro y hy
          exact fun e => lt_ne' (hs2.1 y hy) ((e.trans hk.symm).trans hkey)
        rw [hT, hU]
      · have hgk : g.key ≠ k := fun e => hk (hkey.trans e)
        have h1 := hL k
        rw [lookup_cons_ne h t hk, lookup_cons_ne g u hgk] at h1
        exact h1
    have htu : t = u := eq_of_sorted_lookup t u hs1.2 hs2.2 htail
    have hentry : h = g := by
      rcases h with ⟨hk, hv⟩
      rcases g with ⟨gk, gv⟩
      simp only at hkey hval
      subst hkey
      subst hval
      rfl
    rw [hentry, htu]

/-! ## The laws of the merge -/

theorem mergeMap_comm {α : Type} (comb : α → α → α) (hc : ∀ v w, comb v w = comb w v)
    (a b : List (Entry α)) (ha : Sorted a) (hb : Sorted b) :
    mergeMap comb a b = mergeMap comb b a :=
  eq_of_sorted_lookup _ _ (mergeMap_sorted comb a b) (mergeMap_sorted comb b a)
    (fun k => by
      rw [mergeMap_lookup comb a b ha hb k, mergeMap_lookup comb b a hb ha k]
      exact combOpt_comm comb hc _ _)

theorem mergeMap_idem {α : Type} (comb : α → α → α) (hi : ∀ v, comb v v = v)
    (a : List (Entry α)) (ha : Sorted a) : mergeMap comb a a = a :=
  eq_of_sorted_lookup _ _ (mergeMap_sorted comb a a) ha
    (fun k => by
      rw [mergeMap_lookup comb a a ha ha k]
      exact combOpt_self comb hi _)

theorem lpMax_comm (a b : Lesson) : lpMax a b = lpMax b a := by
  cases a
  cases b
  simp only [lpMax, Nat.max_comm]

theorem lpMax_self (a : Lesson) : lpMax a a = a := by
  cases a
  simp [lpMax]

theorem natCmp_self (x : Nat) : natCmp x x = .eq := by
  simp [natCmp]

theorem cardMerge_self (c : Card) : cardMerge c c = c := by
  simp [cardMerge, cardPick, natCmp_self]

/-- Lessons: the merge is commutative, and idempotent. -/
theorem lessons_comm (a b : List (Entry Lesson)) (ha : Sorted a) (hb : Sorted b) :
    mergeMap lpMax a b = mergeMap lpMax b a :=
  mergeMap_comm lpMax lpMax_comm a b ha hb

theorem lessons_idem (a : List (Entry Lesson)) (ha : Sorted a) : mergeMap lpMax a a = a :=
  mergeMap_idem lpMax lpMax_self a ha

/-- XP per day: the merge is commutative, and idempotent. -/
theorem xp_comm (a b : List (Entry Nat)) (ha : Sorted a) (hb : Sorted b) :
    mergeMap Nat.max a b = mergeMap Nat.max b a :=
  mergeMap_comm Nat.max (fun v w => Nat.max_comm v w) a b ha hb

theorem xp_idem (a : List (Entry Nat)) (ha : Sorted a) : mergeMap Nat.max a a = a :=
  mergeMap_idem Nat.max (fun v => Nat.max_self v) a ha

/-- The total XP is commutative, because the per-day merge is. -/
theorem xsum_comm (a b : List (Entry Nat)) (ha : Sorted a) (hb : Sorted b) :
    xsum (mergeMap Nat.max a b) = xsum (mergeMap Nat.max b a) := by
  rw [xp_comm a b ha hb]

/-- SRS cards: the merge is idempotent. -/
theorem srs_idem (a : List (Entry Card)) (ha : Sorted a) : mergeMap cardMerge a a = a :=
  mergeMap_idem cardMerge cardMerge_self a ha

/-! ## The SRS merge is not commutative: two counterexamples -/

/-- Two cards with the same review time, reps and due date, differing in ease. -/
def cA : Card := ⟨"c1", "l1", 1, 200, 5, 0, 1, some 7⟩
def cB : Card := ⟨"c1", "l1", 1, 250, 5, 0, 1, some 7⟩

/-- A card with no review time against one whose review time is 0. -/
def cC : Card := ⟨"c1", "l1", 1, 200, 5, 0, 1, none⟩
def cD : Card := ⟨"c1", "l1", 1, 200, 5, 0, 1, some 0⟩

theorem cardMerge_cA_cB : cardMerge cA cB = cA := by decide
theorem cardMerge_cB_cA : cardMerge cB cA = cB := by decide
theorem cardMerge_cC_cD : cardMerge cC cD = cC := by decide
theorem cardMerge_cD_cC : cardMerge cD cC = cD := by decide

theorem cA_ne_cB : cA ≠ cB := by decide
theorem cC_ne_cD : cC ≠ cD := by decide

def eA : List (Entry Card) := [⟨"c1", cA⟩]
def eB : List (Entry Card) := [⟨"c1", cB⟩]
def eC : List (Entry Card) := [⟨"c1", cC⟩]
def eD : List (Entry Card) := [⟨"c1", cD⟩]

theorem mergeMap_eA_eB : mergeMap cardMerge eA eB = [⟨"c1", cA⟩] := by decide
theorem mergeMap_eB_eA : mergeMap cardMerge eB eA = [⟨"c1", cB⟩] := by decide
theorem mergeMap_eC_eD : mergeMap cardMerge eC eD = [⟨"c1", cC⟩] := by decide
theorem mergeMap_eD_eC : mergeMap cardMerge eD eC = [⟨"c1", cD⟩] := by decide

/-- SRS merge is not commutative (review ties, cards differ in ease). -/
theorem srs_comm_false_ease :
    ¬ ∀ a b : List (Entry Card), Sorted a → Sorted b →
      mergeMap cardMerge a b = mergeMap cardMerge b a := by
  intro h
  have h2 : mergeMap cardMerge eA eB = mergeMap cardMerge eB eA :=
    h eA eB (sorted_singleton _) (sorted_singleton _)
  rw [mergeMap_eA_eB, mergeMap_eB_eA] at h2
  exact (by decide : ¬ ([⟨"c1", cA⟩] : List (Entry Card)) = [⟨"c1", cB⟩]) h2

/-- SRS merge is not commutative (an absent review time against a review time of 0). -/
theorem srs_comm_false_none :
    ¬ ∀ a b : List (Entry Card), Sorted a → Sorted b →
      mergeMap cardMerge a b = mergeMap cardMerge b a := by
  intro h
  have h2 : mergeMap cardMerge eC eD = mergeMap cardMerge eD eC :=
    h eC eD (sorted_singleton _) (sorted_singleton _)
  rw [mergeMap_eC_eD, mergeMap_eD_eC] at h2
  exact (by decide : ¬ ([⟨"c1", cC⟩] : List (Entry Card)) = [⟨"c1", cD⟩]) h2

/-- The learning state is not commutative, because its SRS part is not. -/
theorem state_comm_false :
    ¬ ∀ a b : State, mergeState a b = mergeState b a := by
  intro h
  have h2 : mergeMap cardMerge eA eB = mergeMap cardMerge eB eA :=
    congrArg State.srs (h ⟨[], eA, []⟩ ⟨[], eB, []⟩)
  rw [mergeMap_eA_eB, mergeMap_eB_eA] at h2
  exact (by decide : ¬ ([⟨"c1", cA⟩] : List (Entry Card)) = [⟨"c1", cB⟩]) h2

/-- The lessons and XP parts of the learning state are commutative. -/
theorem state_lessons_xp_comm (a b : State) (ha : Sorted a.lessons) (hb : Sorted b.lessons)
    (hxa : Sorted a.xp) (hxb : Sorted b.xp) :
    (mergeState a b).lessons = (mergeState b a).lessons ∧
      (mergeState a b).xp = (mergeState b a).xp :=
  ⟨lessons_comm a.lessons b.lessons ha hb, xp_comm a.xp b.xp hxa hxb⟩

end BendMerge

#print axioms BendMerge.lessons_comm
#print axioms BendMerge.lessons_idem
#print axioms BendMerge.xp_comm
#print axioms BendMerge.xp_idem
#print axioms BendMerge.xsum_comm
#print axioms BendMerge.srs_idem
#print axioms BendMerge.srs_comm_false_ease
#print axioms BendMerge.srs_comm_false_none
#print axioms BendMerge.state_comm_false
