/-
CompilerCheck.lean: translation validation of the Bend compiler's JavaScript for the transitions.

The Bend compiler turned core/tcp_transitions.bend into core/tcp_transitions.mjs. This file checks that each
transition's JavaScript export is the Nat semantics of its Bend definition, and proves what the check means for
all inputs. The data section holds the lines of the two files, and the terms that the readers (parseBend and
parseJS, below) make from them. compiler_check.ts runs the readers with `lean --run` and writes their output in;
the kernel does not read the texts (it cannot, in the time and memory it has; see compiler_check.ts). `checked` is
the check, verified by the kernel on those terms. The theorems at the end follow from it.

What the theorems say. For each transition f of tcp_transitions.bend, and every list of integers of f's arity,
the JavaScript export f(args):
  - returns the value of f's Bend definition, when every argument is an integer from 0 to 2^53 (nat_in
    accepts it) and every immediate sum the definition computes is at most 2^48 - 1 (nat_chk's limit);
  - throws otherwise, and not for a reason the definition does not have.
`natE_of_bendE` says that where no immediate limit is hit, the Bend value is the unbounded Nat value, which is
what Bend's proofs use.

What is trusted (not proven here):
  - IEEE 754 doubles: +, - and < on integers from 0 to 2^53 are exact, and a sum above 2^53 is never rounded
    down below 2^53. The definitions below use exact Nat arithmetic, under that assumption.
  - the two readers, parseBend and parseJS. They are run to make the data section, which compiler_check.test.ts
    checks is current; their correctness is not proven. The lines the check reads are the four runtime helpers
    (nat_chk, nat_in, run_lib, run_loop: their texts are compared exactly, and their behaviour is the one the
    definitions model) and every line from the first transition on; the other lines are runtime code that the
    transitions do not use. The generator asserts that each helper is defined once in the file, and that no
    transition comes before the first one.
  - Lean's kernel and Lean.
Not covered: other Bend definitions, and the compiler in general. The check accepts exactly the JavaScript
shapes of the transitions (sums, guarded differences and minima); a compiler change to another shape fails the
check rather than being proven.
-/

namespace CompilerCheck

-- ================================================================================================
-- The semantics
-- ================================================================================================

-- 2^48 - 1: the largest immediate Nat (nat_chk); 2^53: the largest host number (nat_in)
def LIMIT : Nat := 281474976710655
def HOST : Nat := 9007199254740992

-- a JavaScript expression of a transition: a parameter or constant, a number, a sum or difference (exact),
-- nat_chk of an expression, and a conditional (a < b ? t : f)
inductive JE where
  | v (x : String)
  | n (k : Nat)
  | add (a b : JE)
  | sub (a b : JE)
  | chk (e : JE)
  | cond (a b t f : JE)
  deriving DecidableEq, Repr

-- a Bend definition's body: Nat.add (the immediate limit applies to its sum), Nat.sub, Nat.min
inductive BE where
  | var (x : String)
  | add (a b : BE)
  | sub (a b : BE)
  | min (a b : BE)
  deriving DecidableEq, Repr

abbrev Env := String → Nat

def upd (ρ : Env) (x : String) (v : Nat) : Env := fun y => if y = x then v else ρ y

def mkEnv : List String → List Nat → Env
  | p :: ps, a :: as => upd (mkEnv ps as) p a
  | _, _ => fun _ => 0

-- the JavaScript: a refusal (none) is a throw
def jsE (ρ : Env) : JE → Option Nat
  | .v x => some (ρ x)
  | .n k => some k
  | .add a b => (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => some (x + y)
  | .sub a b => (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => some (x - y)
  | .chk e => (jsE ρ e).bind fun v => if v ≤ LIMIT then some v else none
  | .cond a b t f =>
      (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => if x < y then jsE ρ t else jsE ρ f

-- the Bend definition, with the immediate limit: Nat.add refuses a sum past LIMIT; the arguments are strict
def bendE (ρ : Env) : BE → Option Nat
  | .var x => some (ρ x)
  | .add a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y =>
      if x + y ≤ LIMIT then some (x + y) else none
  | .sub a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y => some (x - y)
  | .min a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y => some (min x y)

-- the same Bend definition in unbounded Nat (the value Bend's proofs talk about)
def natE (ρ : Env) : BE → Nat
  | .var x => ρ x
  | .add a b => natE ρ a + natE ρ b
  | .sub a b => natE ρ a - natE ρ b
  | .min a b => min (natE ρ a) (natE ρ b)

-- ================================================================================================
-- The translation: the Bend body of a JavaScript expression. sigma holds the Bend trees of the constants.
-- ================================================================================================

abbrev Sigma := List (String × BE)

def decomp (ps : List String) (σ : Sigma) : JE → Option BE
  | .v x => match σ.lookup x with
    | some t => some t
    | none => if ps.contains x then some (BE.var x) else none
  | .chk (.add a b) => (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.add a' b')
  | .cond a b t f =>
    if t = JE.n 0 ∧ f = JE.sub a b then
      (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.sub a' b')
    else if t = a ∧ f = b then
      (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.min a' b')
    else none
  | _ => none

-- the constants, in order: each one's tree
def buildSigma (ps : List String) : List (String × JE) → Sigma → Option Sigma
  | [], σ => some σ
  | (x, e) :: rest, σ => (decomp ps σ e).bind fun t => buildSigma ps rest (σ ++ [(x, t)])

-- the tree s occurs in t
def hasSub (s : BE) : BE → Bool
  | .var x => decide (s = .var x)
  | .add a b => decide (s = .add a b) || hasSub s a || hasSub s b
  | .sub a b => decide (s = .sub a b) || hasSub s a || hasSub s b
  | .min a b => decide (s = .min a b) || hasSub s a || hasSub s b

-- ================================================================================================
-- The programs: a JavaScript transition (its constants, then its result) and a Bend definition
-- ================================================================================================

structure JSFn where
  name : String
  params : List String
  consts : List (String × JE)
  ret : JE
  deriving Repr

structure BendDef where
  name : String
  params : List String
  body : BE
  deriving Repr

def jsRunC (ρ : Env) : List (String × JE) → Option Env
  | [] => some ρ
  | (x, e) :: rest => (jsE ρ e).bind fun v => jsRunC (upd ρ x v) rest

def jsRun (j : JSFn) (args : List Nat) : Option Nat :=
  (jsRunC (mkEnv j.params args) j.consts).bind fun ρ => jsE ρ j.ret

def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

def disjointB (ps names : List String) : Bool := names.all fun x => !ps.contains x

-- the check of one transition: the parameters are the definition's; the constants are distinct and not
-- parameters; the translation of the result is the definition's body; every constant's tree occurs in it
def checkFn (b : BendDef) (j : JSFn) : Bool :=
  decide (j.params = b.params) && nodupB (j.consts.map Prod.fst) &&
    disjointB j.params (j.consts.map Prod.fst) &&
    (match buildSigma j.params j.consts [] with
     | none => false
     | some σ => match decomp j.params σ j.ret with
       | none => false
       | some B => decide (B = b.body) && σ.all fun e => hasSub e.2 B)

-- the export: nat_in on each argument, then the function; the Bend reference the same, on the Nat arguments
def natIn (a : Int) : Option Nat := if 0 ≤ a ∧ a ≤ (HOST : Int) then some a.toNat else none

def natList : List Int → Option (List Nat)
  | [] => some []
  | a :: as => (natIn a).bind fun n => (natList as).bind fun ns => some (n :: ns)

def exportJS (j : JSFn) (args : List Int) : Option Nat := (natList args).bind fun ns => jsRun j ns

def refOf (b : BendDef) (args : List Int) : Option Nat :=
  (natList args).bind fun ns => bendE (mkEnv b.params ns) b.body

-- ================================================================================================
-- Proofs
-- ================================================================================================

theorem upd_eq (ρ : Env) (x : String) (v : Nat) : upd ρ x v x = v := by
  simp [upd]

theorem upd_ne (ρ : Env) (x y : String) (v : Nat) (h : y ≠ x) : upd ρ x v y = ρ y := by
  simp [upd, h]

theorem lookup_mem : ∀ (σ : Sigma) (x : String) (t : BE), σ.lookup x = some t → (x, t) ∈ σ
  | [], _, _, h => by simp [List.lookup] at h
  | (k, s) :: σ, x, t, h => by
    unfold List.lookup at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq] at hk
      subst hk
      simp only [Option.some.injEq] at h
      subst h
      simp
    · exact List.mem_cons_of_mem _ (lookup_mem σ x t h)

-- decomp, with its inputs: every tree it returns evaluates to the value the JavaScript expression has
theorem decomp_sound (ps : List String) (ρ0 : Env) (σ : Sigma) :
    ∀ (j : JE) (b : BE), decomp ps σ j = some b → ∀ (ρ : Env),
      (∀ p ∈ ps, ρ p = ρ0 p) → (∀ y s, (y, s) ∈ σ → ∃ v, bendE ρ0 s = some v ∧ ρ y = v) →
      jsE ρ j = bendE ρ0 b
  | .v x, b, hd, ρ, hp, ha => by
    cases hl : σ.lookup x with
    | some t =>
      have hd' : decomp ps σ (.v x) = some t := by simp [decomp, hl]
      have hb : t = b := Option.some.inj (hd'.symm.trans hd)
      subst hb
      obtain ⟨v, hv, hρ⟩ := ha x t (lookup_mem σ x t hl)
      simp only [jsE, hρ, hv]
    | none =>
      by_cases hx : ps.contains x = true
      · have hd' : decomp ps σ (.v x) = some (BE.var x) := by
          unfold decomp
          rw [hl]
          simp only [hx, ↓reduceIte]
        have hb : BE.var x = b := Option.some.inj (hd'.symm.trans hd)
        subst hb
        have hmem : x ∈ ps := List.mem_of_elem_eq_true hx
        simp only [jsE, bendE, hp x hmem]
      · have hx' : ps.contains x = false := by simpa using hx
        have hd' : decomp ps σ (.v x) = none := by
          unfold decomp
          rw [hl]
          simp only [hx', Bool.false_eq_true, ↓reduceIte]
        rw [hd'] at hd
        cases hd
  | .n k, b, hd, _, _, _ => by simp [decomp] at hd
  | .add a c, b, hd, _, _, _ => by simp [decomp] at hd
  | .sub a c, b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.v x), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.n k), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.sub a c), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.chk e), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.cond a c t f), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.add a c), b, hd, ρ, hp, ha => by
    unfold decomp at hd
    cases h1 : decomp ps σ a with
    | none => simp [h1] at hd
    | some a' =>
      cases h2 : decomp ps σ c with
      | none => simp [h1, h2] at hd
      | some c' =>
        simp only [h1, h2, Option.bind_some] at hd
        cases hd
        have ia := decomp_sound ps ρ0 σ a a' h1 ρ hp ha
        have ic := decomp_sound ps ρ0 σ c c' h2 ρ hp ha
        simp only [jsE, bendE, ia, ic]
        cases hx : bendE ρ0 a' <;> cases hy : bendE ρ0 c' <;> simp
  | .cond a c t f, b, hd, ρ, hp, ha => by
    unfold decomp at hd
    by_cases h1 : t = JE.n 0 ∧ f = JE.sub a c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hd
      rw [h1.1, h1.2]
      cases h2 : decomp ps σ a with
      | none => simp [h2] at hd
      | some a' =>
        cases h3 : decomp ps σ c with
        | none => simp [h2, h3] at hd
        | some c' =>
          simp only [h2, h3, Option.bind_some] at hd
          cases hd
          have ia := decomp_sound ps ρ0 σ a a' h2 ρ hp ha
          have ic := decomp_sound ps ρ0 σ c c' h3 ρ hp ha
          simp only [jsE, bendE, ia, ic]
          rcases hA : bendE ρ0 a' with _ | x
          · simp []
          · rcases hC : bendE ρ0 c' with _ | y
            · simp []
            · by_cases hxy : x < y
              · simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt hxy)]
              · simp [hxy]
    · by_cases h2 : t = a ∧ f = c
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)] at hd
        rw [h2.1, h2.2]
        cases h3 : decomp ps σ a with
        | none => simp [h3] at hd
        | some a' =>
          cases h4 : decomp ps σ c with
          | none => simp [h3, h4] at hd
          | some c' =>
            simp only [h3, h4, Option.bind_some] at hd
            cases hd
            have ia := decomp_sound ps ρ0 σ a a' h3 ρ hp ha
            have ic := decomp_sound ps ρ0 σ c c' h4 ρ hp ha
            simp only [jsE, bendE, ia, ic]
            rcases hA : bendE ρ0 a' with _ | x
            · simp []
            · rcases hC : bendE ρ0 c' with _ | y
              · simp []
              · by_cases hxy : x < y
                · simp [hxy, Nat.min_eq_left (Nat.le_of_lt hxy)]
                · simp [hxy, Nat.min_eq_right (Nat.le_of_not_lt hxy)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)] at hd
        simp at hd


theorem buildSigma_ext (ps : List String) : ∀ (cs : List (String × JE)) (σ σ' : Sigma),
    buildSigma ps cs σ = some σ' → ∃ e : Sigma, σ' = σ ++ e
  | [], σ, σ', h => by
    simp only [buildSigma, Option.some.injEq] at h
    exact ⟨[], by simp [h]⟩
  | (x, e) :: rest, σ, σ', h => by
    unfold buildSigma at h
    cases hd : decomp ps σ e with
    | none => simp [hd] at h
    | some t =>
      simp only [hd, Option.bind_some] at h
      obtain ⟨e', he'⟩ := buildSigma_ext ps rest (σ ++ [(x, t)]) σ' h
      exact ⟨(x, t) :: e', by simp [he', List.append_assoc]⟩

theorem hasSub_none (ρ : Env) : ∀ (s t : BE), hasSub s t = true → bendE ρ s = none → bendE ρ t = none
  | s, .var x, h, hs => by
    have hx : s = .var x := by simpa [hasSub] using h
    subst hx
    simp [bendE] at hs
  | s, .add a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h
      exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]
  | s, .sub a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h
      exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]
  | s, .min a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h
      exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]

-- where the bounded value is defined, it is the unbounded Nat value: the immediate limit only ever refuses
theorem natE_of_bendE (ρ : Env) : ∀ (t : BE) (v : Nat), bendE ρ t = some v → natE ρ t = v
  | .var x, v, h => by
    simp only [bendE, Option.some.injEq] at h
    simp [natE, h]
  | .add a c, v, h => by
    simp only [bendE] at h
    cases ha : bendE ρ a with
    | none => simp [ha] at h
    | some x =>
      cases hc : bendE ρ c with
      | none => simp [ha, hc] at h
      | some y =>
        simp only [ha, hc, Option.bind_some] at h
        by_cases hl : x + y ≤ LIMIT
        · simp only [hl, ite_true, Option.some.injEq] at h
          simp [natE, natE_of_bendE ρ a x ha, natE_of_bendE ρ c y hc, ← h]
        · simp only [hl, ite_false] at h
          cases h
  | .sub a c, v, h => by
    simp only [bendE] at h
    cases ha : bendE ρ a with
    | none => simp [ha] at h
    | some x =>
      cases hc : bendE ρ c with
      | none => simp [ha, hc] at h
      | some y =>
        simp only [ha, hc, Option.bind_some, Option.some.injEq] at h
        simp [natE, natE_of_bendE ρ a x ha, natE_of_bendE ρ c y hc, ← h]
  | .min a c, v, h => by
    simp only [bendE] at h
    cases ha : bendE ρ a with
    | none => simp [ha] at h
    | some x =>
      cases hc : bendE ρ c with
      | none => simp [ha, hc] at h
      | some y =>
        simp only [ha, hc, Option.bind_some, Option.some.injEq] at h
        simp [natE, natE_of_bendE ρ a x ha, natE_of_bendE ρ c y hc, ← h]

theorem nodupB_sound : ∀ (l : List String), nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hxs⟩ := h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodupB_sound xs hxs⟩
    have := List.elem_eq_true_of_mem hm
    simp_all

theorem disjointB_sound (ps names : List String) (h : disjointB ps names = true) :
    ∀ x ∈ names, x ∉ ps := by
  intro x hx hp
  simp only [disjointB, List.all_eq_true] at h
  have := h x hx
  have hm := List.elem_eq_true_of_mem hp
  simp_all

theorem checkFn_params (b : BendDef) (j : JSFn) (h : checkFn b j = true) : j.params = b.params := by
  unfold checkFn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

-- the run of the constants, against the translation: every constant either has its value, which its tree
-- gives, or its tree refuses and the translation of the result contains that tree
theorem run_build (ps : List String) (ρ0 : Env) : ∀ (cs : List (String × JE)) (σ σ' : Sigma) (ρ : Env),
    buildSigma ps cs σ = some σ' → (∀ p ∈ ps, ρ p = ρ0 p) →
    (∀ y s, (y, s) ∈ σ → ∃ v, bendE ρ0 s = some v ∧ ρ y = v) →
    (∀ y ∈ σ.map Prod.fst, y ∉ cs.map Prod.fst) → (cs.map Prod.fst).Nodup →
    (∀ x ∈ cs.map Prod.fst, x ∉ ps) →
    (∃ ρ', jsRunC ρ cs = some ρ' ∧ (∀ p ∈ ps, ρ' p = ρ0 p) ∧
        (∀ y s, (y, s) ∈ σ' → ∃ v, bendE ρ0 s = some v ∧ ρ' y = v)) ∨
    (jsRunC ρ cs = none ∧ ∃ y s, (y, s) ∈ σ' ∧ bendE ρ0 s = none)
  | [], σ, σ', ρ, hb, hp, ha, _, _, _ => by
    simp only [buildSigma, Option.some.injEq] at hb
    subst hb
    exact Or.inl ⟨ρ, rfl, hp, ha⟩
  | (x, e) :: rest, σ, σ', ρ, hb, hp, ha, hdisj, hnd, hpar => by
    unfold buildSigma at hb
    cases hdec : decomp ps σ e with
    | none => simp [hdec] at hb
    | some t =>
      simp only [hdec, Option.bind_some] at hb
      have hs := decomp_sound ps ρ0 σ e t hdec ρ hp ha
      have hxps : x ∉ ps := hpar x (by simp)
      have hnd' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
      have hxrest : x ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
      have hdisj_rest : ∀ y ∈ σ.map Prod.fst, y ∉ rest.map Prod.fst ∧ y ≠ x := by
        intro y hy
        have hn := hdisj y hy
        simp only [List.map_cons, List.mem_cons, not_or] at hn
        exact ⟨hn.2, fun h => hn.1 h⟩
      cases hv : jsE ρ e with
      | none =>
        right
        have hbt : bendE ρ0 t = none := by rw [← hs, hv]
        obtain ⟨e', he'⟩ := buildSigma_ext ps rest _ σ' hb
        refine ⟨?_, x, t, ?_, hbt⟩
        · simp [jsRunC, hv]
        · rw [he']
          simp
      | some v =>
        have ht : bendE ρ0 t = some v := by rw [← hs, hv]
        have hp' : ∀ p ∈ ps, upd ρ x v p = ρ0 p := fun p hpp => by
          have hne : p ≠ x := fun h => hxps (h ▸ hpp)
          rw [upd_ne ρ x p v hne]
          exact hp p hpp
        have hdisj' : ∀ y ∈ (σ ++ [(x, t)]).map Prod.fst, y ∉ rest.map Prod.fst := by
          intro y hy
          rw [List.map_append, List.mem_append] at hy
          rcases hy with hy | hy
          · exact (hdisj_rest y hy).1
          · have hyx : y = x := by simpa using hy
            subst hyx
            exact hxrest
        have ha' : ∀ y s, (y, s) ∈ σ ++ [(x, t)] → ∃ w, bendE ρ0 s = some w ∧ upd ρ x v y = w := by
          intro y s hm
          rcases List.mem_append.mp hm with hm | hm
          · obtain ⟨w, hw, hρy⟩ := ha y s hm
            refine ⟨w, hw, ?_⟩
            rw [upd_ne ρ x y v (hdisj_rest y (List.mem_map_of_mem hm)).2]
            exact hρy
          · simp only [List.mem_singleton, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            exact ⟨v, ht, upd_eq ρ y v⟩
        have hpar' : ∀ z ∈ rest.map Prod.fst, z ∉ ps := fun z hz => hpar z (by simp [hz])
        rcases run_build ps ρ0 rest (σ ++ [(x, t)]) σ' (upd ρ x v) hb hp' ha' hdisj' hnd' hpar' with
          ⟨ρ', hr, hp'', ha''⟩ | ⟨hr, y, s, hm, hn⟩
        · left
          exact ⟨ρ', by simp [jsRunC, hv, hr], hp'', ha''⟩
        · right
          exact ⟨by simp [jsRunC, hv, hr], y, s, hm, hn⟩

-- THE CHECK, IN MODEL TERMS: a transition's JavaScript returns its Bend definition's value on every argument
-- that the definition's translation covers; the refusals match
theorem fn_correct (b : BendDef) (j : JSFn) (h : checkFn b j = true) (ns : List Nat) :
    jsRun j ns = bendE (mkEnv j.params ns) b.body := by
  have hpar := checkFn_params b j h
  unfold checkFn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hnd⟩, hdis⟩, hd⟩ := h
  rcases hσ : buildSigma j.params j.consts [] with _ | σ'
  · simp [hσ] at hd
  · rcases hdec : decomp j.params σ' j.ret with _ | B
    · simp [hσ, hdec] at hd
    · simp only [hσ, hdec, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
      obtain ⟨hB, hcont⟩ := hd
      have hnd' : (j.consts.map Prod.fst).Nodup := nodupB_sound _ hnd
      have hpar' : ∀ x ∈ j.consts.map Prod.fst, x ∉ j.params := disjointB_sound _ _ hdis
      rcases run_build j.params (mkEnv j.params ns) j.consts [] σ' (mkEnv j.params ns) hσ
          (fun _ _ => rfl) (by simp) (by simp) hnd' hpar' with
        ⟨ρ', hr, hp', ha'⟩ | ⟨hr, y, s, hm, hn⟩
      · have hres := decomp_sound j.params (mkEnv j.params ns) σ' j.ret B hdec ρ' hp' ha'
        simp only [jsRun, hr, Option.bind_some]
        rw [hres, ← hB]
      · have hc := hcont (y, s) hm
        simp only [jsRun, hr, Option.bind_none]
        have hz := hasSub_none (mkEnv j.params ns) s B hc hn
        rw [hB] at hz
        exact hz.symm

theorem natList_length : ∀ (args : List Int) (ns : List Nat), natList args = some ns → ns.length = args.length
  | [], ns, h => by
    simp only [natList, Option.some.injEq] at h
    simp [← h]
  | a :: as, ns, h => by
    simp only [natList] at h
    rcases hn : natIn a with _ | n
    · simp [hn] at h
    · rcases hs : natList as with _ | ms
      · simp [hn, hs] at h
      · simp only [hn, hs, Option.bind_some, Option.some.injEq] at h
        subst h
        simp [natList_length as ms hs]

-- the export of a checked transition is the Bend reference, on every list of integers of its arity
theorem export_correct (b : BendDef) (j : JSFn) (h : checkFn b j = true) (args : List Int)
    (_hl : args.length = b.params.length) : exportJS j args = refOf b args := by
  have hpar := checkFn_params b j h
  unfold exportJS refOf
  rcases hn : natList args with _ | ns
  · simp
  · simp only [Option.bind_some]
    rw [fn_correct b j h ns, hpar]

-- ================================================================================================
-- The texts: lines, tokens, and the readers of the Bend definitions and of the JavaScript transitions
-- ================================================================================================

def isSp (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

-- the fuel of the readers: numerals, which the kernel decrements cheaply (an expression such as l.length + 1
-- grows as it is peeled); a line is read with LINE_FUEL characters, so a longer line fails the check
def LINE_FUEL : Nat := 512
def LINES_FUEL : Nat := 100000

def trimL : List Char → List Char
  | [] => []
  | c :: cs => if isSp c then trimL cs else c :: cs

def trimC (cs : List Char) : List Char := (trimL (trimL cs).reverse).reverse

inductive Tok where
  | id (s : String)
  | num (k : Nat)
  | sym (c : Char)
  deriving DecidableEq

def isIdC (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$' || c == '.'

def takeIdC : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if isIdC c then
      (match takeIdC cs with
       | (a, r) => (c :: a, r))
    else ([], c :: cs)

def takeNumC : List Char → Nat → Nat × List Char
  | [], acc => (acc, [])
  | c :: cs, acc => if c.isDigit then takeNumC cs (acc * 10 + (c.toNat - 48)) else (acc, c :: cs)

def tokenize : Nat → List Char → List Tok
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, c :: cs =>
    if isSp c || c == '\n' then tokenize f cs
    else if c.isDigit then
      (match takeNumC (c :: cs) 0 with
       | (k, r) => Tok.num k :: tokenize f r)
    else if c.isAlpha || c == '_' || c == '$' then
      (match takeIdC (c :: cs) with
       | (a, r) => Tok.id (String.ofList a) :: tokenize f r)
    else Tok.sym c :: tokenize f cs

-- a JavaScript expression: atoms, sums and differences, nat_chk, and the conditional (a < b ? t : f)
mutual
def pAtom : Nat → List Tok → Option (JE × List Tok)
  | 0, _ => none
  | _ + 1, Tok.num k :: r => some (JE.n k, r)
  | f + 1, Tok.id s :: Tok.sym '(' :: r =>
    if s = "nat_chk" then
      (match pExpr f r with
       | some (e, Tok.sym ')' :: r') => some (JE.chk e, r')
       | _ => none)
    else none
  | _ + 1, Tok.id s :: r => some (JE.v s, r)
  | f + 1, Tok.sym '(' :: r =>
    (match pExpr f r with
     | some (e, Tok.sym ')' :: r') => some (e, r')
     | _ => none)
  | _, _ => none

def pSumL : Nat → JE → List Tok → Option (JE × List Tok)
  | 0, e, ts => some (e, ts)
  | f + 1, e, Tok.sym '+' :: r =>
    (match pAtom f r with
     | some (b, r') => pSumL f (JE.add e b) r'
     | none => none)
  | f + 1, e, Tok.sym '-' :: r =>
    (match pAtom f r with
     | some (b, r') => pSumL f (JE.sub e b) r'
     | none => none)
  | _, e, ts => some (e, ts)

def pSum : Nat → List Tok → Option (JE × List Tok)
  | 0, _ => none
  | f + 1, ts =>
    (match pAtom f ts with
     | some (a, r) => pSumL f a r
     | none => none)

def pExpr : Nat → List Tok → Option (JE × List Tok)
  | 0, _ => none
  | f + 1, ts =>
    (match pSum f ts with
     | some (a, Tok.sym '<' :: r) =>
       (match pSum f r with
        | some (b, Tok.sym '?' :: r2) =>
          (match pExpr f r2 with
           | some (t, Tok.sym ':' :: r3) =>
             (match pExpr f r3 with
              | some (e, r4) => some (JE.cond a b t e, r4)
              | none => none)
           | _ => none)
        | _ => none)
     | some (a, r) => some (a, r)
     | none => none)
end

inductive Line where
  | assign (x : String) (e : JE)
  | result (e : JE)

def parseLine (f : Nat) (ts : List Tok) : Option Line :=
  match ts with
  | Tok.id "const" :: Tok.id x :: Tok.sym '=' :: r =>
    (match pExpr f r with
     | some (e, Tok.sym ';' :: []) => some (Line.assign x e)
     | _ => none)
  | Tok.id "return" :: r =>
    (match pExpr f r with
     | some (e, Tok.sym ';' :: []) => some (Line.result e)
     | _ => none)
  | _ => none

def parseLines : List (List Tok) → Option (List Line)
  | [] => some []
  | ts :: rest =>
    (match parseLine LINE_FUEL ts with
     | some ln =>
       (match parseLines rest with
        | some lns => some (ln :: lns)
        | none => none)
     | none => none)

def buildFn (name : String) (ps : List String) : List (String × JE) → List Line → Option JSFn
  | _, [] => none
  | acc, Line.assign x e :: rest => buildFn name ps ((x, e) :: acc) rest
  | acc, Line.result e :: rest =>
    (match rest with
     | [] => some { name := name, params := ps, consts := acc.reverse, ret := e }
     | _ :: _ => none)

def takeBody : List (List Char) → List (List Char) × List (List Char)
  | [] => ([], [])
  | l :: ls =>
    if trimC l == ['}'] then ([], ls)
    else (match takeBody ls with
      | (b, r) => (l :: b, r))

def takeParams : List Tok → Option (List String × List Tok)
  | Tok.sym ')' :: r => some ([], r)
  | Tok.id p :: Tok.sym ',' :: r =>
    (match takeParams r with
     | some (ps, r') => some (p :: ps, r')
     | none => none)
  | Tok.id p :: Tok.sym ')' :: r => some ([p], r)
  | _ => none

def dollarName (s : String) : Option String :=
  match s.toList with
  | '$' :: rest => some (String.ofList rest)
  | _ => none

def parseHeader (ts : List Tok) : Option (String × List String) :=
  match ts with
  | Tok.id "function" :: Tok.id nm :: Tok.sym '(' :: r =>
    (match takeParams r with
     | some (ps, Tok.sym '{' :: []) =>
       (match dollarName nm with
        | some name => some (name, ps)
        | none => none)
     | _ => none)
  | _ => none

-- the transitions of the module: the functions named $name (the helpers are skipped). The loop is tail
-- recursive, with its results in an accumulator: a continuation per line is what the kernel could not evaluate
def parseFnsAux : Nat → List (List Char) → List JSFn → Option (List JSFn)
  | 0, _, acc => some acc.reverse
  | _ + 1, [], acc => some acc.reverse
  | f + 1, l :: ls, acc =>
    (match tokenize LINE_FUEL l with
     | Tok.id "function" :: Tok.id nm :: _ =>
       (match dollarName nm with
        | none => parseFnsAux f ls acc
        | some _ =>
          (match parseHeader (tokenize LINE_FUEL l) with
           | none => none
           | some (name, ps) =>
             (match takeBody ls with
              | (body, rest) =>
                (match parseLines (body.map fun l => tokenize LINE_FUEL l) with
                 | none => none
                 | some lns =>
                   (match buildFn name ps [] lns with
                    | none => none
                    | some j => parseFnsAux f rest (j :: acc))))))
     | _ => parseFnsAux f ls acc)

def parseFns (ls : List (List Char)) : Option (List JSFn) := parseFnsAux LINES_FUEL ls []

-- the Bend definitions: a def line, then its body line; parameters become the JavaScript names _p_0
def jsName (s : String) : String := "_" ++ s ++ "_0"

def bendParamsTail : List Tok → Option (List String × List Tok)
  | Tok.sym ')' :: r => some ([], r)
  | Tok.sym ',' :: Tok.sym '+' :: Tok.id p :: Tok.sym ':' :: Tok.id "Nat" :: r =>
    (match bendParamsTail r with
     | some (ps, r') => some (p :: ps, r')
     | none => none)
  | _ => none

def bendParams : List Tok → Option (List String × List Tok)
  | Tok.sym '+' :: Tok.id p :: Tok.sym ':' :: Tok.id "Nat" :: r =>
    (match bendParamsTail r with
     | some (ps, r') => some (p :: ps, r')
     | none => none)
  | Tok.sym ')' :: r => some ([], r)
  | _ => none

def bendHeader (ts : List Tok) : Option (String × List String) :=
  match ts with
  | Tok.id "def" :: Tok.id nm :: Tok.sym '(' :: r =>
    (match bendParams r with
     | some (ps, Tok.sym '-' :: Tok.sym '>' :: Tok.id "Nat" :: Tok.sym ':' :: []) => some (nm, ps)
     | _ => none)
  | _ => none

mutual
def pBendE : Nat → List String → List Tok → Option (BE × List Tok)
  | 0, _, _ => none
  | f + 1, ps, Tok.id "Nat.add" :: Tok.sym '(' :: r =>
    (match pBendArgs f ps r with
     | some (a, b, r') => some (BE.add a b, r')
     | none => none)
  | f + 1, ps, Tok.id "Nat.sub" :: Tok.sym '(' :: r =>
    (match pBendArgs f ps r with
     | some (a, b, r') => some (BE.sub a b, r')
     | none => none)
  | f + 1, ps, Tok.id "Nat.min" :: Tok.sym '(' :: r =>
    (match pBendArgs f ps r with
     | some (a, b, r') => some (BE.min a b, r')
     | none => none)
  | _ + 1, ps, Tok.id s :: r => if ps.contains s then some (BE.var (jsName s), r) else none
  | _, _, _ => none

def pBendArgs : Nat → List String → List Tok → Option (BE × BE × List Tok)
  | 0, _, _ => none
  | f + 1, ps, ts =>
    (match pBendE f ps ts with
     | some (a, Tok.sym ',' :: r) =>
       (match pBendE f ps r with
        | some (b, Tok.sym ')' :: r') => some (a, b, r')
        | _ => none)
     | _ => none)
end

def bodyLine : List (List Char) → Option (List Tok × List (List Char))
  | [] => none
  | l :: ls =>
    (match tokenize LINE_FUEL l with
     | [] => bodyLine ls
     | Tok.sym '#' :: _ => bodyLine ls
     | ts => some (ts, ls))

def parseBendAux : Nat → List (List Char) → Option (List BendDef)
  | 0, _ => some []
  | _ + 1, [] => some []
  | f + 1, l :: ls =>
    (match tokenize LINE_FUEL l with
     | Tok.id "def" :: _ =>
       (match bendHeader (tokenize LINE_FUEL l) with
        | none => none
        | some (nm, ps) =>
          (match bodyLine ls with
           | none => none
           | some (bts, rest) =>
             (match pBendE LINE_FUEL ps bts with
              | some (e, []) =>
                (match parseBendAux f rest with
                 | none => none
                 | some ds => some ({ name := nm, params := ps.map jsName, body := e } :: ds))
              | _ => none)))
     | _ => parseBendAux f ls)

def parseBend (ls : List String) : Option (List BendDef) :=
  parseBendAux LINES_FUEL (ls.map String.toList)

def parseJS (ls : List String) : Option (List JSFn) :=
  parseFns (ls.map String.toList)

-- the runtime helpers, as the compiler emits them (their texts are compared exactly; the definitions model them)
def natChkBlock : List String :=
  ["function nat_chk(n) {", "  if (n > 281474976710655) {",
   "    throw \"bend: a Nat past the largest immediate 2^48-1\";", "  }", "  return n;", "}"]
def natInBlock : List String :=
  ["function nat_in(n) {", "  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {",
   "    throw \"bend: expected a Nat host number: an integer from 0 to 2^53\";", "  }", "  return n;", "}"]
def runLibBlock : List String :=
  ["function run_lib(f, n) {",
   "  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)",
   "    : run_loop(f(...a));", "}"]
def runLoopBlock : List String :=
  ["function run_loop(r) {", "  while (r !== null && typeof r === \"object\" && r.$ === \"$JMP\") {",
   "    r = r.f(r.x);", "  }", "  return r;", "}"]
def helperBlocks : List (List String) := [natChkBlock, natInBlock, runLibBlock, runLoopBlock]

def isPrefixL : List String → List String → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => (a == b) && isPrefixL as bs

def hasBlock (ls blk : List String) : Bool :=
  match ls with
  | [] => isPrefixL blk []
  | l :: rest => isPrefixL blk (l :: rest) || hasBlock rest blk

def argNames : Nat → List String
  | 0 => []
  | k + 1 => argNames k ++ ["a" ++ toString k]

def joinC : String → List String → String
  | _, [] => ""
  | _, [x] => x
  | sep, x :: xs => x ++ sep ++ joinC sep xs

-- the export line of a transition with k arguments, as the compiler emits it
def exportLine (nm : String) (k : Nat) : String :=
  let args := joinC "," (argNames k)
  let natArgs := joinC "," ((argNames k).map (fun a => "nat_in(" ++ a ++ ")"))
  "  \"" ++ nm ++ "\": run_lib((" ++ args ++ ") => run_loop($" ++ nm ++ "(" ++ natArgs ++ ")), " ++
    toString k ++ "),"

-- the check of a module: its transitions are the Bend definitions, each one checked, each one exported, and
-- the helpers are the expected texts
def checkProgram (defs : List BendDef) (fns : List JSFn) (lines : List String) : Bool :=
  decide (fns.length = defs.length) && nodupB (defs.map BendDef.name) &&
    helperBlocks.all (fun blk => hasBlock lines blk) &&
    defs.all fun b => fns.any fun j =>
      j.name == b.name && checkFn b j && lines.contains (exportLine b.name b.params.length)

-- the check on the parsed texts: the readers (parseBend, parseJS, in the readers section) make the parsed
-- terms, which the data section holds; the kernel checks them here, and does not read the texts itself
def checkAll (defs : List BendDef) (fns : List JSFn) (lines : List String) : Bool :=
  checkProgram defs fns lines

theorem checkProgram_sound (defs : List BendDef) (fns : List JSFn) (lines : List String)
    (h : checkProgram defs fns lines = true) :
    ∀ b ∈ defs, ∃ j ∈ fns, j.name = b.name ∧ checkFn b j = true ∧
      ∀ args : List Int, args.length = b.params.length → exportJS j args = refOf b args := by
  intro b hb
  unfold checkProgram at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  obtain ⟨_, hd⟩ := h
  obtain ⟨j, hj, hcond⟩ := hd b hb
  simp only [beq_iff_eq] at hcond
  obtain ⟨⟨hname, hfn⟩, _⟩ := hcond
  refine ⟨j, hj, hname, hfn, fun args hargs => ?_⟩
  exact export_correct b j hfn args hargs

-- ---- the data (generated from the two files by compiler_check.ts; do not edit between the markers) ----
-- each text is its lines, split on newline by compiler_check.ts (the kernel reads the lines, not one long string)
-- BEGIN-DATA
def bendText : List String :=
[
  "# tcp_transitions.bend: the state transitions of a browser TCP connection, the functions that the relay",
  "# (relay.ts) and the page's client (tcp_relay_client.js) call for every change to a count the invariants",
  "# talk about. The lemmas about them are in tcp_model.bend.",
  "#",
  "#   bend tcp_transitions.bend -o tcp_transitions.mjs     the JavaScript the code imports",
  "#",
  "# The page keeps: tail (bytes accepted by startSend), sent (SEND bytes framed), wp (the relay's written",
  "# count as the page last saw it), taken (bytes given to the program, each one granted to the relay by a READ),",
  "# recvd (DATA bytes received). The relay keeps: wr (bytes the socket took), q (SEND bytes queued), rd (bytes",
  "# read from the socket), gr (the credit the page granted, clamped to the window).",
  "import Base",
  "",
  "# ---- the transitions the code calls ----",
  "",
  "# the page accepts a send of len bytes",
  "def pg_start(+tail: Nat, +len: Nat) -> Nat:",
  "  Nat.add(tail, len)",
  "",
  "# the bytes of the next SEND frame: at most MAX_BODY, the window's slack, and the bytes left to send",
  "def pg_frame_n(+sent: Nat, +wp: Nat, +win: Nat, +tail: Nat, +mx: Nat) -> Nat:",
  "  Nat.min(mx, Nat.min(Nat.sub(win, Nat.sub(sent, wp)), Nat.sub(tail, sent)))",
  "",
  "def pg_sent(+sent: Nat, +n: Nat) -> Nat:",
  "  Nat.add(sent, n)",
  "",
  "# the bytes the program takes: at most max, and no more than were received and not yet taken",
  "def pg_take_n(+taken: Nat, +recvd: Nat, +mx: Nat) -> Nat:",
  "  Nat.min(mx, Nat.sub(recvd, taken))",
  "",
  "def pg_taken(+taken: Nat, +n: Nat) -> Nat:",
  "  Nat.add(taken, n)",
  "",
  "def pg_recv_data(+recvd: Nat, +k: Nat) -> Nat:",
  "  Nat.add(recvd, k)",
  "",
  "# the room the relay has for a SEND: win - q",
  "def rl_room(+win: Nat, +q: Nat) -> Nat:",
  "  Nat.sub(win, q)",
  "",
  "# the relay's test for a SEND of n bytes: 0 when n fits in the room, else more than 0",
  "def rl_over(+n: Nat, +room: Nat) -> Nat:",
  "  Nat.sub(n, room)",
  "",
  "def rl_queue(+q: Nat, +n: Nat) -> Nat:",
  "  Nat.add(q, n)",
  "",
  "def rl_written(+wr: Nat, +m: Nat) -> Nat:",
  "  Nat.add(wr, m)",
  "",
  "def rl_unqueue(+q: Nat, +m: Nat) -> Nat:",
  "  Nat.sub(q, m)",
  "",
  "def rl_read(+rd: Nat, +k: Nat) -> Nat:",
  "  Nat.add(rd, k)",
  "",
  "# the credit after a READ of n: the grant, clamped so that it never runs past the window",
  "def rl_grant(+rd: Nat, +gr: Nat, +win: Nat, +n: Nat) -> Nat:",
  "  Nat.min(Nat.add(rd, win), Nat.add(gr, n))",
  ""
]

def jsText : List String :=
[
  "function $pg_start(_tail_0, _len_0) {",
  "  return nat_chk(_tail_0 + _len_0);",
  "}",
  "",
  "function $pg_frame_n(_sent_0, _wp_0, _win_0, _tail_0, _mx_0) {",
  "  const _x_0 = (_sent_0 < _wp_0 ? 0 : _sent_0 - _wp_0);",
  "  const _x_1 = (_win_0 < _x_0 ? 0 : _win_0 - _x_0);",
  "  const _x_2 = (_tail_0 < _sent_0 ? 0 : _tail_0 - _sent_0);",
  "  const _x_3 = (_x_1 < _x_2 ? _x_1 : _x_2);",
  "  return (_mx_0 < _x_3 ? _mx_0 : _x_3);",
  "}",
  "",
  "function $pg_sent(_sent_0, _n_0) {",
  "  return nat_chk(_sent_0 + _n_0);",
  "}",
  "",
  "function $pg_take_n(_taken_0, _recvd_0, _mx_0) {",
  "  const _x_0 = (_recvd_0 < _taken_0 ? 0 : _recvd_0 - _taken_0);",
  "  return (_mx_0 < _x_0 ? _mx_0 : _x_0);",
  "}",
  "",
  "function $pg_taken(_taken_0, _n_0) {",
  "  return nat_chk(_taken_0 + _n_0);",
  "}",
  "",
  "function $pg_recv_data(_recvd_0, _k_0) {",
  "  return nat_chk(_recvd_0 + _k_0);",
  "}",
  "",
  "function $rl_room(_win_0, _q_0) {",
  "  return (_win_0 < _q_0 ? 0 : _win_0 - _q_0);",
  "}",
  "",
  "function $rl_over(_n_0, _room_0) {",
  "  return (_n_0 < _room_0 ? 0 : _n_0 - _room_0);",
  "}",
  "",
  "function $rl_queue(_q_0, _n_0) {",
  "  return nat_chk(_q_0 + _n_0);",
  "}",
  "",
  "function $rl_written(_wr_0, _m_0) {",
  "  return nat_chk(_wr_0 + _m_0);",
  "}",
  "",
  "function $rl_unqueue(_q_0, _m_0) {",
  "  return (_q_0 < _m_0 ? 0 : _q_0 - _m_0);",
  "}",
  "",
  "function $rl_read(_rd_0, _k_0) {",
  "  return nat_chk(_rd_0 + _k_0);",
  "}",
  "",
  "function $rl_grant(_rd_0, _gr_0, _win_0, _n_0) {",
  "  const _x_0 = nat_chk(_rd_0 + _win_0);",
  "  const _x_1 = nat_chk(_gr_0 + _n_0);",
  "  return (_x_0 < _x_1 ? _x_0 : _x_1);",
  "}",
  "export default {",
  "  \"pg_start\": run_lib((a0,a1) => run_loop($pg_start(nat_in(a0),nat_in(a1))), 2),",
  "  \"pg_frame_n\": run_lib((a0,a1,a2,a3,a4) => run_loop($pg_frame_n(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3),nat_in(a4))), 5),",
  "  \"pg_sent\": run_lib((a0,a1) => run_loop($pg_sent(nat_in(a0),nat_in(a1))), 2),",
  "  \"pg_take_n\": run_lib((a0,a1,a2) => run_loop($pg_take_n(nat_in(a0),nat_in(a1),nat_in(a2))), 3),",
  "  \"pg_taken\": run_lib((a0,a1) => run_loop($pg_taken(nat_in(a0),nat_in(a1))), 2),",
  "  \"pg_recv_data\": run_lib((a0,a1) => run_loop($pg_recv_data(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_room\": run_lib((a0,a1) => run_loop($rl_room(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_over\": run_lib((a0,a1) => run_loop($rl_over(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_queue\": run_lib((a0,a1) => run_loop($rl_queue(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_written\": run_lib((a0,a1) => run_loop($rl_written(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_unqueue\": run_lib((a0,a1) => run_loop($rl_unqueue(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_read\": run_lib((a0,a1) => run_loop($rl_read(nat_in(a0),nat_in(a1))), 2),",
  "  \"rl_grant\": run_lib((a0,a1,a2,a3) => run_loop($rl_grant(nat_in(a0),nat_in(a1),nat_in(a2),nat_in(a3))), 4),",
  "};"
]

def helperText : List String :=
[
  "function nat_chk(n) {",
  "  if (n > 281474976710655) {",
  "    throw \"bend: a Nat past the largest immediate 2^48-1\";",
  "  }",
  "  return n;",
  "}",
  "function nat_in(n) {",
  "  if (!Number.isInteger(n) || n < 0 || n > 2 ** 53) {",
  "    throw \"bend: expected a Nat host number: an integer from 0 to 2^53\";",
  "  }",
  "  return n;",
  "}",
  "function run_lib(f, n) {",
  "  return (...a) => a.length < n ? run_lib((...b) => f(...a, ...b), n - a.length)",
  "    : run_loop(f(...a));",
  "}",
  "function run_loop(r) {",
  "  while (r !== null && typeof r === \"object\" && r.$ === \"$JMP\") {",
  "    r = r.f(r.x);",
  "  }",
  "  return r;",
  "}"
]

def bendAST : List BendDef :=
  [{ name := "pg_start",
     params := ["_tail_0", "_len_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_tail_0") (CompilerCheck.BE.var "_len_0") },
   { name := "pg_frame_n",
     params := ["_sent_0", "_wp_0", "_win_0", "_tail_0", "_mx_0"],
     body := CompilerCheck.BE.min
               (CompilerCheck.BE.var "_mx_0")
               (CompilerCheck.BE.min
                 (CompilerCheck.BE.sub
                   (CompilerCheck.BE.var "_win_0")
                   (CompilerCheck.BE.sub (CompilerCheck.BE.var "_sent_0") (CompilerCheck.BE.var "_wp_0")))
                 (CompilerCheck.BE.sub (CompilerCheck.BE.var "_tail_0") (CompilerCheck.BE.var "_sent_0"))) },
   { name := "pg_sent",
     params := ["_sent_0", "_n_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_sent_0") (CompilerCheck.BE.var "_n_0") },
   { name := "pg_take_n",
     params := ["_taken_0", "_recvd_0", "_mx_0"],
     body := CompilerCheck.BE.min
               (CompilerCheck.BE.var "_mx_0")
               (CompilerCheck.BE.sub (CompilerCheck.BE.var "_recvd_0") (CompilerCheck.BE.var "_taken_0")) },
   { name := "pg_taken",
     params := ["_taken_0", "_n_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_taken_0") (CompilerCheck.BE.var "_n_0") },
   { name := "pg_recv_data",
     params := ["_recvd_0", "_k_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_recvd_0") (CompilerCheck.BE.var "_k_0") },
   { name := "rl_room",
     params := ["_win_0", "_q_0"],
     body := CompilerCheck.BE.sub (CompilerCheck.BE.var "_win_0") (CompilerCheck.BE.var "_q_0") },
   { name := "rl_over",
     params := ["_n_0", "_room_0"],
     body := CompilerCheck.BE.sub (CompilerCheck.BE.var "_n_0") (CompilerCheck.BE.var "_room_0") },
   { name := "rl_queue",
     params := ["_q_0", "_n_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_q_0") (CompilerCheck.BE.var "_n_0") },
   { name := "rl_written",
     params := ["_wr_0", "_m_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_wr_0") (CompilerCheck.BE.var "_m_0") },
   { name := "rl_unqueue",
     params := ["_q_0", "_m_0"],
     body := CompilerCheck.BE.sub (CompilerCheck.BE.var "_q_0") (CompilerCheck.BE.var "_m_0") },
   { name := "rl_read",
     params := ["_rd_0", "_k_0"],
     body := CompilerCheck.BE.add (CompilerCheck.BE.var "_rd_0") (CompilerCheck.BE.var "_k_0") },
   { name := "rl_grant",
     params := ["_rd_0", "_gr_0", "_win_0", "_n_0"],
     body := CompilerCheck.BE.min
               (CompilerCheck.BE.add (CompilerCheck.BE.var "_rd_0") (CompilerCheck.BE.var "_win_0"))
               (CompilerCheck.BE.add (CompilerCheck.BE.var "_gr_0") (CompilerCheck.BE.var "_n_0")) }]

def jsAST : List JSFn :=
  [{ name := "pg_start",
     params := ["_tail_0", "_len_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_tail_0") (CompilerCheck.JE.v "_len_0")) },
   { name := "pg_frame_n",
     params := ["_sent_0", "_wp_0", "_win_0", "_tail_0", "_mx_0"],
     consts := [("_x_0",
                 CompilerCheck.JE.cond
                   (CompilerCheck.JE.v "_sent_0")
                   (CompilerCheck.JE.v "_wp_0")
                   (CompilerCheck.JE.n 0)
                   (CompilerCheck.JE.sub (CompilerCheck.JE.v "_sent_0") (CompilerCheck.JE.v "_wp_0"))),
                ("_x_1",
                 CompilerCheck.JE.cond
                   (CompilerCheck.JE.v "_win_0")
                   (CompilerCheck.JE.v "_x_0")
                   (CompilerCheck.JE.n 0)
                   (CompilerCheck.JE.sub (CompilerCheck.JE.v "_win_0") (CompilerCheck.JE.v "_x_0"))),
                ("_x_2",
                 CompilerCheck.JE.cond
                   (CompilerCheck.JE.v "_tail_0")
                   (CompilerCheck.JE.v "_sent_0")
                   (CompilerCheck.JE.n 0)
                   (CompilerCheck.JE.sub (CompilerCheck.JE.v "_tail_0") (CompilerCheck.JE.v "_sent_0"))),
                ("_x_3",
                 CompilerCheck.JE.cond
                   (CompilerCheck.JE.v "_x_1")
                   (CompilerCheck.JE.v "_x_2")
                   (CompilerCheck.JE.v "_x_1")
                   (CompilerCheck.JE.v "_x_2"))],
     ret := CompilerCheck.JE.cond
              (CompilerCheck.JE.v "_mx_0")
              (CompilerCheck.JE.v "_x_3")
              (CompilerCheck.JE.v "_mx_0")
              (CompilerCheck.JE.v "_x_3") },
   { name := "pg_sent",
     params := ["_sent_0", "_n_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_sent_0") (CompilerCheck.JE.v "_n_0")) },
   { name := "pg_take_n",
     params := ["_taken_0", "_recvd_0", "_mx_0"],
     consts := [("_x_0",
                 CompilerCheck.JE.cond
                   (CompilerCheck.JE.v "_recvd_0")
                   (CompilerCheck.JE.v "_taken_0")
                   (CompilerCheck.JE.n 0)
                   (CompilerCheck.JE.sub (CompilerCheck.JE.v "_recvd_0") (CompilerCheck.JE.v "_taken_0")))],
     ret := CompilerCheck.JE.cond
              (CompilerCheck.JE.v "_mx_0")
              (CompilerCheck.JE.v "_x_0")
              (CompilerCheck.JE.v "_mx_0")
              (CompilerCheck.JE.v "_x_0") },
   { name := "pg_taken",
     params := ["_taken_0", "_n_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_taken_0") (CompilerCheck.JE.v "_n_0")) },
   { name := "pg_recv_data",
     params := ["_recvd_0", "_k_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_recvd_0") (CompilerCheck.JE.v "_k_0")) },
   { name := "rl_room",
     params := ["_win_0", "_q_0"],
     consts := [],
     ret := CompilerCheck.JE.cond
              (CompilerCheck.JE.v "_win_0")
              (CompilerCheck.JE.v "_q_0")
              (CompilerCheck.JE.n 0)
              (CompilerCheck.JE.sub (CompilerCheck.JE.v "_win_0") (CompilerCheck.JE.v "_q_0")) },
   { name := "rl_over",
     params := ["_n_0", "_room_0"],
     consts := [],
     ret := CompilerCheck.JE.cond
              (CompilerCheck.JE.v "_n_0")
              (CompilerCheck.JE.v "_room_0")
              (CompilerCheck.JE.n 0)
              (CompilerCheck.JE.sub (CompilerCheck.JE.v "_n_0") (CompilerCheck.JE.v "_room_0")) },
   { name := "rl_queue",
     params := ["_q_0", "_n_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_q_0") (CompilerCheck.JE.v "_n_0")) },
   { name := "rl_written",
     params := ["_wr_0", "_m_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_wr_0") (CompilerCheck.JE.v "_m_0")) },
   { name := "rl_unqueue",
     params := ["_q_0", "_m_0"],
     consts := [],
     ret := CompilerCheck.JE.cond
              (CompilerCheck.JE.v "_q_0")
              (CompilerCheck.JE.v "_m_0")
              (CompilerCheck.JE.n 0)
              (CompilerCheck.JE.sub (CompilerCheck.JE.v "_q_0") (CompilerCheck.JE.v "_m_0")) },
   { name := "rl_read",
     params := ["_rd_0", "_k_0"],
     consts := [],
     ret := CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_rd_0") (CompilerCheck.JE.v "_k_0")) },
   { name := "rl_grant",
     params := ["_rd_0", "_gr_0", "_win_0", "_n_0"],
     consts := [("_x_0",
                 CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_rd_0") (CompilerCheck.JE.v "_win_0"))),
                ("_x_1",
                 CompilerCheck.JE.chk (CompilerCheck.JE.add (CompilerCheck.JE.v "_gr_0") (CompilerCheck.JE.v "_n_0")))],
     ret := CompilerCheck.JE.cond
              (CompilerCheck.JE.v "_x_0")
              (CompilerCheck.JE.v "_x_1")
              (CompilerCheck.JE.v "_x_0")
              (CompilerCheck.JE.v "_x_1") }]
-- END-DATA

-- ================================================================================================
-- The theorems about the data
-- ================================================================================================

theorem checked : checkAll bendAST jsAST (jsText ++ helperText) = true := by decide +kernel

theorem transitions_correct : ∀ b ∈ bendAST, ∃ j ∈ jsAST, j.name = b.name ∧
    ∀ args : List Int, args.length = b.params.length → exportJS j args = refOf b args := by
  intro b hb
  obtain ⟨j, hj, hname, _, hexp⟩ := checkProgram_sound bendAST jsAST (jsText ++ helperText) checked b hb
  exact ⟨j, hj, hname, hexp⟩

end CompilerCheck
