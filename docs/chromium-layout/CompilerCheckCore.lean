/-
docs/chromium-layout/CompilerCheckCore.lean:
Core semantics, translation validation (`decomp` / `decompRet`), and soundness theorems
for extended translation validation of the Bend compiler's JavaScript output (Phase 5 / M5).

Covers:
  1. `Nat.max` (`BE.max` on the Bend side, compiled to the `>` guard `a > b ? a : b`, `JE.condGt`,
     on the JavaScript side).
  2. Record constructors (`JRet.record` `{ $: "Tag", "field": expr, ... }` on the JavaScript side
     and `BRet.record` `Tag{expr, ...}` on the Bend side, together with record field projections
     `const _f_0 = _p_0["field"];`).

Checked by `docs/chromium-layout/check.sh` with Lean 4.34.0 and `#print axioms` (no `sorryAx`).
-/

namespace CompilerCheck

-- ================================================================================================
-- 1. The Semantics (Extended with `JE.condGt` / `BE.max` and Record Constructors)
-- ================================================================================================

-- 2^48 - 1: the largest immediate Nat (nat_chk); 2^53: the largest host number (nat_in)
def LIMIT : Nat := 281474976710655
def HOST : Nat := 9007199254740992

/-- A JavaScript scalar expression of a transition:
    - variable/field reference `.v x`
    - numeric literal `.n k`
    - exact addition `.add a b` and subtraction `.sub a b`
    - immediate range check `.chk e` (`nat_chk(e)`)
    - `<` conditional `.cond a b t f` (`a < b ? t : f`, used for `Nat.sub` and `Nat.min`)
    - `>` conditional `.condGt a b t f` (`a > b ? t : f`, used for `Nat.max`) -/
inductive JE where
  | v (x : String)
  | n (k : Nat)
  | add (a b : JE)
  | sub (a b : JE)
  | chk (e : JE)
  | cond (a b t f : JE)
  | condGt (a b t f : JE)
  deriving DecidableEq, Repr

/-- A Bend scalar expression: `var`, `add` (`Nat.add`), `sub` (`Nat.sub`),
    `min` (`Nat.min`), and `max` (`Nat.max`). -/
inductive BE where
  | var (x : String)
  | n (k : Nat)
  | add (a b : BE)
  | sub (a b : BE)
  | min (a b : BE)
  | max (a b : BE)
  deriving DecidableEq, Repr

/-- A JavaScript return value: either a scalar expression or a record constructor
    `{$: "Tag", "field_1": e_1, ...}`. -/
inductive JRet where
  | scalar (e : JE)
  | record (tag : String) (fields : List (String × JE))
  deriving DecidableEq, Repr

/-- A Bend body return value: either a scalar expression or a record constructor
    `Tag{b_1, ...}` with field names from its `type` declaration. -/
inductive BRet where
  | scalar (b : BE)
  | record (tag : String) (fields : List (String × BE))
  deriving DecidableEq, Repr

/-- Runtime value returned by a validated function: either a scalar `Nat` or a record of `Nat` fields. -/
inductive Val where
  | scalar (n : Nat)
  | record (tag : String) (fields : List (String × Nat))
  deriving DecidableEq, Repr

abbrev Env := String → Nat

def upd (ρ : Env) (x : String) (v : Nat) : Env := fun y => if y = x then v else ρ y

def mkEnv : List String → List Nat → Env
  | p :: ps, a :: as => upd (mkEnv ps as) p a
  | _, _ => fun _ => 0

-- JavaScript scalar evaluation: `none` represents a runtime throw (`nat_chk`).
def jsE (ρ : Env) : JE → Option Nat
  | .v x => some (ρ x)
  | .n k => some k
  | .add a b => (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => some (x + y)
  | .sub a b => (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => some (x - y)
  | .chk e => (jsE ρ e).bind fun v => if v ≤ LIMIT then some v else none
  | .cond a b t f =>
      (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => if x < y then jsE ρ t else jsE ρ f
  | .condGt a b t f =>
      (jsE ρ a).bind fun x => (jsE ρ b).bind fun y => if x > y then jsE ρ t else jsE ρ f

-- Bend scalar evaluation with the 2^48 - 1 immediate limit on `Nat.add`.
def bendE (ρ : Env) : BE → Option Nat
  | .var x => some (ρ x)
  | .n k => some k
  | .add a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y =>
      if x + y ≤ LIMIT then some (x + y) else none
  | .sub a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y => some (x - y)
  | .min a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y => some (min x y)
  | .max a b => (bendE ρ a).bind fun x => (bendE ρ b).bind fun y => some (Nat.max x y)

-- Unbounded Nat evaluation (the value Bend's proofs reason about).
def natE (ρ : Env) : BE → Nat
  | .var x => ρ x
  | .n k => k
  | .add a b => natE ρ a + natE ρ b
  | .sub a b => natE ρ a - natE ρ b
  | .min a b => min (natE ρ a) (natE ρ b)
  | .max a b => Nat.max (natE ρ a) (natE ρ b)

def jsFieldsE (ρ : Env) : List (String × JE) → Option (List (String × Nat))
  | [] => some []
  | (fnm, e) :: rest =>
    (jsE ρ e).bind fun v =>
      (jsFieldsE ρ rest).bind fun vs =>
        some ((fnm, v) :: vs)

def bendFieldsE (ρ : Env) : List (String × BE) → Option (List (String × Nat))
  | [] => some []
  | (fnm, b) :: rest =>
    (bendE ρ b).bind fun v =>
      (bendFieldsE ρ rest).bind fun vs =>
        some ((fnm, v) :: vs)

def jsRetE (ρ : Env) : JRet → Option Val
  | .scalar e => (jsE ρ e).bind fun v => some (.scalar v)
  | .record tag fs => (jsFieldsE ρ fs).bind fun vs => some (.record tag vs)

def bendRetE (ρ : Env) : BRet → Option Val
  | .scalar b => (bendE ρ b).bind fun v => some (.scalar v)
  | .record tag fs => (bendFieldsE ρ fs).bind fun vs => some (.record tag vs)

-- ================================================================================================
-- 2. Translation Validation (`decomp` and `decompRet`)
-- ================================================================================================

abbrev Sigma := List (String × BE)

def decomp (ps : List String) (σ : Sigma) : JE → Option BE
  | .v x => match σ.lookup x with
    | some t => some t
    | none => if ps.contains x then some (BE.var x) else none
  | .n k => some (BE.n k)
  | .chk (.add a b) => (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.add a' b')
  | .cond a b t f =>
    if t = JE.n 0 ∧ f = JE.sub a b then
      (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.sub a' b')
    else if t = a ∧ f = b then
      (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.min a' b')
    else none
  | .condGt a b t f =>
    if t = a ∧ f = b then
      (decomp ps σ a).bind fun a' => (decomp ps σ b).bind fun b' => some (BE.max a' b')
    else none
  | _ => none

def decompFields (ps : List String) (σ : Sigma) : List (String × JE) → Option (List (String × BE))
  | [] => some []
  | (fnm, e) :: rest =>
    (decomp ps σ e).bind fun b =>
      (decompFields ps σ rest).bind fun bs =>
        some ((fnm, b) :: bs)

def decompRet (ps : List String) (σ : Sigma) : JRet → Option BRet
  | .scalar e => (decomp ps σ e).bind fun b => some (.scalar b)
  | .record tag fs => (decompFields ps σ fs).bind fun bs => some (.record tag bs)

def buildSigma (ps : List String) : List (String × JE) → Sigma → Option Sigma
  | [], σ => some σ
  | (x, e) :: rest, σ => (decomp ps σ e).bind fun t => buildSigma ps rest (σ ++ [(x, t)])

def hasSub (s : BE) : BE → Bool
  | .var x => decide (s = .var x)
  | .n k => decide (s = .n k)
  | .add a b => decide (s = .add a b) || hasSub s a || hasSub s b
  | .sub a b => decide (s = .sub a b) || hasSub s a || hasSub s b
  | .min a b => decide (s = .min a b) || hasSub s a || hasSub s b
  | .max a b => decide (s = .max a b) || hasSub s a || hasSub s b

def hasSubRet (s : BE) : BRet → Bool
  | .scalar b => hasSub s b
  | .record _ fs => fs.any fun (_, b) => hasSub s b

-- ================================================================================================
-- 3. Programs and Equivalence Checkers (Scalar and Record)
-- ================================================================================================

structure JSFn where
  name : String
  params : List String
  consts : List (String × JE)
  ret : JE
  deriving DecidableEq, Repr

structure BendDef where
  name : String
  params : List String
  body : BE
  deriving DecidableEq, Repr

structure JSRecFn where
  name : String
  params : List String
  consts : List (String × JE)
  ret : JRet
  deriving DecidableEq, Repr

structure BendRecDef where
  name : String
  params : List String
  body : BRet
  deriving DecidableEq, Repr

def jsRunC (ρ : Env) : List (String × JE) → Option Env
  | [] => some ρ
  | (x, e) :: rest => (jsE ρ e).bind fun v => jsRunC (upd ρ x v) rest

def jsRun (j : JSFn) (args : List Nat) : Option Nat :=
  (jsRunC (mkEnv j.params args) j.consts).bind fun ρ => jsE ρ j.ret

def jsRecRun (j : JSRecFn) (args : List Nat) : Option Val :=
  (jsRunC (mkEnv j.params args) j.consts).bind fun ρ => jsRetE ρ j.ret

def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

def disjointB (ps names : List String) : Bool := names.all fun x => !ps.contains x

def checkFn (b : BendDef) (j : JSFn) : Bool :=
  decide (j.params = b.params) && nodupB (j.consts.map Prod.fst) &&
    disjointB j.params (j.consts.map Prod.fst) &&
    (match buildSigma j.params j.consts [] with
     | none => false
     | some σ => match decomp j.params σ j.ret with
       | none => false
       | some B => decide (B = b.body) && σ.all fun e => hasSub e.2 B)

def checkRecFn (b : BendRecDef) (j : JSRecFn) : Bool :=
  decide (j.params = b.params) && nodupB (j.consts.map Prod.fst) &&
    disjointB j.params (j.consts.map Prod.fst) &&
    (match buildSigma j.params j.consts [] with
     | none => false
     | some σ => match decompRet j.params σ j.ret with
       | none => false
       | some B => decide (B = b.body) && σ.all fun e => hasSubRet e.2 B)

def natIn (a : Int) : Option Nat := if 0 ≤ a ∧ a ≤ (HOST : Int) then some a.toNat else none

def natList : List Int → Option (List Nat)
  | [] => some []
  | a :: as => (natIn a).bind fun n => (natList as).bind fun ns => some (n :: ns)

def exportJS (j : JSFn) (args : List Int) : Option Nat := (natList args).bind fun ns => jsRun j ns

def refOf (b : BendDef) (args : List Int) : Option Nat :=
  (natList args).bind fun ns => bendE (mkEnv b.params ns) b.body

-- ================================================================================================
-- 4. Soundness Proofs (Extended with `JE.condGt` / `BE.max` and Record Returns)
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
  | .n k, b, hd, _, _, _ => by
    simp only [decomp, Option.some.injEq] at hd
    subst hd
    rfl
  | .add a c, b, hd, _, _, _ => by simp [decomp] at hd
  | .sub a c, b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.v x), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.n k), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.sub a c), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.chk e), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.cond a c t f), b, hd, _, _, _ => by simp [decomp] at hd
  | .chk (.condGt a c t f), b, hd, _, _, _ => by simp [decomp] at hd
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
  | .condGt a c t f, b, hd, ρ, hp, ha => by
    unfold decomp at hd
    by_cases h1 : t = a ∧ f = c
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
            · by_cases hxy : x > y
              · have hle : y ≤ x := Nat.le_of_lt hxy
                simp [hxy, Nat.max_eq_left hle]
              · have hle : x ≤ y := Nat.le_of_not_lt hxy
                simp [hxy, Nat.max_eq_right hle]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)] at hd
      simp at hd

theorem decompFields_sound (ps : List String) (ρ0 : Env) (σ : Sigma) :
    ∀ (jfs : List (String × JE)) (bfs : List (String × BE)),
      decompFields ps σ jfs = some bfs → ∀ (ρ : Env),
      (∀ p ∈ ps, ρ p = ρ0 p) → (∀ y s, (y, s) ∈ σ → ∃ v, bendE ρ0 s = some v ∧ ρ y = v) →
      jsFieldsE ρ jfs = bendFieldsE ρ0 bfs
  | [], bfs, hd, _, _, _ => by
    simp only [decompFields, Option.some.injEq] at hd
    subst hd
    rfl
  | (fnm, e) :: rest, bfs, hd, ρ, hp, ha => by
    unfold decompFields at hd
    cases h1 : decomp ps σ e with
    | none => simp [h1] at hd
    | some b =>
      cases h2 : decompFields ps σ rest with
      | none => simp [h1, h2] at hd
      | some bs =>
        simp only [h1, h2, Option.bind_some, Option.some.injEq] at hd
        subst hd
        have ie := decomp_sound ps ρ0 σ e b h1 ρ hp ha
        have ir := decompFields_sound ps ρ0 σ rest bs h2 ρ hp ha
        simp only [jsFieldsE, bendFieldsE, ie, ir]

theorem decompRet_sound (ps : List String) (ρ0 : Env) (σ : Sigma) :
    ∀ (jr : JRet) (br : BRet),
      decompRet ps σ jr = some br → ∀ (ρ : Env),
      (∀ p ∈ ps, ρ p = ρ0 p) → (∀ y s, (y, s) ∈ σ → ∃ v, bendE ρ0 s = some v ∧ ρ y = v) →
      jsRetE ρ jr = bendRetE ρ0 br
  | .scalar e, br, hd, ρ, hp, ha => by
    unfold decompRet at hd
    cases h1 : decomp ps σ e with
    | none => simp [h1] at hd
    | some b =>
      simp only [h1, Option.bind_some, Option.some.injEq] at hd
      subst hd
      have ie := decomp_sound ps ρ0 σ e b h1 ρ hp ha
      simp only [jsRetE, bendRetE, ie]
  | .record tag jfs, br, hd, ρ, hp, ha => by
    unfold decompRet at hd
    cases h1 : decompFields ps σ jfs with
    | none => simp [h1] at hd
    | some bfs =>
      simp only [h1, Option.bind_some, Option.some.injEq] at hd
      subst hd
      have ifs := decompFields_sound ps ρ0 σ jfs bfs h1 ρ hp ha
      simp only [jsRetE, bendRetE, ifs]

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
  | s, .n k, h, hs => by
    have hk : s = .n k := by simpa [hasSub] using h
    subst hk
    simp [bendE] at hs
  | s, .add a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h; exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]
  | s, .sub a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h; exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]
  | s, .min a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h; exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]
  | s, .max a c, h, hs => by
    simp only [hasSub, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · subst h; exact hs
    · simp [bendE, hasSub_none ρ s a h hs]
    · simp [bendE, hasSub_none ρ s c h hs]

theorem hasSubFields_none (ρ : Env) (s : BE) (hs : bendE ρ s = none) :
    ∀ (fs : List (String × BE)),
      (fs.any fun (_, b) => hasSub s b) = true →
      bendFieldsE ρ fs = none
  | [], h => by simp at h
  | (fnm, b) :: rest, h => by
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with hb | hr
    · have hbn := hasSub_none ρ s b hb hs
      simp [bendFieldsE, hbn]
    · have hrn := hasSubFields_none ρ s hs rest hr
      cases bendE ρ b <;> simp [bendFieldsE, hrn]

theorem hasSubRet_none (ρ : Env) (s : BE) (hs : bendE ρ s = none) :
    ∀ (br : BRet), hasSubRet s br = true → bendRetE ρ br = none
  | .scalar b, h => by
    have hbn := hasSub_none ρ s b h hs
    simp [bendRetE, hbn]
  | .record tag fs, h => by
    have hfn := hasSubFields_none ρ s hs fs h
    simp [bendRetE, hfn]

theorem natE_of_bendE (ρ : Env) : ∀ (t : BE) (v : Nat), bendE ρ t = some v → natE ρ t = v
  | .var x, v, h => by
    simp only [bendE, Option.some.injEq] at h
    simp [natE, h]
  | .n k, v, h => by
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
  | .max a c, v, h => by
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

theorem checkRecFn_params (b : BendRecDef) (j : JSRecFn) (h : checkRecFn b j = true) : j.params = b.params := by
  unfold checkRecFn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

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

theorem fn_correct (b : BendDef) (j : JSFn) (h : checkFn b j = true) (ns : List Nat) :
    jsRun j ns = bendE (mkEnv j.params ns) b.body := by
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

/-- Soundness of record-returning functions validated by `checkRecFn` (including `Nat.max`
    and record constructors `{ $: "Tag", ... }`). -/
theorem rec_fn_correct (b : BendRecDef) (j : JSRecFn) (h : checkRecFn b j = true) (ns : List Nat) :
    jsRecRun j ns = bendRetE (mkEnv j.params ns) b.body := by
  unfold checkRecFn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hnd⟩, hdis⟩, hd⟩ := h
  rcases hσ : buildSigma j.params j.consts [] with _ | σ'
  · simp [hσ] at hd
  · rcases hdec : decompRet j.params σ' j.ret with _ | B
    · simp [hσ, hdec] at hd
    · simp only [hσ, hdec, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hd
      obtain ⟨hB, hcont⟩ := hd
      have hnd' : (j.consts.map Prod.fst).Nodup := nodupB_sound _ hnd
      have hpar' : ∀ x ∈ j.consts.map Prod.fst, x ∉ j.params := disjointB_sound _ _ hdis
      rcases run_build j.params (mkEnv j.params ns) j.consts [] σ' (mkEnv j.params ns) hσ
          (fun _ _ => rfl) (by simp) (by simp) hnd' hpar' with
        ⟨ρ', hr, hp', ha'⟩ | ⟨hr, y, s, hm, hn⟩
      · have hres := decompRet_sound j.params (mkEnv j.params ns) σ' j.ret B hdec ρ' hp' ha'
        simp only [jsRecRun, hr, Option.bind_some]
        rw [hres, ← hB]
      · have hc := hcont (y, s) hm
        simp only [jsRecRun, hr, Option.bind_none]
        have hz := hasSubRet_none (mkEnv j.params ns) s hn B hc
        rw [hB] at hz
        exact hz.symm

theorem export_correct (b : BendDef) (j : JSFn) (h : checkFn b j = true) (args : List Int)
    (_hl : args.length = b.params.length) : exportJS j args = refOf b args := by
  have hpar := checkFn_params b j h
  unfold exportJS refOf
  rcases hn : natList args with _ | ns
  · simp
  · simp only [Option.bind_some]
    rw [fn_correct b j h ns, hpar]

end CompilerCheck
