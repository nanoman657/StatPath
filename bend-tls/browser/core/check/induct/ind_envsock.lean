
namespace Ind
open Timed

theorem relay_step_sock (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) (hcl : s.closed.isSome = false) :
    Relay.step cap s (.sock id g k) = Relay.sockStep cap s id g k := by
  unfold Relay.step
  simp [hcl]

-- the clocked socket event: its relay effect is the socket step's (the closed relay does nothing)
theorem stepK_sock_spec (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk) :
    SockSpec s id (Clock.stepK cap k s (.sock id g kk)).2.1 (Clock.stepK cap k s (.sock id g kk)).2.2 := by
  unfold Clock.stepK
  split
  · exact sockSpec_same s id
  · rename_i hnc
    have hcl : s.closed.isSome = false := by simpa using hnc
    cases kk with
    | drain a =>
      dsimp only
      rcases hc : (s.slot id).conn with _ | c
      · dsimp only
        rw [relay_step_sock cap s id g _ hcl]
        exact sockStep_spec cap s id g _
      · dsimp only
        split
        · rw [relay_step_sock cap s id g _ hcl]
          exact sockStep_spec cap s id g _
        · rw [relay_step_sock cap s id g _ hcl]
          exact sockStep_spec cap s id g _
    | data n =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_spec cap s id g _
    | open_ =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_spec cap s id g _
    | eof =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_spec cap s id g _
    | peerclose =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_spec cap s id g _
    | error e =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_spec cap s id g _

-- an if-then-else keeps the generation counter when both of its branches do
theorem ite_nextGen {p : Prop} [Decidable p] {A B : Relay.St × List Relay.Out} {s : Relay.St}
    (hA : A.1.nextGen = s.nextGen) (hB : B.1.nextGen = s.nextGen) :
    (if p then A else B).1.nextGen = s.nextGen := by
  split <;> assumption

-- a socket event never changes the generation counter (it changes connections, not the counter)
theorem sockStep_nextGen (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) :
    (Relay.sockStep cap s id g k).1.nextGen = s.nextGen := by
  unfold Relay.sockStep
  rcases hc : (s.slot id).conn with _ | c
  · rfl
  · cases k
    all_goals (try dsimp only)
    all_goals (iterate 4 (all_goals (try apply ite_nextGen)))
    all_goals (try rfl)
    all_goals (simp_all [Relay.failConn, flushConn_nextGen, Relay.setConn, Relay.setSlot])

theorem stepK_sock_nextGen (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk) :
    (Clock.stepK cap k s (.sock id g kk)).2.1.nextGen = s.nextGen := by
  unfold Clock.stepK
  split
  · rfl
  · rename_i hnc
    have hcl : s.closed.isSome = false := by simpa using hnc
    cases kk with
    | drain a =>
      dsimp only
      rcases hc : (s.slot id).conn with _ | c
      · dsimp only
        rw [relay_step_sock cap s id g _ hcl]
        exact sockStep_nextGen cap s id g _
      · dsimp only
        split
        · rw [relay_step_sock cap s id g _ hcl]
          exact sockStep_nextGen cap s id g _
        · rw [relay_step_sock cap s id g _ hcl]
          exact sockStep_nextGen cap s id g _
    | data n =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_nextGen cap s id g _
    | open_ =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_nextGen cap s id g _
    | eof =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_nextGen cap s id g _
    | peerclose =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_nextGen cap s id g _
    | error e =>
      dsimp only
      rw [relay_step_sock cap s id g _ hcl]
      exact sockStep_nextGen cap s id g _


-- the socket step's OK frame: only from a connection of the id that was not open (and it opens it)
theorem sockStep_ok_fact (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) (o : Relay.Out)
    (ho : o ∈ (Relay.sockStep cap s id g k).2) (hoe : o = Relay.Out.ok id) :
    ∃ c0, (s.slot id).conn = some c0 ∧ c0.isOpen = false := by
  subst hoe
  unfold Relay.sockStep at ho
  rcases hc : (s.slot id).conn with _ | c
  · rw [hc] at ho; simp at ho
  · rw [hc] at ho
    dsimp only at ho
    split at ho
    · simp at ho
    · cases k with
      | open_ =>
        dsimp only at ho
        split at ho
        · simp at ho
        · rename_i hopen
          exact ⟨c, rfl, by simpa using hopen⟩
      | data n =>
        dsimp only at ho
        split at ho <;> (try split at ho) <;> (try split at ho) <;> simp_all [Relay.failConn]
      | eof => simp at ho
      | peerclose =>
        dsimp only at ho
        split at ho
        · simp_all [Relay.failConn]
        · simp at ho
      | error e => simp_all [Relay.failConn]
      | drain a =>
        dsimp only at ho
        unfold Relay.flushConn at ho
        dsimp only at ho
        iterate 3 (all_goals (try split at ho))
        all_goals simp_all

-- the socket step's FAIL frame: its connection of the id is gone afterwards
theorem sockStep_fail_fact (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) (o : Relay.Out) (e : Nat)
    (ho : o ∈ (Relay.sockStep cap s id g k).2) (hoe : o = Relay.Out.fail id e) :
    ((Relay.sockStep cap s id g k).1.slot id).conn = none := by
  subst hoe
  unfold Relay.sockStep at ho ⊢
  rcases hc : (s.slot id).conn with _ | c
  · rw [hc] at ho; simp at ho
  · rw [hc] at ho
    dsimp only at ho ⊢
    split at ho
    · simp at ho
    · cases k with
      | open_ =>
        dsimp only at ho ⊢
        split at ho
        · simp at ho
        · simp at ho
      | data n =>
        dsimp only at ho ⊢
        iterate 4 (all_goals (try (split at ho)))
        iterate 4 (all_goals (try split))
        all_goals simp_all [Relay.failConn, Relay.slot_setConn_self]
      | eof => simp at ho
      | peerclose =>
        dsimp only at ho ⊢
        split at ho
        · iterate 4 (all_goals (try split))
          all_goals simp_all [Relay.failConn, Relay.slot_setConn_self]
        · simp at ho
      | error e' =>
        iterate 4 (all_goals (try split))
        all_goals simp_all [Relay.failConn, Relay.slot_setConn_self]
      | drain a =>
        dsimp only at ho ⊢
        unfold Relay.flushConn at ho
        dsimp only at ho
        iterate 3 (all_goals (try split at ho))
        all_goals simp_all


-- the clocked socket step's relay effect is the socket step's, with some kind of event (the drain's amount, or
-- the kind itself): the clock only moves the budget and the queues
theorem stepK_sock_eq (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk)
    (hcl : s.closed.isSome = false) :
    ∃ k', (Clock.stepK cap k s (.sock id g kk)).2.1 = (Relay.sockStep cap s id g k').1 ∧
      (Clock.stepK cap k s (.sock id g kk)).2.2 = (Relay.sockStep cap s id g k').2 := by
  unfold Clock.stepK
  rw [if_neg (by simp [hcl])]
  cases kk with
  | drain a =>
    dsimp only
    rcases hc : (s.slot id).conn with _ | c
    · dsimp only
      refine ⟨Relay.Sk.drain a, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
    · dsimp only
      split
      · refine ⟨Relay.Sk.drain (Clock.flushSim (k.chunks id) a k.bud).1, ?_, ?_⟩ <;>
          (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
      · refine ⟨Relay.Sk.drain a, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
  | data n =>
    dsimp only
    refine ⟨Relay.Sk.data n, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
  | open_ =>
    dsimp only
    refine ⟨Relay.Sk.open_, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
  | eof =>
    dsimp only
    refine ⟨Relay.Sk.eof, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
  | peerclose =>
    dsimp only
    refine ⟨Relay.Sk.peerclose, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl
  | error e =>
    dsimp only
    refine ⟨Relay.Sk.error e, ?_, ?_⟩ <;> (rw [relay_step_sock cap s id g _ hcl]) <;> rfl

-- a FAIL frame of the clocked socket step leaves its id with no relay connection
theorem stepK_sock_fail_fact (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk)
    (o : Relay.Out) (id' e : Nat) (ho : o ∈ (Clock.stepK cap k s (.sock id g kk)).2.2)
    (hoe : o = Relay.Out.fail id' e) :
    ((Clock.stepK cap k s (.sock id g kk)).2.1.slot id').conn = none := by
  by_cases hcl : s.closed.isSome = false
  · obtain ⟨k', h1, h2⟩ := stepK_sock_eq cap k s id g kk hcl
    rw [h2] at ho
    rw [h1]
    obtain ⟨_, _, _, _, hout, _⟩ := sockStep_spec cap s id g k'
    obtain ⟨_, hid, _⟩ := hout o ho
    rw [hoe] at hid
    simp [outIdT] at hid
    subst hid
    exact sockStep_fail_fact cap s id' g k' o e ho hoe
  · have hcl' : s.closed.isSome = true := by
      cases hb : s.closed.isSome
      · exact absurd hb hcl
      · rfl
    unfold Clock.stepK at ho
    rw [if_pos hcl'] at ho
    simp at ho

-- an OK frame of the clocked socket step is for a connection of its id that was not open
theorem stepK_sock_ok_fact (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk)
    (o : Relay.Out) (id' : Nat) (ho : o ∈ (Clock.stepK cap k s (.sock id g kk)).2.2)
    (hoe : o = Relay.Out.ok id') :
    ∃ c0, (s.slot id').conn = some c0 ∧ c0.isOpen = false := by
  by_cases hcl : s.closed.isSome = false
  · obtain ⟨k', _, h2⟩ := stepK_sock_eq cap k s id g kk hcl
    rw [h2] at ho
    obtain ⟨_, _, _, _, hout, _⟩ := sockStep_spec cap s id g k'
    obtain ⟨_, hid, _⟩ := hout o ho
    rw [hoe] at hid
    simp [outIdT] at hid
    subst hid
    exact sockStep_ok_fact cap s id' g k' o ho hoe
  · have hcl' : s.closed.isSome = true := by
      cases hb : s.closed.isSome
      · exact absurd hb hcl
      · rfl
    unfold Clock.stepK at ho
    rw [if_pos hcl'] at ho
    simp at ho


-- the flush's frames: at most one WRITTEN, so nothing of an id follows a FAIL
theorem flushConn_outs_pw (s : Relay.St) (id a : Nat) (c : Relay.Conn) :
    List.Pairwise (fun x y => ∀ id' e, x = Relay.Out.fail id' e → outIdT y = some id' → False)
      (Relay.flushConn s id c a).2 := by
  unfold Relay.flushConn
  by_cases h1 : c.isOpen = true
  · by_cases h2 : min a c.queued = 0
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

-- the socket step's frames: a FAIL is the last one (nothing of its id follows it)
theorem sockStep_outs_pw (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) :
    List.Pairwise (fun a b => ∀ id' e, a = Relay.Out.fail id' e → outIdT b = some id' → False)
      (Relay.sockStep cap s id g k).2 := by
  unfold Relay.sockStep
  rcases hc : (s.slot id).conn with _ | c
  · dsimp only
    exact List.Pairwise.nil
  · dsimp only
    split
    · exact List.Pairwise.nil
    · cases k
      case drain a => exact flushConn_outs_pw s id a c
      all_goals
        dsimp only
        (iterate 6 (all_goals (first | split | skip)))
        all_goals (try (cases hco : c.isOpen))
        all_goals (simp_all [Relay.failConn, List.pairwise_cons])

theorem stepK_sock_outs_pw (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk) :
    List.Pairwise (fun a b => ∀ id' e, a = Relay.Out.fail id' e → outIdT b = some id' → False)
      (Clock.stepK cap k s (.sock id g kk)).2.2 := by
  by_cases hcl : s.closed.isSome = false
  · obtain ⟨k', _, h2⟩ := stepK_sock_eq cap k s id g kk hcl
    rw [h2]
    exact sockStep_outs_pw cap s id g k'
  · have hcl' : s.closed.isSome = true := by
      cases hb : s.closed.isSome
      · exact absurd hb hcl
      · rfl
    unfold Clock.stepK
    rw [if_pos hcl']
    exact List.Pairwise.nil

-- a socket step of a kind other than open never reports an OK
theorem sockStep_nonopen_noOk (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) (hk : k ≠ Relay.Sk.open_)
    (o : Relay.Out) (id' : Nat) (ho : o ∈ (Relay.sockStep cap s id g k).2) (hoe : o = Relay.Out.ok id') : False := by
  subst hoe
  unfold Relay.sockStep at ho
  rcases hc : (s.slot id).conn with _ | c
  · rw [hc] at ho; simp at ho
  · rw [hc] at ho
    dsimp only at ho
    split at ho
    · simp at ho
    · cases k with
      | open_ => exact absurd rfl hk
      | data n =>
        dsimp only at ho
        split at ho <;> (try split at ho) <;> (try split at ho) <;> simp_all [Relay.failConn]
      | eof => simp at ho
      | peerclose =>
        dsimp only at ho
        split at ho
        · simp_all [Relay.failConn]
        · simp at ho
      | error e => simp_all [Relay.failConn]
      | drain a =>
        dsimp only at ho
        unfold Relay.flushConn at ho
        dsimp only at ho
        iterate 3 (all_goals (try split at ho))
        all_goals simp_all

-- the post-state of a socket step that reports an OK: the connection of the id is open, with the same generation
theorem sockStep_ok_post (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) (o : Relay.Out) (id' : Nat)
    (ho : o ∈ (Relay.sockStep cap s id g k).2) (hoe : o = Relay.Out.ok id') :
    id' = id ∧ ∃ c0, (s.slot id).conn = some c0 ∧
      ((Relay.sockStep cap s id g k).1.slot id).conn = some { c0 with isOpen := true } := by
  by_cases hk : k = Relay.Sk.open_
  · subst hk
    subst hoe
    rcases hc : (s.slot id).conn with _ | c
    · have hn : Relay.sockStep cap s id g Relay.Sk.open_ = (s, []) := by
        unfold Relay.sockStep; rw [hc]
      rw [hn] at ho
      simp at ho
    · by_cases hg : c.gen = g
      · by_cases hop : c.isOpen = true
        · have hn : Relay.sockStep cap s id g Relay.Sk.open_ = (s, []) := by
            unfold Relay.sockStep; simp [hc, hg, hop]
          rw [hn] at ho
          simp at ho
        · have hopF : c.isOpen = false := by simpa using hop
          have hn : Relay.sockStep cap s id g Relay.Sk.open_ =
              (Relay.setConn s id (some { c with isOpen := true }), [Relay.Out.ok id]) := by
            unfold Relay.sockStep; simp [hc, hg, hopF]
          rw [hn] at ho ⊢
          simp at ho
          refine ⟨ho, c, rfl, ?_⟩
          simp [Relay.setConn, Relay.setSlot, Relay.St.slot]
      · have hn : Relay.sockStep cap s id g Relay.Sk.open_ = (s, []) := by
          unfold Relay.sockStep; simp [hc, hg]
        rw [hn] at ho
        simp at ho
  · exact (sockStep_nonopen_noOk cap s id g k hk o id' ho hoe).elim

theorem stepK_sock_ok_post (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk)
    (o : Relay.Out) (id' : Nat) (ho : o ∈ (Clock.stepK cap k s (.sock id g kk)).2.2)
    (hoe : o = Relay.Out.ok id') :
    id' = id ∧ ∃ c0, (s.slot id).conn = some c0 ∧
      ((Clock.stepK cap k s (.sock id g kk)).2.1.slot id).conn = some { c0 with isOpen := true } := by
  by_cases hcl : s.closed.isSome = false
  · obtain ⟨k', h1, h2⟩ := stepK_sock_eq cap k s id g kk hcl
    rw [h2] at ho
    rw [h1]
    exact sockStep_ok_post cap s id g k' o id' ho hoe
  · have hcl' : s.closed.isSome = true := by
      cases hb : s.closed.isSome
      · exact absurd hb hcl
      · rfl
    unfold Clock.stepK at ho
    rw [if_pos hcl'] at ho
    simp at ho

-- the flush's frames carry no OK, so no two of them are OKs of one id
theorem flushConn_okpw (s : Relay.St) (id a : Nat) (c : Relay.Conn) :
    List.Pairwise (fun x y => ∀ id', x = Relay.Out.ok id' → y ≠ Relay.Out.ok id')
      (Relay.flushConn s id c a).2 := by
  unfold Relay.flushConn
  by_cases h1 : c.isOpen = true
  · by_cases h2 : min a c.queued = 0
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

-- the socket step's frames: at most one of them is an OK
theorem sockStep_okpw (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) :
    List.Pairwise (fun a b => ∀ id', a = Relay.Out.ok id' → b ≠ Relay.Out.ok id')
      (Relay.sockStep cap s id g k).2 := by
  unfold Relay.sockStep
  rcases hc : (s.slot id).conn with _ | c
  · dsimp only
    exact List.Pairwise.nil
  · dsimp only
    split
    · exact List.Pairwise.nil
    · cases k
      case drain a => exact flushConn_okpw s id a c
      all_goals
        dsimp only
        (iterate 6 (all_goals (first | split | skip)))
        all_goals (try (cases hco : c.isOpen))
        all_goals (simp_all [Relay.failConn, List.pairwise_cons])

theorem stepK_sock_okpw (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) (kk : Relay.Sk) :
    List.Pairwise (fun a b => ∀ id', a = Relay.Out.ok id' → b ≠ Relay.Out.ok id')
      (Clock.stepK cap k s (.sock id g kk)).2.2 := by
  by_cases hcl : s.closed.isSome = false
  · obtain ⟨k', _, h2⟩ := stepK_sock_eq cap k s id g kk hcl
    rw [h2]
    exact sockStep_okpw cap s id g k'
  · have hcl' : s.closed.isSome = true := by
      cases hb : s.closed.isSome
      · exact absurd hb hcl
      · rfl
    unfold Clock.stepK
    rw [if_pos hcl']
    exact List.Pairwise.nil

end Ind
