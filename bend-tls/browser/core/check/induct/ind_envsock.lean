
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

end Ind
