
namespace Ind
open Timed

-- a failed connection: the id has no connection, and it keeps its known flag
theorem failConn_slot (s : Relay.St) (id : Nat) (c : Relay.Conn) (e : Nat) :
    (Relay.failConn s id c e).1.slot id = { s.slot id with conn := none } := by
  unfold Relay.failConn
  exact Relay.slot_setConn_self s id none

theorem failConn_others (s : Relay.St) (id : Nat) (c : Relay.Conn) (e j : Nat) (hj : j ≠ id) :
    (Relay.failConn s id c e).1.slot j = s.slot j := by
  unfold Relay.failConn
  exact Relay.slot_setConn_ne s id j none hj

-- the frames of a failure: a WRITTEN frame of the connection's count when it was open (flag 0), then FAIL
theorem failConn_outs (s : Relay.St) (id : Nat) (c : Relay.Conn) (e : Nat) :
    ∀ o ∈ (Relay.failConn s id c e).2, isClosedOut o = false ∧ outIdT o = some id ∧
      (∀ cnt f, o = Relay.Out.written id cnt f → f = 0) ∧
      (∀ cnt c', o = Relay.Out.written id cnt 0 → ((Relay.failConn s id c e).1.slot id).conn = some c' →
        cnt ≤ c'.written) := by
  intro o ho
  have hslot : ((Relay.failConn s id c e).1.slot id).conn = none := by
    rw [failConn_slot]
  rw [failConn_slot] at hslot ⊢
  unfold Relay.failConn at ho
  simp only [List.mem_append, List.mem_singleton] at ho
  rcases ho with ho | ho
  · split at ho
    · simp only [List.mem_singleton] at ho
      subst ho
      refine ⟨rfl, rfl, fun cnt f h => (Relay.Out.written.inj h).2.2.symm, fun cnt c' h hs => ?_⟩
      cases hs
    · simp at ho
  · subst ho
    exact ⟨rfl, rfl, fun cnt f h => (by cases h), fun cnt c' h _ => (by cases h)⟩

end Ind

namespace Ind
open Timed

-- the socket step's effect on the id it names, as one predicate (s': the relay after; outs: its frames)
def SockSpec (s : Relay.St) (id : Nat) (s' : Relay.St) (outs : List Relay.Out) : Prop :=
  (∀ j, j ≠ id → s'.slot j = s.slot j) ∧
  (s'.slot id).known = (s.slot id).known ∧
  ((s.slot id).conn = none → (s'.slot id).conn = none) ∧
  (∀ c, (s.slot id).conn = some c → (s'.slot id).conn = none ∨
    ∃ c', (s'.slot id).conn = some c' ∧ c'.gen = c.gen ∧ (c.isOpen = true → c'.isOpen = true) ∧
      c.written ≤ c'.written ∧ c'.written + c'.queued ≤ c.written + c.queued ∧ c'.queued ≤ c.queued) ∧
  (∀ o ∈ outs, isClosedOut o = false ∧ outIdT o = some id ∧ (∀ cnt f, o = Relay.Out.written id cnt f → f = 0) ∧
    (∀ cnt c', o = Relay.Out.written id cnt 0 → (s'.slot id).conn = some c' → cnt ≤ c'.written)) ∧
  ((s.slot id).conn = none → outs = [])

theorem sockSpec_same (s : Relay.St) (id : Nat) : SockSpec s id s [] := by
  refine ⟨fun _ _ => rfl, rfl, fun h => h, ?_, ?_, fun _ => rfl⟩
  · intro c hc; right; exact ⟨c, hc, rfl, fun h => h, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · intro o ho; simp at ho

-- an update of the connection's fields that keep its generation, written count and queue (open, data, peerclose)
theorem sockSpec_set (s : Relay.St) (id : Nat) (c c' : Relay.Conn) (outs : List Relay.Out)
    (hc : (s.slot id).conn = some c) (hgen : c'.gen = c.gen) (hw : c'.written = c.written)
    (hq : c'.queued = c.queued) (ho : c.isOpen = true → c'.isOpen = true)
    (houts : ∀ o ∈ outs, isClosedOut o = false ∧ outIdT o = some id ∧
      (∀ cnt f, o ≠ Relay.Out.written id cnt f)) :
    SockSpec s id (Relay.setConn s id (some c')) outs := by
  refine ⟨fun j hj => Relay.slot_setConn_ne s id j _ hj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Relay.slot_setConn_self]
  · intro h; rw [hc] at h; cases h
  · intro c0 hc0
    rw [hc] at hc0
    cases hc0
    right
    refine ⟨c', ?_, hgen, ho, Nat.le_of_eq hw.symm, by omega, by omega⟩
    rw [Relay.slot_setConn_self]
  · intro o ho'
    obtain ⟨h1, h2, h3⟩ := houts o ho'
    exact ⟨h1, h2, fun cnt f h => absurd h (h3 cnt f), fun cnt c' h _ => absurd h (h3 cnt 0)⟩
  · intro h; rw [hc] at h; cases h

-- a failed connection
theorem sockSpec_fail (s : Relay.St) (id : Nat) (c0 c : Relay.Conn) (e : Nat) (hc : (s.slot id).conn = some c0) :
    SockSpec s id (Relay.failConn s id c e).1 (Relay.failConn s id c e).2 := by
  refine ⟨fun j hj => failConn_others s id c e j hj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [failConn_slot]
  · intro h; rw [hc] at h; cases h
  · intro c1 _
    left
    rw [failConn_slot]
  · exact failConn_outs s id c e
  · intro h; rw [hc] at h; cases h

-- the socket's frames of an update with no state change, and a flush that takes bytes
theorem sockSpec_sameOuts (s : Relay.St) (id : Nat) (c : Relay.Conn) (outs : List Relay.Out)
    (hc : (s.slot id).conn = some c)
    (houts : ∀ o ∈ outs, isClosedOut o = false ∧ outIdT o = some id ∧ (∀ cnt f, o ≠ Relay.Out.written id cnt f)) :
    SockSpec s id s outs := by
  refine ⟨fun _ _ => rfl, rfl, fun h => h, ?_, ?_, fun h => by rw [hc] at h; cases h⟩
  · intro c1 hc1
    rw [hc] at hc1
    cases hc1
    exact Or.inr ⟨c, hc, rfl, fun h => h, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  · intro o ho
    obtain ⟨h1, h2, h3⟩ := houts o ho
    exact ⟨h1, h2, fun cnt f h => absurd h (h3 cnt f), fun cnt c' h _ => absurd h (h3 cnt 0)⟩

theorem sockSpec_flushset (s : Relay.St) (id : Nat) (c : Relay.Conn) (m : Nat) (hc : (s.slot id).conn = some c)
    (ho : c.isOpen = true) (hm : 0 < m) (hle : m ≤ c.queued) :
    SockSpec s id (Relay.setConn s id (some { c with queued := c.queued - m, written := c.written + m }))
      [Relay.Out.written id (c.written + m) 0] := by
  refine ⟨fun j hj => Relay.slot_setConn_ne _ _ _ _ hj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Relay.slot_setConn_self]
  · intro h; rw [hc] at h; cases h
  · intro c1 hc1
    rw [hc] at hc1
    cases hc1
    refine Or.inr ⟨{ c with queued := c.queued - m, written := c.written + m }, ?_, rfl, fun h => h, ?_, ?_, ?_⟩
    · rw [Relay.slot_setConn_self]
    · exact Nat.le_add_right _ _
    · dsimp only; omega
    · exact Nat.sub_le _ _
  · intro o hmem
    have hmem' : o = Relay.Out.written id (c.written + m) 0 := List.mem_singleton.mp hmem
    subst hmem'
    refine ⟨rfl, rfl, fun cnt f h => (Relay.Out.written.inj h).2.2.symm, fun cnt c' h hs => ?_⟩
    rw [Relay.slot_setConn_self] at hs
    dsimp only at hs
    cases hs
    have hcnt := (Relay.Out.written.inj h).2.1
    dsimp only
    omega
  · intro h; rw [hc] at h; cases h

theorem sockStep_spec (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) :
    SockSpec s id (Relay.sockStep cap s id g k).1 (Relay.sockStep cap s id g k).2 := by
  unfold Relay.sockStep
  rcases hc : (s.slot id).conn with _ | c
  · dsimp only
    exact sockSpec_same s id
  · dsimp only
    split
    · exact sockSpec_same s id
    · cases k
      · dsimp only
        split
        · exact sockSpec_same s id
        · refine sockSpec_set s id c _ [Relay.Out.ok id] hc rfl rfl rfl (fun _ => rfl) ?_
          intro o hmem
          have hmem' : o = Relay.Out.ok id := List.mem_singleton.mp hmem
          subst hmem'
          exact ⟨rfl, rfl, fun cnt f h => (by cases h)⟩
      · dsimp only
        split
        · exact sockSpec_fail s id c c 5 hc
        · split
          · exact sockSpec_fail s id c c 5 hc
          · split
            · exact sockSpec_fail s id c c 27 hc
            · refine sockSpec_set s id c _ [Relay.Out.data id _] hc rfl rfl rfl (fun h => h) ?_
              intro o hmem
              have hmem' : o = Relay.Out.data id _ := List.mem_singleton.mp hmem
              subst hmem'
              exact ⟨rfl, rfl, fun cnt f h => (by cases h)⟩
      · dsimp only
        refine sockSpec_sameOuts s id c [Relay.Out.eof id] hc ?_
        intro o hmem
        have hmem' : o = Relay.Out.eof id := List.mem_singleton.mp hmem
        subst hmem'
        exact ⟨rfl, rfl, fun cnt f h => (by cases h)⟩
      · dsimp only
        split
        · exact sockSpec_fail s id c _ 32 hc
        · refine sockSpec_set s id c _ [] hc rfl rfl rfl (fun h => h) ?_
          intro o hmem
          simp at hmem
      · dsimp only
        exact sockSpec_fail s id c c _ hc
      · dsimp only
        unfold Relay.flushConn
        dsimp only
        split
        · exact sockSpec_sameOuts s id c [] hc (fun o ho => by simp at ho)
        · split
          · exact sockSpec_sameOuts s id c [] hc (fun o ho => by simp at ho)
          · rename_i hopen hm
            exact sockSpec_flushset s id c _ hc (by simpa using hopen) (Nat.pos_of_ne_zero hm)
              (Nat.min_le_right _ _)

end Ind
