
namespace Ind
open Timed

-- the relation a flush (the ticker, or a socket drain) leaves on the relay's connections: no id is added or
-- removed, the generation and the open state are kept, the known flag is kept, and each connection keeps its total
-- (written plus queued) while its queue shrinks and its written grows
def Flushed (s s' : Relay.St) : Prop :=
  ∀ j, (s'.slot j).known = (s.slot j).known ∧
    (∀ c, (s.slot j).conn = some c → ∃ c', (s'.slot j).conn = some c' ∧ c'.gen = c.gen ∧ c'.isOpen = c.isOpen ∧
      c.written ≤ c'.written ∧ c'.written + c'.queued = c.written + c.queued ∧ c'.queued ≤ c.queued) ∧
    ((s.slot j).conn = none → (s'.slot j).conn = none)

theorem flushed_refl (s : Relay.St) : Flushed s s := by
  intro j
  refine ⟨rfl, ?_, ?_⟩
  · intro c h; exact ⟨c, h, rfl, rfl, Nat.le_refl _, rfl, Nat.le_refl _⟩
  · intro h; exact h

theorem flushed_setConn (s : Relay.St) (id : Nat) (c c' : Relay.Conn) (hc : (s.slot id).conn = some c)
    (hg : c'.gen = c.gen) (ho : c'.isOpen = c.isOpen) (hw : c.written ≤ c'.written)
    (ht : c'.written + c'.queued = c.written + c.queued) (hq : c'.queued ≤ c.queued) :
    Flushed s (Relay.setConn s id (some c')) := by
  intro j
  by_cases hj : j = id
  · subst hj
    rw [Relay.slot_setConn_self]
    refine ⟨rfl, ?_, ?_⟩
    · intro d hd
      rw [hc] at hd
      cases hd
      exact ⟨c', rfl, hg, ho, hw, ht, hq⟩
    · intro hn
      rw [hc] at hn
      cases hn
  · rw [Relay.slot_setConn_ne _ _ _ _ hj]
    exact flushed_refl s j

theorem flushConn_take (s : Relay.St) (id : Nat) (c : Relay.Conn) (a : Nat) (ho : c.isOpen = true)
    (ha : 0 < a) (hle : a ≤ c.queued) :
    (Relay.flushConn s id c a).1 =
      Relay.setConn s id (some { c with queued := c.queued - a, written := c.written + a }) := by
  unfold Relay.flushConn
  have hmin : min a c.queued = a := Nat.min_eq_left hle
  simp [ho, hmin, Nat.pos_iff_ne_zero.mp ha]

theorem flushOne_flushed (k : Clock.Clk) (s : Relay.St) (id : Nat) (hM : Clock.Mirror k s) :
    Flushed s (Clock.flushOne k s id).2.1 := by
  unfold Clock.flushOne
  cases hc : (s.slot id).conn with
  | none => simp only [hc]; exact flushed_refl s
  | some c =>
    simp only [hc]
    by_cases ho : c.isOpen = true
    · simp only [ho, if_true]
      by_cases hm : (Clock.flushSim (k.chunks id) 4294967295 k.bud).1 > 0
      · simp only [hm, if_true]
        have hsum : (k.chunks id).sum = c.queued := by
          have := hM id
          unfold Clock.MirrorAt at this
          exact this.2.1 c hc
        have hle : (Clock.flushSim (k.chunks id) 4294967295 k.bud).1 ≤ c.queued := by
          rw [← hsum]; exact Clock.flushSim_le _ _ _
        rw [flushConn_take s id c _ ho hm hle]
        exact flushed_setConn s id c _ hc rfl rfl (by simp) (by simp; omega) (by simp)
      · simp only [hm]; exact flushed_refl s
    · simp only [ho]; exact flushed_refl s

end Ind
