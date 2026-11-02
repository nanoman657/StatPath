
namespace Ind
open Timed

theorem flushed_trans {s t u : Relay.St} (h1 : Flushed s t) (h2 : Flushed t u) : Flushed s u := by
  intro j
  obtain ⟨k1, c1, n1⟩ := h1 j
  obtain ⟨k2, c2, n2⟩ := h2 j
  refine ⟨by rw [k2, k1], ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, hg, ho, hw, ht, hq⟩ := c1 c hc
    obtain ⟨e, he, hg', ho', hw', ht', hq'⟩ := c2 d hd
    exact ⟨e, he, hg'.trans hg, ho'.trans ho, Nat.le_trans hw hw', ht'.trans ht, Nat.le_trans hq' hq⟩
  · intro hn; exact n2 (n1 hn)

theorem flushConn_take_outs (s : Relay.St) (id : Nat) (c : Relay.Conn) (a : Nat) (ho : c.isOpen = true)
    (ha : 0 < a) (hle : a ≤ c.queued) :
    (Relay.flushConn s id c a).2 = [Relay.Out.written id (c.written + a) 0] := by
  unfold Relay.flushConn
  have hmin : min a c.queued = a := Nat.min_eq_left hle
  simp [ho, hmin, Nat.pos_iff_ne_zero.mp ha]

-- the reports of one id's flush: a WRITTEN frame with the connection's count after the flush
theorem flushOne_outs (k : Clock.Clk) (s : Relay.St) (id : Nat) (hM : Clock.Mirror k s) :
    ∀ o ∈ (Clock.flushOne k s id).2.2, ∃ cnt, o = Relay.Out.written id cnt 0 ∧
      ∃ c1, ((Clock.flushOne k s id).2.1.slot id).conn = some c1 ∧ c1.written = cnt := by
  unfold Clock.flushOne
  cases hc : (s.slot id).conn with
  | none => simp only [hc]; intro o ho; simp at ho
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
        rw [flushConn_take s id c _ ho hm hle, flushConn_take_outs s id c _ ho hm hle]
        intro o hmem
        simp at hmem
        refine ⟨c.written + (Clock.flushSim (k.chunks id) 4294967295 k.bud).1, hmem,
          { c with queued := c.queued - (Clock.flushSim (k.chunks id) 4294967295 k.bud).1,
                   written := c.written + (Clock.flushSim (k.chunks id) 4294967295 k.bud).1 }, ?_, rfl⟩
        simp [Relay.slot_setConn_self]
      · simp only [hm]; intro o hmem; simp at hmem
    · simp only [ho]; intro o hmem; simp at hmem

theorem flushed_back {s t : Relay.St} (h : Flushed s t) (j : Nat) (c0 : Relay.Conn)
    (hc0 : (t.slot j).conn = some c0) : ∃ c, (s.slot j).conn = some c ∧ c.gen = c0.gen := by
  cases hs : (s.slot j).conn with
  | none =>
    have := (h j).2.2 hs
    rw [this] at hc0
    cases hc0
  | some c =>
    obtain ⟨d, hd, hg, _⟩ := (h j).2.1 c hs
    rw [hd] at hc0
    cases hc0
    exact ⟨c, rfl, hg.symm⟩

theorem flushIds_spec (ids : List Nat) : ∀ (k : Clock.Clk) (s : Relay.St), Clock.Mirror k s →
    Flushed s (Clock.flushIds k s ids).2.1 ∧
    ∀ o ∈ (Clock.flushIds k s ids).2.2, ∃ j cnt d, o = Relay.Out.written j cnt 0 ∧
      ((Clock.flushIds k s ids).2.1.slot j).conn = some d ∧ cnt ≤ d.written ∧
      ∃ c0, (s.slot j).conn = some c0 ∧ c0.gen = d.gen := by
  induction ids with
  | nil =>
    intro k s _
    simp only [Clock.flushIds]
    exact ⟨flushed_refl s, fun o ho => by simp at ho⟩
  | cons id ids ih =>
    intro k s hM
    have hM1 : Clock.Mirror (Clock.flushOne k s id).1 (Clock.flushOne k s id).2.1 :=
      Clock.mirror_flushOne k s id hM
    obtain ⟨hF2, hO2⟩ := ih _ _ hM1
    have hF1 := flushOne_flushed k s id hM
    simp only [Clock.flushIds]
    refine ⟨flushed_trans hF1 hF2, ?_⟩
    intro o ho
    rcases List.mem_append.mp ho with h1 | h2
    · obtain ⟨cnt, hcnt, c1, hc1, hw1⟩ := flushOne_outs k s id hM o h1
      obtain ⟨d, hd, hg, _, hw, _, _⟩ := (hF2 id).2.1 c1 hc1
      obtain ⟨c0, hc0, hg0⟩ := flushed_back hF1 id c1 hc1
      exact ⟨id, cnt, d, hcnt, hd, by rw [← hw1]; exact hw, c0, hc0, by rw [hg0, hg]⟩
    · obtain ⟨j, cnt, d, hj, hd, hcnt, c0, hc0, hg⟩ := hO2 o h2
      obtain ⟨c, hc, hgc⟩ := flushed_back hF1 j c0 hc0
      exact ⟨j, cnt, d, hj, hd, hcnt, c, hc, hgc.trans hg⟩

end Ind
