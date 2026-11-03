
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

theorem flushConn_outs_ge (s : Relay.St) (id : Nat) (c : Relay.Conn) (a : Nat) :
    ∀ o ∈ (Relay.flushConn s id c a).2, ∃ cnt, o = Relay.Out.written id cnt 0 ∧ c.written ≤ cnt := by
  intro o ho
  unfold Relay.flushConn at ho
  by_cases h1 : c.isOpen = true
  · by_cases h2 : min a c.queued = 0
    · simp [h1, h2] at ho
    · simp [h1, h2] at ho
      exact ⟨_, ho, Nat.le_add_right _ _⟩
  · simp [h1] at ho

-- a flush's frame: its count is at least the written count the connection had before the flush
theorem flushOne_outs_pre (k : Clock.Clk) (s : Relay.St) (id : Nat) :
    ∀ o ∈ (Clock.flushOne k s id).2.2, ∃ cnt, o = Relay.Out.written id cnt 0 ∧
      ∃ c0, (s.slot id).conn = some c0 ∧ c0.written ≤ cnt := by
  unfold Clock.flushOne
  cases hc : (s.slot id).conn with
  | none => simp only [hc]; intro o ho; simp at ho
  | some c =>
    simp only [hc]
    by_cases ho : c.isOpen = true
    · simp only [ho, if_true]
      by_cases hm : (Clock.flushSim (k.chunks id) 4294967295 k.bud).1 > 0
      · simp only [hm, if_true]
        intro o hmem
        obtain ⟨cnt, hcnt, hle⟩ := flushConn_outs_ge s id c _ o hmem
        exact ⟨cnt, hcnt, c, rfl, hle⟩
      · simp only [hm, if_false]
        intro o hmem
        simp at hmem
    · simp only [ho, if_false]
      intro o hmem
      simp at hmem

-- one flush emits at most one frame
theorem flushOne_outs_len (k : Clock.Clk) (s : Relay.St) (id : Nat) :
    (Clock.flushOne k s id).2.2.length ≤ 1 := by
  unfold Clock.flushOne
  cases hc : (s.slot id).conn with
  | none => simp
  | some c =>
    by_cases ho : c.isOpen = true
    · by_cases hm : (Clock.flushSim (k.chunks id) 4294967295 k.bud).1 > 0 <;> simp [ho, hm, Relay.flushConn]
      split <;> simp
    · simp [ho]

theorem flushIds_spec (ids : List Nat) : ∀ (k : Clock.Clk) (s : Relay.St), Clock.Mirror k s →
    Flushed s (Clock.flushIds k s ids).2.1 ∧
    ∀ o ∈ (Clock.flushIds k s ids).2.2, ∃ j, j ∈ ids ∧ ∃ cnt d, o = Relay.Out.written j cnt 0 ∧
      ((Clock.flushIds k s ids).2.1.slot j).conn = some d ∧ cnt ≤ d.written ∧
      ∃ c0, (s.slot j).conn = some c0 ∧ c0.gen = d.gen ∧ c0.written ≤ cnt := by
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
      obtain ⟨cnt', hcnt', c0, hc0, hle⟩ := flushOne_outs_pre k s id o h1
      rw [hcnt] at hcnt'
      cases hcnt'
      obtain ⟨d, hd, hg, _, hw, _, _⟩ := (hF2 id).2.1 c1 hc1
      obtain ⟨c', hc', hgc', _, _, _, _⟩ := (hF1 id).2.1 c0 hc0
      rw [hc1] at hc'
      have hcc := Option.some.inj hc'
      have hgq : c1.gen = c0.gen := by rw [hcc]; exact hgc'
      exact ⟨id, by simp, cnt, d, hcnt, hd, by rw [← hw1]; exact hw, c0, hc0, by rw [hg, hgq], hle⟩
    · obtain ⟨j, hj, cnt, d, hjo, hd, hcnt, c0, hc0, hg, hle⟩ := hO2 o h2
      obtain ⟨c, hc, hgc⟩ := flushed_back hF1 j c0 hc0
      obtain ⟨c', hc', _, _, hw', _, _⟩ := (hF1 j).2.1 c hc
      rw [hc0] at hc'
      cases Option.some.inj hc'
      exact ⟨j, List.mem_cons_of_mem _ hj, cnt, d, hjo, hd, hcnt, c, hc,
        by rw [hgc, hg], Nat.le_trans hw' hle⟩

theorem eq_of_mem_len1 {α : Type} : ∀ (l : List α), l.length ≤ 1 → ∀ a ∈ l, ∀ b ∈ l, a = b
  | [], _, a, ha, _, _ => by simp at ha
  | [x], _, a, ha, b, hb => by
    simp at ha hb
    rw [ha, hb]
  | x :: y :: t, h, _, _, _, _ => by simp at h

-- the frames of a flush of distinct ids are distinct for each id
theorem flushIds_outs_uniq : ∀ (ids : List Nat), ids.Nodup → ∀ (k : Clock.Clk) (s : Relay.St), Clock.Mirror k s →
    ∀ o1 ∈ (Clock.flushIds k s ids).2.2, ∀ o2 ∈ (Clock.flushIds k s ids).2.2, ∀ j c1 c2,
      o1 = Relay.Out.written j c1 0 → o2 = Relay.Out.written j c2 0 → o1 = o2 := by
  intro ids
  induction ids with
  | nil => intro _ k s _ o1 ho1; simp [Clock.flushIds] at ho1
  | cons id ids ih =>
    intro hnd k s hM o1 ho1 o2 ho2 j c1 c2 e1 e2
    have hnd' := List.nodup_cons.mp hnd
    have hM1 : Clock.Mirror (Clock.flushOne k s id).1 (Clock.flushOne k s id).2.1 :=
      Clock.mirror_flushOne k s id hM
    have hmem := (flushIds_spec ids _ _ hM1).2
    simp only [Clock.flushIds] at ho1 ho2 ⊢
    rcases List.mem_append.mp ho1 with h1 | h1 <;> rcases List.mem_append.mp ho2 with h2 | h2
    · exact eq_of_mem_len1 _ (flushOne_outs_len k s id) o1 h1 o2 h2
    · exfalso
      obtain ⟨cnt1, hcnt1, _⟩ := flushOne_outs k s id hM o1 h1
      rw [e1] at hcnt1
      have hjid := (Relay.Out.written.inj hcnt1).1
      obtain ⟨j', hj', cnt, d, hjo, _⟩ := hmem o2 h2
      rw [e2] at hjo
      have hj'j := (Relay.Out.written.inj hjo).1
      have hmemid : id ∈ ids := by rw [← hjid, hj'j]; exact hj'
      exact (List.nodup_cons.mp hnd).1 hmemid
    · exfalso
      obtain ⟨cnt2, hcnt2, _⟩ := flushOne_outs k s id hM o2 h2
      rw [e2] at hcnt2
      have hjid := (Relay.Out.written.inj hcnt2).1
      obtain ⟨j', hj', cnt, d, hjo, _⟩ := hmem o1 h1
      rw [e1] at hjo
      have hj'j := (Relay.Out.written.inj hjo).1
      have hmemid : id ∈ ids := by rw [← hjid, hj'j]; exact hj'
      exact (List.nodup_cons.mp hnd).1 hmemid
    · exact ih hnd'.2 _ _ hM1 o1 h1 o2 h2 j c1 c2 e1 e2

end Ind
