
namespace Ind
open Timed

-- the generation counter is never changed by a flush, nor by a tick
theorem flushConn_nextGen (s : Relay.St) (id : Nat) (c : Relay.Conn) (a : Nat) :
    (Relay.flushConn s id c a).1.nextGen = s.nextGen := by
  unfold Relay.flushConn
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp [Relay.setConn, Relay.setSlot]

theorem flushOne_nextGen (k : Clock.Clk) (s : Relay.St) (id : Nat) :
    (Clock.flushOne k s id).2.1.nextGen = s.nextGen := by
  unfold Clock.flushOne
  rcases hc : (s.slot id).conn with _ | c
  · rfl
  · dsimp only
    by_cases ho : c.isOpen = true <;> by_cases hm : 0 < (Clock.flushSim (k.chunks id) 4294967295 k.bud).fst <;>
      simp [ho, hm, flushConn_nextGen]

theorem flushIds_nextGen (k : Clock.Clk) (s : Relay.St) (ids : List Nat) :
    (Clock.flushIds k s ids).2.1.nextGen = s.nextGen := by
  induction ids generalizing k s with
  | nil => rfl
  | cons id ids ih =>
    dsimp only [Clock.flushIds]
    rw [ih, flushOne_nextGen]

theorem tickK_nextGen (k : Clock.Clk) (s : Relay.St) (ms : Nat) :
    (Clock.tickK k s ms).2.1.nextGen = s.nextGen := by
  unfold Clock.tickK
  split
  · rfl
  · exact flushIds_nextGen _ _ _

theorem tickK_spec (k : Clock.Clk) (s : Relay.St) (ms : Nat) (hM : Clock.Mirror k s) :
    Flushed s (Clock.tickK k s ms).2.1 ∧
    ∀ o ∈ (Clock.tickK k s ms).2.2, ∃ j cnt d, o = Relay.Out.written j cnt 0 ∧
      ((Clock.tickK k s ms).2.1.slot j).conn = some d ∧ cnt ≤ d.written ∧
      ∃ c0, (s.slot j).conn = some c0 ∧ c0.gen = d.gen ∧ c0.written ≤ cnt := by
  unfold Clock.tickK
  split
  · exact ⟨flushed_refl s, fun o ho => by simp at ho⟩
  · have hM1 : Clock.Mirror (Clock.refill { k with now := k.now + ms }) s := by
      intro id
      simpa [Clock.MirrorAt, Clock.refill] using hM id
    obtain ⟨hF, hO⟩ := flushIds_spec (List.range 256) _ s hM1
    refine ⟨hF, fun o ho => ?_⟩
    obtain ⟨j, -, cnt, d, h⟩ := hO o ho
    exact ⟨j, cnt, d, h⟩

theorem tick_outs_uniq (k : Clock.Clk) (s : Relay.St) (ms : Nat) (hM : Clock.Mirror k s) :
    ∀ o1 ∈ (Clock.tickK k s ms).2.2, ∀ o2 ∈ (Clock.tickK k s ms).2.2, ∀ j c1 c2,
      o1 = Relay.Out.written j c1 0 → o2 = Relay.Out.written j c2 0 → o1 = o2 := by
  unfold Clock.tickK
  split
  · intro o1 ho1; simp at ho1
  · have hM1 : Clock.Mirror (Clock.refill { k with now := k.now + ms }) s := by
      intro id
      simpa [Clock.MirrorAt, Clock.refill] using hM id
    exact flushIds_outs_uniq (List.range 256) List.nodup_range _ s hM1

theorem inv_tick (T : TSys) (ms : Nat) (h : Inv T) : Inv (tTick T ms) := by
  obtain ⟨hF, hO⟩ := tickK_spec T.clk T.c.rs ms h.mirror
  refine inv_flush T (tTick T ms) h rfl rfl rfl hF ?_ _ rfl ?_ ?_ ?_ (Clock.mirror_tickK T.clk T.c.rs ms h.mirror)
    (Clock.good_tickK T.clk T.c.rs ms h.good)
  · exact tickK_nextGen T.clk T.c.rs ms
  · intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    obtain ⟨j, cnt, d, rfl, hd, hcnt, c0, hc0, hg, hlow⟩ := hO o ho
    refine ⟨j, cnt, d, rfl, hd, hcnt, ?_⟩
    show ((T.c.rs.slot j).conn.map (fun c => c.gen)).getD 0 = d.gen
    rw [hc0]
    simp [hg]
  · intro q hq j cnt hqj
    simp only [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    obtain ⟨j', cnt', d, eo, hd, hcnt, c0, hc0, hg, hlow⟩ := hO o ho
    rw [eo] at hqj
    have hjj := (Relay.Out.written.inj hqj).1
    have hcc := (Relay.Out.written.inj hqj).2.1
    rw [hjj] at hc0
    rw [hcc] at hlow
    refine ⟨c0, hc0, ?_, hlow⟩
    rw [eo, hjj]
    simp only [outIdT]
    rw [hc0]
    rfl
  · intro a ha b hb j c1 c2 f1 f2 ha1 hb1
    simp only [List.mem_map] at ha hb
    obtain ⟨oa, hoa, rfl⟩ := ha
    obtain ⟨ob, hob, rfl⟩ := hb
    obtain ⟨ja, cnta, da, ea, -⟩ := hO oa hoa
    obtain ⟨jb, cntb, db, eb, -⟩ := hO ob hob
    have hf1 : f1 = 0 := by
      simp only at ha1
      rw [ea] at ha1
      exact (Relay.Out.written.inj ha1).2.2.symm
    have hf2 : f2 = 0 := by
      simp only at hb1
      rw [eb] at hb1
      exact (Relay.Out.written.inj hb1).2.2.symm
    simp only at ha1 hb1 ⊢
    have hab := tick_outs_uniq T.clk T.c.rs ms h.mirror oa hoa ob hob j c1 c2
      (by rw [ha1, hf1]) (by rw [hb1, hf2])
    rw [hab]

end Ind
