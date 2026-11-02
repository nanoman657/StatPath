
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
      ∃ c0, (s.slot j).conn = some c0 ∧ c0.gen = d.gen := by
  unfold Clock.tickK
  split
  · exact ⟨flushed_refl s, fun o ho => by simp at ho⟩
  · have hM1 : Clock.Mirror (Clock.refill { k with now := k.now + ms }) s := by
      intro id
      simpa [Clock.MirrorAt, Clock.refill] using hM id
    exact flushIds_spec (List.range 256) _ s hM1

theorem inv_tick (T : TSys) (ms : Nat) (h : Inv T) : Inv (tTick T ms) := by
  obtain ⟨hF, hO⟩ := tickK_spec T.clk T.c.rs ms h.mirror
  refine inv_flush T (tTick T ms) h rfl rfl rfl hF ?_ _ rfl ?_ (Clock.mirror_tickK T.clk T.c.rs ms h.mirror)
    (Clock.good_tickK T.clk T.c.rs ms h.good)
  · exact tickK_nextGen T.clk T.c.rs ms
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨o, ho, rfl⟩ := hq
  obtain ⟨j, cnt, d, rfl, hd, hcnt, c0, hc0, hg⟩ := hO o ho
  refine ⟨j, cnt, d, rfl, hd, hcnt, ?_⟩
  show ((T.c.rs.slot j).conn.map (fun c => c.gen)).getD 0 = d.gen
  rw [hc0]
  simp [hg]

end Ind
