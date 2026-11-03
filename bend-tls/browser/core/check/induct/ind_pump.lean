namespace Ind
open Timed

-- a pump that cannot send (no send in progress, a discard pending, or the connection not open) takes nothing
theorem pump_idle (id : Nat) (c : Page.PConn) (f : Nat)
    (hc : (c.op.isNone || c.discardPending || !c.isOpen) = true) : Page.pump id c f = (c, []) := by
  cases f with
  | zero => simp [Page.pump]
  | succ f => simp [Page.pump, hc]

-- the pump: the SEND frames it queues are the windows it takes, in order; they sum to the increase of the sent count,
-- and the connection stays in the invariant (the sent bytes stay within the window of the written ones)
theorem pump_spec (id : Nat) : ∀ (fuel : Nat) (c : Page.PConn), Page.PInv c →
    ∃ ns : List Nat, (Page.pump id c fuel).2 = ns.map (fun n => Page.Obs.toRelay (Relay.Ev.send id n) 0) ∧
      (Page.pump id c fuel).1.seq = c.seq ∧ (Page.pump id c fuel).1.isOpen = c.isOpen ∧
      (Page.pump id c fuel).1.written = c.written ∧ (Page.pump id c fuel).1.tail = c.tail ∧
      (Page.pump id c fuel).1.discardPending = c.discardPending ∧ (Page.pump id c fuel).1.op = c.op ∧
      (Page.pump id c fuel).1.sent = c.sent + ns.sum ∧ Page.PInv (Page.pump id c fuel).1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro c hc
    exact ⟨[], by simp [Page.pump], rfl, rfl, rfl, rfl, rfl, rfl, by simp [Page.pump], by simp [Page.pump]; exact hc⟩
  | succ f ih =>
    intro c hc
    have hc' := hc
    unfold Page.PInv at hc'
    obtain ⟨hw, hs, ht⟩ := hc'
    by_cases hcond : (c.op.isNone || c.discardPending || !c.isOpen) = true
    · refine ⟨[], by simp [Page.pump, hcond], by simp [Page.pump, hcond], by simp [Page.pump, hcond],
        by simp [Page.pump, hcond], by simp [Page.pump, hcond], by simp [Page.pump, hcond],
        by simp [Page.pump, hcond], by simp [Page.pump, hcond], ?_⟩
      simp only [Page.pump, hcond, if_true]
      exact hc
    · by_cases hz : min Page.MAX_BODY (min (Page.SEND_W - (c.sent - c.written)) (c.tail - c.sent)) = 0
      · refine ⟨[], by simp [Page.pump, hcond, hz], by simp [Page.pump, hcond, hz],
          by simp [Page.pump, hcond, hz], by simp [Page.pump, hcond, hz], by simp [Page.pump, hcond, hz],
          by simp [Page.pump, hcond, hz], by simp [Page.pump, hcond, hz], by simp [Page.pump, hcond, hz], ?_⟩
        simp only [Page.pump, hcond, hz, if_true]
        exact hc
      · obtain ⟨N, hN⟩ : ∃ N, N = min Page.MAX_BODY (min (Page.SEND_W - (c.sent - c.written)) (c.tail - c.sent)) :=
          ⟨_, rfl⟩
        rw [← hN] at hz
        have hn1 : N ≤ Page.SEND_W - (c.sent - c.written) := by
          rw [hN]; exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
        have hn2 : N ≤ c.tail - c.sent := by
          rw [hN]; exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        have hpeq : Page.pump id c (f + 1) = ((Page.pump id { c with sent := c.sent + N } f).1,
            Page.Obs.toRelay (Relay.Ev.send id N) 0 :: (Page.pump id { c with sent := c.sent + N } f).2) := by
          simp [Page.pump, hcond, ← hN, hz]
        obtain ⟨ns, hobs, hseq, hopen, hwr, htail, hdp, hop, hsent, hpi⟩ :=
          ih { c with sent := c.sent + N } (by unfold Page.PInv; simp only; omega)
        refine ⟨N :: ns, ?_, ?_⟩
        · rw [hpeq]
          simp [hobs]
        · rw [hpeq]
          simp only [List.sum_cons]
          refine ⟨hseq, hopen, hwr, htail, hdp, hop, ?_, hpi⟩
          have h5 : (Page.pump id { c with sent := c.sent + N } f).1.sent = c.sent + N + ns.sum := hsent
          omega

-- the pump keeps the connection's received count
theorem pump_received (id : Nat) : ∀ (fuel : Nat) (c : Page.PConn), (Page.pump id c fuel).1.received = c.received := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [Page.pump]
  | succ f ih =>
    intro c
    by_cases hcond : (c.op.isNone || c.discardPending || !c.isOpen) = true
    · simp [Page.pump, hcond]
    · by_cases hz : min Page.MAX_BODY (min (Page.SEND_W - (c.sent - c.written)) (c.tail - c.sent)) = 0
      · simp [Page.pump, hcond, hz]
      · obtain ⟨N, hN⟩ : ∃ N, N = min Page.MAX_BODY (min (Page.SEND_W - (c.sent - c.written)) (c.tail - c.sent)) :=
          ⟨_, rfl⟩
        rw [← hN] at hz
        have hpeq : Page.pump id c (f + 1) = ((Page.pump id { c with sent := c.sent + N } f).1,
            Page.Obs.toRelay (Relay.Ev.send id N) 0 :: (Page.pump id { c with sent := c.sent + N } f).2) := by
          simp [Page.pump, hcond, ← hN, hz]
        rw [hpeq]
        have := ih { c with sent := c.sent + N }
        simpa using this

-- an idle pump queues nothing
theorem pump_idle_nil (id : Nat) (c : Page.PConn) (f : Nat)
    (h : c.op = none ∨ c.discardPending = true ∨ c.isOpen = false) : (Page.pump id c f).2 = [] := by
  have hc : (c.op.isNone || c.discardPending || !c.isOpen) = true := by
    rcases h with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  rw [pump_idle id c f hc]

end Ind
