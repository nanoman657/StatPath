namespace Ind
open Timed

-- the WRITTEN frame of the page, restated in parts (the same text as Page.frame's WRITTEN branch)
-- the in-progress send's completion
def wrC2 (id cnt : Nat) (c1 : Page.PConn) : Page.PConn × List Page.Obs :=
  match c1.op with
  | some (start, len) =>
    if cnt >= start + len then ({ c1 with op := none }, [Page.Obs.cb s!"sent {id}"])
    else (c1, [])
  | none => (c1, [])

-- the discard reply (flag 1 with a discard pending): the connection is reset to what the relay wrote
def wrC3 (id cnt flag : Nat) (c2 : Page.PConn) : Page.PConn × List Page.Obs :=
  if flag = 1 && c2.discardPending then
    ({ c2 with discardPending := false, op := none, sent := c2.written, tail := c2.written },
     [Page.Obs.cb s!"discarded {id} {cnt}"])
  else (c2, [])

-- the frame of a WRITTEN on an id with a connection: the connection with its count (c1), its completion, the discard
-- reset, and the pump of what is left
def wrFrameC (st : Page.State) (id cnt flag : Nat) (c1 : Page.PConn) : Page.State × List Page.Obs :=
  let p2 := wrC2 id cnt c1
  let p3 := wrC3 id cnt flag p2.1
  let st1 := Page.setSlot st id { st.slots id with conn := some p3.1 }
  let p4 := match (st1.slots id).conn with
    | some c => Page.pump id c (c.tail - c.sent + 1)
    | none => (p3.1, [])
  (Page.setSlot st1 id { st1.slots id with conn := some p4.1 }, p2.2 ++ p3.2 ++ p4.2)

theorem frame_written_eq (st : Page.State) (id cnt flag : Nat) (c0 : Page.PConn)
    (hc : (st.slots id).conn = some c0) (hcl : (st.slots id).closing = false) :
    Page.frame st (Relay.Out.written id cnt flag) = wrFrameC st id cnt flag { c0 with written := cnt } := by
  have hap : Page.applies st (Relay.Out.written id cnt flag) = some c0.seq := by
    simp [Page.applies, hcl, hc]
  unfold Page.frame wrFrameC
  rw [hap]
  simp only [hc]
  rfl

theorem wrC2_props (id cnt : Nat) (c1 : Page.PConn) :
    (wrC2 id cnt c1).1.seq = c1.seq ∧ (wrC2 id cnt c1).1.isOpen = c1.isOpen ∧
    (wrC2 id cnt c1).1.written = c1.written ∧ (wrC2 id cnt c1).1.received = c1.received ∧
    (wrC2 id cnt c1).1.sent = c1.sent ∧ (wrC2 id cnt c1).1.tail = c1.tail ∧
    (wrC2 id cnt c1).1.discardPending = c1.discardPending := by
  unfold wrC2
  split
  · split <;> simp
  · simp

theorem wrC3_props (id cnt flag : Nat) (c2 : Page.PConn) :
    (flag = 1 ∧ c2.discardPending = true →
      (wrC3 id cnt flag c2).1.discardPending = false ∧ (wrC3 id cnt flag c2).1.sent = c2.written ∧
      (wrC3 id cnt flag c2).1.tail = c2.written ∧ (wrC3 id cnt flag c2).1.op = none ∧
      (wrC3 id cnt flag c2).1.written = c2.written) ∧
    (¬ (flag = 1 ∧ c2.discardPending = true) → wrC3 id cnt flag c2 = (c2, [])) := by
  unfold wrC3
  constructor
  · rintro ⟨h1, h2⟩
    simp [h1, h2]
  · intro h
    have : ¬ (flag = 1 ∧ c2.discardPending = true) := h
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    simp [this]

theorem wrC3_gen (id cnt flag : Nat) (c2 : Page.PConn) :
    (wrC3 id cnt flag c2).1.seq = c2.seq ∧ (wrC3 id cnt flag c2).1.isOpen = c2.isOpen ∧
    (wrC3 id cnt flag c2).1.received = c2.received ∧ (wrC3 id cnt flag c2).1.written = c2.written := by
  unfold wrC3
  split <;> simp

theorem wrC2_obs (id cnt : Nat) (c1 : Page.PConn) : ∀ o ∈ (wrC2 id cnt c1).2, ∃ str, o = Page.Obs.cb str := by
  intro o ho
  unfold wrC2 at ho
  split at ho
  · split at ho
    · simp at ho
      exact ⟨_, ho⟩
    · simp at ho
  · simp at ho

theorem wrC3_obs (id cnt flag : Nat) (c2 : Page.PConn) : ∀ o ∈ (wrC3 id cnt flag c2).2, ∃ str, o = Page.Obs.cb str := by
  intro o ho
  unfold wrC3 at ho
  split at ho
  · simp at ho
    exact ⟨_, ho⟩
  · simp at ho

-- the SEND frames of a pump, seen through any observation filter that keeps toRelay observations
theorem filterMap_sends_gen (id : Nat) (f : Page.Obs → Option (Relay.Ev × Nat))
    (hf : ∀ e p, f (Page.Obs.toRelay e p) = some (e, p)) : ∀ (ns : List Nat),
    (ns.map (fun n => Page.Obs.toRelay (Relay.Ev.send id n) 0)).filterMap f =
      ns.map (fun n => (Relay.Ev.send id n, 0))
  | [] => rfl
  | n :: ns => by
    have ih := filterMap_sends_gen id f hf ns
    simp only [List.map_cons, List.filterMap_cons, hf, ih]

-- the WRITTEN frame: the page's connection after it, and the SEND frames the pump queues
theorem wr_frame_spec (st : Page.State) (id cnt flag : Nat) (c0 c1 : Page.PConn)
    (hc1s : c1.seq = c0.seq) (hc1o : c1.isOpen = c0.isOpen) (hc1w : c1.written = cnt)
    (hc1r : c1.received = c0.received) (hc1x : c1.sent = c0.sent) (hc1t : c1.tail = c0.tail)
    (hc1d : c1.discardPending = c0.discardPending)
    (hw : c0.written ≤ cnt) (hacc : cnt ≤ c0.sent) (hPI : Page.PInv c0) :
    ∃ (c4 : Page.PConn) (ns : List Nat),
      (wrFrameC st id cnt flag c1).1.slots id = { st.slots id with conn := some c4 } ∧
      (∀ j, j ≠ id → (wrFrameC st id cnt flag c1).1.slots j = st.slots j) ∧
      (wrFrameC st id cnt flag c1).1.nextSeq = st.nextSeq ∧
      ((wrFrameC st id cnt flag c1).2.filterMap
        (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) =
        ns.map (fun n => (Relay.Ev.send id n, 0)) ∧
      c4.seq = c0.seq ∧ c4.isOpen = c0.isOpen ∧ c4.written = cnt ∧ c4.received = c0.received ∧
      Page.PInv c4 ∧
      (flag = 1 ∧ c0.discardPending = true → ns = [] ∧ c4.discardPending = false ∧ c4.sent = cnt ∧ c4.tail = cnt) ∧
      (¬ (flag = 1 ∧ c0.discardPending = true) →
        c4.sent = c0.sent + ns.sum ∧ c4.tail = c0.tail ∧ c4.discardPending = c0.discardPending) ∧
      (c0.discardPending = true ∨ c0.isOpen = false → ns = []) := by
  unfold wrFrameC
  obtain ⟨h2seq, h2open, h2wr, h2rec, h2sent, h2tail, h2pd⟩ := wrC2_props id cnt c1
  have hob2 := wrC2_obs id cnt c1
  obtain ⟨hR, hN⟩ := wrC3_props id cnt flag (wrC2 id cnt c1).1
  obtain ⟨g3seq, g3open, g3rec, g3wr⟩ := wrC3_gen id cnt flag (wrC2 id cnt c1).1
  have hob3 := wrC3_obs id cnt flag (wrC2 id cnt c1).1
  generalize wrC2 id cnt c1 = p2 at h2seq h2open h2wr h2rec h2sent h2tail h2pd hR hN g3seq g3open g3rec g3wr hob2 hob3 ⊢
  have hPI3 : Page.PInv (wrC3 id cnt flag p2.1).1 := by
    by_cases hf : flag = 1 ∧ p2.1.discardPending = true
    · obtain ⟨hpd, hs, ht, hop3, hwr3⟩ := hR hf
      unfold Page.PInv
      rw [hs, ht, hwr3, h2wr, hc1w]
      omega
    · rw [hN hf]
      unfold Page.PInv
      rw [h2wr, h2sent, h2tail, hc1w, hc1x, hc1t]
      have hP := hPI
      unfold Page.PInv at hP
      omega
  have e3seq : (wrC3 id cnt flag p2.1).1.seq = c0.seq := g3seq.trans (h2seq.trans hc1s)
  have e3open : (wrC3 id cnt flag p2.1).1.isOpen = c0.isOpen := g3open.trans (h2open.trans hc1o)
  have e3rec : (wrC3 id cnt flag p2.1).1.received = c0.received := g3rec.trans (h2rec.trans hc1r)
  have e3wr : (wrC3 id cnt flag p2.1).1.written = cnt := g3wr.trans (h2wr.trans hc1w)
  have hcase : (flag = 1 ∧ c0.discardPending = true →
      (wrC3 id cnt flag p2.1).1.discardPending = false ∧ (wrC3 id cnt flag p2.1).1.sent = cnt ∧ (wrC3 id cnt flag p2.1).1.tail = cnt ∧ (wrC3 id cnt flag p2.1).1.op = none) ∧
      (¬ (flag = 1 ∧ c0.discardPending = true) →
        (wrC3 id cnt flag p2.1).1.discardPending = c0.discardPending ∧ (wrC3 id cnt flag p2.1).1.sent = c0.sent ∧ (wrC3 id cnt flag p2.1).1.tail = c0.tail) := by
    constructor
    · intro hf
      obtain ⟨hpd, hs, ht, hop3, hwr3⟩ := hR ⟨hf.1, (h2pd.trans hc1d).trans hf.2⟩
      refine ⟨hpd, ?_, ?_, hop3⟩
      · rw [hs, h2wr, hc1w]
      · rw [ht, h2wr, hc1w]
    · intro hf
      have hf' : ¬ (flag = 1 ∧ p2.1.discardPending = true) := fun h' =>
        hf ⟨h'.1, (hc1d.symm.trans h2pd.symm).trans h'.2⟩
      rw [hN hf']
      exact ⟨h2pd.trans hc1d, h2sent.trans hc1x, h2tail.trans hc1t⟩
  obtain ⟨ns, hobs, hseq, hopen, hwr, htail, hdp, hop, hsent, hpi⟩ :=
    pump_spec id ((wrC3 id cnt flag p2.1).1.tail - (wrC3 id cnt flag p2.1).1.sent + 1) (wrC3 id cnt flag p2.1).1 hPI3
  have hcb2 : p2.2.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro o ho
    obtain ⟨str, rfl⟩ := hob2 o ho
    rfl
  have hcb3 : (wrC3 id cnt flag p2.1).2.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro o ho
    obtain ⟨str, rfl⟩ := hob3 o ho
    rfl
  have hnsidle : ((wrC3 id cnt flag p2.1).1.op = none ∨ (wrC3 id cnt flag p2.1).1.discardPending = true ∨ (wrC3 id cnt flag p2.1).1.isOpen = false) → ns = [] := by
    intro h
    have h0 := pump_idle_nil id (wrC3 id cnt flag p2.1).1 ((wrC3 id cnt flag p2.1).1.tail - (wrC3 id cnt flag p2.1).1.sent + 1) h
    rw [hobs] at h0
    exact List.map_eq_nil_iff.mp h0
  refine ⟨(Page.pump id (wrC3 id cnt flag p2.1).1 ((wrC3 id cnt flag p2.1).1.tail - (wrC3 id cnt flag p2.1).1.sent + 1)).1, ns, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Page.setSlot]
  · intro j hj
    simp [Page.setSlot, hj]
  · simp [Page.setSlot]
  · have hsl : ((Page.setSlot st id { conn := some (wrC3 id cnt flag p2.1).1, closing := (st.slots id).closing, lastErr := (st.slots id).lastErr }).slots id).conn = some (wrC3 id cnt flag p2.1).1 := by
      simp [Page.setSlot]
    simp only [List.filterMap_append, hcb2, hcb3, List.nil_append, List.append_nil, hsl]
    rw [hobs]
    refine filterMap_sends_gen id _ ?_ ns
    intro e p
    rfl
  · rw [hseq]; exact e3seq
  · rw [hopen]; exact e3open
  · rw [hwr]; exact e3wr
  · rw [pump_received]; exact e3rec
  · exact hpi
  · intro hf
    obtain ⟨h1, h2, h3, h4⟩ := hcase.1 hf
    have hns : ns = [] := hnsidle (Or.inl h4)
    subst hns
    exact ⟨rfl, by rw [hdp, h1], by rw [hsent, h2]; simp, by rw [htail, h3]⟩
  · intro hf
    obtain ⟨h1, h2, h3⟩ := hcase.2 hf
    exact ⟨by rw [hsent, h2], by rw [htail, h3], by rw [hdp, h1]⟩
  · intro hpd
    rcases hpd with hpd | hopen0
    · by_cases hf : flag = 1 ∧ c0.discardPending = true
      · obtain ⟨h1, h2, h3, h4⟩ := hcase.1 hf
        exact hnsidle (Or.inl h4)
      · obtain ⟨h1, h2, h3⟩ := hcase.2 hf
        exact hnsidle (Or.inr (Or.inl (h1.trans hpd)))
    · exact hnsidle (Or.inr (Or.inr (e3open.trans hopen0)))

theorem qsumT_app_w (id : Nat) (l1 l2 : List (Relay.Ev × Nat)) :
    qsumT id (l1 ++ l2) = qsumT id l1 + qsumT id l2 := by
  induction l1 with
  | nil => simp [qsumT]
  | cons x xs ih =>
    obtain ⟨e, p⟩ := x
    simp only [List.cons_append, qsumT, ih]
    omega

-- the queue sum of SEND frames of an id is the sum of their amounts
theorem qsumT_sends (j id : Nat) : ∀ (ns : List Nat),
    qsumT j (ns.map (fun n => (Relay.Ev.send id n, 0))) = if id = j then ns.sum else 0
  | [] => by simp [qsumT]
  | n :: ns => by
    simp only [List.map_cons, qsumT, qsumT_sends j id ns, List.sum_cons]
    by_cases h : id = j
    · simp [h]; try omega
    · simp [h]

theorem qs_sends (j id : Nat) (rs : Relay.St) (page : Page.State) (L : List (Relay.Ev × Nat))
    (d : List (Relay.Out × Nat)) (e : List (Nat × Nat)) (f g : Bool) (hh : List (Nat × Nat × Nat))
    (clk : Clock.Clk) (ns : List Nat) :
    qs j ⟨⟨rs, page, L ++ ns.map (fun n => (Relay.Ev.send id n, 0)), d, e, f, g, hh⟩, clk⟩ =
      qs j ⟨⟨rs, page, L, d, e, f, g, hh⟩, clk⟩ + (if id = j then ns.sum else 0) := by
  simp only [qs, qsumT_app_w, qsumT_sends]

end Ind
