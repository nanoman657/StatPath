namespace Ind
open Timed

-- the queue sum of a list of READs is nothing (for any id)
theorem qs_app_reads (j id : Nat) (rs : Relay.St) (page : Page.State) (L L' : List (Relay.Ev × Nat))
    (d : List (Relay.Out × Nat)) (e : List (Nat × Nat)) (f : Bool) (g : Bool) (hh : List (Nat × Nat × Nat))
    (clk : Clock.Clk) (hL' : ∀ x ∈ L', ∃ k, x = (Relay.Ev.read id k, 0)) :
    qs j ⟨⟨rs, page, L ++ L', d, e, f, g, hh⟩, clk⟩ = qs j ⟨⟨rs, page, L, d, e, f, g, hh⟩, clk⟩ := by
  simp only [qs, qsumT_app]
  rw [qsumT_reads j id L' hL']
  simp

-- the wake loop's state: the connection's fields that the invariant reads are those of c0, and the outputs
-- are READs of the id and messages
def WRd (id : Nat) (c0 : Page.PConn) (s : Page.PConn × List Nat × List Page.Obs) : Prop :=
  s.1.seq = c0.seq ∧ s.1.isOpen = c0.isOpen ∧ s.1.tail = c0.tail ∧ s.1.sent = c0.sent ∧
  s.1.written = c0.written ∧ s.1.received = c0.received ∧ s.1.op = c0.op ∧
  s.1.discardPending = c0.discardPending ∧ s.1.eof = c0.eof ∧
  ∀ o ∈ s.2.2, (∃ k, o = Page.Obs.toRelay (Relay.Ev.read id k) 0) ∨ ∃ str, o = Page.Obs.cb str

theorem wake_body_step (id : Nat) (c0 : Page.PConn) (I : Page.PConn × List Nat × List Page.Obs)
    (hI : WRd id c0 I) (mx : Nat) :
    ∃ t, ((match (Page.takeFor id I.1 mx).2.1 with
      | some ob => pure (ForInStep.yield ((Page.takeFor id I.1 mx).1, I.2.1,
          I.2.2 ++ [ob, Page.Obs.cb (toString "data " ++ toString id ++ toString " " ++
            toString ((Page.takeFor id I.1 mx).1.taken - I.1.taken))]))
      | none => if I.1.eof = true then
          pure (ForInStep.yield (I.1, I.2.1, I.2.2 ++ [Page.Obs.cb (toString "eof " ++ toString id)]))
        else pure (ForInStep.yield (I.1, I.2.1 ++ [mx], I.2.2)) :
        Id (ForInStep (Page.PConn × List Nat × List Page.Obs))) = pure (ForInStep.yield t)) ∧ WRd id c0 t := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, eo⟩ := hI
  by_cases hr : I.1.received > I.1.taken
  · simp only [Page.takeFor, hr, if_true]
    refine ⟨_, rfl, ?_⟩
    refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, ?_⟩
    intro o ho
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with ho | ho | ho
    · exact eo o ho
    · exact Or.inl ⟨_, ho⟩
    · exact Or.inr ⟨_, ho⟩
  · simp only [Page.takeFor, hr, if_false]
    by_cases he : I.1.eof = true
    · simp only [he, if_true]
      refine ⟨_, rfl, ?_⟩
      refine ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, ?_⟩
      intro o ho
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ho
      rcases ho with ho | ho
      · exact eo o ho
      · exact Or.inr ⟨_, ho⟩
    · simp only [he]
      refine ⟨_, rfl, ?_⟩
      exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, eo⟩

-- the wake loop, over any list of readers: it ends in a state with the same invariant
theorem wake_loop_inv (id : Nat) (c0 : Page.PConn) : ∀ (L : List Nat) (I : Page.PConn × List Nat × List Page.Obs),
    WRd id c0 I → ∃ R, (forIn L I (fun (mx : Nat) (__s : Page.PConn × List Nat × List Page.Obs) =>
      match (Page.takeFor id __s.1 mx).2.1 with
      | some ob => pure (ForInStep.yield ((Page.takeFor id __s.1 mx).1, __s.2.1,
          __s.2.2 ++ [ob, Page.Obs.cb (toString "data " ++ toString id ++ toString " " ++
            toString ((Page.takeFor id __s.1 mx).1.taken - __s.1.taken))]))
      | none => if __s.1.eof = true then
          pure (ForInStep.yield (__s.1, __s.2.1, __s.2.2 ++ [Page.Obs.cb (toString "eof " ++ toString id)]))
        else pure (ForInStep.yield (__s.1, __s.2.1 ++ [mx], __s.2.2)))
      : Id (Page.PConn × List Nat × List Page.Obs)) = pure R ∧ WRd id c0 R := by
  intro L
  induction L with
  | nil => intro I hI; exact ⟨I, by simp, hI⟩
  | cons a L ih =>
    intro I hI
    obtain ⟨t, ht, hRt⟩ := wake_body_step id c0 I hI a
    obtain ⟨R, hR, hRR⟩ := ih t hRt
    refine ⟨R, ?_, hRR⟩
    simp only [List.forIn_cons]
    rw [ht, pure_bind]
    exact hR

-- the page's wake of an id with a connection: the connection's new state keeps the fields of the old one (the
-- readers and the taken count change), and the wake's outputs are READs of the id and messages
theorem wake_spec (st : Page.State) (id : Nat) (c0 : Page.PConn) (h : (st.slots id).conn = some c0) :
    ∃ c2 : Page.PConn, ∃ obs : List Page.Obs,
      Page.wake st id = (Page.setSlot st id { st.slots id with conn := some c2 }, obs) ∧
      c2.seq = c0.seq ∧ c2.isOpen = c0.isOpen ∧ c2.tail = c0.tail ∧ c2.sent = c0.sent ∧
      c2.written = c0.written ∧ c2.received = c0.received ∧ c2.op = c0.op ∧
      c2.discardPending = c0.discardPending ∧ c2.eof = c0.eof ∧
      ∀ o ∈ obs, (∃ k, o = Page.Obs.toRelay (Relay.Ev.read id k) 0) ∨ ∃ str, o = Page.Obs.cb str := by
  obtain ⟨R, hR, hRR⟩ := wake_loop_inv id c0 c0.readers (c0, [], [])
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun o ho => by simp at ho⟩
  refine ⟨{ R.1 with readers := R.2.1 }, R.2.2, ?_, hRR.1, hRR.2.1, hRR.2.2.1, hRR.2.2.2.1,
    hRR.2.2.2.2.1, hRR.2.2.2.2.2.1, hRR.2.2.2.2.2.2.1, hRR.2.2.2.2.2.2.2.1, hRR.2.2.2.2.2.2.2.2.1,
    hRR.2.2.2.2.2.2.2.2.2⟩
  unfold Page.wake
  simp only [h]
  rw [hR]
  simp only [pure_bind]
  rfl

-- the page's frames DATA and EOF: the frame's connection changes, then the page wakes the readers
theorem frame_data_wake (st : Page.State) (id n : Nat) (c : Page.PConn) (hc : (st.slots id).conn = some c)
    (hcl : (st.slots id).closing = false) :
    (Page.frame st (Relay.Out.data id n)).1 =
        (Page.wake (Page.setSlot st id { st.slots id with conn := some { c with received := c.received + n } }) id).1 ∧
    (Page.frame st (Relay.Out.data id n)).2 =
        (Page.wake (Page.setSlot st id { st.slots id with conn := some { c with received := c.received + n } }) id).2 := by
  have hap : Page.applies st (Relay.Out.data id n) = some c.seq := by
    simp [Page.applies, hcl, hc]
  unfold Page.frame
  rw [hap]
  simp [hc]

theorem frame_eof_wake (st : Page.State) (id : Nat) (c : Page.PConn) (hc : (st.slots id).conn = some c)
    (hcl : (st.slots id).closing = false) :
    (Page.frame st (Relay.Out.eof id)).1 =
        (Page.wake (Page.setSlot st id { st.slots id with conn := some { c with eof := true } }) id).1 ∧
    (Page.frame st (Relay.Out.eof id)).2 =
        (Page.wake (Page.setSlot st id { st.slots id with conn := some { c with eof := true } }) id).2 := by
  have hap : Page.applies st (Relay.Out.eof id) = some c.seq := by
    simp [Page.applies, hcl, hc]
  unfold Page.frame
  rw [hap]
  simp [hc]

-- the core of a frame that wakes the readers of its id: the connection of the id keeps its ordering fields
theorem inv_wake_core (T : TSys) (h : Inv T) (c' : Client.Sys) (id t : Nat) (o : Relay.Out)
    (rest : List (Relay.Out × Nat)) (hq : T.c.toPage = (o, t) :: rest) (hid : outIdT o = some id)
    (hcl' : isClosedOut o = false) (c : Page.PConn) (hc : (T.c.page.slots id).conn = some c)
    (hcl0 : (T.c.page.slots id).closing = false) (c2 : Page.PConn) (hseq : c2.seq = c.seq)
    (hop : c2.isOpen = c.isOpen) (htail : c2.tail = c.tail) (hsent : c2.sent = c.sent)
    (hwr : c2.written = c.written) (hdp : c2.discardPending = c.discardPending)
    (P : Page.State) (L' : List (Relay.Ev × Nat)) (hL' : ∀ x ∈ L', ∃ k, x = (Relay.Ev.read id k, 0))
    (hrs : c'.rs = T.c.rs) (hr : c'.toRelay = T.c.toRelay ++ L') (hg : c'.genOf = T.c.genOf)
    (hs : c'.toPage = rest) (hp : c'.page = P)
    (hconn : ∀ j, j ≠ id → (P.slots j).conn = (T.c.page.slots j).conn)
    (hconn2 : (P.slots id).conn = some c2) (hcl : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing)
    (hnext : P.nextSeq = T.c.page.nextSeq) : Inv ⟨c', T.clk⟩ := by
  obtain ⟨rs', pg', tr', tp', gg', bd', pr', sk'⟩ := c'
  dsimp only at hrs hr hg hs hp
  subst hrs hr hg
  subst tp'
  subst pg'
  have hmemq : (o, t) ∈ T.c.toPage := by rw [hq]; simp
  have hsub : ∀ q ∈ rest, q ∈ T.c.toPage := fun q hq' => by
    rw [hq]
    exact List.mem_cons_of_mem _ hq'
  have hsl : rest.Sublist T.c.toPage := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hpo : ∀ j, (P.slots j).conn = if j = id then some c2 else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · rw [hj, hconn2, if_pos rfl]
    · rw [hconn j hj, if_neg hj]
  have hsv := h.apply (o, t) hmemq id hcl' hid c hc
  have hgen : (c.seq, t) ∈ T.c.genOf := by
    rcases hsv with h1 | h1
    · rw [hcl0] at h1
      cases h1
    · exact h1
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_, discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_, wrSent := ?_, replyFrozen := ?_, replyMax := ?_, noDeny := ?_, closeUniq := ?closeUniq, connSeq := ?connSeq }
  case closeUniq =>
    intro id
    rw [count_app_nil (CloseIs id) _ _ (by intro x hx; obtain ⟨k, rfl⟩ := hL' x hx; rfl)]
    exact h.closeUniq id
  case connSeq =>
    intro s
    rw [count_app_nil (ConnSeqIs s) _ _ (by intro x hx; obtain ⟨k, rfl⟩ := hL' x hx; rfl)]
    exact h.connSeq s
  · -- pi
    intro j pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      have hpi := h.pi id c hc
      unfold Page.PInv at hpi ⊢
      rw [hwr, hsent, htail]
      exact hpi
    · rw [if_neg hj] at hpc
      exact h.pi j pc hpc
  · -- link
    intro j c3 hc3
    rcases h.link j c3 hc3 with ⟨pc0, hpc0, hm⟩ | ⟨hn0, hcl2⟩
    · by_cases hj : j = id
      · left
        have hpc0c : pc0 = c := by
          have h1 : (T.c.page.slots j).conn = some pc0 := hpc0
          rw [hj, hc] at h1
          exact (Option.some.inj h1).symm
        rw [hpc0c] at hm
        refine ⟨c2, ?_, ?_⟩
        · show (P.slots j).conn = some c2
          rw [hj]
          exact hconn2
        · rw [hseq]
          exact hm
      · left
        refine ⟨pc0, ?_, hm⟩
        show (P.slots j).conn = some pc0
        rw [hpo j, if_neg hj]
        exact hpc0
    · by_cases hj : j = id
      · exfalso
        have h1 : (T.c.page.slots j).conn = none := hn0
        rw [hj, hc] at h1
        cases h1
      · right
        refine ⟨?_, ?_⟩
        · show (P.slots j).conn = none
          rw [hpo j, if_neg hj]
          exact hn0
        · show (P.slots j).closing = true
          rw [hcl j]
          exact hcl2
  · -- acc
    intro j pc c3 hpc hc3 hm
    rw [qs_app_reads j id _ _ _ _ _ _ _ _ _ _ hL']
    by_cases hj : j = id
    · change (P.slots j).conn = some pc at hpc
      rw [hpo j, if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hc3
      rw [hj]
      rw [hseq] at hm
      obtain ⟨a, b⟩ := h.acc id c c3 hc hc3 hm
      exact ⟨by rw [hsent]; exact a, by rw [hwr]; exact b⟩
    · change (P.slots j).conn = some pc at hpc
      rw [hpo j, if_neg hj] at hpc
      exact h.acc j pc c3 hpc hc3 hm
  · -- wq
    intro j c3 hc3
    rw [qs_app_reads j id _ _ _ _ _ _ _ _ _ _ hL']
    exact h.wq j c3 hc3
  · -- gen
    intro q hq' j hqj c3 hc3
    exact h.gen q (hsub q hq') j hqj c3 hc3
  · -- apply
    intro q hq' j hcl'' hqj pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
    rw [hcl j]
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hqj
      have hq2 := h.apply q (hsub q hq') id hcl'' hqj c hc
      rw [hcl0] at hq2
      rcases hq2 with h2 | h2
      · cases h2
      · rw [hseq]
        exact Or.inr h2
    · rw [if_neg hj] at hpc
      exact h.apply q (hsub q hq') j hcl'' hqj pc hpc
  · -- noOrphan
    intro q hq' j hcl'' hqj hn
    change (P.slots j).conn = none at hn
    rw [hpo j] at hn
    show (P.slots j).closing = true
    rw [hcl j]
    by_cases hj : j = id
    · rw [if_pos hj] at hn
      cases hn
    · rw [if_neg hj] at hn
      exact h.noOrphan q (hsub q hq') j hcl'' hqj hn
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    exact h.written q (hsub q hq') j cnt f hqj c3 hc3 hg3
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp' hg3 c3 hc3 hgen
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    rw [qs_app_reads j id _ _ _ _ _ _ _ _ _ _ hL']
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hqj hc3
      rw [hj]
      rw [hseq] at hg3
      rw [hdp] at hdp'
      exact h.reset q (hsub q hq') id cnt hqj c hc hdp' hg3 c3 hc3 hgen
    · rw [if_neg hj] at hpc
      exact h.reset q (hsub q hq') j cnt hqj pc hpc hdp' hg3 c3 hc3 hgen
  · -- barrier
    rw [List.pairwise_append]
    refine ⟨h.barrier, pairwise_of_forall _ L' (fun a ha b hb => ?_), ?_⟩
    · obtain ⟨k, rfl⟩ := hL' a ha
      obtain ⟨k', rfl⟩ := hL' b hb
      simp [FwdEv]
    · intro x hx y hy
      obtain ⟨k, rfl⟩ := hL' y hy
      intro hf
      obtain ⟨e, p⟩ := x
      cases e with
      | connect a =>
        simp [FwdEv] at hf
        subst hf
        exact h.connPend _ hx a rfl (o, t) hmemq hid
      | deny a => simp [FwdEv] at hf
      | send a n => simp [FwdEv] at hf
      | discard a => simp [FwdEv] at hf
      | read a k' => simp [FwdEv] at hf
      | close a => simp [FwdEv] at hf
      | sock a g k' => simp [FwdEv] at hf
  · -- connClean
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.connClean x h1 j hxj
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- notOpen
    intro j pc hpc hop'
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      have hcop : c.isOpen = false := by rw [← hop]; exact hop'
      have hn := h.notOpen id c hc hcop
      rw [hsent, hwr]
      exact hn
    · rw [if_neg hj] at hpc
      exact h.notOpen j pc hpc hop'
  · -- cl
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · rcases h.cl x h1 j hxj with ⟨pc, hpc, hs'⟩ | ⟨hn, hcl2⟩
      · by_cases hj : j = id
        · left
          have h1' : (T.c.page.slots j).conn = some pc := hpc
          rw [hj, hc] at h1'
          cases Option.some.inj h1'
          refine ⟨c2, ?_, ?_⟩
          · show (P.slots j).conn = some c2
            rw [hj]
            exact hconn2
          · rw [hseq]
            exact hs'
        · left
          refine ⟨pc, ?_, hs'⟩
          show (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]
          exact hpc
      · by_cases hj : j = id
        · exfalso
          have h1' : (T.c.page.slots j).conn = none := hn
          rw [hj, hc] at h1'
          cases h1'
        · right
          refine ⟨?_, ?_⟩
          · show (P.slots j).conn = none
            rw [hpo j, if_neg hj]
            exact hn
          · show (P.slots j).closing = true
            rw [hcl j]
            exact hcl2
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- rq
    intro q hq' j cnt hqj x hx n
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.rq q (hsub q hq') j cnt hqj x h1 n
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp
  · -- gensLt
    intro j c3 hc3
    exact h.gensLt j c3 hc3
  · -- gp
    intro x hx j hxj g
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.gp x h1 j hxj g
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- openG
    intro j pc hpc hop'
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      have hcop : c.isOpen = true := by rw [← hop]; exact hop'
      obtain ⟨g, hg'⟩ := h.openG id c hc hcop
      exact ⟨g, by rw [hseq]; exact hg'⟩
    · rw [if_neg hj] at hpc
      exact h.openG j pc hpc hop'
  · -- mirror
    exact h.mirror
  · -- good
    exact h.good
  · -- seqG
    intro p g hm
    rw [hnext]
    exact h.seqG p g hm
  · -- seqQ
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · rw [hnext]
      exact h.seqQ x h1 j hxj
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- disc
    intro x hx j hxj pc hpc hop'
    rcases List.mem_append.mp hx with h1 | h1
    · change (P.slots j).conn = some pc at hpc
      rw [hpo j] at hpc
      by_cases hj : j = id
      · rw [if_pos hj] at hpc
        cases Option.some.inj hpc
        have hcop : c.isOpen = true := by rw [← hop]; exact hop'
        rw [hdp]
        rw [hj] at hxj
        exact h.disc x h1 id hxj c hc hcop
      · rw [if_neg hj] at hpc
        exact h.disc x h1 j hxj pc hpc hop'
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- rep
    intro q hq' j cnt hqj
    rcases h.rep q (hsub q hq') j cnt hqj with ⟨pc, hpc, hd⟩ | ⟨hn, hcl2⟩
    · by_cases hj : j = id
      · left
        have h1' : (T.c.page.slots j).conn = some pc := hpc
        rw [hj, hc] at h1'
        cases Option.some.inj h1'
        refine ⟨c2, ?_, ?_⟩
        · show (P.slots j).conn = some c2
          rw [hj]
          exact hconn2
        · rw [hdp]
          exact hd
      · left
        refine ⟨pc, ?_, hd⟩
        show (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]
        exact hpc
    · by_cases hj : j = id
      · exfalso
        have h1' : (T.c.page.slots j).conn = none := hn
        rw [hj, hc] at h1'
        cases h1'
      · right
        refine ⟨?_, ?_⟩
        · show (P.slots j).conn = none
          rw [hpo j, if_neg hj]
          exact hn
        · show (P.slots j).closing = true
          rw [hcl j]
          exact hcl2
  · -- recvG
    intro j pc hpc hrc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      exact ⟨t, by rw [hseq]; exact hgen⟩
    · rw [if_neg hj] at hpc
      exact h.recvG j pc hpc hrc
  · -- failNone
    intro q hq' j e hqj
    exact h.failNone q (hsub q hq') j e hqj
  · -- closedNone
    intro q hq' j hqj
    exact h.closedNone q (hsub q hq') j hqj
  · -- closedClosing
    intro q hq' j hqj
    show (P.slots j).closing = true
    rw [hcl j]
    exact h.closedClosing q (hsub q hq') j hqj
  · -- closedOrd
    exact List.Pairwise.sublist hsl h.closedOrd
  · -- closeClosing
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · show (P.slots j).closing = true
      rw [hcl j]
      exact h.closeClosing x h1 j hxj
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q (hsub q hq') j hqj x h1
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp
  · -- openRel
    intro j pc hpc hop'
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    intro c3 hc3
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hc3
      have hcop : c.isOpen = true := by rw [← hop]; exact hop'
      exact h.openRel id c hc hcop c3 hc3
    · rw [if_neg hj] at hpc
      exact h.openRel j pc hpc hop' c3 hc3
  · -- okOpen
    intro q hq' j hqj hcl'' pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hqj hcl''
      have hcl3 : (T.c.page.slots id).closing = false := by
        rw [← hcl id]
        exact hcl''
      rw [hop]
      exact h.okOpen q (hsub q hq') id hqj hcl3 c hc
    · rw [if_neg hj] at hpc
      have hcl3 : (T.c.page.slots j).closing = false := by
        rw [← hcl j]
        exact hcl''
      exact h.okOpen q (hsub q hq') j hqj hcl3 pc hpc
  · -- okNoDisc
    intro q hq' j hqj hcl'' x hx
    rcases List.mem_append.mp hx with h1 | h1
    · have hcl3 : (T.c.page.slots j).closing = false := by
        rw [← hcl j]
        exact hcl''
      exact h.okNoDisc q (hsub q hq') j hqj hcl3 x h1
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp
  · -- discRel
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · by_cases hj : j = id
      · rw [hj] at hxj ⊢
        rcases h.discRel x h1 id hxj with h0 | ⟨pc, hpc, hop'⟩ | ⟨hn, hcl2⟩
        · exact Or.inl h0
        · refine Or.inr (Or.inl ⟨c2, ?_, ?_⟩)
          · show (P.slots id).conn = some c2
            exact hconn2
          · have h1' : (T.c.page.slots id).conn = some pc := hpc
            rw [hc] at h1'
            cases Option.some.inj h1'
            rw [hop]
            exact hop'
        · exfalso
          have h1' : (T.c.page.slots id).conn = none := hn
          rw [hc] at h1'
          cases h1'
      · rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop'⟩ | ⟨hn, hcl2⟩
        · exact Or.inl h0
        · refine Or.inr (Or.inl ⟨pc, ?_, hop'⟩)
          change (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]
          exact hpc
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]
            exact hn
          · change (P.slots j).closing = true
            rw [hcl j]
            exact hcl2
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- closingNone
    intro j hcl''
    rw [hcl j] at hcl''
    show (P.slots j).conn = none
    by_cases hj : j = id
    · rw [hj, hcl0] at hcl''
      cases hcl''
    · rw [hpo j, if_neg hj]
      exact h.closingNone j hcl''
  · -- closedNoClose
    intro q hq' j hqj x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q (hsub q hq') j hqj x h1
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp
  · -- failOrd
    exact List.Pairwise.sublist hsl h.failOrd
  · -- connPend
    intro x hx j hxj q hq'
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.connPend x h1 j hxj q (hsub q hq')
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp at hxj
  · -- okRel
    intro q hq' j hqj
    exact h.okRel q (hsub q hq') j hqj
  · -- okOrd
    exact List.Pairwise.sublist hsl h.okOrd
  · -- discOnce
    intro q hq' id cnt hqj x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.discOnce q (hsub q hq') id cnt hqj x h1
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp
  · -- discUniq
    intro id
    exact discUniq_of_sub _ _ id hsl (h.discUniq id)
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hg
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hqj
      rw [hseq] at hg
      rw [hwr]
      exact h.wrMono q (hsub q hq') id cnt f hqj c hc hg
    · rw [if_neg hj] at hpc
      exact h.wrMono q (hsub q hq') j cnt f hqj pc hpc hg
  · -- wrOrd
    exact List.Pairwise.sublist hsl h.wrOrd
  · -- genFun
    exact h.genFun
  · -- wrSent
    intro q hq id' cnt f hqj pc hpc hgq
    by_cases hid : id' = id
    · unfold PageOf at hpc
      rw [hid, hconn2] at hpc
      have hpe : pc = c2 := (Option.some.inj hpc).symm
      rw [hpe, hsent]
      rw [hid] at hqj
      exact h.wrSent q (hsub q hq) id cnt f hqj c hc (by rw [← hseq, ← hpe]; exact hgq)
    · exact h.wrSent q (hsub q hq) id' cnt f hqj pc (by unfold PageOf at hpc ⊢; rw [← hconn id' hid]; exact hpc) hgq
  · -- replyFrozen
    intro q hq id' cnt hqj c' hc' hcg'
    exact h.replyFrozen q (hsub q hq) id' cnt hqj c' hc' hcg'
  · -- replyMax
    intro q hq r hr id' c1 c2' f h1 h2 hg
    exact h.replyMax q (hsub q hq) r (hsub r hr) id' c1 c2' f h1 h2 hg
  · intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.noDeny x h1
    · obtain ⟨k, rfl⟩ := hL' x h1
      simp

-- the page takes a DATA frame: the id's connection gains the bytes, the readers wake, and the wake's READs are
-- queued
theorem inv_tDoPage_data (T T' : TSys) (h : Inv T) (id n t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.data id n, t) :: rest) (c : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c) (hcl0 : (T.c.page.slots id).closing = false)
    (hT : tDoPage T = some T') : Inv T' := by
  unfold tDoPage lift Client.doPage at hT
  simp only [hq] at hT
  generalize hG : Page.frame T.c.page (Relay.Out.data id n) = G at hT
  obtain ⟨st', obs⟩ := G
  have hfr := frame_data_wake T.c.page id n c hc hcl0
  rw [hG] at hfr
  dsimp only at hfr
  obtain ⟨hst, hob⟩ := hfr
  obtain ⟨c2, obs2, hw, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hobs⟩ :=
    wake_spec (Page.setSlot T.c.page id { T.c.page.slots id with conn := some { c with received := c.received + n } })
      id { c with received := c.received + n } (by simp [Page.setSlot, hc])
  rw [hw] at hst hob
  dsimp only at hst hob
  subst hst
  subst hob
  simp only [Option.map_some, Option.some.injEq] at hT
  subst hT
  exact inv_wake_core T h _ id t (Relay.Out.data id n) rest hq (by simp [outIdT]) (by simp [isClosedOut]) c hc
    hcl0 c2 hs1 hs2 hs3 hs4 hs5 hs8 _ _
    (by
      intro x hx
      obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hx
      rcases hobs a ha with ⟨k, rfl⟩ | ⟨str, rfl⟩
      · exact ⟨k, by simp_all⟩
      · simp at hfa)
    rfl rfl rfl rfl rfl
    (by intro j hj; simp [Page.setSlot, hj])
    (by simp [Page.setSlot])
    (by intro j; by_cases hj : j = id <;> simp [Page.setSlot, hj])
    (by simp [Page.setSlot])

-- the page takes an EOF frame: the id's connection hears the end, the readers wake, and the wake's READs are queued
theorem inv_tDoPage_eof (T T' : TSys) (h : Inv T) (id t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.eof id, t) :: rest) (c : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c) (hcl0 : (T.c.page.slots id).closing = false)
    (hT : tDoPage T = some T') : Inv T' := by
  unfold tDoPage lift Client.doPage at hT
  simp only [hq] at hT
  generalize hG : Page.frame T.c.page (Relay.Out.eof id) = G at hT
  obtain ⟨st', obs⟩ := G
  have hfr := frame_eof_wake T.c.page id c hc hcl0
  rw [hG] at hfr
  dsimp only at hfr
  obtain ⟨hst, hob⟩ := hfr
  obtain ⟨c2, obs2, hw, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hobs⟩ :=
    wake_spec (Page.setSlot T.c.page id { T.c.page.slots id with conn := some { c with eof := true } })
      id { c with eof := true } (by simp [Page.setSlot, hc])
  rw [hw] at hst hob
  dsimp only at hst hob
  subst hst
  subst hob
  simp only [Option.map_some, Option.some.injEq] at hT
  subst hT
  exact inv_wake_core T h _ id t (Relay.Out.eof id) rest hq (by simp [outIdT]) (by simp [isClosedOut]) c hc
    hcl0 c2 hs1 hs2 hs3 hs4 hs5 hs8 _ _
    (by
      intro x hx
      obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hx
      rcases hobs a ha with ⟨k, rfl⟩ | ⟨str, rfl⟩
      · exact ⟨k, by simp_all⟩
      · simp at hfa)
    rfl rfl rfl rfl rfl
    (by intro j hj; simp [Page.setSlot, hj])
    (by simp [Page.setSlot])
    (by intro j; by_cases hj : j = id <;> simp [Page.setSlot, hj])
    (by simp [Page.setSlot])

end Ind
