namespace Ind
open Timed

theorem qsumT_app (id : Nat) (l1 l2 : List (Relay.Ev × Nat)) :
    qsumT id (l1 ++ l2) = qsumT id l1 + qsumT id l2 := by
  induction l1 with
  | nil => simp [qsumT]
  | cons x xs ih =>
    obtain ⟨e, p⟩ := x
    simp only [List.cons_append, qsumT, ih]
    omega

theorem qsumT_connect (id a seq : Nat) : qsumT id [(Relay.Ev.connect a, seq)] = 0 := by
  simp [qsumT]

theorem fwd_connect_right (x : Relay.Ev) (b : Nat) (h : FwdEv x (Relay.Ev.connect b)) :
    (∃ a, x = Relay.Ev.connect a ∧ a = b) ∨ (∃ a, x = Relay.Ev.close a ∧ a = b) := by
  cases x <;> simp_all [FwdEv]

-- a CONNECT of the page for an id without a connection and not closing: the page's new connection (fresh
-- sequence number) and the frame it adds to the queue keep the invariant
theorem inv_page_connect (T : TSys) (h : Inv T) (id : Nat) (c : Page.PConn) (P : Page.State)
    (hnone : (T.c.page.slots id).conn = none) (hcl : (T.c.page.slots id).closing = false)
    (hc : c.seq = T.c.page.nextSeq) (hopen : c.isOpen = false) (hsent : c.sent = 0) (hwr : c.written = 0)
    (hdp : c.discardPending = false) (hrec : c.received = 0)
    (hother : ∀ j, j ≠ id → P.slots j = T.c.page.slots j)
    (hslotc : (P.slots id).conn = some c) (hslotcl : (P.slots id).closing = (T.c.page.slots id).closing)
    (hnext : P.nextSeq = c.seq + 1) :
    Inv ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ [(Relay.Ev.connect id, c.seq)] }, T.clk⟩ := by
  have hpo : ∀ j, (P.slots j).conn = if j = id then some c else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · subst hj; simp [hslotc]
    · simp [hj, hother j hj]
  have hcl' : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing := by
    intro j
    by_cases hj : j = id
    · subst hj; exact hslotcl
    · rw [hother j hj]
  have hcon : ConnOf T id = none := by
    cases hc0 : ConnOf T id with
    | none => rfl
    | some cc =>
      rcases h.link id cc hc0 with ⟨pc, hpc, _⟩ | ⟨hpn, hcl2⟩
      · simp [PageOf, hnone] at hpc
      · rw [hcl] at hcl2; exact absurd hcl2 (by simp)
  have hq : ∀ x, x ∈ (T.c.toRelay ++ [(Relay.Ev.connect id, c.seq)]) ↔
      x ∈ T.c.toRelay ∨ x = (Relay.Ev.connect id, c.seq) := by
    intro x; simp
  have hqs : ∀ j, qs j ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ [(Relay.Ev.connect id, c.seq)] }, T.clk⟩
      = qs j T := by
    intro j; simp only [qs, qsumT_app, qsumT_connect]; simp [qsumT]
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_, failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_, closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_, closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_ }
  · intro j pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    split at hpc
    · cases hpc
      unfold Page.PInv; simp [hsent, hwr]
    · exact h.pi j pc (by unfold PageOf; exact hpc)
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj; rw [hcon] at hcc'; cases hcc'
    · rcases h.link j cc hcc' with ⟨pc, hpc, hg⟩ | ⟨hpn, hcl2⟩
      · left
        refine ⟨pc, ?_, hg⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc cc hpc hcc hg
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj; rw [hcon] at hcc'; cases hcc'
    · have hpc' : PageOf T j = some pc := by
        change (P.slots j).conn = some pc at hpc
        rw [hpo j, if_neg hj] at hpc; exact hpc
      rw [hqs j]
      exact h.acc j pc cc hpc' hcc' hg
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rw [hqs j]
    exact h.wq j cc hcc'
  · intro q hq j hoj cc hcc
    exact h.gen q hq j hoj cc hcc
  · intro q hq j hnc hoj pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj
      exfalso
      have hn : PageOf T j = none := by unfold PageOf; rw [hnone]
      have hc2 := h.noOrphan q hq j hnc hoj hn
      rw [hcl] at hc2; cases hc2
    · rw [if_neg hj] at hpc
      show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
      rw [hcl' j]
      exact h.apply q hq j hnc hoj pc (by unfold PageOf; exact hpc)
  · intro q hq j hnc hoj hpn
    change (P.slots j).conn = none at hpn
    rw [hpo j] at hpn
    by_cases hj : j = id
    · subst hj; simp at hpn
    · rw [if_neg hj] at hpn
      show (P.slots j).closing = true
      rw [hcl' j]
      exact h.noOrphan q hq j hnc hoj (by unfold PageOf; exact hpn)
  · intro q hq j cnt f hq1 cc hcc hg
    exact h.written q hq j cnt f hq1 cc hcc hg
  · intro q hq j cnt hq1 pc hpc hdp' hg cc hcc hgg
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp_all
    · rw [if_neg hj] at hpc
      rw [hqs j]
      exact h.reset q hq j cnt hq1 pc (by unfold PageOf; exact hpc) hdp' hg cc hcc hgg
  · show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) (T.c.toRelay ++ [(Relay.Ev.connect id, c.seq)])
    rw [List.pairwise_append]
    refine ⟨h.barrier, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    show ¬ FwdEv a.1 (Relay.Ev.connect id)
    intro hF
    rcases fwd_connect_right a.1 id hF with ⟨a', ha', haid⟩ | ⟨a', ha', haid⟩
    · rcases h.cl a ha a' ha' with ⟨pc, hpc, _⟩ | ⟨hpn, hcl2⟩
      · rw [haid] at hpc; unfold PageOf at hpc; rw [hnone] at hpc; cases hpc
      · rw [haid, hcl] at hcl2; cases hcl2
    · have hcc := h.closeClosing a ha a' ha'
      rw [haid, hcl] at hcc
      cases hcc
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.connClean q h1 j hqc
    · rw [List.mem_singleton] at h1; subst h1
      simp at hqc; subst hqc; exact hcon
  · intro j pc hpc hop
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp at hpc; subst hpc; exact ⟨hsent, hwr⟩
    · rw [if_neg hj] at hpc; exact h.notOpen j pc hpc hop
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · rcases h.cl q h1 j hqc with ⟨pc, hpc, hs⟩ | ⟨hpn, hcl2⟩
      · left
        by_cases hj : j = id
        · subst hj; unfold PageOf at hpc; rw [hnone] at hpc; cases hpc
        · refine ⟨pc, ?_, hs⟩
          change (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]; exact hpc
      · by_cases hj : j = id
        · subst hj; rw [hcl] at hcl2; cases hcl2
        · right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
    · rw [List.mem_singleton] at h1; subst h1
      simp at hqc; subst hqc
      exact Or.inl ⟨c, by show (P.slots id).conn = some c; exact hslotc, rfl⟩
  · intro q hq j cnt hq1 x hx n
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.rq q hq j cnt hq1 x h1 n
    · rw [List.mem_singleton] at h1; subst h1; simp
  · intro j cc hcc
    exact h.gensLt j cc hcc
  · intro q hq j hqc g
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.gp q h1 j hqc g
    · rw [List.mem_singleton] at h1; subst h1
      intro hm
      have := h.seqG c.seq g hm
      omega
  · intro j pc hpc hop
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp at hpc; subst hpc; rw [hopen] at hop; cases hop
    · rw [if_neg hj] at hpc; exact h.openG j pc hpc hop
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < P.nextSeq
    rw [hnext]
    have := h.seqG p g hm
    omega
  · intro q hq j hqc
    show q.2 < P.nextSeq
    rw [hnext]
    rcases List.mem_append.mp hq with h1 | h1
    · have := h.seqQ q h1 j hqc
      omega
    · rw [List.mem_singleton] at h1; subst h1
      omega

  · intro q hq j hd pc hp hop
    rcases List.mem_append.mp hq with h1 | h1
    · by_cases hj : j = id
      · subst hj
        change (P.slots j).conn = some pc at hp
        rw [hpo j] at hp
        simp at hp
        subst hp
        rw [hopen] at hop; cases hop
      · change (P.slots j).conn = some pc at hp
        rw [hpo j, if_neg hj] at hp
        exact h.disc q h1 j hd pc (by unfold PageOf; exact hp) hop
    · rw [List.mem_singleton] at h1; subst h1; simp at hd
  · intro q hq j cnt hq1
    rcases h.rep q hq j cnt hq1 with ⟨pc, hpc, hpd⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj; unfold PageOf at hpc; rw [hnone] at hpc; cases hpc
      · left
        refine ⟨pc, ?_, hpd⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc
    · by_cases hj : j = id
      · subst hj; rw [hcl] at hcl2; cases hcl2
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc hp hr
    change (P.slots j).conn = some pc at hp
    rw [hpo j] at hp
    by_cases hj : j = id
    · subst hj; simp at hp; subst hp; simp [hrec] at hr
    · rw [if_neg hj] at hp; exact h.recvG j pc (by unfold PageOf; exact hp) hr

  · intro q hq j e hfl
    exact h.failNone q hq j e hfl
  · intro q hq j hfl
    exact h.closedNone q hq j hfl
  · intro q hq j hfl
    show (P.slots j).closing = true
    rw [hcl' j]
    exact h.closedClosing q hq j hfl
  · exact h.closedOrd
  · intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · show (P.slots j).closing = true
      rw [hcl' j]
      exact h.closeClosing x h1 j hxj
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q hq j hfl x h1 hxe
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxe
      subst hxe
      have hc2 := h.closedClosing q hq _ hfl
      rw [hcl] at hc2
      cases hc2
  · intro j pc hpcI hop cc hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      rw [hopen] at hop
      cases hop
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.openRel j pc (by unfold PageOf; exact hpcI) hop cc hcc
  · intro q hq j hfl hcl2 pc hpcI
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      exact hopen
    · change (P.slots j).closing = false at hcl2
      rw [hcl' j] at hcl2
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.okOpen q hq j hfl hcl2 pc (by unfold PageOf; exact hpcI)
  · intro q hq j hfl hcl2 x hx
    have hcl3 : (T.c.page.slots j).closing = false := by
      change (P.slots j).closing = false at hcl2
      rw [hcl' j] at hcl2
      exact hcl2
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.okNoDisc q hq j hfl hcl3 x h1
    · rw [List.mem_singleton] at h1
      subst h1
      simp
  · intro x hx j hxj
    by_cases hj : j = id
    · subst hj
      exact Or.inl hcon
    · rcases List.mem_append.mp hx with h1 | h1
      · rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop⟩ | ⟨hpn, hcl2⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨pc, by change (P.slots j).conn = some pc; rw [hpo j, if_neg hj]; exact hpc, hop⟩)
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
      · rw [List.mem_singleton] at h1
        subst h1
        simp at hxj
  · intro j hcl2
    change (P.slots j).closing = true at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      rw [hcl] at hcl2
      cases hcl2
    · change (P.slots j).conn = none
      rw [hpo j, if_neg hj]
      exact h.closingNone j hcl2
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q hq j hfl x h1 hxe
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxe
  · exact h.failOrd
  · intro x hx j hxj q hq'
    try simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | h1
    · exact h.connPend x h1 j hxj q hq'
    · subst h1
      simp at hxj
  · intro q hq' id hqi
    exact h.okRel q hq' id hqi
  · exact h.okOrd
  · intro x hx j hxj q hq'
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.connPend x h1 j hxj q hq'
    · rw [List.mem_singleton] at h1
      subst h1
      have hj : id = j := by simpa using hxj
      subst hj
      exact no_frame_of_free T h _ hnone hcl q hq'
  · intro q hq' id hqi
    exact h.okRel q hq' id hqi
  · exact h.okOrd

-- the page's CONNECT call, as the composed step does it: with no free id nothing changes; with one, the
-- connection is made and its CONNECT frame queued
theorem inv_tPageConnect (T T' : TSys) (h : Inv T) (hT : tPageCall T .connect = some T') : Inv T' := by
  unfold tPageCall lift at hT
  simp only [Client.pageCall, Page.step, Option.map_some, Option.some.injEq] at hT
  unfold Page.doConnect at hT
  split at hT
  · subst hT
    simpa using h
  · rename_i id hfind
    have hs := List.find?_some hfind
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
    obtain ⟨hn, hc⟩ := hs
    have hcl : (T.c.page.slots id).closing = false := by simpa using hc
    subst hT
    refine inv_page_connect T h id (Page.PConn.mk T.c.page.nextSeq false 0 0 0 0 0 false none false []) _ hn hcl rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
    · intro j hj; simp [Page.setSlot, hj]
    · simp [Page.setSlot]
    · simp [Page.setSlot]
    · rfl


theorem qsumT_close (id a p : Nat) : qsumT id [(Relay.Ev.close a, p)] = 0 := by
  simp [qsumT]

theorem fwd_close_right (x : Relay.Ev) (b : Nat) : ¬ FwdEv x (Relay.Ev.close b) := by
  cases x <;> simp [FwdEv]

-- what the page's CLOSE does to an id with a connection: the slot ends with no connection, closing (the fixed page),
-- the other slots and the sequence counter are the same, and the one frame queued is the CLOSE
theorem doClose_spec (st : Page.State) (i : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c) :
    ((Page.doClose st i).1.slots i).conn = none ∧
    ((Page.doClose st i).1.slots i).closing = st.fixed ∧
    (∀ j, j ≠ i → (Page.doClose st i).1.slots j = st.slots j) ∧
    (Page.doClose st i).1.nextSeq = st.nextSeq ∧
    (Page.doClose st i).1.fixed = st.fixed ∧
    ((Page.doClose st i).2.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) =
      [(Relay.Ev.close i, 0)] := by
  unfold Page.doClose
  rw [hc]
  refine ⟨by simp [Page.die, Page.setSlot], by simp [Page.die, Page.setSlot], ?_,
    by simp [Page.die, Page.setSlot], by simp [Page.die, Page.setSlot], ?_⟩
  · intro j hj
    simp [Page.die, Page.setSlot, hj]
  · cases ho : c.isOpen <;> cases hop : c.op <;> cases hd : c.discardPending <;>
      simp [Page.die, Page.setSlot, hc, ho, hop, hd, List.filterMap_map]

-- the page's CLOSE of an id with a connection keeps the invariant (the fixed page: the id is closing, the frame
-- queued is the CLOSE)
theorem inv_page_close (T : TSys) (h : Inv T) (id : Nat) (P : Page.State)
    (hn : (P.slots id).conn = none) (hcl1 : (P.slots id).closing = true)
    (hother : ∀ j, j ≠ id → P.slots j = T.c.page.slots j)
    (hnext : P.nextSeq = T.c.page.nextSeq) (hold : ∃ c0, (T.c.page.slots id).conn = some c0) :
    Inv ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ [(Relay.Ev.close id, 0)] }, T.clk⟩ := by
  have hpo : ∀ j, (P.slots j).conn = if j = id then none else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · subst hj; simp [hn]
    · simp [hj, hother j hj]
  have hcl' : ∀ j, (P.slots j).closing = if j = id then true else (T.c.page.slots j).closing := by
    intro j
    by_cases hj : j = id
    · subst hj; simp [hcl1]
    · simp [hj, hother j hj]
  have hq : ∀ x, x ∈ (T.c.toRelay ++ [(Relay.Ev.close id, 0)]) ↔ x ∈ T.c.toRelay ∨ x = (Relay.Ev.close id, 0) := by
    intro x; simp
  have hqs : ∀ j, qs j ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ [(Relay.Ev.close id, 0)] }, T.clk⟩
      = qs j T := by
    intro j; simp only [qs, qsumT_app, qsumT_close]; simp [qsumT]
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_, failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_, closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_, closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_ }
  · intro j pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    split at hpc
    · cases hpc
    · exact h.pi j pc (by unfold PageOf; exact hpc)
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj
      right
      refine ⟨?_, ?_⟩
      · change (P.slots j).conn = none; exact hn
      · change (P.slots j).closing = true; exact hcl1
    · rcases h.link j cc hcc' with ⟨pc, hpc, hg⟩ | ⟨hpn, hcl2⟩
      · left
        refine ⟨pc, ?_, hg⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j, if_neg hj]; exact hcl2
  · intro j pc cc hpc hcc hg
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpc
      simp [hn] at hpc
    · have hpc' : PageOf T j = some pc := by
        change (P.slots j).conn = some pc at hpc
        rw [hpo j, if_neg hj] at hpc; exact hpc
      rw [hqs j]
      exact h.acc j pc cc hpc' hcc' hg
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rw [hqs j]
    exact h.wq j cc hcc'
  · intro q hq j hoj cc hcc
    exact h.gen q hq j hoj cc hcc
  · intro q hq j hnc hoj pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp [hn] at hpc
    · rw [if_neg hj] at hpc
      show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
      rw [hcl' j, if_neg hj]
      exact h.apply q hq j hnc hoj pc (by unfold PageOf; exact hpc)
  · intro q hq j hnc hoj hpn
    change (P.slots j).conn = none at hpn
    rw [hpo j] at hpn
    show (P.slots j).closing = true
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj; simp
    · rw [if_neg hj] at hpn
      rw [if_neg hj]
      exact h.noOrphan q hq j hnc hoj (by unfold PageOf; exact hpn)
  · intro q hq j cnt f hq1 cc hcc hg
    exact h.written q hq j cnt f hq1 cc hcc hg
  · intro q hq j cnt hq1 pc hpc hdp' hg cc hcc hgg
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp [hn] at hpc
    · rw [if_neg hj] at hpc
      rw [hqs j]
      exact h.reset q hq j cnt hq1 pc (by unfold PageOf; exact hpc) hdp' hg cc hcc hgg
  · show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) (T.c.toRelay ++ [(Relay.Ev.close id, 0)])
    rw [List.pairwise_append]
    refine ⟨h.barrier, by simp, ?_⟩
    intro a _ b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact fwd_close_right a.1 id
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.connClean q h1 j hqc
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro j pc hpc hop
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp [hn] at hpc
    · rw [if_neg hj] at hpc; exact h.notOpen j pc hpc hop
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · rcases h.cl q h1 j hqc with ⟨pc, hpc, hs⟩ | ⟨hpn, hcl2⟩
      · by_cases hj : j = id
        · subst hj
          right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none; exact hn
          · change (P.slots j).closing = true; exact hcl1
        · left
          refine ⟨pc, ?_, hs⟩
          change (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]; exact hpc
      · by_cases hj : j = id
        · subst hj
          right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none; exact hn
          · change (P.slots j).closing = true; exact hcl1
        · right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j, if_neg hj]; exact hcl2
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro q hq j cnt hq1 x hx n
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.rq q hq j cnt hq1 x h1 n
    · rw [List.mem_singleton] at h1; subst h1; simp
  · intro j cc hcc
    exact h.gensLt j cc hcc
  · intro q hq j hqc g
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.gp q h1 j hqc g
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro j pc hpc hop
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · subst hj; simp [hn] at hpc
    · rw [if_neg hj] at hpc; exact h.openG j pc hpc hop
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < P.nextSeq
    rw [hnext]
    exact h.seqG p g hm
  · intro q hq j hqc
    show q.2 < P.nextSeq
    rw [hnext]
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.seqQ q h1 j hqc
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc

  · intro q hq j hd pc hp hop
    rcases List.mem_append.mp hq with h1 | h1
    · by_cases hj : j = id
      · subst hj
        change (P.slots j).conn = some pc at hp
        rw [hpo j] at hp
        simp at hp
      · change (P.slots j).conn = some pc at hp
        rw [hpo j, if_neg hj] at hp
        exact h.disc q h1 j hd pc (by unfold PageOf; exact hp) hop
    · rw [List.mem_singleton] at h1; subst h1; simp at hd
  · intro q hq j cnt hq1
    rcases h.rep q hq j cnt hq1 with ⟨pc, hpc, hpd⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none; exact hn
        · change (P.slots j).closing = true; exact hcl1
      · left
        refine ⟨pc, ?_, hpd⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc
    · by_cases hj : j = id
      · subst hj
        right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none; exact hn
        · change (P.slots j).closing = true; exact hcl1
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j, if_neg hj]; exact hcl2
  · intro j pc hp hr
    change (P.slots j).conn = some pc at hp
    rw [hpo j] at hp
    by_cases hj : j = id
    · subst hj; simp at hp
    · rw [if_neg hj] at hp; exact h.recvG j pc (by unfold PageOf; exact hp) hr

  · intro q hq j e hfl
    exact h.failNone q hq j e hfl
  · intro q hq j hfl
    exact h.closedNone q hq j hfl
  · intro q hq j hfl
    by_cases hj : j = id
    · subst hj
      show (P.slots j).closing = true
      rw [hcl' j]
      simp
    · show (P.slots j).closing = true
      rw [hcl' j, if_neg hj]
      exact h.closedClosing q hq j hfl
  · exact h.closedOrd
  · intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · by_cases hj : j = id
      · subst hj
        show (P.slots j).closing = true
        rw [hcl' j]
        simp
      · show (P.slots j).closing = true
        rw [hcl' j, if_neg hj]
        exact h.closeClosing x h1 j hxj
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
      rw [← hxj]
      show (P.slots id).closing = true
      rw [hcl' id]
      simp
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q hq j hfl x h1 hxe
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxe
  · intro j pc hpcI hop cc hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.openRel j pc (by unfold PageOf; exact hpcI) hop cc hcc
  · intro q hq j hfl hcl2 pc hpcI
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
    · change (P.slots j).closing = false at hcl2
      rw [hcl' j, if_neg hj] at hcl2
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.okOpen q hq j hfl hcl2 pc (by unfold PageOf; exact hpcI)
  · intro q hq j hfl hcl2 x hx
    have hcl3 : (T.c.page.slots j).closing = false := by
      change (P.slots j).closing = false at hcl2
      rw [hcl' j] at hcl2
      by_cases hj : j = id
      · subst hj
        simp at hcl2
      · rw [if_neg hj] at hcl2
        exact hcl2
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.okNoDisc q hq j hfl hcl3 x h1
    · rw [List.mem_singleton] at h1
      subst h1
      simp
  · intro x hx j hxj
    by_cases hj : j = id
    · subst hj
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · change (P.slots j).conn = none
        rw [hpo j]
        simp
      · change (P.slots j).closing = true
        rw [hcl' j]
        simp
    · rcases List.mem_append.mp hx with h1 | h1
      · rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop⟩ | ⟨hpn, hcl2⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨pc, by change (P.slots j).conn = some pc; rw [hpo j, if_neg hj]; exact hpc, hop⟩)
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j, if_neg hj]; exact hcl2
      · rw [List.mem_singleton] at h1
        subst h1
        simp at hxj
  · intro j hcl2
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = none
      rw [hpo j]
      simp
    · change (P.slots j).closing = true at hcl2
      rw [hcl' j, if_neg hj] at hcl2
      change (P.slots j).conn = none
      rw [hpo j, if_neg hj]
      exact h.closingNone j hcl2
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q hq j hfl x h1 hxe
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxe
      subst hxe
      have hcc := h.closingNone _ (h.closedClosing q hq _ hfl)
      obtain ⟨c0, hc0⟩ := hold
      rw [hc0] at hcc
      cases hcc
  · exact h.failOrd
  · intro x hx j hxj q hq'
    try simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | h1
    · exact h.connPend x h1 j hxj q hq'
    · subst h1
      simp at hxj
  · intro q hq' id hqi
    exact h.okRel q hq' id hqi
  · exact h.okOrd

theorem fwd_discard_left (x : Relay.Ev) (id : Nat) (h : FwdEv x (Relay.Ev.discard id)) :
    (∃ a, x = Relay.Ev.connect a ∧ a = id) ∨ (∃ a, x = Relay.Ev.discard a ∧ a = id) := by
  cases x <;> simp_all [FwdEv]

-- the page's DISCARD of an open connection that is not already discarding: the connection is pending, and the
-- DISCARD frame is queued behind everything the page has sent
theorem inv_page_discard (T : TSys) (h : Inv T) (id : Nat) (c c2 : Page.PConn) (P : Page.State)
    (hpc : (T.c.page.slots id).conn = some c) (hopen : c.isOpen = true) (hdp : c.discardPending = false)
    (hPc : (P.slots id).conn = some c2) (hcl' : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing)
    (hother : ∀ j, j ≠ id → P.slots j = T.c.page.slots j) (hnext : P.nextSeq = T.c.page.nextSeq)
    (hseq : c2.seq = c.seq) (hopen2 : c2.isOpen = true) (hdp2 : c2.discardPending = true)
    (hsent : c2.sent = c.sent) (hwr : c2.written = c.written) (hrec : c2.received = c.received)
    (hPI2 : Page.PInv c2) :
    Inv ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ [(Relay.Ev.discard id, 0)] }, T.clk⟩ := by
  have hpo : ∀ j, (P.slots j).conn = if j = id then some c2 else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · subst hj; simp [hPc]
    · simp [hj, hother j hj]
  have hcon : PageOf T id = some c := hpc
  have hlink : ∀ cc, ConnOf T id = some cc → (c.seq, cc.gen) ∈ T.c.genOf := by
    intro cc hcc
    rcases h.link id cc hcc with ⟨pc, hpc', hg⟩ | ⟨hpn, _⟩
    · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
      subst hpe; exact hg
    · rw [hcon] at hpn; cases hpn
  have hq : ∀ x, x ∈ (T.c.toRelay ++ [(Relay.Ev.discard id, 0)]) ↔ x ∈ T.c.toRelay ∨ x = (Relay.Ev.discard id, 0) := by
    intro x; simp
  have hqs : ∀ j, qs j ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ [(Relay.Ev.discard id, 0)] }, T.clk⟩
      = qs j T := by
    intro j; simp only [qs, qsumT_app]; simp [qsumT]
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_, failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_, closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_, closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_ }
  · intro j pc hpc'
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    split at hpc'
    · cases hpc'
      exact hPI2
    · exact h.pi j pc (by unfold PageOf; exact hpc')
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rcases h.link j cc hcc' with ⟨pc, hpc', hg⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
        subst hpe
        left
        refine ⟨c2, ?_, ?_⟩
        · change (P.slots j).conn = some c2; exact hPc
        · rw [hseq]; exact hg
      · left
        refine ⟨pc, ?_, hg⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc'
    · by_cases hj : j = id
      · subst hj; rw [hcon] at hpn; cases hpn
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc cc hpc' hcc hg
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpc'
      rw [hpo j] at hpc'
      simp at hpc'
      subst hpc'
      rw [hseq] at hg
      have hm := h.acc j c cc hcon hcc' (hlink cc hcc')
      rw [hqs j, hsent, hwr]
      exact hm
    · have hpc2 : PageOf T j = some pc := by
        change (P.slots j).conn = some pc at hpc'
        rw [hpo j, if_neg hj] at hpc'; exact hpc'
      rw [hqs j]
      exact h.acc j pc cc hpc2 hcc' hg
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rw [hqs j]
    exact h.wq j cc hcc'
  · intro q hq j hoj cc hcc
    exact h.gen q hq j hoj cc hcc
  · intro q hq j hnc hoj pc hpc'
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj
      simp at hpc'
      subst hpc'
      rw [hseq]
      exact h.apply q hq j hnc hoj c hcon
    · rw [if_neg hj] at hpc'
      exact h.apply q hq j hnc hoj pc (by unfold PageOf; exact hpc')
  · intro q hq j hnc hoj hpn
    change (P.slots j).conn = none at hpn
    rw [hpo j] at hpn
    show (P.slots j).closing = true
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj; simp at hpn
    · rw [if_neg hj] at hpn
      exact h.noOrphan q hq j hnc hoj (by unfold PageOf; exact hpn)
  · intro q hq j cnt f hq1 cc hcc hg
    exact h.written q hq j cnt f hq1 cc hcc hg
  · intro q hq j cnt hq1 pc hpc' hdp' hg cc hcc hgg
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj
      exfalso
      rcases h.rep q hq j cnt hq1 with ⟨pc0, hp0, hd0⟩ | ⟨hpn, _⟩
      · have hpe : pc0 = c := by rw [hcon] at hp0; exact (Option.some.inj hp0).symm
        subst hpe
        rw [hdp] at hd0; cases hd0
      · rw [hcon] at hpn; cases hpn
    · rw [if_neg hj] at hpc'
      rw [hqs j]
      exact h.reset q hq j cnt hq1 pc (by unfold PageOf; exact hpc') hdp' hg cc hcc hgg
  · show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) (T.c.toRelay ++ [(Relay.Ev.discard id, 0)])
    rw [List.pairwise_append]
    refine ⟨h.barrier, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    show ¬ FwdEv a.1 (Relay.Ev.discard id)
    intro hF
    rcases fwd_discard_left a.1 id hF with ⟨a', ha', hae⟩ | ⟨a', ha', hae⟩
    · rcases h.cl a ha a' ha' with ⟨pc, hpc', hs⟩ | ⟨hpn, _⟩
      · have h1 : PageOf T a' = some c := by rw [hae]; exact hcon
        have hpe : pc = c := by rw [h1] at hpc'; exact (Option.some.inj hpc').symm
        rw [hpe] at hs
        obtain ⟨g, hg⟩ := h.openG id c hcon hopen
        rw [hae] at ha'
        exact h.gp a ha id ha' g (by rw [← hs, hseq] at *; rw [← hs]; exact hg)
      · rw [hae] at hpn; rw [hcon] at hpn; cases hpn
    · have h1 : PageOf T a' = some c := by rw [hae]; exact hcon
      have hd := h.disc a ha a' ha' c h1 hopen
      rw [hdp] at hd; cases hd
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.connClean q h1 j hqc
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro j pc hpc' hop
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj; simp at hpc'; subst hpc'; rw [hopen2] at hop; cases hop
    · rw [if_neg hj] at hpc'; exact h.notOpen j pc hpc' hop
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · rcases h.cl q h1 j hqc with ⟨pc, hpc', hs⟩ | ⟨hpn, hcl2⟩
      · by_cases hj : j = id
        · subst hj
          left
          refine ⟨c2, ?_, ?_⟩
          · change (P.slots j).conn = some c2; exact hPc
          · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
            subst hpe
            rw [hseq]; exact hs
        · left
          refine ⟨pc, ?_, hs⟩
          change (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]; exact hpc'
      · by_cases hj : j = id
        · subst hj; rw [hcon] at hpn; cases hpn
        · right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro q hq j cnt hq1 x hx n
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.rq q hq j cnt hq1 x h1 n
    · rw [List.mem_singleton] at h1; subst h1; simp
  · intro j cc hcc
    exact h.gensLt j cc hcc
  · intro q hq j hqc g
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.gp q h1 j hqc g
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro j pc hpc' hop
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj
      simp at hpc'; subst hpc'
      obtain ⟨g, hg⟩ := h.openG j c hcon hopen
      exact ⟨g, by rw [hseq]; exact hg⟩
    · rw [if_neg hj] at hpc'; exact h.openG j pc hpc' hop
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < P.nextSeq
    rw [hnext]
    exact h.seqG p g hm
  · intro q hq j hqc
    show q.2 < P.nextSeq
    rw [hnext]
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.seqQ q h1 j hqc
    · rw [List.mem_singleton] at h1; subst h1; simp at hqc
  · intro q hq j hd pc hp hop'
    rcases List.mem_append.mp hq with h1 | h1
    · by_cases hj : j = id
      · subst hj
        change (P.slots j).conn = some pc at hp
        rw [hpo j] at hp
        simp at hp
        subst hp
        exact hdp2
      · change (P.slots j).conn = some pc at hp
        rw [hpo j, if_neg hj] at hp
        exact h.disc q h1 j hd pc (by unfold PageOf; exact hp) hop'
    · rw [List.mem_singleton] at h1; subst h1
      simp at hd
      subst hd
      change (P.slots id).conn = some pc at hp
      rw [hPc] at hp
      have := Option.some.inj hp
      subst this
      exact hdp2
  · intro q hq j cnt hq1
    rcases h.rep q hq j cnt hq1 with ⟨pc, hpc', hpd⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        left
        refine ⟨c2, ?_, hdp2⟩
        change (P.slots j).conn = some c2; exact hPc
      · left
        refine ⟨pc, ?_, hpd⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc'
    · by_cases hj : j = id
      · subst hj; rw [hcon] at hpn; cases hpn
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc hp hr
    change (P.slots j).conn = some pc at hp
    rw [hpo j] at hp
    by_cases hj : j = id
    · subst hj
      simp at hp
      subst hp
      have hr' : 0 < c.received := by rw [← hrec]; exact hr
      obtain ⟨g, hg⟩ := h.recvG j c hcon hr'
      exact ⟨g, by rw [hseq]; exact hg⟩
    · rw [if_neg hj] at hp
      exact h.recvG j pc (by unfold PageOf; exact hp) hr

  · intro q hq j e hfl
    exact h.failNone q hq j e hfl
  · intro q hq j hfl
    exact h.closedNone q hq j hfl
  · intro q hq j hfl
    show (P.slots j).closing = true
    rw [hcl' j]
    exact h.closedClosing q hq j hfl
  · exact h.closedOrd
  · intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · show (P.slots j).closing = true
      rw [hcl' j]
      exact h.closeClosing x h1 j hxj
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q hq j hfl x h1 hxe
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxe
  · intro j pc hpcI hop cc hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      exact h.openRel j c hcon hopen cc hcc
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.openRel j pc (by unfold PageOf; exact hpcI) hop cc hcc
  · intro q hq j hfl hcl2 pc hpcI
    change (P.slots j).closing = false at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      have h3 := h.okOpen q hq j hfl hcl2 c hcon
      rw [hopen] at h3
      cases h3
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.okOpen q hq j hfl hcl2 pc (by unfold PageOf; exact hpcI)
  · intro q hq j hfl hcl2 x hx
    have hcl3 : (T.c.page.slots j).closing = false := by
      change (P.slots j).closing = false at hcl2
      rw [hcl' j] at hcl2
      exact hcl2
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.okNoDisc q hq j hfl hcl3 x h1
    · rw [List.mem_singleton] at h1
      subst h1
      by_cases hj : j = id
      · subst hj
        exfalso
        have h3 := h.okOpen q hq j hfl hcl3 c hcon
        rw [hopen] at h3
        cases h3
      · intro e
        simp at e
        exact hj e.symm
  · intro x hx j hxj
    by_cases hj : j = id
    · subst hj
      exact Or.inr (Or.inl ⟨c2, hPc, hopen2⟩)
    · rcases List.mem_append.mp hx with h1 | h1
      · rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop⟩ | ⟨hpn, hcl2⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨pc, by change (P.slots j).conn = some pc; rw [hpo j, if_neg hj]; exact hpc, hop⟩)
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
      · rw [List.mem_singleton] at h1
        subst h1
        simp at hxj
        exact absurd hxj.symm hj
  · intro j hcl2
    change (P.slots j).closing = true at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      exfalso
      have hcc := h.closingNone j hcl2
      rw [hpc] at hcc
      cases hcc
    · change (P.slots j).conn = none
      rw [hpo j, if_neg hj]
      exact h.closingNone j hcl2
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q hq j hfl x h1 hxe
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxe
  · exact h.failOrd
  · intro x hx j hxj q hq'
    try simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | h1
    · exact h.connPend x h1 j hxj q hq'
    · subst h1
      simp at hxj
  · intro q hq' id hqi
    exact h.okRel q hq' id hqi
  · exact h.okOrd

-- the page's DISCARD: its four outcomes, as the page's step gives them
theorem doDiscard_none (st : Page.State) (i : Nat) (hc : (st.slots i).conn = none) :
    Page.doDiscard st i = (st, [Page.Obs.cb s!"discardErr {i} {Page.missing (st.slots i)}"]) := by
  unfold Page.doDiscard; rw [hc]

theorem doDiscard_closed (st : Page.State) (i : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (ho : c.isOpen = false) :
    Page.doDiscard st i = (st, [Page.Obs.cb s!"discardErr {i} {Page.missing (st.slots i)}"]) := by
  unfold Page.doDiscard; rw [hc]; simp [ho]

theorem doDiscard_pending (st : Page.State) (i : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (ho : c.isOpen = true) (hd : c.discardPending = true) :
    Page.doDiscard st i = (st, [Page.Obs.cb s!"discardErr {i} 16"]) := by
  unfold Page.doDiscard; rw [hc]; simp [ho, hd]

theorem doDiscard_set (st : Page.State) (i : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (ho : c.isOpen = true) (hd : c.discardPending = false) :
    Page.doDiscard st i = (Page.setSlot st i { st.slots i with conn := some { c with discardPending := true } },
      [Page.Obs.toRelay (Relay.Ev.discard i) 0]) := by
  unfold Page.doDiscard; rw [hc]; simp [ho, hd, Page.setSlot]

-- the page's DISCARD call, through the composed step
theorem inv_tPageDiscard (T T' : TSys) (h : Inv T) (i : Nat) (hT : tPageCall T (.discard i) = some T') :
    Inv T' := by
  unfold tPageCall lift at hT
  simp only [Client.pageCall, Page.step, Option.map_some, Option.some.injEq] at hT
  cases hc : (T.c.page.slots i).conn with
  | none =>
    rw [doDiscard_none T.c.page i hc] at hT
    simp only [List.filterMap_cons, List.filterMap_nil] at hT
    subst hT
    simpa using h
  | some c =>
    cases ho : c.isOpen with
    | false =>
      rw [doDiscard_closed T.c.page i c hc ho] at hT
      simp only [List.filterMap_cons, List.filterMap_nil] at hT
      subst hT
      simpa using h
    | true =>
      cases hd : c.discardPending with
      | true =>
        rw [doDiscard_pending T.c.page i c hc ho hd] at hT
        simp only [List.filterMap_cons, List.filterMap_nil] at hT
        subst hT
        simpa using h
      | false =>
        rw [doDiscard_set T.c.page i c hc ho hd] at hT
        subst hT
        exact inv_page_discard T h i c { c with discardPending := true } _ hc ho hd
          (by simp [Page.setSlot]) (by intro j; by_cases hj : j = i <;> simp [Page.setSlot, hj])
          (by intro j hj; simp [Page.setSlot, hj]) rfl rfl ho rfl rfl rfl rfl
          (h.pi i c (by unfold PageOf; exact hc))


-- the page's CLOSE call, through the composed step (the fixed page: the id closes until CLOSED)
theorem inv_tPageClose (T T' : TSys) (h : Inv T) (hfix : T.c.page.fixed = true) (i : Nat)
    (hT : tPageCall T (.close i) = some T') : Inv T' := by
  unfold tPageCall lift at hT
  simp only [Client.pageCall, Page.step, Option.map_some, Option.some.injEq] at hT
  cases hc : (T.c.page.slots i).conn with
  | none =>
    have hs : Page.doClose T.c.page i = (T.c.page, []) := by unfold Page.doClose; rw [hc]
    rw [hs] at hT
    simp only [List.filterMap_nil, List.append_nil] at hT
    subst hT
    simpa using h
  | some c =>
    obtain ⟨h1, h2, h3, h4, _, h6⟩ := doClose_spec T.c.page i c hc
    subst hT
    have hcl1 : ((Page.doClose T.c.page i).1.slots i).closing = true := by rw [h2, hfix]
    have key := inv_page_close T h i (Page.doClose T.c.page i).1 h1 hcl1 h3 h4 ⟨c, hc⟩
    rw [h6]
    exact key


theorem qsumT_reads (j id : Nat) (L : List (Relay.Ev × Nat)) (hL : ∀ x ∈ L, ∃ k, x = (Relay.Ev.read id k, 0)) :
    qsumT j L = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, hk⟩ := hL x (by simp)
    rw [hk]
    have ih' := ih (fun y hy => hL y (by simp [hy]))
    simp only [qsumT, ih']

theorem fwd_read_right (x : Relay.Ev) (b k : Nat) (h : FwdEv x (Relay.Ev.read b k)) :
    ∃ a, x = Relay.Ev.connect a ∧ a = b := by
  cases x <;> simp_all [FwdEv]

theorem pairwise_reads (id : Nat) (L : List (Relay.Ev × Nat)) (hL : ∀ x ∈ L, ∃ k, x = (Relay.Ev.read id k, 0)) :
    List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) L := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    refine List.Pairwise.cons ?_ (ih (fun y hy => hL y (by simp [hy])))
    intro b hb
    obtain ⟨k, hk⟩ := hL x (by simp)
    obtain ⟨k', hk'⟩ := hL b (by simp [hb])
    rw [hk, hk']
    simp [FwdEv]

-- the page's RECV effects, as one lemma: the connection's page state changes in fields the invariant does not
-- read (taken, readers), and the queue gains only READ frames (none, or the one that takes the data)
theorem inv_page_recv (T : TSys) (h : Inv T) (id : Nat) (c c2 : Page.PConn) (P : Page.State)
    (L : List (Relay.Ev × Nat))
    (hpc : PageOf T id = some c) (hPc : (P.slots id).conn = some c2)
    (hcl' : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing)
    (hother : ∀ j, j ≠ id → P.slots j = T.c.page.slots j) (hnext : P.nextSeq = T.c.page.nextSeq)
    (hseq : c2.seq = c.seq) (hopen : c2.isOpen = c.isOpen) (hdp : c2.discardPending = c.discardPending)
    (hsent : c2.sent = c.sent) (hwr : c2.written = c.written) (hrec : c2.received = c.received)
    (htail : c2.tail = c.tail) (hPI2 : Page.PInv c2)
    (hL : ∀ x ∈ L, ∃ k, x = (Relay.Ev.read id k, 0))
    (hnoC : L ≠ [] → ∀ q ∈ T.c.toRelay, q.1 ≠ Relay.Ev.connect id) :
    Inv ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ L }, T.clk⟩ := by
  have hpo : ∀ j, (P.slots j).conn = if j = id then some c2 else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · subst hj; simp [hPc]
    · simp [hj, hother j hj]
  have hcon : PageOf T id = some c := hpc
  have hlink : ∀ cc, ConnOf T id = some cc → (c.seq, cc.gen) ∈ T.c.genOf := by
    intro cc hcc
    rcases h.link id cc hcc with ⟨pc, hpc', hg⟩ | ⟨hpn, _⟩
    · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
      subst hpe; exact hg
    · rw [hcon] at hpn; cases hpn
  have hq : ∀ x, x ∈ (T.c.toRelay ++ L) ↔ x ∈ T.c.toRelay ∨ x ∈ L := by
    intro x; simp
  have hqs : ∀ j, qs j ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ L }, T.clk⟩ = qs j T := by
    intro j; simp only [qs, qsumT_app, qsumT_reads j id L hL]; simp [qsumT]
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_, failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_, closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_, closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_ }
  · intro j pc hpc'
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    split at hpc'
    · cases hpc'
      exact hPI2
    · exact h.pi j pc (by unfold PageOf; exact hpc')
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rcases h.link j cc hcc' with ⟨pc, hpc', hg⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
        subst hpe
        left
        refine ⟨c2, ?_, ?_⟩
        · change (P.slots j).conn = some c2; exact hPc
        · rw [hseq]; exact hg
      · left
        refine ⟨pc, ?_, hg⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc'
    · by_cases hj : j = id
      · subst hj; rw [hcon] at hpn; cases hpn
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc cc hpc' hcc hg
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpc'
      rw [hpo j] at hpc'
      simp at hpc'
      subst hpc'
      rw [hseq] at hg
      have hm := h.acc j c cc hcon hcc' (hlink cc hcc')
      rw [hqs j, hsent, hwr]
      exact hm
    · have hpc2 : PageOf T j = some pc := by
        change (P.slots j).conn = some pc at hpc'
        rw [hpo j, if_neg hj] at hpc'; exact hpc'
      rw [hqs j]
      exact h.acc j pc cc hpc2 hcc' hg
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rw [hqs j]
    exact h.wq j cc hcc'
  · intro q hq j hoj cc hcc
    exact h.gen q hq j hoj cc hcc
  · intro q hq j hnc hoj pc hpc'
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj
      simp at hpc'
      subst hpc'
      rw [hseq]
      exact h.apply q hq j hnc hoj c hcon
    · rw [if_neg hj] at hpc'
      exact h.apply q hq j hnc hoj pc (by unfold PageOf; exact hpc')
  · intro q hq j hnc hoj hpn
    change (P.slots j).conn = none at hpn
    rw [hpo j] at hpn
    show (P.slots j).closing = true
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj; simp at hpn
    · rw [if_neg hj] at hpn
      exact h.noOrphan q hq j hnc hoj (by unfold PageOf; exact hpn)
  · intro q hq j cnt f hq1 cc hcc hg
    exact h.written q hq j cnt f hq1 cc hcc hg
  · intro q hq j cnt hq1 pc hpc' hdp' hg cc hcc hgg
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj
      simp at hpc'
      subst hpc'
      rw [hqs j]
      have hdc : c.discardPending = true := by rw [← hdp]; exact hdp'
      have hgc : (c.seq, q.2) ∈ T.c.genOf := by rw [← hseq]; exact hg
      exact h.reset q hq j cnt hq1 c hcon hdc hgc cc hcc hgg
    · rw [if_neg hj] at hpc'
      rw [hqs j]
      exact h.reset q hq j cnt hq1 pc (by unfold PageOf; exact hpc') hdp' hg cc hcc hgg
  · show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) (T.c.toRelay ++ L)
    rw [List.pairwise_append]
    refine ⟨h.barrier, pairwise_reads id L hL, ?_⟩
    intro a ha b hb
    obtain ⟨k, hk⟩ := hL b hb
    rw [hk]
    show ¬ FwdEv a.1 (Relay.Ev.read id k)
    intro hF
    obtain ⟨a', ha', hae⟩ := fwd_read_right a.1 id k hF
    exact hnoC (fun e => by rw [e] at hb; simp at hb) a ha (by rw [ha', hae])
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.connClean q h1 j hqc
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro j pc hpc' hop
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj; simp at hpc'; subst hpc'
      obtain ⟨h1', h2'⟩ := h.notOpen j c hcon (by rw [← hopen]; exact hop)
      exact ⟨by rw [hsent]; exact h1', by rw [hwr]; exact h2'⟩
    · rw [if_neg hj] at hpc'; exact h.notOpen j pc hpc' hop
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · rcases h.cl q h1 j hqc with ⟨pc, hpc', hs⟩ | ⟨hpn, hcl2⟩
      · by_cases hj : j = id
        · subst hj
          left
          refine ⟨c2, ?_, ?_⟩
          · change (P.slots j).conn = some c2; exact hPc
          · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
            subst hpe
            rw [hseq]; exact hs
        · left
          refine ⟨pc, ?_, hs⟩
          change (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]; exact hpc'
      · by_cases hj : j = id
        · subst hj; rw [hcon] at hpn; cases hpn
        · right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro q hq j cnt hq1 x hx n
    rcases hq' : (List.mem_append.mp hx) with h1 | h1
    · exact h.rq q hq j cnt hq1 x h1 n
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk]; simp
  · intro j cc hcc
    exact h.gensLt j cc hcc
  · intro q hq j hqc g
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.gp q h1 j hqc g
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro j pc hpc' hop
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj
      simp at hpc'; subst hpc'
      rw [hopen] at hop
      obtain ⟨g, hg⟩ := h.openG j c hcon hop
      exact ⟨g, by rw [hseq]; exact hg⟩
    · rw [if_neg hj] at hpc'; exact h.openG j pc hpc' hop
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < P.nextSeq
    rw [hnext]
    exact h.seqG p g hm
  · intro q hq j hqc
    show q.2 < P.nextSeq
    rw [hnext]
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.seqQ q h1 j hqc
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro q hq j hd pc hp hop'
    rcases List.mem_append.mp hq with h1 | h1
    · by_cases hj : j = id
      · subst hj
        change (P.slots j).conn = some pc at hp
        rw [hpo j] at hp
        simp at hp
        subst hp
        have hdc := h.disc q h1 j hd c hcon (by rw [← hopen]; exact hop')
        rw [hdp]; exact hdc
      · change (P.slots j).conn = some pc at hp
        rw [hpo j, if_neg hj] at hp
        exact h.disc q h1 j hd pc (by unfold PageOf; exact hp) hop'
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hd; simp at hd
  · intro q hq j cnt hq1
    rcases h.rep q hq j cnt hq1 with ⟨pc, hpc', hpd⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
        subst hpe
        left
        refine ⟨c2, ?_, ?_⟩
        · change (P.slots j).conn = some c2; exact hPc
        · rw [hdp]; exact hpd
      · left
        refine ⟨pc, ?_, hpd⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc'
    · by_cases hj : j = id
      · subst hj; rw [hcon] at hpn; cases hpn
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc hp hr
    change (P.slots j).conn = some pc at hp
    rw [hpo j] at hp
    by_cases hj : j = id
    · subst hj
      simp at hp
      subst hp
      have hr' : 0 < c.received := by rw [← hrec]; exact hr
      obtain ⟨g, hg⟩ := h.recvG j c hcon hr'
      exact ⟨g, by rw [hseq]; exact hg⟩
    · rw [if_neg hj] at hp
      exact h.recvG j pc (by unfold PageOf; exact hp) hr

  · intro q hq j e hfl
    exact h.failNone q hq j e hfl
  · intro q hq j hfl
    exact h.closedNone q hq j hfl
  · intro q hq j hfl
    show (P.slots j).closing = true
    rw [hcl' j]
    exact h.closedClosing q hq j hfl
  · exact h.closedOrd
  · intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · show (P.slots j).closing = true
      rw [hcl' j]
      exact h.closeClosing x h1 j hxj
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxj
      simp at hxj
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q hq j hfl x h1 hxe
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxe
      simp at hxe
  · intro j pc hpcI hop cc hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      have hop' : c.isOpen = true := by
        rw [← hopen]
        exact hop
      exact h.openRel j c hcon hop' cc hcc
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.openRel j pc (by unfold PageOf; exact hpcI) hop cc hcc
  · intro q hq j hfl hcl2 pc hpcI
    change (P.slots j).closing = false at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      rw [hopen]
      exact h.okOpen q hq j hfl hcl2 c hcon
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.okOpen q hq j hfl hcl2 pc (by unfold PageOf; exact hpcI)
  · intro q hq j hfl hcl2 x hx
    have hcl3 : (T.c.page.slots j).closing = false := by
      change (P.slots j).closing = false at hcl2
      rw [hcl' j] at hcl2
      exact hcl2
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.okNoDisc q hq j hfl hcl3 x h1
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk]
      simp
  · intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · by_cases hj : j = id
      · subst hj
        rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop⟩ | ⟨hpn, hcl2⟩
        · exact Or.inl h0
        · have hpe : pc = c := by
            rw [hcon] at hpc
            exact (Option.some.inj hpc).symm
          subst hpe
          exact Or.inr (Or.inl ⟨c2, hPc, by rw [hopen]; exact hop⟩)
        · rw [hcon] at hpn
          cases hpn
      · rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop⟩ | ⟨hpn, hcl2⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨pc, by change (P.slots j).conn = some pc; rw [hpo j, if_neg hj]; exact hpc, hop⟩)
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxj
      simp at hxj
  · intro j hcl2
    change (P.slots j).closing = true at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      exfalso
      have hcc := h.closingNone j hcl2
      have hc0 : (T.c.page.slots j).conn = some c := hpc
      rw [hc0] at hcc
      cases hcc
    · change (P.slots j).conn = none
      rw [hpo j, if_neg hj]
      exact h.closingNone j hcl2
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q hq j hfl x h1 hxe
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxe
      simp at hxe
  · exact h.failOrd
  · intro x hx j hxj q hq'
    try simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | h1
    · exact h.connPend x h1 j hxj q hq'
    · subst h1
      simp at hxj
  · intro q hq' id hqi
    exact h.okRel q hq' id hqi
  · exact h.okOrd

theorem doRecv_take_spec (st : Page.State) (i max : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (hgt : c.received > c.taken) :
    (Page.doRecv st i max).1 = Page.setSlot st i
      { st.slots i with conn := some { c with taken := c.taken + min max (c.received - c.taken) } } ∧
    ((Page.doRecv st i max).2.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) =
      [(Relay.Ev.read i (min max (c.received - c.taken)), 0)] := by
  unfold Page.doRecv
  rw [hc]
  simp [Page.takeFor, hgt, Page.setSlot]

theorem doRecv_wait_spec (st : Page.State) (i max : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (hgt : ¬ c.received > c.taken) (he : c.eof = false) :
    (Page.doRecv st i max).1 = Page.setSlot st i
      { st.slots i with conn := some { c with readers := c.readers ++ [max] } } ∧
    ((Page.doRecv st i max).2.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) = [] := by
  unfold Page.doRecv
  rw [hc]
  simp [hgt, he, Page.setSlot]

theorem doRecv_none_spec (st : Page.State) (i max : Nat) (hc : (st.slots i).conn = none) :
    (Page.doRecv st i max).1 = st := by
  unfold Page.doRecv
  rw [hc]

theorem doRecv_eof_spec (st : Page.State) (i max : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (hgt : ¬ c.received > c.taken) (he : c.eof = true) :
    Page.doRecv st i max = (st, [Page.Obs.cb s!"eof {i}"]) := by
  unfold Page.doRecv
  rw [hc]
  simp [hgt, he]

theorem doRecv_none_eq (st : Page.State) (i max : Nat) (hc : (st.slots i).conn = none) :
    Page.doRecv st i max = (st, [Page.Obs.cb s!"recvErr {i} {Page.missing (st.slots i)}"]) := by
  unfold Page.doRecv; rw [hc]

-- the page's RECV call, through the composed step
theorem inv_tPageRecv (T T' : TSys) (h : Inv T) (i max : Nat) (hT : tPageCall T (.recv i max) = some T') :
    Inv T' := by
  unfold tPageCall lift at hT
  simp only [Client.pageCall, Page.step, Option.map_some, Option.some.injEq] at hT
  rcases hd : Page.doRecv T.c.page i max with ⟨st', obs⟩
  rw [hd] at hT
  dsimp only at hT
  subst hT
  cases hc : (T.c.page.slots i).conn with
  | none =>
    rw [doRecv_none_eq T.c.page i max hc] at hd
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simpa using h
  | some c =>
    by_cases hgt : c.received > c.taken
    · obtain ⟨h1, h2⟩ := doRecv_take_spec T.c.page i max c hc hgt
      rw [hd] at h1 h2
      dsimp only at h1 h2
      subst h1
      rw [h2]
      exact inv_page_recv T h i c { c with taken := c.taken + min max (c.received - c.taken) } _
        [(Relay.Ev.read i (min max (c.received - c.taken)), 0)] (by unfold PageOf; exact hc)
        (by simp [Page.setSlot]) (by intro j; by_cases hj : j = i <;> simp [Page.setSlot, hj])
        (by intro j hj; simp [Page.setSlot, hj]) rfl rfl rfl rfl rfl rfl rfl rfl
        (h.pi i c (by unfold PageOf; exact hc))
        (fun x hx => by simp at hx; exact ⟨_, hx⟩)
        (fun _ q hq hqc => by
          rcases h.cl q hq i hqc with ⟨pc, hpc', hs⟩ | ⟨hpn, _⟩
          · have hpe : pc = c := by
              have h1 : PageOf T i = some c := by unfold PageOf; exact hc
              rw [h1] at hpc'; exact (Option.some.inj hpc').symm
            subst hpe
            obtain ⟨g, hg⟩ := h.recvG i pc (by unfold PageOf; exact hc) (by omega)
            exact h.gp q hq i hqc g (by rw [← hs]; exact hg)
          · rw [show PageOf T i = (T.c.page.slots i).conn from rfl, hc] at hpn; cases hpn)
    · by_cases he : c.eof = true
      · rw [doRecv_eof_spec T.c.page i max c hc hgt he] at hd
        simp only [Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        simpa using h
      · obtain ⟨h1, h2⟩ := doRecv_wait_spec T.c.page i max c hc hgt (by simpa using he)
        rw [hd] at h1 h2
        dsimp only at h1 h2
        subst h1
        rw [h2]
        exact inv_page_recv T h i c { c with readers := c.readers ++ [max] } _ []
          (by unfold PageOf; exact hc)
          (by simp [Page.setSlot]) (by intro j; by_cases hj : j = i <;> simp [Page.setSlot, hj])
          (by intro j hj; simp [Page.setSlot, hj]) rfl rfl rfl rfl rfl rfl rfl rfl
          (h.pi i c (by unfold PageOf; exact hc))
          (fun x hx => by simp at hx)
          (fun hne => absurd rfl hne)


-- the pump keeps the connection's identity (seq, open, discarding, received), and frames only SENDs of this id
theorem pump_shape (id : Nat) : ∀ (fuel : Nat) (c : Page.PConn),
    (Page.pump id c fuel).1.seq = c.seq ∧ (Page.pump id c fuel).1.isOpen = c.isOpen ∧
    (Page.pump id c fuel).1.discardPending = c.discardPending ∧ (Page.pump id c fuel).1.received = c.received ∧
    (∀ x ∈ (Page.pump id c fuel).2, ∃ k, x = Page.Obs.toRelay (Relay.Ev.send id k) 0) := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [Page.pump]
  | succ f ih =>
    intro c
    simp only [Page.pump]
    by_cases hstop : (c.op.isNone || c.discardPending || !c.isOpen) = true
    · rw [if_pos hstop]; simp
    · rw [if_neg hstop]
      obtain ⟨n, hn⟩ : ∃ n, n = min Page.MAX_BODY (min (Page.SEND_W - (c.sent - c.written)) (c.tail - c.sent)) :=
        ⟨_, rfl⟩
      rw [← hn]
      by_cases hn0 : n = 0
      · rw [if_pos hn0]; simp
      · rw [if_neg hn0]
        obtain ⟨R1, R2, R3, R4, R5⟩ := ih { c with sent := c.sent + n }
        rcases hpc : Page.pump id { c with sent := c.sent + n } f with ⟨c', obs⟩
        rw [hpc] at R1 R2 R3 R4 R5
        dsimp only at R1 R2 R3 R4 R5 ⊢
        refine ⟨R1, R2, R3, R4, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨n, rfl⟩
        · exact R5 x hx

theorem qsumT_sends_other (j id : Nat) (hj : j ≠ id) : ∀ (L : List (Relay.Ev × Nat)),
    (∀ x ∈ L, ∃ k, x = (Relay.Ev.send id k, 0)) → qsumT j L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hL
    obtain ⟨k, hk⟩ := hL x (by simp)
    rw [hk]
    have ih' := ih (fun y hy => hL y (by simp [hy]))
    simp [qsumT, Ne.symm hj, ih']

-- the frames a pumped SEND queues: the SENDs of this id (with their sum), in the page's order
theorem qsumT_of_sends (id : Nat) : ∀ (obs : List Page.Obs),
    (∀ x ∈ obs, ∃ k, x = Page.Obs.toRelay (Relay.Ev.send id k) 0) →
    qsumT id (obs.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) =
      (obs.map Page.sendBytes).sum := by
  intro obs
  induction obs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro hx
    obtain ⟨k, hk⟩ := hx x (by simp)
    rw [hk]
    have ih' := ih (fun y hy => hx y (by simp [hy]))
    simp only [List.filterMap_cons, List.map_cons, List.sum_cons, Page.sendBytes, qsumT]
    simp [ih']

theorem filter_sends_form (id : Nat) (obs : List Page.Obs)
    (hobs : ∀ x ∈ obs, ∃ k, x = Page.Obs.toRelay (Relay.Ev.send id k) 0) :
    ∀ x ∈ obs.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none),
      ∃ k, x = (Relay.Ev.send id k, 0) := by
  intro x hx
  obtain ⟨a, ha, hfa⟩ := List.mem_filterMap.mp hx
  obtain ⟨k, hk⟩ := hobs a ha
  rw [hk] at hfa
  simp at hfa
  exact ⟨k, hfa.symm⟩

theorem fwd_send_right (x : Relay.Ev) (b k : Nat) (h : FwdEv x (Relay.Ev.send b k)) :
    (∃ a, x = Relay.Ev.connect a ∧ a = b) ∨ (∃ a, x = Relay.Ev.discard a ∧ a = b) := by
  cases x <;> simp_all [FwdEv]

theorem pairwise_sends (id : Nat) : ∀ (L : List (Relay.Ev × Nat)),
    (∀ x ∈ L, ∃ k, x = (Relay.Ev.send id k, 0)) → List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) L := by
  intro L
  induction L with
  | nil => intro _; exact List.Pairwise.nil
  | cons x xs ih =>
    intro hL
    refine List.Pairwise.cons ?_ (ih (fun y hy => hL y (by simp [hy])))
    intro b hb
    obtain ⟨k, hk⟩ := hL x (by simp)
    obtain ⟨k', hk'⟩ := hL b (by simp [hb])
    rw [hk, hk']
    simp [FwdEv]

-- the page's SEND of n (pumped, with the connection open and not discarding): the connection's counts move by
-- the bytes framed, which are the SEND frames queued; the window of the relay is kept (wq)
theorem inv_page_send (T : TSys) (h : Inv T) (id : Nat) (c c3 : Page.PConn) (P : Page.State)
    (L : List (Relay.Ev × Nat))
    (hpc : PageOf T id = some c) (hopen : c.isOpen = true) (hdp : c.discardPending = false)
    (hPc : (P.slots id).conn = some c3)
    (hcl' : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing)
    (hother : ∀ j, j ≠ id → P.slots j = T.c.page.slots j) (hnext : P.nextSeq = T.c.page.nextSeq)
    (hseq : c3.seq = c.seq) (hopen3 : c3.isOpen = true) (hdp3 : c3.discardPending = false)
    (hrec : c3.received = c.received) (hwr : c3.written = c.written)
    (hsum : c3.sent = c.sent + qsumT id L) (hPI3 : Page.PInv c3)
    (hL : ∀ x ∈ L, ∃ k, x = (Relay.Ev.send id k, 0)) :
    Inv ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ L }, T.clk⟩ := by
  have hpo : ∀ j, (P.slots j).conn = if j = id then some c3 else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · subst hj; simp [hPc]
    · simp [hj, hother j hj]
  have hcon : PageOf T id = some c := hpc
  have hlink : ∀ cc, ConnOf T id = some cc → (c.seq, cc.gen) ∈ T.c.genOf := by
    intro cc hcc
    rcases h.link id cc hcc with ⟨pc, hpc', hg⟩ | ⟨hpn, _⟩
    · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
      subst hpe; exact hg
    · rw [hcon] at hpn; cases hpn
  have hq : ∀ x, x ∈ (T.c.toRelay ++ L) ↔ x ∈ T.c.toRelay ∨ x ∈ L := by
    intro x; simp
  have hqs : ∀ j, qs j ⟨{ T.c with page := P, toRelay := T.c.toRelay ++ L }, T.clk⟩ = qs j T + qsumT j L := by
    intro j; simp only [qs, qsumT_app]
  -- a connect of this id queued behind an open connection is impossible (its generation is not yet given)
  have hnoConn : ∀ q ∈ T.c.toRelay, q.1 ≠ Relay.Ev.connect id := by
    intro q hq hqc
    rcases h.cl q hq id hqc with ⟨pc, hpc', hs⟩ | ⟨hpn, _⟩
    · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
      subst hpe
      obtain ⟨g, hg⟩ := h.openG id pc hcon hopen
      exact h.gp q hq id hqc g (by rw [← hs]; exact hg)
    · rw [hcon] at hpn; cases hpn
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_, failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_, closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_, closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_ }
  · intro j pc hpc'
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    split at hpc'
    · cases hpc'
      exact hPI3
    · exact h.pi j pc (by unfold PageOf; exact hpc')
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rcases h.link j cc hcc' with ⟨pc, hpc', hg⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
        subst hpe
        left
        refine ⟨c3, ?_, ?_⟩
        · change (P.slots j).conn = some c3; exact hPc
        · rw [hseq]; exact hg
      · left
        refine ⟨pc, ?_, hg⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc'
    · by_cases hj : j = id
      · subst hj; rw [hcon] at hpn; cases hpn
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc cc hpc' hcc hg
    have hcc' : ConnOf T j = some cc := hcc
    rw [hqs j]
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpc'
      rw [hpo j] at hpc'
      simp at hpc'
      subst hpc'
      rw [hseq] at hg
      obtain ⟨hm1, hm2⟩ := h.acc j c cc hcon hcc' (hlink cc hcc')
      rw [hsum, hwr]
      exact ⟨by omega, hm2⟩
    · have hpc2 : PageOf T j = some pc := by
        change (P.slots j).conn = some pc at hpc'
        rw [hpo j, if_neg hj] at hpc'; exact hpc'
      rw [qsumT_sends_other j id hj L hL, Nat.add_zero]
      exact h.acc j pc cc hpc2 hcc' hg
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    rw [hqs j]
    by_cases hj : j = id
    · subst hj
      obtain ⟨hm1, hm2⟩ := h.acc j c cc hcon hcc' (hlink cc hcc')
      obtain ⟨_, _, hW⟩ := hPI3
      unfold Page.SEND_W at hW
      omega
    · rw [qsumT_sends_other j id hj L hL, Nat.add_zero]
      exact h.wq j cc hcc'
  · intro q hq j hoj cc hcc
    exact h.gen q hq j hoj cc hcc
  · intro q hq j hnc hoj pc hpc'
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj
      simp at hpc'
      subst hpc'
      rw [hseq]
      exact h.apply q hq j hnc hoj c hcon
    · rw [if_neg hj] at hpc'
      exact h.apply q hq j hnc hoj pc (by unfold PageOf; exact hpc')
  · intro q hq j hnc hoj hpn
    change (P.slots j).conn = none at hpn
    rw [hpo j] at hpn
    show (P.slots j).closing = true
    rw [hcl' j]
    by_cases hj : j = id
    · subst hj; simp at hpn
    · rw [if_neg hj] at hpn
      exact h.noOrphan q hq j hnc hoj (by unfold PageOf; exact hpn)
  · intro q hq j cnt f hq1 cc hcc hg
    exact h.written q hq j cnt f hq1 cc hcc hg
  · intro q hq j cnt hq1 pc hpc' hdp' hg cc hcc hgg
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj
      simp at hpc'
      subst hpc'
      rw [hdp3] at hdp'; cases hdp'
    · rw [if_neg hj] at hpc'
      rw [hqs j, qsumT_sends_other j id hj L hL, Nat.add_zero]
      exact h.reset q hq j cnt hq1 pc (by unfold PageOf; exact hpc') hdp' hg cc hcc hgg
  · show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) (T.c.toRelay ++ L)
    rw [List.pairwise_append]
    refine ⟨h.barrier, pairwise_sends id L hL, ?_⟩
    intro a ha b hb
    obtain ⟨k, hk⟩ := hL b hb
    rw [hk]
    show ¬ FwdEv a.1 (Relay.Ev.send id k)
    intro hF
    rcases fwd_send_right a.1 id k hF with ⟨a', ha', hae⟩ | ⟨a', ha', hae⟩
    · exact hnoConn a ha (by rw [ha', hae])
    · have h1 : PageOf T a' = some c := by rw [hae]; exact hcon
      have hd := h.disc a ha a' ha' c h1 hopen
      rw [hdp] at hd; cases hd
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.connClean q h1 j hqc
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro j pc hpc' hop
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj; simp at hpc'; subst hpc'
      rw [hopen3] at hop; cases hop
    · rw [if_neg hj] at hpc'; exact h.notOpen j pc hpc' hop
  · intro q hq j hqc
    rcases List.mem_append.mp hq with h1 | h1
    · rcases h.cl q h1 j hqc with ⟨pc, hpc', hs⟩ | ⟨hpn, hcl2⟩
      · by_cases hj : j = id
        · subst hj
          left
          refine ⟨c3, ?_, ?_⟩
          · change (P.slots j).conn = some c3; exact hPc
          · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
            subst hpe
            rw [hseq]; exact hs
        · left
          refine ⟨pc, ?_, hs⟩
          change (P.slots j).conn = some pc
          rw [hpo j, if_neg hj]; exact hpc'
      · by_cases hj : j = id
        · subst hj; rw [hcon] at hpn; cases hpn
        · right
          refine ⟨?_, ?_⟩
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro q hq j cnt hq1 x hx n
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.rq q hq j cnt hq1 x h1 n
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk]
      by_cases hj : j = id
      · subst hj
        exfalso
        rcases h.rep q hq j cnt hq1 with ⟨pc, hpc', hpd⟩ | ⟨hpn, _⟩
        · have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
          subst hpe
          rw [hdp] at hpd; cases hpd
        · rw [hcon] at hpn; cases hpn
      · intro e
        simp at e
        exact hj e.1.symm
  · intro j cc hcc
    exact h.gensLt j cc hcc
  · intro q hq j hqc g
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.gp q h1 j hqc g
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro j pc hpc' hop
    change (P.slots j).conn = some pc at hpc'
    rw [hpo j] at hpc'
    by_cases hj : j = id
    · subst hj
      simp at hpc'; subst hpc'
      obtain ⟨g, hg⟩ := h.openG j c hcon hopen
      exact ⟨g, by rw [hseq]; exact hg⟩
    · rw [if_neg hj] at hpc'; exact h.openG j pc hpc' hop
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < P.nextSeq
    rw [hnext]
    exact h.seqG p g hm
  · intro q hq j hqc
    show q.2 < P.nextSeq
    rw [hnext]
    rcases List.mem_append.mp hq with h1 | h1
    · exact h.seqQ q h1 j hqc
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hqc; simp at hqc
  · intro q hq j hd pc hp hop'
    rcases List.mem_append.mp hq with h1 | h1
    · by_cases hj : j = id
      · subst hj
        exfalso
        have hdc := h.disc q h1 j hd c hcon hopen
        rw [hdp] at hdc; cases hdc
      · change (P.slots j).conn = some pc at hp
        rw [hpo j, if_neg hj] at hp
        exact h.disc q h1 j hd pc (by unfold PageOf; exact hp) hop'
    · obtain ⟨k, hk⟩ := hL q h1
      rw [hk] at hd; simp at hd
  · intro q hq j cnt hq1
    rcases h.rep q hq j cnt hq1 with ⟨pc, hpc', hpd⟩ | ⟨hpn, hcl2⟩
    · by_cases hj : j = id
      · subst hj
        have hpe : pc = c := by rw [hcon] at hpc'; exact (Option.some.inj hpc').symm
        subst hpe
        rw [hdp] at hpd; cases hpd
      · left
        refine ⟨pc, ?_, hpd⟩
        change (P.slots j).conn = some pc
        rw [hpo j, if_neg hj]; exact hpc'
    · by_cases hj : j = id
      · subst hj; rw [hcon] at hpn; cases hpn
      · right
        refine ⟨?_, ?_⟩
        · change (P.slots j).conn = none
          rw [hpo j, if_neg hj]; exact hpn
        · change (P.slots j).closing = true
          rw [hcl' j]; exact hcl2
  · intro j pc hp hr
    change (P.slots j).conn = some pc at hp
    rw [hpo j] at hp
    by_cases hj : j = id
    · subst hj
      simp at hp
      subst hp
      have hr' : 0 < c.received := by rw [← hrec]; exact hr
      obtain ⟨g, hg⟩ := h.recvG j c hcon hr'
      exact ⟨g, by rw [hseq]; exact hg⟩
    · rw [if_neg hj] at hp
      exact h.recvG j pc (by unfold PageOf; exact hp) hr

  · intro q hq j e hfl
    exact h.failNone q hq j e hfl
  · intro q hq j hfl
    exact h.closedNone q hq j hfl
  · intro q hq j hfl
    show (P.slots j).closing = true
    rw [hcl' j]
    exact h.closedClosing q hq j hfl
  · exact h.closedOrd
  · intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · show (P.slots j).closing = true
      rw [hcl' j]
      exact h.closeClosing x h1 j hxj
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxj
      simp at hxj
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q hq j hfl x h1 hxe
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxe
      simp at hxe
  · intro j pc hpcI hop cc hcc
    by_cases hj : j = id
    · subst hj
      change (P.slots j).conn = some pc at hpcI
      rw [hpo j] at hpcI
      simp at hpcI
      subst hpcI
      exact h.openRel j c hcon hopen cc hcc
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.openRel j pc (by unfold PageOf; exact hpcI) hop cc hcc
  · intro q hq j hfl hcl2 pc hpcI
    change (P.slots j).closing = false at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      exfalso
      have h3 := h.okOpen q hq j hfl hcl2 c hcon
      rw [hopen] at h3
      cases h3
    · change (P.slots j).conn = some pc at hpcI
      rw [hpo j, if_neg hj] at hpcI
      exact h.okOpen q hq j hfl hcl2 pc (by unfold PageOf; exact hpcI)
  · intro q hq j hfl hcl2 x hx
    have hcl3 : (T.c.page.slots j).closing = false := by
      change (P.slots j).closing = false at hcl2
      rw [hcl' j] at hcl2
      exact hcl2
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.okNoDisc q hq j hfl hcl3 x h1
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk]
      simp
  · intro x hx j hxj
    by_cases hj : j = id
    · subst hj
      exact Or.inr (Or.inl ⟨c3, hPc, hopen3⟩)
    · rcases List.mem_append.mp hx with h1 | h1
      · rcases h.discRel x h1 j hxj with h0 | ⟨pc, hpc, hop⟩ | ⟨hpn, hcl2⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨pc, by change (P.slots j).conn = some pc; rw [hpo j, if_neg hj]; exact hpc, hop⟩)
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · change (P.slots j).conn = none
            rw [hpo j, if_neg hj]; exact hpn
          · change (P.slots j).closing = true
            rw [hcl' j]; exact hcl2
      · obtain ⟨k, hk⟩ := hL x h1
        rw [hk] at hxj
        simp at hxj
  · intro j hcl2
    change (P.slots j).closing = true at hcl2
    rw [hcl' j] at hcl2
    by_cases hj : j = id
    · subst hj
      exfalso
      have hcc := h.closingNone j hcl2
      have hc0 : (T.c.page.slots j).conn = some c := hpc
      rw [hc0] at hcc
      cases hcc
    · change (P.slots j).conn = none
      rw [hpo j, if_neg hj]
      exact h.closingNone j hcl2
  · intro q hq j hfl x hx hxe
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q hq j hfl x h1 hxe
    · obtain ⟨k, hk⟩ := hL x h1
      rw [hk] at hxe
      simp at hxe
  · exact h.failOrd
  · intro x hx j hxj q hq'
    try simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with h1 | h1
    · exact h.connPend x h1 j hxj q hq'
    · subst h1
      simp at hxj
  · intro q hq' id hqi
    exact h.okRel q hq' id hqi
  · exact h.okOrd

-- the pumped SEND of n > 0 on an open connection with no SEND in progress and not discarding
theorem doSend_pump (st : Page.State) (i n : Nat) (c : Page.PConn) (hc : (st.slots i).conn = some c)
    (ho : c.isOpen = true) (hp : c.op = none) (hd : c.discardPending = false) (hn : n ≠ 0) :
    Page.doSend st i n = (Page.setSlot st i { st.slots i with conn := some (Page.pump i { c with tail := c.tail + n, op := some (c.tail, n) } (c.tail + n - c.sent + 1)).1 }, (Page.pump i { c with tail := c.tail + n, op := some (c.tail, n) } (c.tail + n - c.sent + 1)).2) := by
  unfold Page.doSend
  rw [hc]
  simp [ho, hp, hd, hn]

-- the page's SEND call, through the composed step
theorem inv_tPageSend (T T' : TSys) (h : Inv T) (i n : Nat) (hT : tPageCall T (.send i n) = some T') :
    Inv T' := by
  unfold tPageCall lift at hT
  simp only [Client.pageCall, Page.step, Option.map_some, Option.some.injEq] at hT
  rcases hd : Page.doSend T.c.page i n with ⟨st', obs⟩
  rw [hd] at hT
  dsimp only at hT
  subst hT
  cases hc : (T.c.page.slots i).conn with
  | none =>
    obtain ⟨s, hs⟩ : ∃ s, Page.doSend T.c.page i n = (T.c.page, [Page.Obs.cb s]) :=
      ⟨_, by unfold Page.doSend; rw [hc]⟩
    rw [hs] at hd
    simp only [Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simpa using h
  | some c =>
    cases ho : c.isOpen with
    | false =>
      have hs : Page.doSend T.c.page i n = (T.c.page, [Page.Obs.cb s!"sendErr {i} 22 {c.written}"]) := by
        unfold Page.doSend; rw [hc]; simp [ho]
      rw [hs] at hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      simpa using h
    | true =>
      by_cases hop : c.op = none
      · by_cases hdp : c.discardPending = true
        · have hs : Page.doSend T.c.page i n = (T.c.page, [Page.Obs.thrown]) := by
            unfold Page.doSend; rw [hc]; simp [ho, hop, hdp]
          rw [hs] at hd
          simp only [Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          simpa using h
        · have hdp' : c.discardPending = false := by simpa using hdp
          by_cases hn : n = 0
          · have hs : Page.doSend T.c.page i n = (Page.setSlot T.c.page i
                { T.c.page.slots i with conn := some { c with tail := c.tail + n } },
                [Page.Obs.cb s!"sent {i}"]) := by
              unfold Page.doSend; rw [hc]; simp [ho, hop, hdp', hn, Page.setSlot]
            rw [hs] at hd
            simp only [Prod.mk.injEq] at hd
            obtain ⟨hst, hobs⟩ := hd
            subst hst
            subst hobs
            simp only [List.filterMap_cons, List.filterMap_nil]
            exact inv_page_recv T h i c { c with tail := c.tail + n } _ []
              (by unfold PageOf; exact hc)
              (by simp [Page.setSlot]) (by intro j; by_cases hj : j = i <;> simp [Page.setSlot, hj])
              (by intro j hj; simp [Page.setSlot, hj]) rfl rfl rfl rfl rfl rfl rfl (by simp [hn])
              (by
                have hp := h.pi i c (by unfold PageOf; exact hc)
                unfold Page.PInv at hp ⊢
                simp only [hn, Nat.add_zero]
                exact hp)
              (fun x hx => by simp at hx)
              (fun hne => absurd rfl hne)
          · have hPI : Page.PInv c := h.pi i c (by unfold PageOf; exact hc)
            have hPI2 : Page.PInv { c with tail := c.tail + n, op := some (c.tail, n) } := by
              unfold Page.PInv at hPI ⊢
              obtain ⟨a, b, d⟩ := hPI
              exact ⟨a, by dsimp only; omega, d⟩
            have hs := doSend_pump T.c.page i n c hc ho hop hdp' hn
            rw [hs] at hd
            simp only [Prod.mk.injEq] at hd
            obtain ⟨hst, hobs⟩ := hd
            subst hst
            subst hobs
            have F1 := Page.pump_props i (c.tail + n - c.sent + 1)
              { c with tail := c.tail + n, op := some (c.tail, n) } hPI2
            have F2 := pump_shape i (c.tail + n - c.sent + 1)
              { c with tail := c.tail + n, op := some (c.tail, n) }
            generalize Page.pump i { c with tail := c.tail + n, op := some (c.tail, n) }
              (c.tail + n - c.sent + 1) = pr at F1 F2 ⊢
            obtain ⟨c3, ob⟩ := pr
            dsimp only at F1 F2 ⊢
            obtain ⟨W1, _, S2, hPI3, S3, _⟩ := F1
            obtain ⟨Q1, Q2, Q3, Q4, Q5⟩ := F2
            have hsumL : qsumT i (ob.filterMap (fun o => match o with | .toRelay e p => some (e, p) | _ => none))
                = (ob.map Page.sendBytes).sum := qsumT_of_sends i ob Q5
            exact inv_page_send T h i c c3 _ _ (by unfold PageOf; exact hc) ho hdp'
              (by simp [Page.setSlot])
              (by intro j; by_cases hj : j = i <;> simp [Page.setSlot, hj])
              (by intro j hj; simp [Page.setSlot, hj]) rfl
              Q1 (by rw [Q2]; exact ho) (by rw [Q3]; exact hdp') Q4 W1
              (by rw [hsumL]; omega) hPI3
              (filter_sends_form i ob Q5)

      · have hs : Page.doSend T.c.page i n = (T.c.page, [Page.Obs.thrown]) := by
          unfold Page.doSend; rw [hc]; simp [ho, hop]
        rw [hs] at hd
        simp only [Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        simpa using h

end Ind
