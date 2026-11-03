namespace Ind
open Timed

-- the queue sum of a READ is nothing: appending a READ leaves the sum of every id as it was
theorem qs_read (j id k : Nat) (rs : Relay.St) (page : Page.State) (L : List (Relay.Ev × Nat))
    (d : List (Relay.Out × Nat)) (e : List (Nat × Nat)) (f : Bool) (g : Bool) (hh : List (Nat × Nat × Nat))
    (clk : Clock.Clk) :
    qs j ⟨⟨rs, page, L ++ [(Relay.Ev.read id k, 0)], d, e, f, g, hh⟩, clk⟩ =
      qs j ⟨⟨rs, page, L, d, e, f, g, hh⟩, clk⟩ := by
  simp [qs, qsumT_app, qsumT]

-- the page's frame OK of an id whose connection is closed and not closing: the connection opens, and the
-- page asks the relay for a read window (one READ, and the connected message)
theorem frame_ok_some (st : Page.State) (id : Nat) (c : Page.PConn) (hc : (st.slots id).conn = some c)
    (hcl : (st.slots id).closing = false) (hop : c.isOpen = false) :
    (Page.frame st (Relay.Out.ok id)).1 =
        Page.setSlot st id { st.slots id with conn := some { c with isOpen := true } } ∧
    ((Page.frame st (Relay.Out.ok id)).2.filterMap
        (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) =
      [(Relay.Ev.read id Page.READ_W, 0)] := by
  have hap : Page.applies st (Relay.Out.ok id) = some c.seq := by
    simp [Page.applies, hcl, hc]
  unfold Page.frame
  rw [hap]
  simp [hc, hop, Page.setSlot]

-- the core: the page's connection of the OK frame's id opens; the queue loses the frame and gains one READ
theorem inv_ok_core (T : TSys) (h : Inv T) (c' : Client.Sys) (id t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.ok id, t) :: rest) (c : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c) (hcl0 : (T.c.page.slots id).closing = false)
    (hop : c.isOpen = false) (P : Page.State)
    (hrs : c'.rs = T.c.rs) (hr : c'.toRelay = T.c.toRelay ++ [(Relay.Ev.read id Page.READ_W, 0)])
    (hg : c'.genOf = T.c.genOf) (hs : c'.toPage = rest)
    (hp : c'.page = P) (hconn : ∀ j, j ≠ id → (P.slots j).conn = (T.c.page.slots j).conn)
    (hopen : (P.slots id).conn = some { c with isOpen := true })
    (hcl : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing) (hnext : P.nextSeq = T.c.page.nextSeq) :
    Inv ⟨c', T.clk⟩ := by
  obtain ⟨rs', pg', tr', tp', gg', bd', pr', sk'⟩ := c'
  dsimp only at hrs hr hg hs hp
  subst hrs hr hg
  subst tp'
  subst pg'
  have hmemq : (Relay.Out.ok id, t) ∈ T.c.toPage := by rw [hq]; simp
  have hord := h.okOrd
  rw [hq] at hord
  have hrest := (List.pairwise_cons.mp hord).1
  have hsub : ∀ q ∈ rest, q ∈ T.c.toPage := fun q hq' => by
    rw [hq]
    exact List.mem_cons_of_mem _ hq'
  have hsl : rest.Sublist T.c.toPage := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hokr := h.okRel _ hmemq id rfl
  have hpo : ∀ j, (P.slots j).conn = if j = id then some { c with isOpen := true } else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · rw [hj, hopen, if_pos rfl]
    · rw [hconn j hj, if_neg hj]
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_, discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_ }
  · -- pi
    intro j pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      exact h.pi id c hc
    · rw [if_neg hj] at hpc
      exact h.pi j pc hpc
  · -- link
    intro j c2 hc2
    rcases h.link j c2 hc2 with ⟨pc0, hpc0, hm⟩ | ⟨hn0, hcl2⟩
    · by_cases hj : j = id
      · left
        have hpc0c : pc0 = c := by
          have h1 : (T.c.page.slots j).conn = some pc0 := hpc0
          rw [hj, hc] at h1
          exact (Option.some.inj h1).symm
        rw [hpc0c] at hm
        refine ⟨{ c with isOpen := true }, ?_, hm⟩
        show (P.slots j).conn = some { c with isOpen := true }
        rw [hj, hopen]
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
    intro j pc c2 hpc hc2 hm
    rw [qs_read]
    by_cases hj : j = id
    · change (P.slots j).conn = some pc at hpc
      rw [hpo j, if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hc2
      rw [hj]
      exact h.acc id c c2 hc hc2 hm
    · change (P.slots j).conn = some pc at hpc
      rw [hpo j, if_neg hj] at hpc
      exact h.acc j pc c2 hpc hc2 hm
  · -- wq
    intro j c2 hc2
    rw [qs_read]
    exact h.wq j c2 hc2
  · -- gen
    intro q hq' j hqj c2 hc2
    exact h.gen q (hsub q hq') j hqj c2 hc2
  · -- apply
    intro q hq' j hcl' hqj pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
    rw [hcl j]
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hqj
      have hq2 := h.apply q (hsub q hq') id hcl' hqj c hc
      rw [hcl0] at hq2
      rcases hq2 with h2 | h2
      · cases h2
      · exact Or.inr h2
    · rw [if_neg hj] at hpc
      exact h.apply q (hsub q hq') j hcl' hqj pc hpc
  · -- noOrphan
    intro q hq' j hcl' hqj hn
    change (P.slots j).conn = none at hn
    rw [hpo j] at hn
    show (P.slots j).closing = true
    rw [hcl j]
    by_cases hj : j = id
    · rw [if_pos hj] at hn
      cases hn
    · rw [if_neg hj] at hn
      exact h.noOrphan q (hsub q hq') j hcl' hqj hn
  · -- written
    intro q hq' j cnt f hqj c2 hc2 hg2
    exact h.written q (hsub q hq') j cnt f hqj c2 hc2 hg2
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hg2 c2 hc2 hgen
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    rw [qs_read]
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      exact h.reset q (hsub q hq') j cnt hqj c (by rw [hj]; exact hc) hdp hg2 c2 hc2 hgen
    · rw [if_neg hj] at hpc
      exact h.reset q (hsub q hq') j cnt hqj pc hpc hdp hg2 c2 hc2 hgen
  · -- barrier
    rw [List.pairwise_append]
    refine ⟨h.barrier, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    rw [List.mem_singleton] at hy
    subst hy
    intro hf
    obtain ⟨e, p⟩ := x
    cases e with
    | connect a =>
      simp [FwdEv] at hf
      subst hf
      exact h.connPend _ hx a rfl (Relay.Out.ok a, t) hmemq rfl
    | deny a => simp [FwdEv] at hf
    | send a n => simp [FwdEv] at hf
    | discard a => simp [FwdEv] at hf
    | read a k => simp [FwdEv] at hf
    | close a => simp [FwdEv] at hf
    | sock a g k => simp [FwdEv] at hf
  · -- connClean
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.connClean x h1 j hxj
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- notOpen
    intro j pc hpc hop'
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      simp at hop'
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
          refine ⟨{ c with isOpen := true }, ?_, hs'⟩
          show (P.slots j).conn = some { c with isOpen := true }
          rw [hj, hopen]
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
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- rq
    intro q hq' j cnt hqj x hx n
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.rq q (hsub q hq') j cnt hqj x h1 n
    · rw [List.mem_singleton] at h1
      subst h1
      simp
  · -- gensLt
    intro j c2 hc2
    exact h.gensLt j c2 hc2
  · -- gp
    intro x hx j hxj g
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.gp x h1 j hxj g
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- openG
    intro j pc hpc hop'
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      have hap := h.apply (Relay.Out.ok id, t) hmemq id rfl rfl c hc
      rw [hcl0] at hap
      rcases hap with h2 | h2
      · cases h2
      · exact ⟨t, h2⟩
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
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- disc
    intro x hx j hxj pc hpc hop'
    rcases List.mem_append.mp hx with h1 | h1
    · by_cases hj : j = id
      · exfalso
        exact (h.okNoDisc _ hmemq id rfl hcl0 x h1) (by rw [hj] at hxj; exact hxj)
      · change (P.slots j).conn = some pc at hpc
        rw [hpo j, if_neg hj] at hpc
        exact h.disc x h1 j hxj pc hpc hop'
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- rep
    intro q hq' j cnt hqj
    rcases h.rep q (hsub q hq') j cnt hqj with ⟨pc, hpc, hd⟩ | ⟨hn, hcl2⟩
    · by_cases hj : j = id
      · left
        have h1' : (T.c.page.slots j).conn = some pc := hpc
        rw [hj, hc] at h1'
        cases Option.some.inj h1'
        refine ⟨{ c with isOpen := true }, ?_, hd⟩
        show (P.slots j).conn = some { c with isOpen := true }
        rw [hj, hopen]
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
      exact h.recvG id c hc hrc
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
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoConn q (hsub q hq') j hqj x h1
    · rw [List.mem_singleton] at h1
      subst h1
      simp
  · -- openRel
    intro j pc hpc hop'
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    intro c2 hc2
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      rw [hj] at hc2
      have hc2' : ConnOf T id = some c2 := hc2
      rcases hokr with hn | ⟨c0, hc0, _, ho⟩
      · rw [hc2'] at hn
        cases hn
      · rw [hc2'] at hc0
        cases Option.some.inj hc0
        exact ho
    · rw [if_neg hj] at hpc
      exact h.openRel j pc hpc hop' c2 hc2
  · -- okOpen
    intro q hq' j hqj hcl' pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hpo j] at hpc
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hrest q hq' id rfl hqj).elim
    · rw [if_neg hj] at hpc
      have hcl'' : (T.c.page.slots j).closing = false := by
        rw [← hcl j]
        exact hcl'
      exact h.okOpen q (hsub q hq') j hqj hcl'' pc hpc
  · -- okNoDisc
    intro q hq' j hqj hcl' x hx
    rcases List.mem_append.mp hx with h1 | h1
    · have hcl'' : (T.c.page.slots j).closing = false := by
        rw [← hcl j]
        exact hcl'
      exact h.okNoDisc q (hsub q hq') j hqj hcl'' x h1
    · rw [List.mem_singleton] at h1
      subst h1
      simp
  · -- discRel
    intro x hx j hxj
    rcases List.mem_append.mp hx with h1 | h1
    · by_cases hj : j = id
      · exfalso
        exact (h.okNoDisc _ hmemq id rfl hcl0 x h1) (by rw [hj] at hxj; exact hxj)
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
    · rw [List.mem_singleton] at h1
      subst h1
      simp at hxj
  · -- closingNone
    intro j hcl'
    rw [hcl j] at hcl'
    show (P.slots j).conn = none
    by_cases hj : j = id
    · rw [hj, hcl0] at hcl'
      cases hcl'
    · rw [hpo j, if_neg hj]
      exact h.closingNone j hcl'
  · -- closedNoClose
    intro q hq' j hqj x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.closedNoClose q (hsub q hq') j hqj x h1
    · rw [List.mem_singleton] at h1
      subst h1
      simp
  · -- failOrd
    exact List.Pairwise.sublist hsl h.failOrd
  · -- connPend
    intro x hx j hxj q hq'
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.connPend x h1 j hxj q (hsub q hq')
    · rw [List.mem_singleton] at h1
      subst h1
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
    · rw [List.mem_singleton] at h1
      subst h1
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
      exact h.wrMono q (hsub q hq') id cnt f hqj c hc hg
    · rw [if_neg hj] at hpc
      exact h.wrMono q (hsub q hq') j cnt f hqj pc hpc hg
  · -- wrOrd
    exact List.Pairwise.sublist hsl h.wrOrd
  · -- genFun
    exact h.genFun

-- the page takes an OK frame: the frame's id has a connection (closed, not closing), and the frame applies
theorem inv_tDoPage_ok (T T' : TSys) (h : Inv T) (id t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.ok id, t) :: rest) (c : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c) (hcl0 : (T.c.page.slots id).closing = false)
    (hop : c.isOpen = false) (hT : tDoPage T = some T') : Inv T' := by
  unfold tDoPage lift Client.doPage at hT
  simp only [hq] at hT
  generalize hG : Page.frame T.c.page (Relay.Out.ok id) = G at hT
  obtain ⟨st', obs⟩ := G
  have hfr := frame_ok_some T.c.page id c hc hcl0 hop
  rw [hG] at hfr
  dsimp only at hfr
  obtain ⟨hst, hob⟩ := hfr
  subst hst
  simp only [hob, Option.map_some, Option.some.injEq] at hT
  subst hT
  exact inv_ok_core T h _ id t rest hq c hc hcl0 hop _ rfl rfl rfl rfl rfl
    (by intro j hj; simp [Page.setSlot, hj]) (by simp [Page.setSlot])
    (by intro j; by_cases hj : j = id <;> simp [Page.setSlot, hj]) (by simp [Page.setSlot])

end Ind
