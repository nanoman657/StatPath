namespace Ind
open Timed

-- the head CONNECT of the queue, and the rest of the queue behind it (the barrier)
theorem connect_head_mem (T : TSys) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) : (Relay.Ev.connect id, p) ∈ T.c.toRelay := by
  rw [hq]
  exact List.mem_cons_self

theorem connect_rest_barrier (T : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) :
    ∀ y ∈ rest, ¬ FwdEv (Relay.Ev.connect id) y.1 := by
  have hb := h.barrier
  rw [hq] at hb
  exact (List.pairwise_cons.mp hb).1

theorem connect_rest_no_id (T : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) : ∀ y ∈ rest, y.1 ≠ Relay.Ev.connect id :=
  fun y hy e => connect_rest_barrier T h id p rest hq y hy (by rw [e]; simp [FwdEv])

theorem connect_rest_no_send (T : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) : ∀ y ∈ rest, ∀ n, y.1 ≠ Relay.Ev.send id n :=
  fun y hy n e => connect_rest_barrier T h id p rest hq y hy (by rw [e]; simp [FwdEv])

-- a queued CONNECT's sequence number belongs to no other queued CONNECT (the count of the sequence is at most one)
theorem connect_rest_seq (T : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) (x : Relay.Ev × Nat) (hx : x ∈ rest)
    (j : Nat) (hxc : x.1 = Relay.Ev.connect j) (hxp : x.2 = p) : False := by
  have hc := h.connSeq p
  rw [hq] at hc
  have hmemF : x ∈ rest.filter (ConnSeqIs p) :=
    List.mem_filter.mpr ⟨hx, by simp [ConnSeqIs, hxc, hxp]⟩
  have hpos := List.length_pos_of_mem hmemF
  have hpa : ConnSeqIs p (Relay.Ev.connect id, p) = true := by simp [ConnSeqIs]
  rw [List.filter_cons_of_pos hpa] at hc
  simp only [List.length_cons] at hc
  omega

theorem qs_connect_head (T : TSys) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) (j : Nat) : qs j T = qsumT j rest := by
  unfold qs
  rw [hq]
  simp [qsumT]

-- the keep step of a CONNECT: the connections are unchanged, the page is unchanged, and the generation the CONNECT
-- registers is the one the relay gives next (the closed relay, and a refused CONNECT: a FAIL of the id, tagged with it)
theorem inv_connect_keep (T : TSys) (h : Inv T) (c' : Client.Sys) (clk' : Clock.Clk) (id p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest)
    (new : List (Relay.Out × Nat)) (hnewLen : new.length ≤ 1)
    (hnewF : ∀ q ∈ new, outIdT q.1 = none ∨ q = (Relay.Out.fail id 11, T.c.rs.nextGen))
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page)
    (hG : c'.genOf = (p, T.c.rs.nextGen) :: T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ new) (hrs : c'.rs = T.c.rs)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have hmem := connect_head_mem T id p rest hq
  have hpos : 0 < p := h.connAux.1.2 _ hmem id rfl
  have hconnNone : ConnOf T id = none := h.connClean _ hmem id rfl
  have hcl0 := h.cl _ hmem id rfl
  have hseqQ : p < T.c.page.nextSeq := h.seqQ _ hmem id rfl
  have hgp0 : ∀ g, (p, g) ∉ T.c.genOf := fun g => h.gp _ hmem id rfl g
  have hrest_sub : rest.Sublist T.c.toRelay := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hxrest : ∀ x ∈ c'.toRelay, x ∈ T.c.toRelay := fun x hx => by
    rw [hTR] at hx
    exact hrest_sub.subset hx
  have hsubP : ∀ q ∈ c'.toPage, q ∈ T.c.toPage ∨ q ∈ new := fun q hq' => by
    rw [hTP] at hq'
    exact List.mem_append.mp hq'
  have hPO : ∀ j, PageOf ⟨c', clk'⟩ j = PageOf T j := fun j => by
    unfold PageOf
    rw [hpg]
  have hConnEq : ∀ j, ConnOf ⟨c', clk'⟩ j = ConnOf T j := fun j => by
    show (c'.rs.slot j).conn = (T.c.rs.slot j).conn
    rw [hrs]
  have hcl' : ∀ j, (c'.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpg]
  have hGmem : ∀ x ∈ c'.genOf, x = (p, T.c.rs.nextGen) ∨ x ∈ T.c.genOf := fun x hx => by
    rw [hG] at hx
    rcases List.mem_cons.mp hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hGold : ∀ x ∈ T.c.genOf, x ∈ c'.genOf := fun x hx => by
    rw [hG]
    exact List.mem_cons_of_mem _ hx
  have hqsEq : ∀ j, qs j ⟨c', clk'⟩ = qs j T := fun j => by
    show qsumT j c'.toRelay = qsumT j T.c.toRelay
    rw [hTR, hq]
    simp [qsumT]
  have hnoFrame : ∀ q ∈ T.c.toPage, outIdT q.1 ≠ some id := fun q hq' => h.connPend _ hmem id rfl q hq'
  have hnewCase : ∀ q ∈ new, outIdT q.1 = none ∨ (q.1 = Relay.Out.fail id 11 ∧ q.2 = T.c.rs.nextGen) := by
    intro q hq'
    rcases hnewF q hq' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨by rw [h1], by rw [h1]⟩
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_,
      discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_, wrSent := ?_, replyFrozen := ?_, replyMax := ?_,
      noDeny := ?_, closeUniq := ?_, connSeq := ?_, connAux := ?_ }
  · -- pi
    intro j pc hpc
    exact h.pi j pc ((hPO j).symm.trans hpc)
  · -- link
    intro j c3 hc3
    rw [hConnEq] at hc3
    rcases h.link j c3 hc3 with ⟨pc, hpc, hm⟩ | ⟨hn, hcl2⟩
    · exact Or.inl ⟨pc, (hPO j).trans hpc, hGold _ hm⟩
    · exact Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩
  · -- acc
    intro j pc c3 hpc hc3 hgc
    rw [hPO j] at hpc
    rw [hConnEq] at hc3
    rcases hGmem _ hgc with h1 | h1
    · exfalso
      have hgen : c3.gen = T.c.rs.nextGen := (Prod.mk.inj h1).2
      have hlt := h.gensLt j c3 hc3
      omega
    · rw [hqsEq j]
      exact h.acc j pc c3 hpc hc3 h1
  · -- wq
    intro j c3 hc3
    rw [hConnEq] at hc3
    have hW := h.wq j c3 hc3
    rw [hqsEq j]
    exact hW
  · -- gen
    intro q hq' j hoj c3 hc3
    rw [hConnEq] at hc3
    rcases hsubP q hq' with h1 | h1
    · exact h.gen q h1 j hoj c3 hc3
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hno] at hoj
        cases hoj
      · have hj : j = id := by
          rw [hqa] at hoj
          simp [outIdT] at hoj
          omega
        rw [hj, hconnNone] at hc3
        cases hc3
  · -- apply
    intro q hq' j hcl2 hoj pc hpc
    rw [hPO j] at hpc
    rcases hsubP q hq' with h1 | h1
    · rcases h.apply q h1 j hcl2 hoj pc hpc with h2 | h2
      · exact Or.inl (by rw [hcl' j]; exact h2)
      · exact Or.inr (hGold _ h2)
    · rcases hnewCase q h1 with hno | ⟨hqa, hqb⟩
      · rw [hno] at hoj
        cases hoj
      · have hjid : j = id := by
          rw [hqa] at hoj
          simp [outIdT] at hoj
          omega
        rw [hjid] at hpc
        rcases hcl0 with ⟨pc0, hpc0, hs0⟩ | ⟨hn0, hcl3⟩
        · have hpe : pc = pc0 := Option.some.inj (hpc.symm.trans hpc0)
          refine Or.inr ?_
          rw [hqb, hG, hpe, hs0]
          exact List.mem_cons_self
        · rw [hn0] at hpc
          cases hpc
  · -- noOrphan
    intro q hq' j hcl2 hoj hpn
    rw [hPO j] at hpn
    rcases hsubP q hq' with h1 | h1
    · rw [hcl' j]
      exact h.noOrphan q h1 j hcl2 hoj hpn
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hno] at hoj
        cases hoj
      · have hjid : j = id := by
          rw [hqa] at hoj
          simp [outIdT] at hoj
          omega
        rw [hjid] at hpn
        rcases hcl0 with ⟨pc0, hpc0, -⟩ | ⟨-, hcl3⟩
        · rw [hpc0] at hpn
          cases hpn
        · rw [hcl' j, hjid]
          exact hcl3
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    rw [hConnEq] at hc3
    rcases hsubP q hq' with h1 | h1
    · exact h.written q h1 j cnt f hqj c3 hc3 hg3
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hgq c3 hc3 hg3
    rw [hPO j] at hpc
    rw [hConnEq] at hc3
    rcases hsubP q hq' with h1 | h1
    · have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rcases hGmem _ hgq with h2 | h2
        · exfalso
          have hq2 := h.connAux.2 q h1 j cnt 1 hqj
          have hqe : q.2 = T.c.rs.nextGen := (Prod.mk.inj h2).2
          omega
        · exact h2
      rw [hqsEq j]
      exact h.reset q h1 j cnt hqj pc hpc hdp hgq' c3 hc3 hg3
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- barrier
    show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) c'.toRelay
    rw [hTR]
    exact List.Pairwise.sublist hrest_sub h.barrier
  · -- connClean
    intro x hx j hxj
    rw [hConnEq]
    exact h.connClean x (hxrest x hx) j hxj
  · -- notOpen
    intro j pc hpc hop
    exact h.notOpen j pc ((hPO j).symm.trans hpc) hop
  · -- cl
    intro x hx j hxj
    rcases h.cl x (hxrest x hx) j hxj with ⟨pc, hpc, hs⟩ | ⟨hn, hcl2⟩
    · exact Or.inl ⟨pc, (hPO j).trans hpc, hs⟩
    · exact Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩
  · -- rq
    intro q hq' j cnt hqj x hx n
    rcases hsubP q hq' with h1 | h1
    · exact h.rq q h1 j cnt hqj x (hxrest x hx) n
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- gensLt
    intro j c3 hc3
    rw [hConnEq] at hc3
    show c3.gen < c'.rs.nextGen
    rw [hrs]
    exact h.gensLt j c3 hc3
  · -- gp
    intro x hx j hxj g
    show (x.2, g) ∉ c'.genOf
    intro hgx
    rcases hGmem _ hgx with h2 | h2
    · have hx2 : x.2 = p := (Prod.mk.inj h2).1
      have hxr : x ∈ rest := by
        rw [← hTR]
        exact hx
      exact connect_rest_seq T h id p rest hq x hxr j hxj hx2
    · exact h.gp x (hxrest x hx) j hxj g h2
  · -- openG
    intro j pc hpc hop
    obtain ⟨g, hg⟩ := h.openG j pc ((hPO j).symm.trans hpc) hop
    exact ⟨g, hGold _ hg⟩
  · -- mirror
    exact hM
  · -- good
    exact hGd
  · -- seqG
    intro p' g hpg'
    show p' < c'.page.nextSeq
    rw [hpg]
    rcases hGmem _ hpg' with h2 | h2
    · rw [(Prod.mk.inj h2).1]
      exact hseqQ
    · exact h.seqG p' g h2
  · -- seqQ
    intro x hx j hxj
    show x.2 < c'.page.nextSeq
    rw [hpg]
    exact h.seqQ x (hxrest x hx) j hxj
  · -- disc
    intro x hx j hxj pc hpc hop
    exact h.disc x (hxrest x hx) j hxj pc ((hPO j).symm.trans hpc) hop
  · -- rep
    intro q hq' j cnt hqj
    rcases hsubP q hq' with h1 | h1
    · rcases h.rep q h1 j cnt hqj with ⟨pc, hpc, hdp⟩ | ⟨hn, hcl2⟩
      · exact Or.inl ⟨pc, (hPO j).trans hpc, hdp⟩
      · exact Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- recvG
    intro j pc hpc hr0
    obtain ⟨g, hg⟩ := h.recvG j pc ((hPO j).symm.trans hpc) hr0
    exact ⟨g, hGold _ hg⟩
  · -- failNone
    intro q hq' j e hqj
    rw [hConnEq]
    rcases hsubP q hq' with h1 | h1
    · exact h.failNone q h1 j e hqj
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        obtain ⟨rfl, -⟩ := Relay.Out.fail.inj hqj
        exact hconnNone
  · -- closedNone
    intro q hq' j hqj
    rw [hConnEq]
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNone q h1 j hqj
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- closedClosing
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · rw [hcl' j]
      exact h.closedClosing q h1 j hqj
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- closedOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.closedOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b hb j' hpa _
      rcases hnewCase a ha with hno | ⟨hqa, -⟩
      · rw [hpa] at hno
        simp [outIdT] at hno
      · rw [hqa] at hpa
        simp at hpa
    · intro a ha b hb j' hpa hob
      rcases hnewCase b hb with hno | ⟨hqb, -⟩
      · rw [hno] at hob
        cases hob
      · rw [hqb] at hob
        have hj : id = j' := Option.some.inj hob
        exact hnoFrame a ha (by rw [hpa]; simp [outIdT, ← hj])
  · -- closeClosing
    intro x hx j hxj
    rw [hcl' j]
    exact h.closeClosing x (hxrest x hx) j hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNoConn q h1 j hqj x (hxrest x hx)
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- openRel
    intro j pc hpc hop c3 hc3
    rw [hConnEq] at hc3
    exact h.openRel j pc ((hPO j).symm.trans hpc) hop c3 hc3
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    rw [hPO j] at hpc
    rcases hsubP q hq' with h1 | h1
    · exact h.okOpen q h1 j hqj ((hcl' j).symm.trans hcl2) pc hpc
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.okNoDisc q h1 j hqj ((hcl' j).symm.trans hcl2) x (hxrest x hx)
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- discRel
    intro x hx j hxj
    rcases h.discRel x (hxrest x hx) j hxj with hn | ⟨pc, hpc, hop⟩ | ⟨hn, hcl2⟩
    · exact Or.inl (by rw [hConnEq]; exact hn)
    · exact Or.inr (Or.inl ⟨pc, (hPO j).trans hpc, hop⟩)
    · exact Or.inr (Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩)
  · -- closingNone
    intro j hcl2
    have hcl3 : (T.c.page.slots j).closing = true := by
      rw [← hcl' j]
      exact hcl2
    show (c'.page.slots j).conn = none
    rw [hpg]
    exact h.closingNone j hcl3
  · -- closedNoClose
    intro q hq' j hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNoClose q h1 j hqj x (hxrest x hx)
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- failOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.failOrd, pairwise_le_one _ _ hnewLen, ?_⟩
    intro a ha b hb j' e' hpa hob
    exfalso
    rcases hnewCase b hb with hno | ⟨hqb, -⟩
    · rw [hno] at hob
      cases hob
    · rw [hqb] at hob
      have hj : id = j' := Option.some.inj hob
      exact hnoFrame a ha (by rw [hpa]; simp [outIdT, ← hj])
  · -- connPend
    intro x hx j hxj q hq'
    rcases hsubP q hq' with h1 | h1
    · exact h.connPend x (hxrest x hx) j hxj q h1
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hno]
        simp
      · intro hj'
        rw [hqa] at hj'
        have hjid : id = j := Option.some.inj hj'
        have hxr : x ∈ rest := by
          rw [← hTR]
          exact hx
        have hxid : x.1 = Relay.Ev.connect id := by rw [hxj, hjid]
        exact connect_rest_no_id T h id p rest hq x hxr hxid
  · -- okRel
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · rcases h.okRel q h1 j hqj with hn | ⟨c, hc, hgc, hop⟩
      · exact Or.inl (by rw [hConnEq]; exact hn)
      · exact Or.inr ⟨c, by rw [hConnEq]; exact hc, hgc, hop⟩
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- okOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.okOrd, pairwise_le_one _ _ hnewLen, ?_⟩
    intro a ha b hb j' _ hbo
    rcases hnewCase b hb with hno | ⟨hqb, -⟩
    · rw [hbo] at hno
      simp [outIdT] at hno
    · rw [hqb] at hbo
      cases hbo
  · -- discOnce
    intro q hq' j cnt hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.discOnce q h1 j cnt hqj x (hxrest x hx)
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- discUniq
    intro id'
    show ((c'.toPage).filter (DiscRep id')).length ≤ 1
    have hN : ∀ x ∈ new, DiscRep id' x = false := by
      intro x hx
      rcases hnewCase x hx with hno | ⟨hqa, -⟩
      · exact discRep_none id' x hno
      · simp [hqa, DiscRep]
    rw [hTP, count_app_nil _ _ _ hN]
    exact h.discUniq id'
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hgq
    rw [hPO j] at hpc
    rcases hsubP q hq' with h1 | h1
    · have hgT : (pc.seq, q.2) ∈ T.c.genOf := by
        rcases hGmem _ hgq with h2 | h2
        · exfalso
          have hq2 := h.connAux.2 q h1 j cnt f hqj
          have hqe : q.2 = T.c.rs.nextGen := (Prod.mk.inj h2).2
          omega
        · exact h2
      exact h.wrMono q h1 j cnt f hqj pc hpc hgT
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- wrOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.wrOrd, pairwise_le_one _ _ hnewLen, ?_⟩
    intro a ha b hb j' c1 f1 c2 f2 hap hbw _
    rcases hnewCase b hb with hno | ⟨hqb, -⟩
    · rw [hbw] at hno
      simp [outIdT] at hno
    · rw [hqb] at hbw
      cases hbw
  · -- genFun
    intro p1 g1 g2 h1 h2
    rcases hGmem _ h1 with e1 | o1 <;> rcases hGmem _ h2 with e2 | o2
    · rw [(Prod.mk.inj e1).2, (Prod.mk.inj e2).2]
    · exfalso
      have hp1 : p1 = p := (Prod.mk.inj e1).1
      rw [hp1] at o2
      exact hgp0 g2 o2
    · exfalso
      have hp2 : p1 = p := (Prod.mk.inj e2).1
      rw [hp2] at o1
      exact hgp0 g1 o1
    · exact h.genFun p1 g1 g2 o1 o2
  · -- wrSent
    intro q hq' j cnt f hqj pc hpc hgq
    rw [hPO j] at hpc
    rcases hsubP q hq' with h1 | h1
    · have hgT : (pc.seq, q.2) ∈ T.c.genOf := by
        rcases hGmem _ hgq with h2 | h2
        · exfalso
          have hq2 := h.connAux.2 q h1 j cnt f hqj
          have hqe : q.2 = T.c.rs.nextGen := (Prod.mk.inj h2).2
          omega
        · exact h2
      exact h.wrSent q h1 j cnt f hqj pc hpc hgT
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- replyFrozen
    intro q hq' j cnt hqj c3 hc3 hg3
    rw [hConnEq] at hc3
    rcases hsubP q hq' with h1 | h1
    · exact h.replyFrozen q h1 j cnt hqj c3 hc3 hg3
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    rcases hsubP q hq' with hq1 | hq1
    · rcases hsubP r hr with hr1 | hr1
      · exact h.replyMax q hq1 r hr1 j c1 c2 f h1 h2 hg
      · rcases hnewCase r hr1 with hno | ⟨hra, -⟩
        · rw [h2] at hno
          simp [outIdT] at hno
        · rw [hra] at h2
          simp at h2
    · rcases hnewCase q hq1 with hno | ⟨hqa, -⟩
      · rw [h1] at hno
        simp [outIdT] at hno
      · rw [hqa] at h1
        simp at h1
  · -- noDeny
    intro x hx
    exact h.noDeny x (hxrest x hx)
  · -- closeUniq
    intro j
    show ((c'.toRelay).filter (CloseIs j)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest_sub (h.closeUniq j)
  · -- connSeq
    intro s
    show ((c'.toRelay).filter (ConnSeqIs s)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest_sub (h.connSeq s)
  · -- connAux
    refine ⟨⟨by rw [hpg]; exact h.connAux.1.1, fun q hq j hqj => h.connAux.1.2 q (hxrest q hq) j hqj⟩, ?_⟩
    intro q hq j cnt f hqj
    rw [hrs]
    rcases hsubP q hq with h1 | h1
    · exact h.connAux.2 q h1 j cnt f hqj
    · rcases hnewCase q h1 with hno | ⟨hqa, -⟩
      · rw [hqj] at hno
        simp [outIdT] at hno
      · rw [hqa] at hqj
        simp at hqj


-- the relay's CONNECT of a free id: a connection of the next generation; the next generation goes up by one
theorem connectStep_free_conn (s : Relay.St) (id : Nat) (hc : (s.slot id).conn = none) :
    ((Relay.connectStep s id).1.slot id).conn = some { gen := s.nextGen, isOpen := false, queued := 0, written := 0, rd := 0, gr := 0, peerClosed := false } := by
  unfold Relay.connectStep
  have hc' : (s.slots id).conn = none := hc
  simp [hc', Relay.setSlot, Relay.St.slot]

theorem connectStep_slot_ne (s : Relay.St) (id j : Nat) (h : j ≠ id) :
    (Relay.connectStep s id).1.slot j = s.slot j := by
  unfold Relay.connectStep
  split <;> simp [Relay.setSlot, Relay.St.slot, h, Relay.protoClose]

theorem connectStep_nextGen (s : Relay.St) (id : Nat) (hc : (s.slot id).conn = none) :
    (Relay.connectStep s id).1.nextGen = s.nextGen + 1 := by
  unfold Relay.connectStep
  simp [hc]

-- the clock's relay step of a CONNECT of a free id: the relay refuses it (a FAIL of the id, the tokens short), or takes it
theorem stepK_connect_refused (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id : Nat)
    (hcl : s.closed.isSome = false) (hc : (s.slot id).conn = none) (hk : (Clock.refill k).tokens < 1000) :
    (Clock.stepK cap k s (Relay.Ev.connect id)).2.1 = s ∧
    (Clock.stepK cap k s (Relay.Ev.connect id)).2.2 = [Relay.Out.fail id 11] := by
  unfold Clock.stepK
  simp [hcl, hc, hk]

theorem stepK_connect_taken (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id : Nat)
    (hcl : s.closed.isSome = false) (hc : (s.slot id).conn = none) (hk : ¬ (Clock.refill k).tokens < 1000) :
    (Clock.stepK cap k s (Relay.Ev.connect id)).2.1 = (Relay.connectStep s id).1 ∧
    (Clock.stepK cap k s (Relay.Ev.connect id)).2.2 = (Relay.connectStep s id).2 := by
  unfold Clock.stepK
  simp [hcl, hc, hk, Relay.step]

-- a CONNECT the relay takes for a free id: the connection of the next generation, and nothing for the page yet
theorem inv_connect_create (T : TSys) (h : Inv T) (c' : Client.Sys) (clk' : Clock.Clk) (id p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest)
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page)
    (hG : c'.genOf = (p, T.c.rs.nextGen) :: T.c.genOf)
    (hTP : c'.toPage = T.c.toPage) (hrs : c'.rs = (Relay.connectStep T.c.rs id).1)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have hmem := connect_head_mem T id p rest hq
  have hpos : 0 < p := h.connAux.1.2 _ hmem id rfl
  have hconnNone : ConnOf T id = none := h.connClean _ hmem id rfl
  have hcT : (T.c.rs.slot id).conn = none := hconnNone
  have hcl0 := h.cl _ hmem id rfl
  have hseqQ : p < T.c.page.nextSeq := h.seqQ _ hmem id rfl
  have hgp0 : ∀ g, (p, g) ∉ T.c.genOf := fun g => h.gp _ hmem id rfl g
  have hrest_sub : rest.Sublist T.c.toRelay := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hxrest : ∀ x ∈ c'.toRelay, x ∈ T.c.toRelay := fun x hx => by
    rw [hTR] at hx
    exact hrest_sub.subset hx
  have hsubP : ∀ q ∈ c'.toPage, q ∈ T.c.toPage := fun q hq' => by
    rw [hTP] at hq'
    exact hq'
  have hPO : ∀ j, PageOf ⟨c', clk'⟩ j = PageOf T j := fun j => by
    unfold PageOf
    rw [hpg]
  have hcl' : ∀ j, (c'.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpg]
  have hCid : ConnOf ⟨c', clk'⟩ id = some { gen := T.c.rs.nextGen, isOpen := false, queued := 0, written := 0, rd := 0, gr := 0, peerClosed := false } := by
    show (c'.rs.slot id).conn = _
    rw [hrs]
    exact connectStep_free_conn T.c.rs id hcT
  have hCother : ∀ j, j ≠ id → ConnOf ⟨c', clk'⟩ j = ConnOf T j := fun j hj => by
    show (c'.rs.slot j).conn = (T.c.rs.slot j).conn
    rw [hrs, connectStep_slot_ne T.c.rs id j hj]
  have hN : c'.rs.nextGen = T.c.rs.nextGen + 1 := by
    rw [hrs]
    exact connectStep_nextGen T.c.rs id hcT
  have hGmem : ∀ x ∈ c'.genOf, x = (p, T.c.rs.nextGen) ∨ x ∈ T.c.genOf := fun x hx => by
    rw [hG] at hx
    rcases List.mem_cons.mp hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hGold : ∀ x ∈ T.c.genOf, x ∈ c'.genOf := fun x hx => by
    rw [hG]
    exact List.mem_cons_of_mem _ hx
  have hqsEq : ∀ j, qs j ⟨c', clk'⟩ = qs j T := fun j => by
    show qsumT j c'.toRelay = qsumT j T.c.toRelay
    rw [hTR, hq]
    simp [qsumT]
  have hqsZ : qs id T = 0 := by
    rw [qs_connect_head T id p rest hq id]
    exact qsumT_no_send rest id (fun y hy n => connect_rest_no_send T h id p rest hq y hy n)
  have hnoFrame : ∀ q ∈ T.c.toPage, outIdT q.1 ≠ some id := fun q hq' => h.connPend _ hmem id rfl q hq'
  have hpcSeq : ∀ pc, PageOf T id = some pc → pc.seq = p := fun pc hpc => by
    rcases hcl0 with ⟨pc0, hpc0, hs0⟩ | ⟨hn0, -⟩
    · have hpe : pc = pc0 := Option.some.inj (hpc.symm.trans hpc0)
      rw [hpe]
      exact hs0
    · rw [hn0] at hpc
      cases hpc
  have hpcOpen : ∀ pc, PageOf T id = some pc → pc.isOpen = false := by
    intro pc hpc
    cases hb : pc.isOpen with
    | false => rfl
    | true =>
      obtain ⟨g, hg⟩ := h.openG id pc hpc hb
      rw [hpcSeq pc hpc] at hg
      exact absurd hg (hgp0 g)
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_,
      discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_, wrSent := ?_, replyFrozen := ?_, replyMax := ?_,
      noDeny := ?_, closeUniq := ?_, connSeq := ?_, connAux := ?_ }
  · -- pi
    intro j pc hpc
    exact h.pi j pc ((hPO j).symm.trans hpc)
  · -- link
    intro j c3 hc3
    by_cases hj : j = id
    · rw [hj] at hc3 ⊢
      rw [hCid] at hc3
      have hc3e := (Option.some.inj hc3).symm
      rcases hcl0 with ⟨pc0, hpc0, hs0⟩ | ⟨hn0, hcl3⟩
      · refine Or.inl ⟨pc0, by rw [hPO id]; exact hpc0, ?_⟩
        rw [hc3e, hG, hs0]
        exact List.mem_cons_self
      · exact Or.inr ⟨by rw [hPO id]; exact hn0, by rw [hcl' id]; exact hcl3⟩
    · rw [hCother j hj] at hc3
      rcases h.link j c3 hc3 with ⟨pc, hpc, hm⟩ | ⟨hn, hcl2⟩
      · exact Or.inl ⟨pc, (hPO j).trans hpc, hGold _ hm⟩
      · exact Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩
  · -- acc
    intro j pc c3 hpc hc3 hgc
    by_cases hj : j = id
    · rw [hj] at hpc hc3 ⊢
      rw [hPO id] at hpc
      rw [hCid] at hc3
      have hc3e := (Option.some.inj hc3).symm
      have hno := h.notOpen id pc hpc (hpcOpen pc hpc)
      rw [hc3e]
      constructor
      · simp [hqsEq id, hqsZ]
      · simp [hno.2]
    · rw [hCother j hj] at hc3
      rcases hGmem _ hgc with h1 | h1
      · exfalso
        have hgen : c3.gen = T.c.rs.nextGen := (Prod.mk.inj h1).2
        have hlt := h.gensLt j c3 hc3
        omega
      · rw [hqsEq j]
        exact h.acc j pc c3 ((hPO j).symm.trans hpc) hc3 h1
  · -- wq
    intro j c3 hc3
    by_cases hj : j = id
    · rw [hj] at hc3 ⊢
      rw [hCid] at hc3
      have hc3e := (Option.some.inj hc3).symm
      rw [hc3e, hqsEq id, hqsZ]
      simp
    · rw [hCother j hj] at hc3
      rw [hqsEq j]
      exact h.wq j c3 hc3
  · -- gen
    intro q hq' j hoj c3 hc3
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hoj
      exact (hnoFrame q h1 hoj).elim
    · rw [hCother j hj] at hc3
      exact h.gen q h1 j hoj c3 hc3
  · -- apply
    intro q hq' j hcl2 hoj pc hpc
    have h1 := hsubP q hq'
    rw [hPO j] at hpc
    rcases h.apply q h1 j hcl2 hoj pc hpc with h2 | h2
    · exact Or.inl (by rw [hcl' j]; exact h2)
    · exact Or.inr (hGold _ h2)
  · -- noOrphan
    intro q hq' j hcl2 hoj hpn
    have h1 := hsubP q hq'
    rw [hPO j] at hpn
    rw [hcl' j]
    exact h.noOrphan q h1 j hcl2 hoj hpn
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hnoFrame q h1 (by rw [hqj]; simp [outIdT])).elim
    · rw [hCother j hj] at hc3
      exact h.written q h1 j cnt f hqj c3 hc3 hg3
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hgq c3 hc3 hg3
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hnoFrame q h1 (by rw [hqj]; simp [outIdT])).elim
    · rw [hPO j] at hpc
      rw [hCother j hj] at hc3
      have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rcases hGmem _ hgq with h2 | h2
        · exfalso
          have hq2 := h.connAux.2 q h1 j cnt 1 hqj
          have hqe : q.2 = T.c.rs.nextGen := (Prod.mk.inj h2).2
          omega
        · exact h2
      rw [hqsEq j]
      exact h.reset q h1 j cnt hqj pc hpc hdp hgq' c3 hc3 hg3
  · -- barrier
    show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) c'.toRelay
    rw [hTR]
    exact List.Pairwise.sublist hrest_sub h.barrier
  · -- connClean
    intro x hx j hxj
    by_cases hj : j = id
    · have hxr : x ∈ rest := by
        rw [← hTR]
        exact hx
      exact (connect_rest_no_id T h id p rest hq x hxr (by rw [hxj, hj])).elim
    · rw [hCother j hj]
      exact h.connClean x (hxrest x hx) j hxj
  · -- notOpen
    intro j pc hpc hop
    exact h.notOpen j pc ((hPO j).symm.trans hpc) hop
  · -- cl
    intro x hx j hxj
    rcases h.cl x (hxrest x hx) j hxj with ⟨pc, hpc, hs⟩ | ⟨hn, hcl2⟩
    · exact Or.inl ⟨pc, (hPO j).trans hpc, hs⟩
    · exact Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩
  · -- rq
    intro q hq' j cnt hqj x hx n
    exact h.rq q (hsubP q hq') j cnt hqj x (hxrest x hx) n
  · -- gensLt
    intro j c3 hc3
    show c3.gen < c'.rs.nextGen
    rw [hN]
    by_cases hj : j = id
    · rw [hj, hCid] at hc3
      have hc3e := (Option.some.inj hc3).symm
      rw [hc3e]
      exact Nat.lt_succ_self _
    · rw [hCother j hj] at hc3
      have := h.gensLt j c3 hc3
      omega
  · -- gp
    intro x hx j hxj g
    show (x.2, g) ∉ c'.genOf
    intro hgx
    rcases hGmem _ hgx with h2 | h2
    · have hx2 : x.2 = p := (Prod.mk.inj h2).1
      have hxr : x ∈ rest := by
        rw [← hTR]
        exact hx
      exact connect_rest_seq T h id p rest hq x hxr j hxj hx2
    · exact h.gp x (hxrest x hx) j hxj g h2
  · -- openG
    intro j pc hpc hop
    by_cases hj : j = id
    · rw [hj] at hpc
      rw [hPO id] at hpc
      rw [hpcOpen pc hpc] at hop
      cases hop
    · rw [hPO j] at hpc
      obtain ⟨g, hg⟩ := h.openG j pc hpc hop
      exact ⟨g, hGold _ hg⟩
  · -- mirror
    exact hM
  · -- good
    exact hGd
  · -- seqG
    intro p' g hpg'
    show p' < c'.page.nextSeq
    rw [hpg]
    rcases hGmem _ hpg' with h2 | h2
    · rw [(Prod.mk.inj h2).1]
      exact hseqQ
    · exact h.seqG p' g h2
  · -- seqQ
    intro x hx j hxj
    show x.2 < c'.page.nextSeq
    rw [hpg]
    exact h.seqQ x (hxrest x hx) j hxj
  · -- disc
    intro x hx j hxj pc hpc hop
    exact h.disc x (hxrest x hx) j hxj pc ((hPO j).symm.trans hpc) hop
  · -- rep
    intro q hq' j cnt hqj
    rcases h.rep q (hsubP q hq') j cnt hqj with ⟨pc, hpc, hdp⟩ | ⟨hn, hcl2⟩
    · exact Or.inl ⟨pc, (hPO j).trans hpc, hdp⟩
    · exact Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩
  · -- recvG
    intro j pc hpc hr0
    obtain ⟨g, hg⟩ := h.recvG j pc ((hPO j).symm.trans hpc) hr0
    exact ⟨g, hGold _ hg⟩
  · -- failNone
    intro q hq' j e hqj
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hnoFrame q h1 (by rw [hqj]; simp [outIdT])).elim
    · rw [hCother j hj]
      exact h.failNone q h1 j e hqj
  · -- closedNone
    intro q hq' j hqj
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hnoFrame q h1 (by rw [hqj]; simp [outIdT])).elim
    · rw [hCother j hj]
      exact h.closedNone q h1 j hqj
  · -- closedClosing
    intro q hq' j hqj
    rw [hcl' j]
    exact h.closedClosing q (hsubP q hq') j hqj
  · -- closedOrd
    rw [hTP]
    exact h.closedOrd
  · -- closeClosing
    intro x hx j hxj
    rw [hcl' j]
    exact h.closeClosing x (hxrest x hx) j hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    exact h.closedNoConn q (hsubP q hq') j hqj x (hxrest x hx)
  · -- openRel
    intro j pc hpc hop c3 hc3
    by_cases hj : j = id
    · rw [hj] at hpc
      rw [hPO id] at hpc
      rw [hpcOpen pc hpc] at hop
      cases hop
    · rw [hCother j hj] at hc3
      rw [hPO j] at hpc
      exact h.openRel j pc hpc hop c3 hc3
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    rw [hPO j] at hpc
    exact h.okOpen q (hsubP q hq') j hqj ((hcl' j).symm.trans hcl2) pc hpc
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    exact h.okNoDisc q (hsubP q hq') j hqj ((hcl' j).symm.trans hcl2) x (hxrest x hx)
  · -- discRel
    intro x hx j hxj
    rcases h.discRel x (hxrest x hx) j hxj with hn | ⟨pc, hpc, hop⟩ | ⟨hn, hcl2⟩
    · by_cases hj : j = id
      · have hxr : x ∈ rest := by
          rw [← hTR]
          exact hx
        exact (connect_rest_barrier T h id p rest hq x hxr (by rw [hxj, hj]; simp [FwdEv])).elim
      · exact Or.inl (by rw [hCother j hj]; exact hn)
    · exact Or.inr (Or.inl ⟨pc, (hPO j).trans hpc, hop⟩)
    · exact Or.inr (Or.inr ⟨(hPO j).trans hn, by rw [hcl' j]; exact hcl2⟩)
  · -- closingNone
    intro j hcl2
    have hcl3 : (T.c.page.slots j).closing = true := by
      rw [← hcl' j]
      exact hcl2
    show (c'.page.slots j).conn = none
    rw [hpg]
    exact h.closingNone j hcl3
  · -- closedNoClose
    intro q hq' j hqj x hx
    exact h.closedNoClose q (hsubP q hq') j hqj x (hxrest x hx)
  · -- failOrd
    rw [hTP]
    exact h.failOrd
  · -- connPend
    intro x hx j hxj q hq'
    exact h.connPend x (hxrest x hx) j hxj q (hsubP q hq')
  · -- okRel
    intro q hq' j hqj
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hnoFrame q h1 (by rw [hqj]; simp [outIdT])).elim
    · rcases h.okRel q h1 j hqj with hn | ⟨c, hc, hgc, hop⟩
      · exact Or.inl (by rw [hCother j hj]; exact hn)
      · exact Or.inr ⟨c, by rw [hCother j hj]; exact hc, hgc, hop⟩
  · -- okOrd
    rw [hTP]
    exact h.okOrd
  · -- discOnce
    intro q hq' j cnt hqj x hx
    exact h.discOnce q (hsubP q hq') j cnt hqj x (hxrest x hx)
  · -- discUniq
    intro id'
    show ((c'.toPage).filter (DiscRep id')).length ≤ 1
    rw [hTP]
    exact h.discUniq id'
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hgq
    rw [hPO j] at hpc
    have h1 := hsubP q hq'
    have hgT : (pc.seq, q.2) ∈ T.c.genOf := by
      rcases hGmem _ hgq with h2 | h2
      · exfalso
        have hq2 := h.connAux.2 q h1 j cnt f hqj
        have hqe : q.2 = T.c.rs.nextGen := (Prod.mk.inj h2).2
        omega
      · exact h2
    exact h.wrMono q h1 j cnt f hqj pc hpc hgT
  · -- wrOrd
    rw [hTP]
    exact h.wrOrd
  · -- genFun
    intro p1 g1 g2 h1 h2
    rcases hGmem _ h1 with e1 | o1 <;> rcases hGmem _ h2 with e2 | o2
    · rw [(Prod.mk.inj e1).2, (Prod.mk.inj e2).2]
    · exfalso
      have hp1 : p1 = p := (Prod.mk.inj e1).1
      rw [hp1] at o2
      exact hgp0 g2 o2
    · exfalso
      have hp2 : p1 = p := (Prod.mk.inj e2).1
      rw [hp2] at o1
      exact hgp0 g1 o1
    · exact h.genFun p1 g1 g2 o1 o2
  · -- wrSent
    intro q hq' j cnt f hqj pc hpc hgq
    rw [hPO j] at hpc
    have h1 := hsubP q hq'
    have hgT : (pc.seq, q.2) ∈ T.c.genOf := by
      rcases hGmem _ hgq with h2 | h2
      · exfalso
        have hq2 := h.connAux.2 q h1 j cnt f hqj
        have hqe : q.2 = T.c.rs.nextGen := (Prod.mk.inj h2).2
        omega
      · exact h2
    exact h.wrSent q h1 j cnt f hqj pc hpc hgT
  · -- replyFrozen
    intro q hq' j cnt hqj c3 hc3 hg3
    have h1 := hsubP q hq'
    by_cases hj : j = id
    · rw [hj] at hqj
      exact (hnoFrame q h1 (by rw [hqj]; simp [outIdT])).elim
    · rw [hCother j hj] at hc3
      exact h.replyFrozen q h1 j cnt hqj c3 hc3 hg3
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    exact h.replyMax q (hsubP q hq') r (hsubP r hr) j c1 c2 f h1 h2 hg
  · -- noDeny
    intro x hx
    exact h.noDeny x (hxrest x hx)
  · -- closeUniq
    intro j
    show ((c'.toRelay).filter (CloseIs j)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest_sub (h.closeUniq j)
  · -- connSeq
    intro s'
    show ((c'.toRelay).filter (ConnSeqIs s')).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest_sub (h.connSeq s')
  · -- connAux
    refine ⟨⟨by rw [hpg]; exact h.connAux.1.1, fun q hq j hqj => h.connAux.1.2 q (hxrest q hq) j hqj⟩, ?_⟩
    intro q hq' j cnt f hqj
    rw [hN]
    have := h.connAux.2 q (hsubP q hq') j cnt f hqj
    omega

-- a CONNECT at the head of the relay's queue, through the clock: the closed relay, a refused CONNECT, or a CONNECT the
-- relay takes (a free id)
theorem inv_tDoRelay_connect (T T' : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.connect id, p) :: rest) (hT : tDoRelay T = some T') : Inv T' := by
  unfold tDoRelay at hT
  simp only [hq] at hT
  simp only [Option.some.injEq] at hT
  subst hT
  have hmem := connect_head_mem T id p rest hq
  have hpos : 0 < p := h.connAux.1.2 _ hmem id rfl
  have hconnNone : ConnOf T id = none := h.connClean _ hmem id rfl
  have hcT : (T.c.rs.slot id).conn = none := hconnNone
  by_cases hcl : T.c.rs.closed.isSome = true
  · rw [stepK_closed_gen Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.connect id) hcl]
    exact inv_connect_keep T h _ _ id p rest hq [] (by simp) (by simp) rfl rfl (by simp [hpos]) rfl rfl
      h.mirror h.good
  · have hcl' : T.c.rs.closed.isSome = false := by simpa using hcl
    by_cases hk : (Clock.refill T.clk).tokens < 1000
    · obtain ⟨hR1, hR2⟩ := stepK_connect_refused Relay.DEFAULT_CAP T.clk T.c.rs id hcl' hcT hk
      have hM := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.connect id) h.mirror
      have hGd := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.connect id) h.good
      rw [hR1] at hM
      rw [hR1, hR2]
      exact inv_connect_keep T h _ _ id p rest hq _ (by simp) (by simp [Client.tagOf]) rfl rfl (by simp [hpos])
        rfl rfl hM hGd
    · have hk' : ¬ (Clock.refill T.clk).tokens < 1000 := hk
      obtain ⟨hR1, hR2⟩ := stepK_connect_taken Relay.DEFAULT_CAP T.clk T.c.rs id hcl' hcT hk'
      have hOut : (Relay.connectStep T.c.rs id).2 = [] := by
        unfold Relay.connectStep
        simp [hcT]
      exact inv_connect_create T h _ _ id p rest hq rfl rfl (by simp [hpos]) (by rw [hR2, hOut]; simp) hR1
        (Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.connect id) h.mirror)
        (Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.connect id) h.good)

end Ind
