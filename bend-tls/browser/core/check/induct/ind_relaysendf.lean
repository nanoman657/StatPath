namespace Ind
open Timed

-- a SEND at the head of the relay's queue, taken by an open connection that fails: the socket's written count goes
-- to the page (a WRITTEN of flag 0), then the failure (a FAIL); the id's connection is gone
theorem inv_relay_send_fail (T : TSys) (h : Inv T) (c' : Client.Sys) (clk' : Clock.Clk) (id n p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest) (cc : Relay.Conn)
    (hcc : (T.c.rs.slot id).conn = some cc) (e : Nat)
    (new : List (Relay.Out × Nat))
    (hnew : new = [(Relay.Out.written id cc.written 0, cc.gen), (Relay.Out.fail id e, cc.gen)])
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ new) (hng : c'.rs.nextGen = T.c.rs.nextGen)
    (hqs : ∀ j, qs j ⟨c', clk'⟩ + (if id = j then n else 0) = qs j T)
    (hcN : ∀ j c'', ConnOf ⟨c', clk'⟩ j = some c'' → j ≠ id ∧ ∃ c, ConnOf T j = some c ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed)
    (hcN1 : ∀ j c, ConnOf T j = some c → j ≠ id → ∃ c'', ConnOf ⟨c', clk'⟩ j = some c'' ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed)
    (hnone1 : ∀ j, ConnOf T j = none → ConnOf ⟨c', clk'⟩ j = none)
    (hnoneId : ConnOf ⟨c', clk'⟩ id = none)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have hmem : (Relay.Ev.send id n, p) ∈ T.c.toRelay := by
    rw [hq]
    exact List.mem_cons_self
  have hrest : rest.Sublist T.c.toRelay := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hxrest : ∀ x ∈ c'.toRelay, x ∈ T.c.toRelay := fun x hx => by
    rw [hTR] at hx
    exact hrest.subset hx
  have hsubP : ∀ q ∈ c'.toPage, q ∈ T.c.toPage ∨ q ∈ new := fun q hq' => by
    rw [hTP] at hq'
    exact List.mem_append.mp hq'
  have hPO : ∀ j, PageOf ⟨c', clk'⟩ j = PageOf T j := fun j => by
    unfold PageOf
    rw [hpg]
  have hcl' : ∀ j, (c'.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpg]
  have hconnId : ∀ c, ConnOf T id = some c → c = cc := fun c hc =>
    (Option.some.inj (hcc.symm.trans hc)).symm
  have hqneq : ∀ j, j ≠ id → qs j ⟨c', clk'⟩ = qs j T := fun j hj => by
    have := hqs j
    rw [if_neg (fun e => hj e.symm)] at this
    omega
  have hnoRep : ∀ q ∈ T.c.toPage, ∀ cnt, q.1 = Relay.Out.written id cnt 1 → False := fun q hq' cnt hqj =>
    (h.rq q hq' id cnt hqj _ hmem n rfl).elim
  -- the new frames: the two of the id, of the connection's generation
  have hnewMem : ∀ q ∈ new, (q.1 = Relay.Out.written id cc.written 0 ∧ q.2 = cc.gen) ∨
      (q.1 = Relay.Out.fail id e ∧ q.2 = cc.gen) := by
    intro q hq'
    rw [hnew] at hq'
    simp at hq'
    rcases hq' with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hfr : ∀ q ∈ new, outIdT q.1 = some id := by
    intro q hq'
    rcases hnewMem q hq' with ⟨a, -⟩ | ⟨a, -⟩ <;> simp [a, outIdT]
  have hfg : ∀ q ∈ new, q.2 = cc.gen := by
    intro q hq'
    rcases hnewMem q hq' with ⟨-, b⟩ | ⟨-, b⟩ <;> exact b
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_,
      discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_, wrSent := ?_, replyFrozen := ?_, replyMax := ?_,
      noDeny := ?_, closeUniq := ?_, connSeq := ?_ }
  · -- pi
    intro j pc hpc
    exact h.pi j pc ((hPO j).symm.trans hpc)
  · -- link
    intro j c3 hc3
    obtain ⟨hj, c, hc, hg, -⟩ := hcN j c3 hc3
    rcases h.link j c hc with ⟨pc', hpc', hm⟩ | ⟨hn, hcl2⟩
    · left
      refine ⟨pc', (hPO j).trans hpc', ?_⟩
      show (pc'.seq, c3.gen) ∈ c'.genOf
      rw [hG, hg]
      exact hm
    · right
      refine ⟨(hPO j).trans hn, ?_⟩
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact hcl2
  · -- acc
    intro j pc c3 hpc hc3 hgc
    obtain ⟨hj, c, hc, hg, -, hw1, hq1, -⟩ := hcN j c3 hc3
    have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
    have hgc' : (pc.seq, c.gen) ∈ T.c.genOf := by
      have h1 : (pc.seq, c3.gen) ∈ T.c.genOf := by
        rw [← hG]
        exact hgc
      rw [hg] at h1
      exact h1
    obtain ⟨hA, hB⟩ := h.acc j pc c hpc' hc hgc'
    have hqj := hqneq j hj
    show c3.written + c3.queued + qs j ⟨c', clk'⟩ ≤ pc.sent ∧ pc.written ≤ c3.written
    constructor <;> omega
  · -- wq
    intro j c3 hc3
    obtain ⟨hj, c, hc, -, -, -, hq1, -⟩ := hcN j c3 hc3
    have hW := h.wq j c hc
    have hqj := hqneq j hj
    show c3.queued + qs j ⟨c', clk'⟩ ≤ Relay.SEND_WINDOW
    omega
  · -- gen
    intro q hq' j hoj c3 hc3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨hj, c, hc, hg, -⟩ := hcN j c3 hc3
      rw [hg]
      exact h.gen q h1 j hoj c hc
    · obtain ⟨hj, -⟩ := hcN j c3 hc3
      have hjid : j = id := Option.some.inj (hoj.symm.trans (hfr q h1))
      exact (hj hjid).elim
  · -- apply
    intro q hq' j hcl2 hoj pc hpc
    rcases hsubP q hq' with h1 | h1
    · have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      show (c'.page.slots j).closing = true ∨ (pc.seq, q.2) ∈ c'.genOf
      rw [hcl' j, hG]
      exact h.apply q h1 j hcl2 hoj pc hpc'
    · have hjid : j = id := Option.some.inj (hoj.symm.trans (hfr q h1))
      have hpcT : PageOf T id = some pc := by
        rw [← hjid]
        exact (hPO j).symm.trans hpc
      rcases h.link id cc hcc with ⟨pc2, hpc2, hm2⟩ | ⟨hn2, -⟩
      · have hpe : pc2 = pc := Option.some.inj (hpc2.symm.trans hpcT)
        right
        rw [hfg q h1, hG, ← hpe]
        exact hm2
      · exact absurd (hpcT.symm.trans hn2) (by simp)
  · -- noOrphan
    intro q hq' j hcl2 hoj hpn
    rcases hsubP q hq' with h1 | h1
    · have hpn' : PageOf T j = none := (hPO j).symm.trans hpn
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact h.noOrphan q h1 j hcl2 hoj hpn'
    · have hjid : j = id := Option.some.inj (hoj.symm.trans (hfr q h1))
      have hpn' : PageOf T j = none := (hPO j).symm.trans hpn
      rcases h.link id cc hcc with ⟨pc2, hpc2, -⟩ | ⟨-, hcl3⟩
      · rw [hjid, hpc2] at hpn'
        cases hpn'
      · show (c'.page.slots j).closing = true
        rw [hcl' j, hjid]
        exact hcl3
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨hj, c, hc, hg, -, hw1, -, -⟩ := hcN j c3 hc3
      rw [hw1]
      exact h.written q h1 j cnt f hqj c hc (hg.symm.trans hg3)
    · obtain ⟨hj, -⟩ := hcN j c3 hc3
      have hjid : j = id := by
        have := hfr q h1
        rw [hqj] at this
        simp [outIdT] at this
        omega
      exact (hj hjid).elim
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hgq c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨hj, c, hc, hg, -, hw1, hq1, -⟩ := hcN j c3 hc3
      have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rw [← hG]
        exact hgq
      obtain ⟨r1, r2, r3⟩ := h.reset q h1 j cnt hqj pc hpc' hdp hgq' c hc (hg.symm.trans hg3)
      have hqj2 := hqneq j hj
      show c3.queued = 0 ∧ qs j ⟨c', clk'⟩ = 0 ∧ c3.written = cnt
      exact ⟨by omega, by omega, by omega⟩
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- barrier
    show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) c'.toRelay
    rw [hTR]
    exact List.Pairwise.sublist hrest h.barrier
  · -- connClean
    intro x hx j hxj
    by_cases hj : j = id
    · rw [hj]
      exact hnoneId
    · exact hnone1 j (h.connClean x (hxrest x hx) j hxj)
  · -- notOpen
    intro j pc hpc hop
    exact h.notOpen j pc ((hPO j).symm.trans hpc) hop
  · -- cl
    intro x hx j hxj
    rcases h.cl x (hxrest x hx) j hxj with ⟨pc, hpc, hs⟩ | ⟨hn, hcl2⟩
    · left
      exact ⟨pc, (hPO j).trans hpc, hs⟩
    · right
      refine ⟨(hPO j).trans hn, ?_⟩
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact hcl2
  · -- rq
    intro q hq' j cnt hqj x hx n'
    rcases hsubP q hq' with h1 | h1
    · exact h.rq q h1 j cnt hqj x (hxrest x hx) n'
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- gensLt
    intro j c3 hc3
    obtain ⟨-, c, hc, hg, -⟩ := hcN j c3 hc3
    show c3.gen < c'.rs.nextGen
    rw [hng, hg]
    exact h.gensLt j c hc
  · -- gp
    intro x hx j hxj g
    show (x.2, g) ∉ c'.genOf
    rw [hG]
    exact h.gp x (hxrest x hx) j hxj g
  · -- openG
    intro j pc hpc hop
    show ∃ g, (pc.seq, g) ∈ c'.genOf
    rw [hG]
    exact h.openG j pc ((hPO j).symm.trans hpc) hop
  · -- mirror
    exact hM
  · -- good
    exact hGd
  · -- seqG
    intro p' g hpg'
    show p' < c'.page.nextSeq
    rw [hpg]
    exact h.seqG p' g (by rw [← hG]; exact hpg')
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
      · left
        exact ⟨pc, (hPO j).trans hpc, hdp⟩
      · right
        refine ⟨(hPO j).trans hn, ?_⟩
        show (c'.page.slots j).closing = true
        rw [hcl' j]
        exact hcl2
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- recvG
    intro j pc hpc hr0
    show ∃ g, (pc.seq, g) ∈ c'.genOf
    rw [hG]
    exact h.recvG j pc ((hPO j).symm.trans hpc) hr0
  · -- failNone
    intro q hq' j e' hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.failNone q h1 j e' hqj)
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩
      · simp [hqa] at hqj
      · rw [hqa] at hqj
        obtain ⟨rfl, -⟩ := Relay.Out.fail.inj hqj
        exact hnoneId
  · -- closedNone
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.closedNone q h1 j hqj)
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- closedClosing
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact h.closedClosing q h1 j hqj
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- closedOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.closedOrd, by rw [hnew]; simp,
      fun a ha b hb id' hpa hob => ?_⟩
    have hid : id = id' := Option.some.inj ((hfr b hb).symm.trans hob)
    have h1 : (T.c.rs.slot id').conn = none := h.closedNone a ha id' hpa
    rw [← hid, hcc] at h1
    cases h1
  · -- closeClosing
    intro x hx j hxj
    show (c'.page.slots j).closing = true
    rw [hcl' j]
    exact h.closeClosing x (hxrest x hx) j hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNoConn q h1 j hqj x (hxrest x hx)
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- openRel
    intro j pc hpc hop c3 hc3
    obtain ⟨hj, c, hc, -, ho, -, -, -⟩ := hcN j c3 hc3
    rw [ho]
    exact h.openRel j pc ((hPO j).symm.trans hpc) hop c hc
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    rcases hsubP q hq' with h1 | h1
    · exact h.okOpen q h1 j hqj ((hcl' j).symm.trans hcl2) pc ((hPO j).symm.trans hpc)
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.okNoDisc q h1 j hqj ((hcl' j).symm.trans hcl2) x (hxrest x hx)
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- discRel
    intro x hx j hxj
    rcases h.discRel x (hxrest x hx) j hxj with hn | ⟨pc, hpc, hop⟩ | ⟨hn, hcl2⟩
    · exact Or.inl (hnone1 j hn)
    · exact Or.inr (Or.inl ⟨pc, (hPO j).trans hpc, hop⟩)
    · refine Or.inr (Or.inr ⟨(hPO j).trans hn, ?_⟩)
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact hcl2
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
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- failOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.failOrd, by rw [hnew]; simp,
      fun a ha b hb id' e' hpf hob => ?_⟩
    have hid : id = id' := Option.some.inj ((hfr b hb).symm.trans hob)
    have h1 : (T.c.rs.slot id').conn = none := h.failNone a ha id' e' hpf
    rw [← hid, hcc] at h1
    cases h1
  · -- connPend
    intro x hx j hxj q hq'
    rcases hsubP q hq' with h1 | h1
    · exact h.connPend x (hxrest x hx) j hxj q h1
    · intro hj'
      have hjid : id = j := Option.some.inj ((hfr q h1).symm.trans hj')
      have h3 : (T.c.rs.slot j).conn = none := h.connClean x (hxrest x hx) j hxj
      rw [← hjid, hcc] at h3
      cases h3
  · -- okRel
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · by_cases hj : j = id
      · exact Or.inl (by rw [hj]; exact hnoneId)
      · rcases h.okRel q h1 j hqj with hn | ⟨c, hc, hgc, hop⟩
        · exact Or.inl (hnone1 j hn)
        · obtain ⟨c'', hc'', hg, ho, -, -, -⟩ := hcN1 j c hc hj
          exact Or.inr ⟨c'', hc'', hg.trans hgc, ho.trans hop⟩
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- okOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.okOrd, by rw [hnew]; simp,
      fun a ha b hb id' _ hbo => ?_⟩
    rcases hnewMem b hb with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hbo
  · -- discOnce
    intro q hq' j cnt hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.discOnce q h1 j cnt hqj x (hxrest x hx)
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- discUniq
    intro id'
    show ((c'.toPage).filter (DiscRep id')).length ≤ 1
    have hN : ∀ x ∈ new, DiscRep id' x = false := by
      intro x hx
      rcases hnewMem x hx with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa, DiscRep]
    rw [hTP, count_app_nil _ _ _ hN]
    exact h.discUniq id'
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hgq
    rcases hsubP q hq' with h1 | h1
    · exact h.wrMono q h1 j cnt f hqj pc ((hPO j).symm.trans hpc) (by rw [← hG]; exact hgq)
    · rcases hnewMem q h1 with ⟨hqa, hqb⟩ | ⟨hqa, -⟩
      · rw [hqa] at hqj
        obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj
        have hpc' : PageOf T id = some pc := (hPO id).symm.trans hpc
        have hg2 : (pc.seq, cc.gen) ∈ T.c.genOf := by
          rw [← hqb, ← hG]
          exact hgq
        obtain ⟨-, hB⟩ := h.acc id pc cc hpc' hcc hg2
        omega
      · simp [hqa] at hqj
  · -- wrOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.wrOrd, by rw [hnew]; simp,
      fun a ha b hb id' c1 f1 c2 f2 hap hbw hag => ?_⟩
    rcases hnewMem b hb with ⟨hqa, hqb⟩ | ⟨hqa, -⟩
    · rw [hqa] at hbw
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hbw
      have hc1 := h.written a ha id c1 f1 hap cc hcc ((hag.trans hqb).symm)
      omega
    · simp [hqa] at hbw
  · -- genFun
    intro p g1 g2 h1 h2
    have h1' : (p, g1) ∈ T.c.genOf := by
      rw [← hG]
      exact h1
    have h2' : (p, g2) ∈ T.c.genOf := by
      rw [← hG]
      exact h2
    exact h.genFun p g1 g2 h1' h2'
  · -- wrSent
    intro q hq' j cnt f hqj pc hpc hgq
    rcases hsubP q hq' with h1 | h1
    · exact h.wrSent q h1 j cnt f hqj pc ((hPO j).symm.trans hpc) (by rw [← hG]; exact hgq)
    · rcases hnewMem q h1 with ⟨hqa, hqb⟩ | ⟨hqa, -⟩
      · rw [hqa] at hqj
        obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj
        have hpc' : PageOf T id = some pc := (hPO id).symm.trans hpc
        have hg2 : (pc.seq, cc.gen) ∈ T.c.genOf := by
          rw [← hqb, ← hG]
          exact hgq
        obtain ⟨hA, -⟩ := h.acc id pc cc hpc' hcc hg2
        omega
      · simp [hqa] at hqj
  · -- replyFrozen
    intro q hq' j cnt hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨hj, c, hc, hg, -, hw1, hq1, -⟩ := hcN j c3 hc3
      obtain ⟨r1, r2⟩ := h.replyFrozen q h1 j cnt hqj c hc (hg.symm.trans hg3)
      exact ⟨by omega, by omega⟩
    · rcases hnewMem q h1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at hqj
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    rcases hsubP q hq' with hq1 | hq1
    · rcases hsubP r hr with hr1 | hr1
      · exact h.replyMax q hq1 r hr1 j c1 c2 f h1 h2 hg
      · rcases hnewMem r hr1 with ⟨hra, -⟩ | ⟨hra, -⟩
        · rw [hra] at h2
          obtain ⟨rfl, -, -⟩ := Relay.Out.written.inj h2
          exact (hnoRep q hq1 c1 h1).elim
        · simp [hra] at h2
    · rcases hnewMem q hq1 with ⟨hqa, -⟩ | ⟨hqa, -⟩ <;> simp [hqa] at h1
  · -- noDeny
    intro x hx
    exact h.noDeny x (hxrest x hx)
  · -- closeUniq
    intro j
    show ((c'.toRelay).filter (CloseIs j)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest (h.closeUniq j)
  · -- connSeq
    intro s
    show ((c'.toRelay).filter (ConnSeqIs s)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest (h.connSeq s)

end Ind
