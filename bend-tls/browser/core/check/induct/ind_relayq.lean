namespace Ind
open Timed

-- a frame with no id is never a discard reply
theorem discRep_none (id : Nat) (x : Relay.Out × Nat) (h : outIdT x.1 = none) : DiscRep id x = false := by
  rcases x with ⟨o, n⟩
  cases o <;> simp_all [DiscRep, outIdT]

-- a property of a queue that holds for the queue's pairs, and for pairs whose second frame has no id, appends
theorem pw_append_none {α : Type} (R : α → α → Prop) (noId : α → Prop) (L new : List α) (hL : L.Pairwise R)
    (hN : ∀ b ∈ new, noId b) (hV : ∀ a b, noId b → R a b) : (L ++ new).Pairwise R := by
  rw [List.pairwise_append]
  exact ⟨hL, pairwise_of_forall R new (fun a ha b hb => hV a b (hN b hb)), fun a _ b hb => hV a b (hN b hb)⟩

-- a relay step that keeps every connection's data (generation, open flag, counts, the peer's close) and the page
-- and genOf map, and that adds only id-less frames to the page's queue
theorem inv_relay_keep (T : TSys) (h : Inv T) (c' : Client.Sys) (clk' : Clock.Clk) (e : Relay.Ev) (p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (e, p) :: rest) (new : List (Relay.Out × Nat))
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ new) (hnew : ∀ q ∈ new, outIdT q.1 = none)
    (hng : c'.rs.nextGen = T.c.rs.nextGen) (hqs : ∀ j, qs j ⟨c', clk'⟩ ≤ qs j T)
    (hconn1 : ∀ j c, ConnOf T j = some c → ∃ c'', ConnOf ⟨c', clk'⟩ j = some c'' ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed)
    (hconn2 : ∀ j c'', ConnOf ⟨c', clk'⟩ j = some c'' → ∃ c, ConnOf T j = some c ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed)
    (hnone1 : ∀ j, ConnOf T j = none → ConnOf ⟨c', clk'⟩ j = none)
    (hnone2 : ∀ j, ConnOf ⟨c', clk'⟩ j = none → ConnOf T j = none)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
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
  have hcl : ∀ j, (c'.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpg]
  have hsnd : ∀ id, (new.filter (DiscRep id)).length = 0 := fun id => by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx hxt
    rw [discRep_none id x (hnew x hx)] at hxt
    cases hxt
  have hcount : ∀ id, (c'.toPage.filter (DiscRep id)).length = (T.c.toPage.filter (DiscRep id)).length := by
    intro id
    rw [hTP, List.filter_append, List.length_append, hsnd id, Nat.add_zero]
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_,
      discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_, wrSent := ?_, replyFrozen := ?_, replyMax := ?_,
      noDeny := ?_, closeUniq := ?closeUniq, connSeq := ?connSeq, connAux := ?connAux }
  case closeUniq =>
    intro j
    show ((c'.toRelay).filter (CloseIs j)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest (h.closeUniq j)
  case connSeq =>
    intro s
    show ((c'.toRelay).filter (ConnSeqIs s)).length ≤ 1
    rw [hTR]
    exact count_le_sub _ _ _ hrest (h.connSeq s)
  case connAux =>
    refine ⟨⟨by rw [hpg]; exact h.connAux.1.1, fun q hq id hqid => h.connAux.1.2 q (hxrest q hq) id hqid⟩, ?_⟩
    intro q hq id cnt f hqf
    rw [hTP] at hq
    rcases List.mem_append.mp hq with h1 | h1
    · rw [hng]
      exact h.connAux.2 q h1 id cnt f hqf
    · have h2 := hnew q h1
      rw [hqf] at h2
      simp [outIdT] at h2
  · -- pi
    intro j pc hpc
    exact h.pi j pc ((hPO j).symm.trans hpc)
  · -- link
    intro j c3 hc3
    obtain ⟨c, hc, hg, -⟩ := hconn2 j c3 hc3
    rcases h.link j c hc with ⟨pc, hpc, hm⟩ | ⟨hn, hcl2⟩
    · left
      refine ⟨pc, (hPO j).trans hpc, ?_⟩
      have hm' : (pc.seq, c3.gen) ∈ T.c.genOf := by
        rw [hg]
        exact hm
      show (pc.seq, c3.gen) ∈ c'.genOf
      rw [hG]
      exact hm'
    · right
      refine ⟨(hPO j).trans hn, ?_⟩
      show (c'.page.slots j).closing = true
      rw [hcl j]
      exact hcl2
  · -- acc
    intro j pc c3 hpc hc3 hgc
    obtain ⟨c, hc, hg, -, hw, hq1, -⟩ := hconn2 j c3 hc3
    have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
    have hgc' : (pc.seq, c.gen) ∈ T.c.genOf := by
      have h1 : (pc.seq, c3.gen) ∈ T.c.genOf := by
        rw [← hG]
        exact hgc
      rw [hg] at h1
      exact h1
    obtain ⟨hA, hB⟩ := h.acc j pc c hpc' hc hgc'
    show c3.written + c3.queued + qs j ⟨c', clk'⟩ ≤ pc.sent ∧ pc.written ≤ c3.written
    have hqj := hqs j
    rw [hw, hq1]
    exact ⟨by omega, hB⟩
  · -- wq
    intro j c3 hc3
    obtain ⟨c, hc, -, -, -, hq1, -⟩ := hconn2 j c3 hc3
    show c3.queued + qs j ⟨c', clk'⟩ ≤ Relay.SEND_WINDOW
    have hqj := hqs j
    rw [hq1]
    have := h.wq j c hc
    omega
  · -- gen
    intro q hq' j hoj c3 hc3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -⟩ := hconn2 j c3 hc3
      rw [hg]
      exact h.gen q h1 j hoj c hc
    · exact absurd (hnew q h1) (by rw [hoj]; simp)
  · -- apply
    intro q hq' j hcl' hoj pc hpc
    rcases hsubP q hq' with h1 | h1
    · have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      show (c'.page.slots j).closing = true ∨ (pc.seq, q.2) ∈ c'.genOf
      rw [hcl j, hG]
      exact h.apply q h1 j hcl' hoj pc hpc'
    · exact absurd (hnew q h1) (by rw [hoj]; simp)
  · -- noOrphan
    intro q hq' j hcl' hoj hpn
    rcases hsubP q hq' with h1 | h1
    · have hpn' : PageOf T j = none := (hPO j).symm.trans hpn
      show (c'.page.slots j).closing = true
      rw [hcl j]
      exact h.noOrphan q h1 j hcl' hoj hpn'
    · exact absurd (hnew q h1) (by rw [hoj]; simp)
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -, hw, -, -⟩ := hconn2 j c3 hc3
      rw [hw]
      exact h.written q h1 j cnt f hqj c hc (hg.symm.trans hg3)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hgq c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -, hw, hq1, -⟩ := hconn2 j c3 hc3
      have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rw [← hG]
        exact hgq
      obtain ⟨r1, r2, r3⟩ := h.reset q h1 j cnt hqj pc hpc' hdp hgq' c hc (hg.symm.trans hg3)
      show c3.queued = 0 ∧ qs j ⟨c', clk'⟩ = 0 ∧ c3.written = cnt
      rw [hq1, hw]
      have hqj := hqs j
      exact ⟨r1, by omega, r3⟩
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- barrier
    show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) c'.toRelay
    rw [hTR]
    exact List.Pairwise.sublist hrest h.barrier
  · -- connClean
    intro x hx j hxj
    exact hnone1 j (h.connClean x (hxrest x hx) j hxj)
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
      rw [hcl j]
      exact hcl2
  · -- rq
    intro q hq' j cnt hqj x hx n
    rcases hsubP q hq' with h1 | h1
    · exact h.rq q h1 j cnt hqj x (hxrest x hx) n
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- gensLt
    intro j c3 hc3
    obtain ⟨c, hc, hg, -⟩ := hconn2 j c3 hc3
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
    intro p g hpg'
    show p < c'.page.nextSeq
    rw [hpg]
    exact h.seqG p g (by rw [← hG]; exact hpg')
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
        rw [hcl j]
        exact hcl2
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- recvG
    intro j pc hpc hr0
    show ∃ g, (pc.seq, g) ∈ c'.genOf
    rw [hG]
    exact h.recvG j pc ((hPO j).symm.trans hpc) hr0
  · -- failNone
    intro q hq' j eo hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.failNone q h1 j eo hqj)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- closedNone
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.closedNone q h1 j hqj)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- closedClosing
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · show (c'.page.slots j).closing = true
      rw [hcl j]
      exact h.closedClosing q h1 j hqj
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- closedOrd
    rw [hTP]
    exact pw_append_none _ (fun x => outIdT x.1 = none) T.c.toPage new h.closedOrd (fun b hb => hnew b hb)
      (fun a b hb id _ h2 => by simp [hb] at h2)
  · -- closeClosing
    intro x hx j hxj
    show (c'.page.slots j).closing = true
    rw [hcl j]
    exact h.closeClosing x (hxrest x hx) j hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNoConn q h1 j hqj x (hxrest x hx)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- openRel
    intro j pc hpc hop c3 hc3
    obtain ⟨c, hc, -, hop', -⟩ := hconn2 j c3 hc3
    rw [hop']
    exact h.openRel j pc ((hPO j).symm.trans hpc) hop c hc
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    rcases hsubP q hq' with h1 | h1
    · exact h.okOpen q h1 j hqj ((hcl j).symm.trans hcl2) pc ((hPO j).symm.trans hpc)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.okNoDisc q h1 j hqj ((hcl j).symm.trans hcl2) x (hxrest x hx)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- discRel
    intro x hx j hxj
    rcases h.discRel x (hxrest x hx) j hxj with hn | ⟨pc, hpc, hop⟩ | ⟨hn, hcl2⟩
    · exact Or.inl (hnone1 j hn)
    · exact Or.inr (Or.inl ⟨pc, (hPO j).trans hpc, hop⟩)
    · refine Or.inr (Or.inr ⟨(hPO j).trans hn, ?_⟩)
      show (c'.page.slots j).closing = true
      rw [hcl j]
      exact hcl2
  · -- closingNone
    intro j hcl'
    have hcl'' : (T.c.page.slots j).closing = true := by
      rw [← hcl j]
      exact hcl'
    show (c'.page.slots j).conn = none
    rw [hpg]
    exact h.closingNone j hcl''
  · -- closedNoClose
    intro q hq' j hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNoClose q h1 j hqj x (hxrest x hx)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- failOrd
    rw [hTP]
    exact pw_append_none _ (fun x => outIdT x.1 = none) T.c.toPage new h.failOrd (fun b hb => hnew b hb)
      (fun a b hb id e _ h2 => by simp [hb] at h2)
  · -- connPend
    intro x hx j hxj q hq'
    rcases hsubP q hq' with h1 | h1
    · exact h.connPend x (hxrest x hx) j hxj q h1
    · rw [hnew q h1]
      simp
  · -- okRel
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · rcases h.okRel q h1 j hqj with hn | ⟨c, hc, hgc, hop⟩
      · exact Or.inl (hnone1 j hn)
      · obtain ⟨c'', hc'', hg, hop', -, -, -⟩ := hconn1 j c hc
        exact Or.inr ⟨c'', hc'', hg.trans hgc, hop'.trans hop⟩
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- okOrd
    rw [hTP]
    exact pw_append_none _ (fun x => outIdT x.1 = none) T.c.toPage new h.okOrd (fun b hb => hnew b hb)
      (fun a b hb id _ h2 => by rw [h2] at hb; simp [outIdT] at hb)
  · -- discOnce
    intro q hq' j cnt hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.discOnce q h1 j cnt hqj x (hxrest x hx)
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- discUniq
    intro id
    show (c'.toPage.filter (DiscRep id)).length ≤ 1
    rw [hcount id]
    exact h.discUniq id
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hgq
    rcases hsubP q hq' with h1 | h1
    · have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rw [← hG]
        exact hgq
      exact h.wrMono q h1 j cnt f hqj pc ((hPO j).symm.trans hpc) hgq'
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- wrOrd
    rw [hTP]
    exact pw_append_none _ (fun x => outIdT x.1 = none) T.c.toPage new h.wrOrd (fun b hb => hnew b hb)
      (fun a b hb id c1 f1 c2 f2 _ h2 _ => by rw [h2] at hb; simp [outIdT] at hb)
  · -- genFun
    intro p g1 g2 h1' h2'
    have h1'' : (p, g1) ∈ T.c.genOf := by
      rw [← hG]
      exact h1'
    have h2'' : (p, g2) ∈ T.c.genOf := by
      rw [← hG]
      exact h2'
    exact h.genFun p g1 g2 h1'' h2''
  · -- wrSent
    intro q hq' j cnt f hqj pc hpc hgq
    rcases hsubP q hq' with h1 | h1
    · have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rw [← hG]
        exact hgq
      exact h.wrSent q h1 j cnt f hqj pc ((hPO j).symm.trans hpc) hgq'
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- replyFrozen
    intro q hq' j cnt hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -, hw, hq1, -⟩ := hconn2 j c3 hc3
      obtain ⟨r1, r2⟩ := h.replyFrozen q h1 j cnt hqj c hc (hg.symm.trans hg3)
      rw [hq1, hw]
      exact ⟨r1, r2⟩
    · exact absurd (hnew q h1) (by rw [hqj]; simp [outIdT])
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    rcases hsubP q hq' with h1' | h1'
    · rcases hsubP r hr with h2' | h2'
      · exact h.replyMax q h1' r h2' j c1 c2 f h1 h2 hg
      · exact absurd (hnew r h2') (by rw [h2]; simp [outIdT])
    · exact absurd (hnew q h1') (by rw [h1]; simp [outIdT])
  · -- noDeny
    intro x hx
    exact h.noDeny x (hxrest x hx)

-- the relay's slot update, and the protocol close, as the relay's slots see them
theorem setConn_conn (s : Relay.St) (id j : Nat) (c : Option Relay.Conn) :
    ((Relay.setConn s id c).slot j).conn = if j = id then c else (s.slot j).conn := by
  unfold Relay.setConn Relay.setSlot Relay.St.slot
  by_cases hj : j = id
  · simp [hj]
  · simp [hj]

theorem protoClose_slot (s : Relay.St) (code j : Nat) :
    ((Relay.protoClose s code).1.slot j) = s.slot j := by
  unfold Relay.protoClose Relay.St.slot
  rfl

theorem protoClose_nextGen (s : Relay.St) (code : Nat) : (Relay.protoClose s code).1.nextGen = s.nextGen := rfl

-- a READ keeps every connection's data (its read window moves, nothing else)
theorem read_slot_data (cap : Nat) (s : Relay.St) (id k j : Nat) (c : Relay.Conn) (hc : (s.slot j).conn = some c) :
    ∃ c'', ((Relay.step cap s (Relay.Ev.read id k)).1.slot j).conn = some c'' ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed := by
  unfold Relay.step
  split
  · exact ⟨c, hc, rfl, rfl, rfl, rfl, rfl⟩
  · unfold Relay.readStep
    rcases hs : (s.slot id).conn with _ | c0
    · simp only [hs]
      split
      · exact ⟨c, hc, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨c, by rw [protoClose_slot]; exact hc, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [hs]
      split
      · exact ⟨c, by rw [protoClose_slot]; exact hc, rfl, rfl, rfl, rfl, rfl⟩
      · by_cases hj : j = id
        · subst hj
          have hcc : c0 = c := Option.some.inj (hs.symm.trans hc)
          subst hcc
          refine ⟨{ c0 with gr := min (c0.rd + Relay.READ_WINDOW) (c0.gr + k) }, ?_, rfl, rfl, rfl, rfl, rfl⟩
          rw [setConn_conn]
          simp
        · refine ⟨c, ?_, rfl, rfl, rfl, rfl, rfl⟩
          rw [setConn_conn, if_neg hj]
          exact hc

-- and a READ leaves a connection-less id connection-less
theorem read_slot_none (cap : Nat) (s : Relay.St) (id k j : Nat) (hc : (s.slot j).conn = none) :
    ((Relay.step cap s (Relay.Ev.read id k)).1.slot j).conn = none := by
  unfold Relay.step
  split
  · exact hc
  · unfold Relay.readStep
    rcases hs : (s.slot id).conn with _ | c0
    · simp only [hs]
      split
      · exact hc
      · rw [protoClose_slot]
        exact hc
    · simp only [hs]
      split
      · rw [protoClose_slot]
        exact hc
      · by_cases hj : j = id
        · subst hj
          rw [hs] at hc
          cases hc
        · rw [setConn_conn, if_neg hj]
          exact hc

theorem read_nextGen (cap : Nat) (s : Relay.St) (id k : Nat) :
    (Relay.step cap s (Relay.Ev.read id k)).1.nextGen = s.nextGen := by
  unfold Relay.step
  split
  · rfl
  · unfold Relay.readStep
    rcases hs : (s.slot id).conn with _ | c0
    · simp only [hs]
      split
      · rfl
      · rfl
    · simp only [hs]
      split
      · rfl
      · rfl

-- a READ's frames carry no id
theorem read_outs_noid (cap : Nat) (s : Relay.St) (id k : Nat) :
    ∀ o ∈ (Relay.step cap s (Relay.Ev.read id k)).2, outIdT o = none := by
  intro o ho
  unfold Relay.step at ho
  split at ho
  · simp at ho
  · unfold Relay.readStep at ho
    rcases hs : (s.slot id).conn with _ | c0 <;> simp only [hs] at ho
    · split at ho
      · simp at ho
      · simp [Relay.protoClose] at ho
        subst ho
        rfl
    · split at ho
      · simp [Relay.protoClose] at ho
        subst ho
        rfl
      · simp at ho

theorem stepK_read_rs (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) :
    (Clock.stepK cap k s (Relay.Ev.read id g)).2.1 = (Relay.step cap s (Relay.Ev.read id g)).1 := by
  unfold Clock.stepK
  by_cases hcl : s.closed.isSome = true
  · simp [hcl, Relay.step]
  · simp [hcl, Relay.step]

theorem stepK_read_outs (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id g : Nat) :
    (Clock.stepK cap k s (Relay.Ev.read id g)).2.2 = (Relay.step cap s (Relay.Ev.read id g)).2 := by
  unfold Clock.stepK
  by_cases hcl : s.closed.isSome = true
  · simp [hcl, Relay.step]
  · simp [hcl, Relay.step]

-- the READ at the head of the relay's queue: the relay takes it, the page hears only id-less frames, and the queue
-- loses its head
theorem inv_tDoRelay_read (T T' : TSys) (h : Inv T) (id k p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.read id k, p) :: rest) (hT : tDoRelay T = some T') : Inv T' := by
  unfold tDoRelay at hT
  simp only [hq] at hT
  simp only [Option.some.injEq] at hT
  subst hT
  refine inv_relay_keep T h _ _ (Relay.Ev.read id k) p rest hq
    ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k)).2.2.map
      (fun o => (o, Client.tagOf T.c.rs (Relay.Ev.read id k)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · intro q hq'
    rw [List.mem_map] at hq'
    obtain ⟨o, ho, rfl⟩ := hq'
    rw [stepK_read_outs] at ho
    exact read_outs_noid _ _ _ _ o ho
  · show (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k)).2.1.nextGen = T.c.rs.nextGen
    rw [stepK_read_rs, read_nextGen]
  · intro j
    show qsumT j rest ≤ qs j T
    unfold qs
    rw [hq]
    simp [qsumT]
  · intro j c hc
    obtain ⟨c'', hc'', hg, ho, hw, hq1, hp⟩ := read_slot_data Relay.DEFAULT_CAP T.c.rs id k j c hc
    refine ⟨c'', ?_, hg, ho, hw, hq1, hp⟩
    show ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k)).2.1.slot j).conn = some c''
    rw [stepK_read_rs]
    exact hc''
  · intro j c'' hc''
    change ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k)).2.1.slot j).conn = some c'' at hc''
    rw [stepK_read_rs] at hc''
    rcases hcj : (T.c.rs.slot j).conn with _ | c
    · have hn := read_slot_none Relay.DEFAULT_CAP T.c.rs id k j hcj
      rw [hn] at hc''
      cases hc''
    · obtain ⟨c2, hc2, hg, ho, hw, hq1, hp⟩ := read_slot_data Relay.DEFAULT_CAP T.c.rs id k j c hcj
      rw [hc2] at hc''
      have hcc : c2 = c'' := Option.some.inj hc''
      subst hcc
      exact ⟨c, hcj, hg, ho, hw, hq1, hp⟩
  · intro j hn
    change (T.c.rs.slot j).conn = none at hn
    change ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k)).2.1.slot j).conn = none
    rw [stepK_read_rs]
    exact read_slot_none Relay.DEFAULT_CAP T.c.rs id k j hn
  · intro j hn
    change ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k)).2.1.slot j).conn = none at hn
    rw [stepK_read_rs] at hn
    show (T.c.rs.slot j).conn = none
    rcases hcj : (T.c.rs.slot j).conn with _ | c
    · rfl
    · obtain ⟨c2, hc2, -⟩ := read_slot_data Relay.DEFAULT_CAP T.c.rs id k j c hcj
      rw [hc2] at hn
      cases hn
  · exact Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k) h.mirror
  · exact Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.read id k) h.good

end Ind
