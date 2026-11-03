namespace Ind
open Timed

-- two elements with a predicate in a list whose head and one later element both have it: the count is at least two
theorem two_filter {α : Type} (p : α → Bool) (a : α) (rest : List α) (q : α) (hq : q ∈ rest) (ha : p a = true)
    (hqb : p q = true) : 2 ≤ ((a :: rest).filter p).length := by
  rw [List.filter_cons_of_pos ha]
  simp only [List.length_cons]
  have : 0 < (rest.filter p).length := List.length_pos_of_mem (List.mem_filter.mpr ⟨hq, hqb⟩)
  omega

-- a list of at most one element is pairwise related by anything
theorem pairwise_le_one {α : Type} (R : α → α → Prop) : ∀ (L : List α), L.length ≤ 1 → L.Pairwise R
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton R a
  | _ :: _ :: _, h => absurd h (by simp)

-- a CLOSE at the head of the relay's queue, and the relay's connection of its id is taken down (the page's frame
-- is CLOSED); the rest of the queue has no CONNECT and no other CLOSE of the id
theorem inv_relay_close (T : TSys) (h : Inv T) (c' : Client.Sys) (clk' : Clock.Clk) (id p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (Relay.Ev.close id, p) :: rest)
    (new : List (Relay.Out × Nat)) (hnewC : new = [] ∨ ∃ t, new = [(Relay.Out.closed id, t)])
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ new)
    (hng : c'.rs.nextGen = T.c.rs.nextGen) (hqs : ∀ j, qs j ⟨c', clk'⟩ = qs j T)
    (hconn1 : ∀ j c, j ≠ id → ConnOf T j = some c → ∃ c'', ConnOf ⟨c', clk'⟩ j = some c'' ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed)
    (hconn2 : ∀ j c'', ConnOf ⟨c', clk'⟩ j = some c'' → j ≠ id ∧ ∃ c, ConnOf T j = some c ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.queued = c.queued ∧ c''.peerClosed = c.peerClosed)
    (hgone : ConnOf ⟨c', clk'⟩ id = none)
    (hnone1 : ∀ j, ConnOf T j = none → ConnOf ⟨c', clk'⟩ j = none)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have hmem : (Relay.Ev.close id, p) ∈ T.c.toRelay := by
    rw [hq]
    exact List.mem_cons_self
  have hcl : (T.c.page.slots id).closing = true := h.closeClosing _ hmem id rfl
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
  -- the rest of the queue: no CONNECT of the id (the barrier), no other CLOSE of it (closeUniq)
  have hnoConn : ∀ y ∈ rest, y.1 ≠ Relay.Ev.connect id := by
    intro y hy hyc
    have hb := h.barrier
    rw [hq] at hb
    have h1 := (List.pairwise_cons.mp hb).1 y hy
    rw [hyc] at h1
    exact h1 (by simp [FwdEv])
  have hnoClose : ∀ y ∈ rest, CloseIs id y = false := by
    intro y hy
    cases hcy : CloseIs id y with
    | false => rfl
    | true =>
      have h1 := h.closeUniq id
      rw [hq] at h1
      have := two_filter (CloseIs id) (Relay.Ev.close id, p) rest y hy (by simp [CloseIs]) hcy
      omega
  -- the new frames: at most one CLOSED of the id
  have hnewL : new.length ≤ 1 := by
    rcases hnewC with rfl | ⟨t, rfl⟩ <;> simp
  have hnewP : ∀ q ∈ new, q.1 = Relay.Out.closed id := by
    intro q hq'
    rcases hnewC with rfl | ⟨t, rfl⟩
    · cases hq'
    · rw [List.mem_singleton] at hq'
      rw [hq']
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
    obtain ⟨-, c, hc, hg, -⟩ := hconn2 j c3 hc3
    rcases h.link j c hc with ⟨pc, hpc, hm⟩ | ⟨hn, hcl2⟩
    · left
      refine ⟨pc, (hPO j).trans hpc, ?_⟩
      show (pc.seq, c3.gen) ∈ c'.genOf
      rw [hG, hg]
      exact hm
    · right
      refine ⟨(hPO j).trans hn, ?_⟩
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact hcl2
  · -- acc
    intro j pc c3 hpc hc3 hgc
    obtain ⟨-, c, hc, hg, -, hw, hq1, -⟩ := hconn2 j c3 hc3
    have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
    have hgc' : (pc.seq, c.gen) ∈ T.c.genOf := by
      have h1 : (pc.seq, c3.gen) ∈ T.c.genOf := by
        rw [← hG]
        exact hgc
      rw [hg] at h1
      exact h1
    obtain ⟨hA, hB⟩ := h.acc j pc c hpc' hc hgc'
    show c3.written + c3.queued + qs j ⟨c', clk'⟩ ≤ pc.sent ∧ pc.written ≤ c3.written
    rw [hqs j, hw, hq1]
    exact ⟨hA, hB⟩
  · -- wq
    intro j c3 hc3
    obtain ⟨-, c, hc, -, -, -, hq1, -⟩ := hconn2 j c3 hc3
    show c3.queued + qs j ⟨c', clk'⟩ ≤ Relay.SEND_WINDOW
    rw [hqs j, hq1]
    exact h.wq j c hc
  · -- gen
    intro q hq' j hoj c3 hc3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨-, c, hc, hg, -⟩ := hconn2 j c3 hc3
      rw [hg]
      exact h.gen q h1 j hoj c hc
    · rw [hnewP q h1] at hoj
      simp [outIdT] at hoj
      subst hoj
      rw [hgone] at hc3
      cases hc3
  · -- apply
    intro q hq' j hcl2 hoj pc hpc
    rcases hsubP q hq' with h1 | h1
    · have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      show (c'.page.slots j).closing = true ∨ (pc.seq, q.2) ∈ c'.genOf
      rw [hcl' j, hG]
      exact h.apply q h1 j hcl2 hoj pc hpc'
    · rw [hnewP q h1] at hcl2
      simp [isClosedOut] at hcl2
  · -- noOrphan
    intro q hq' j hcl2 hoj hpn
    rcases hsubP q hq' with h1 | h1
    · have hpn' : PageOf T j = none := (hPO j).symm.trans hpn
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact h.noOrphan q h1 j hcl2 hoj hpn'
    · rw [hnewP q h1] at hcl2
      simp [isClosedOut] at hcl2
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨-, c, hc, hg, -, hw, -⟩ := hconn2 j c3 hc3
      rw [hw]
      exact h.written q h1 j cnt f hqj c hc (hg.symm.trans hg3)
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hgq c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨-, c, hc, hg, -, hw, hq1, -⟩ := hconn2 j c3 hc3
      have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
        rw [← hG]
        exact hgq
      obtain ⟨r1, r2, r3⟩ := h.reset q h1 j cnt hqj pc hpc' hdp hgq' c hc (hg.symm.trans hg3)
      show c3.queued = 0 ∧ qs j ⟨c', clk'⟩ = 0 ∧ c3.written = cnt
      rw [hq1, hw, hqs j]
      exact ⟨r1, r2, r3⟩
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- barrier
    show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) c'.toRelay
    rw [hTR]
    exact List.Pairwise.sublist hrest h.barrier
  · -- connClean
    intro x hx j hxj
    by_cases hj : j = id
    · rw [hj]
      exact hgone
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
    intro q hq' j cnt hqj x hx n
    rcases hsubP q hq' with h1 | h1
    · exact h.rq q h1 j cnt hqj x (hxrest x hx) n
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- gensLt
    intro j c3 hc3
    obtain ⟨-, c, hc, hg, -⟩ := hconn2 j c3 hc3
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
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- recvG
    intro j pc hpc hr0
    show ∃ g, (pc.seq, g) ∈ c'.genOf
    rw [hG]
    exact h.recvG j pc ((hPO j).symm.trans hpc) hr0
  · -- failNone
    intro q hq' j eo hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.failNone q h1 j eo hqj)
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- closedNone
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.closedNone q h1 j hqj)
    · rw [hnewP q h1] at hqj
      cases hqj
      exact hgone
  · -- closedClosing
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact h.closedClosing q h1 j hqj
    · rw [hnewP q h1] at hqj
      cases hqj
      show (c'.page.slots id).closing = true
      rw [hcl' id]
      exact hcl
  · -- closedOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.closedOrd, pairwise_le_one _ _ hnewL, fun a ha b hb id' hpa hob => ?_⟩
    rw [hnewP b hb] at hob
    have hid : id = id' := Option.some.inj hob
    exact h.closedNoClose a ha id' hpa (Relay.Ev.close id, p) hmem (by rw [hid])
  · -- closeClosing
    intro x hx j hxj
    show (c'.page.slots j).closing = true
    rw [hcl' j]
    exact h.closeClosing x (hxrest x hx) j hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    have hx' : x ∈ rest := by
      rw [← hTR]
      exact hx
    rcases hsubP q hq' with h1 | h1
    · exact h.closedNoConn q h1 j hqj x (hxrest x hx)
    · rw [hnewP q h1] at hqj
      have hjid : j = id := (Relay.Out.closed.inj hqj).symm
      rw [hjid]
      exact hnoConn x hx'
  · -- openRel
    intro j pc hpc hop c3 hc3
    obtain ⟨-, c, hc, -, hop', -⟩ := hconn2 j c3 hc3
    rw [hop']
    exact h.openRel j pc ((hPO j).symm.trans hpc) hop c hc
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    rcases hsubP q hq' with h1 | h1
    · exact h.okOpen q h1 j hqj ((hcl' j).symm.trans hcl2) pc ((hPO j).symm.trans hpc)
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.okNoDisc q h1 j hqj ((hcl' j).symm.trans hcl2) x (hxrest x hx)
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- discRel
    intro x hx j hxj
    rcases h.discRel x (hxrest x hx) j hxj with hn | ⟨pc, hpc, hop⟩ | ⟨hn, hcl2⟩
    · exact Or.inl (hnone1 j hn)
    · by_cases hj : j = id
      · exact Or.inl (by rw [hj]; exact hgone)
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
    · rw [hnewP q h1] at hqj
      have hjid : j = id := (Relay.Out.closed.inj hqj).symm
      have hx' : x ∈ rest := by
        rw [← hTR]
        exact hx
      intro hxc
      exact absurd (hnoClose x hx') (by simp [CloseIs, hxc, hjid])
  · -- failOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.failOrd, pairwise_le_one _ _ hnewL, fun a ha b hb id' e _ _ => ?_⟩
    rw [hnewP b hb]
    rfl
  · -- connPend
    intro x hx j hxj q hq'
    rcases hsubP q hq' with h1 | h1
    · exact h.connPend x (hxrest x hx) j hxj q h1
    · rw [hnewP q h1]
      intro hj
      have hjid : id = j := Option.some.inj hj
      have hx' : x ∈ rest := by
        rw [← hTR]
        exact hx
      exact hnoConn x hx' (by rw [hxj, hjid])
  · -- okRel
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · rcases h.okRel q h1 j hqj with hn | ⟨c, hc, hgc, hop⟩
      · exact Or.inl (hnone1 j hn)
      · by_cases hj : j = id
        · exact Or.inl (by rw [hj]; exact hgone)
        · obtain ⟨c'', hc'', hg', ho', -⟩ := hconn1 j c hj hc
          exact Or.inr ⟨c'', hc'', hg'.trans hgc, ho'.trans hop⟩
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- okOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.okOrd, pairwise_le_one _ _ hnewL, fun a ha b hb id' _ hbo => ?_⟩
    rw [hnewP b hb] at hbo
    cases hbo
  · -- discOnce
    intro q hq' j cnt hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.discOnce q h1 j cnt hqj x (hxrest x hx)
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- discUniq
    intro id'
    show ((c'.toPage).filter (DiscRep id')).length ≤ 1
    rw [hTP, count_app_nil (DiscRep id') _ _ (fun x hx => by simp [DiscRep, hnewP x hx])]
    exact h.discUniq id'
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hgq
    rcases hsubP q hq' with h1 | h1
    · exact h.wrMono q h1 j cnt f hqj pc ((hPO j).symm.trans hpc) (by rw [← hG]; exact hgq)
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- wrOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.wrOrd, pairwise_le_one _ _ hnewL, fun a ha b hb id c1 f1 c2 f2 _ hbw _ => ?_⟩
    rw [hnewP b hb] at hbw
    cases hbw
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
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- replyFrozen
    intro q hq' j cnt hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨-, c, hc, hg, -, hw, hq1, -⟩ := hconn2 j c3 hc3
      obtain ⟨r1, r2⟩ := h.replyFrozen q h1 j cnt hqj c hc (hg.symm.trans hg3)
      rw [hq1, hw]
      exact ⟨r1, r2⟩
    · rw [hnewP q h1] at hqj
      cases hqj
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    rcases hsubP q hq' with hq1 | hq1
    · rcases hsubP r hr with hr1 | hr1
      · exact h.replyMax q hq1 r hr1 j c1 c2 f h1 h2 hg
      · rw [hnewP r hr1] at h2
        cases h2
    · rw [hnewP q hq1] at h1
      cases h1
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

-- the CLOSE step: its frames (none, or one CLOSED of the id), its connection of the id (gone), the others (kept)
theorem closeStep_outs (s : Relay.St) (id : Nat) :
    (Relay.closeStep s id).2 = [] ∨ (Relay.closeStep s id).2 = [Relay.Out.closed id] := by
  unfold Relay.closeStep
  cases (s.slot id).conn <;> split <;> simp

theorem closeStep_slot_other (s : Relay.St) (id j : Nat) (hj : j ≠ id) :
    (Relay.closeStep s id).1.slot j = s.slot j := by
  unfold Relay.closeStep
  cases (s.slot id).conn
  · rfl
  · unfold Relay.setConn Relay.setSlot Relay.St.slot
    simp [hj]

theorem closeStep_conn_id (s : Relay.St) (id : Nat) :
    ((Relay.closeStep s id).1.slot id).conn = none := by
  unfold Relay.closeStep
  rcases hc : (s.slot id).conn with _ | c
  · simpa [Relay.St.slot] using hc
  · simp [Relay.setConn, Relay.setSlot, Relay.St.slot]

theorem closeStep_nextGen (s : Relay.St) (id : Nat) : (Relay.closeStep s id).1.nextGen = s.nextGen := by
  unfold Relay.closeStep
  cases (s.slot id).conn <;> rfl

theorem stepK_close_closed (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id : Nat) (hc : s.closed.isSome = true) :
    Clock.stepK cap k s (Relay.Ev.close id) = (k, s, []) := by
  unfold Clock.stepK
  simp [hc]

theorem stepK_close_open (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id : Nat) (hc : s.closed.isSome = false) :
    Clock.stepK cap k s (Relay.Ev.close id) =
      (Clock.clearGone k (Relay.closeStep s id).1 id, (Relay.closeStep s id).1, (Relay.closeStep s id).2) := by
  unfold Clock.stepK
  simp [hc, Relay.step, Relay.evId]

-- a CLOSE at the head of the relay's queue
theorem inv_tDoRelay_close (T T' : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.close id, p) :: rest) (hT : tDoRelay T = some T') : Inv T' := by
  unfold tDoRelay at hT
  simp only [hq] at hT
  simp only [Option.some.injEq] at hT
  subst hT
  by_cases hc : T.c.rs.closed.isSome = true
  · -- the relay is closed: nothing happens to it, the head is taken
    rw [stepK_close_closed Relay.DEFAULT_CAP T.clk T.c.rs id hc]
    refine inv_relay_keep T h _ _ (Relay.Ev.close id) p rest hq [] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · simp
    · intro q hq'
      simp at hq'
    · rfl
    · intro j
      show qsumT j rest = qs j T
      unfold qs
      rw [hq]
      simp [qsumT]
    · intro j c hc'
      exact ⟨c, hc', rfl, rfl, rfl, rfl, rfl⟩
    · intro j c'' hc''
      exact ⟨c'', hc'', rfl, rfl, rfl, rfl, rfl⟩
    · intro j hn
      exact hn
    · intro j hn
      exact hn
    · have hM := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id) h.mirror
      rw [stepK_close_closed Relay.DEFAULT_CAP T.clk T.c.rs id hc] at hM
      exact hM
    · have hG := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id) h.good
      rw [stepK_close_closed Relay.DEFAULT_CAP T.clk T.c.rs id hc] at hG
      exact hG
  · -- the relay is open: its CLOSE takes the id's connection down, and the page hears CLOSED if it knew the id
    have hc' : T.c.rs.closed.isSome = false := by simpa using hc
    have hS := stepK_close_open Relay.DEFAULT_CAP T.clk T.c.rs id hc'
    refine inv_relay_close T h _ _ id p rest hq
      ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id)).2.2.map
        (fun o => (o, Client.tagOf T.c.rs (Relay.Ev.close id)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hS]
      rcases closeStep_outs T.c.rs id with h1 | h1
      · left
        simp [h1]
      · right
        exact ⟨Client.tagOf T.c.rs (Relay.Ev.close id), by simp [h1]⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · show (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id)).2.1.nextGen = T.c.rs.nextGen
      rw [hS]
      exact closeStep_nextGen _ _
    · intro j
      show qsumT j rest = qs j T
      unfold qs
      rw [hq]
      simp [qsumT]
    · intro j c hj hc'
      refine ⟨c, ?_, rfl, rfl, rfl, rfl, rfl⟩
      show ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id)).2.1.slot j).conn = some c
      rw [hS]
      change ((Relay.closeStep T.c.rs id).1.slot j).conn = some c
      rw [closeStep_slot_other _ _ _ hj]
      exact hc'
    · intro j c'' hc''
      change ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id)).2.1.slot j).conn = some c'' at hc''
      rw [hS] at hc''
      change ((Relay.closeStep T.c.rs id).1.slot j).conn = some c'' at hc''
      have hj : j ≠ id := by
        intro hji
        rw [hji, closeStep_conn_id] at hc''
        cases hc''
      rw [closeStep_slot_other _ _ _ hj] at hc''
      exact ⟨hj, c'', hc'', rfl, rfl, rfl, rfl, rfl⟩
    · change ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id)).2.1.slot id).conn = none
      rw [hS]
      change ((Relay.closeStep T.c.rs id).1.slot id).conn = none
      exact closeStep_conn_id _ _
    · intro j hn
      change (T.c.rs.slot j).conn = none at hn
      change ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id)).2.1.slot j).conn = none
      rw [hS]
      change ((Relay.closeStep T.c.rs id).1.slot j).conn = none
      by_cases hj : j = id
      · rw [hj]
        exact closeStep_conn_id _ _
      · rw [closeStep_slot_other _ _ _ hj]
        exact hn
    · exact Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id) h.mirror
    · exact Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.close id) h.good

end Ind
