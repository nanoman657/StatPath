namespace Ind
open Timed

-- two discard replies of an id in a queue: the head and a later one (the count of the discard replies is at most one)
theorem two_discRep (id : Nat) (a : Relay.Out × Nat) (rest : List (Relay.Out × Nat)) (q : Relay.Out × Nat)
    (hq : q ∈ rest) (ha : DiscRep id a = true) (hqb : DiscRep id q = true) :
    2 ≤ ((a :: rest).filter (DiscRep id)).length := by
  rw [List.filter_cons_of_pos ha]
  simp only [List.length_cons]
  have : 0 < (rest.filter (DiscRep id)).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hq, hqb⟩)
  omega

-- the WRITTEN frame of the page, as a client state: the page's connection of the id after the frame (c4), the SEND
-- frames its pump queued (ns), and the queue without the frame.  Every invariant field is kept.
theorem inv_written_core (T : TSys) (h : Inv T) (c' : Client.Sys) (id t cnt flag : Nat)
    (rest : List (Relay.Out × Nat)) (hq : T.c.toPage = (Relay.Out.written id cnt flag, t) :: rest)
    (c0 : Page.PConn) (hc : (T.c.page.slots id).conn = some c0) (hcl0 : (T.c.page.slots id).closing = false)
    (ns : List Nat) (P : Page.State) (c4 : Page.PConn)
    (hrs : c'.rs = T.c.rs) (hr : c'.toRelay = T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0)))
    (hg : c'.genOf = T.c.genOf) (hs : c'.toPage = rest) (hp : c'.page = P)
    (hslot : P.slots id = { T.c.page.slots id with conn := some c4 })
    (hother : ∀ j, j ≠ id → P.slots j = T.c.page.slots j)
    (hnext : P.nextSeq = T.c.page.nextSeq)
    (hs4 : c4.seq = c0.seq) (ho4 : c4.isOpen = c0.isOpen) (hw4 : c4.written = cnt) (hr4 : c4.received = c0.received)
    (hPI4 : Page.PInv c4)
    (hdisc : flag = 1 ∧ c0.discardPending = true → ns = [] ∧ c4.discardPending = false ∧ c4.sent = cnt ∧ c4.tail = cnt)
    (hnd : ¬ (flag = 1 ∧ c0.discardPending = true) →
      c4.sent = c0.sent + ns.sum ∧ c4.tail = c0.tail ∧ c4.discardPending = c0.discardPending)
    (hnsd : c0.discardPending = true ∨ c0.isOpen = false → ns = []) :
    Inv ⟨c', T.clk⟩ := by
  obtain ⟨rs', pg', tr', tp', gg', bd', pr', sk'⟩ := c'
  dsimp only at hrs hr hg hs hp
  subst hrs hr hg
  subst tp'
  subst pg'
  -- membership and the head
  have hmemq : (Relay.Out.written id cnt flag, t) ∈ T.c.toPage := by rw [hq]; simp
  have hsub : ∀ q ∈ rest, q ∈ T.c.toPage := fun q hq' => by
    rw [hq]
    exact List.mem_cons_of_mem _ hq'
  have hsl : rest.Sublist T.c.toPage := by
    rw [hq]
    exact List.sublist_cons_self _ _
  -- the page: only id's connection changes, and its closing flags stay
  have hPo : ∀ j, (P.slots j).conn = if j = id then some c4 else (T.c.page.slots j).conn := by
    intro j
    by_cases hj : j = id
    · rw [hj, hslot]
      simp
    · rw [if_neg hj, hother j hj]
  have hPcl : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing := by
    intro j
    by_cases hj : j = id
    · rw [hj, hslot]
    · rw [hother j hj]
  -- the head's facts: its generation is the page connection's, and its count is bounded by the page's sent
  have hgen0 : (c0.seq, t) ∈ T.c.genOf := by
    rcases h.apply _ hmemq id (by simp [isClosedOut]) (by simp [outIdT]) c0 hc with h1 | h1
    · rw [hcl0] at h1
      cases h1
    · exact h1
  have hcS : cnt ≤ c0.sent := h.wrSent _ hmemq id cnt flag rfl c0 hc hgen0
  -- the relay connection of id has the head's generation
  have hconnGen : ∀ c3, ConnOf T id = some c3 → c3.gen = t := fun c3 hc3 =>
    h.gen _ hmemq id (by simp [outIdT]) c3 hc3
  -- the queue sum of the new SENDs
  have hqs : ∀ j, qsumT j (T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0))) =
      qs j T + (if id = j then ns.sum else 0) := by
    intro j
    unfold qs
    rw [qsumT_app_w, qsumT_sends j id ns]
  -- the connection of id after the frame, counted with the sends it has queued: the acc bound
  have accId : ∀ c3, ConnOf T id = some c3 →
      c3.written + c3.queued + (qs id T + ns.sum) ≤ c4.sent ∧ c4.written ≤ c3.written := by
    intro c3 hc3
    have hg3 : (c0.seq, c3.gen) ∈ T.c.genOf := by
      rw [hconnGen c3 hc3]
      exact hgen0
    by_cases hd : flag = 1 ∧ c0.discardPending = true
    · obtain ⟨hns, -, hsent4, -⟩ := hdisc hd
      obtain ⟨hq0, hqs0, hw3⟩ := h.reset _ hmemq id cnt (by rw [hd.1]) c0 hc hd.2 hgen0 c3 hc3
        (hconnGen c3 hc3)
      subst hns
      refine ⟨?_, ?_⟩
      · simp [hsent4, hw3, hq0, hqs0]
      · simp [hw4, hw3]
    · obtain ⟨hsum4, -, -⟩ := hnd hd
      obtain ⟨hA, -⟩ := h.acc id c0 c3 hc hc3 hg3
      have hw3 : cnt ≤ c3.written := h.written _ hmemq id cnt flag rfl c3 hc3 (hconnGen c3 hc3)
      refine ⟨?_, ?_⟩
      · rw [hsum4]
        omega
      · rw [hw4]
        exact hw3
  -- the relay connections are the same; the window of the page's connection
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_, connPend := ?_, okRel := ?_, okOrd := ?_, discOnce := ?_,
      discUniq := ?_, wrMono := ?_, wrOrd := ?_, genFun := ?_, wrSent := ?_, replyFrozen := ?_, replyMax := ?_, noDeny := ?_ }
  · -- pi
    intro j pc hpc
    change (P.slots j).conn = some pc at hpc
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      cases Option.some.inj hpc
      exact hPI4
    · rw [if_neg hj] at hpc
      exact h.pi j pc hpc
  · -- link
    intro j c3 hc3
    change ConnOf T j = some c3 at hc3
    rcases h.link j c3 hc3 with ⟨pc0, hpc0, hm⟩ | ⟨hn0, hcl2⟩
    · by_cases hj : j = id
      · have h1 : (T.c.page.slots id).conn = some pc0 := by
          rw [← hj]
          exact hpc0
        have hpe0 : pc0 = c0 := Option.some.inj (h1.symm.trans hc)
        left
        refine ⟨c4, ?_, ?_⟩
        · show (P.slots j).conn = some c4
          rw [hPo j, if_pos hj]
        · show (c4.seq, c3.gen) ∈ T.c.genOf
          rw [hs4, ← hpe0]
          exact hm
      · left
        refine ⟨pc0, ?_, hm⟩
        show (P.slots j).conn = some pc0
        rw [hPo j, if_neg hj]
        exact hpc0
    · by_cases hj : j = id
      · exfalso
        have hn1 : (T.c.page.slots id).conn = none := by
          rw [← hj]
          exact hn0
        rw [hc] at hn1
        cases hn1
      · right
        refine ⟨?_, ?_⟩
        · show (P.slots j).conn = none
          rw [hPo j, if_neg hj]
          exact hn0
        · show (P.slots j).closing = true
          rw [hPcl j]
          exact hcl2
  · -- acc
    intro j pc c3 hpc hc3 hgc
    change (P.slots j).conn = some pc at hpc
    change ConnOf T j = some c3 at hc3
    by_cases hj : j = id
    · rw [hj] at hpc hc3 ⊢
      rw [hPo id, if_pos rfl] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe]
      show c3.written + c3.queued + (qsumT id (T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0)))) ≤ c4.sent ∧ c4.written ≤ c3.written
      rw [hqs id, if_pos rfl]
      exact accId c3 hc3
    · rw [hPo j, if_neg hj] at hpc
      have hA := h.acc j pc c3 hpc hc3 hgc
      show c3.written + c3.queued + (qsumT j (T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0)))) ≤ pc.sent ∧ pc.written ≤ c3.written
      rw [hqs j, if_neg (fun e => hj e.symm), Nat.add_zero]
      exact hA
  · -- wq
    intro j c3 hc3
    change ConnOf T j = some c3 at hc3
    by_cases hj : j = id
    · rw [hj] at hc3 ⊢
      have hAcc := accId c3 hc3
      have hPW := hPI4
      obtain ⟨-, -, hPW⟩ := hPW
      have hW : Page.SEND_W = Relay.SEND_WINDOW := rfl
      rw [hW] at hPW
      show c3.queued + (qsumT id (T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0)))) ≤ Relay.SEND_WINDOW
      rw [hqs id, if_pos rfl]
      omega
    · have hW := h.wq j c3 hc3
      show c3.queued + (qsumT j (T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0)))) ≤ Relay.SEND_WINDOW
      rw [hqs j, if_neg (fun e => hj e.symm), Nat.add_zero]
      exact hW
  · -- gen
    intro q hq' j hoj c3 hc3
    exact h.gen q (hsub q hq') j hoj c3 hc3
  · -- apply
    intro q hq' j hcl hoj pc hpc
    change (P.slots j).conn = some pc at hpc
    show (P.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
    rw [hPcl j]
    by_cases hj : j = id
    · rw [hPo j, if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe]
      rcases h.apply q (hsub q hq') j hcl hoj c0 (by rw [hj]; exact hc) with h1 | h1
      · left
        exact h1
      · right
        rw [hs4]
        exact h1
    · rw [hPo j, if_neg hj] at hpc
      rcases h.apply q (hsub q hq') j hcl hoj pc hpc with h1 | h1
      · left
        exact h1
      · right
        exact h1
  · -- noOrphan
    intro q hq' j hcl hoj hpn
    change (P.slots j).conn = none at hpn
    show (P.slots j).closing = true
    rw [hPcl j]
    rw [hPo j] at hpn
    by_cases hj : j = id
    · rw [if_pos hj] at hpn
      cases hpn
    · rw [if_neg hj] at hpn
      exact h.noOrphan q (hsub q hq') j hcl hoj hpn
  · -- written
    intro q hq' j cnt' f' hqj c3 hc3 hg3
    exact h.written q (hsub q hq') j cnt' f' hqj c3 hc3 hg3
  · -- reset
    intro q hq' j cnt' hqj pc hpc hdp hgq c3 hc3 hg3
    change (P.slots j).conn = some pc at hpc
    change ConnOf T j = some c3 at hc3
    rw [hPo j] at hpc
    show c3.queued = 0 ∧ (qsumT j (T.c.toRelay ++ ns.map (fun n => (Relay.Ev.send id n, 0)))) = 0 ∧ c3.written = cnt'
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      by_cases hd : flag = 1 ∧ c0.discardPending = true
      · obtain ⟨-, hdp4, -, -⟩ := hdisc hd
        rw [hpe, hdp4] at hdp
        cases hdp
      · obtain ⟨-, -, hdp4⟩ := hnd hd
        have hc0dp : c0.discardPending = true := by
          rw [← hdp4, ← hpe]
          exact hdp
        have hns : ns = [] := hnsd (Or.inl hc0dp)
        rw [hpe, hs4] at hgq
        obtain ⟨q1, q2, q3⟩ := h.reset q (hsub q hq') j cnt' hqj c0 (by rw [hj]; exact hc) hc0dp hgq c3
          hc3 hg3
        refine ⟨q1, ?_, q3⟩
        rw [hqs j, if_pos hj.symm, hns]
        simp [q2]
    · rw [if_neg hj] at hpc
      obtain ⟨q1, q2, q3⟩ := h.reset q (hsub q hq') j cnt' hqj pc hpc hdp hgq c3 hc3 hg3
      refine ⟨q1, ?_, q3⟩
      rw [hqs j, if_neg (fun e => hj e.symm), Nat.add_zero]
      exact q2
  · -- barrier
    rw [List.pairwise_append]
    refine ⟨h.barrier, ?_, ?_⟩
    · exact pairwise_of_forall _ _ (fun a ha b hb => by
        obtain ⟨m, -, rfl⟩ := List.mem_map.mp ha
        obtain ⟨n, -, rfl⟩ := List.mem_map.mp hb
        simp [FwdEv])
    · intro x hx y hy
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hy
      show ¬ FwdEv x.1 (Relay.Ev.send id m)
      intro hF
      have hgood : ¬ (c0.discardPending = true ∨ c0.isOpen = false) := fun hh => by
        have hnil := hnsd hh
        rw [hnil] at hm
        simp at hm
      have hopen0 : c0.isOpen = true := by
        cases hb : c0.isOpen
        · exact absurd (Or.inr hb) hgood
        · rfl
      cases hxe : x.1 with
      | discard a =>
        rw [hxe] at hF
        simp only [FwdEv] at hF
        have hdc : c0.discardPending = true :=
          h.disc x hx a (by rw [hxe]) c0 (by rw [hF]; exact hc) hopen0
        exact hgood (Or.inl hdc)
      | connect a =>
        rw [hxe] at hF
        simp only [FwdEv] at hF
        rcases h.cl x hx a (by rw [hxe]) with ⟨pc, hpc, hs'⟩ | ⟨hn, -⟩
        · have hpe : pc = c0 := Option.some.inj
            ((show (T.c.page.slots a).conn = some pc from hpc).symm.trans (by rw [hF]; exact hc))
          obtain ⟨g, hg'⟩ := h.openG a c0 (by rw [hF]; exact hc) hopen0
          exact h.gp x hx a (by rw [hxe]) g (by rw [← hs', hpe]; exact hg')
        · exact absurd hn (by simp [PageOf, hF, hc])
      | _ => simp [FwdEv, hxe] at hF
  · -- connClean
    intro x hx j hxj
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.connClean x hx1 j hxj
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- notOpen
    intro j pc hpc hop
    change (P.slots j).conn = some pc at hpc
    rw [hPo j] at hpc
    show pc.sent = 0 ∧ pc.written = 0
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe] at hop ⊢
      have hop0 : c0.isOpen = false := by
        rw [← ho4]
        exact hop
      have hnil := hnsd (Or.inr hop0)
      obtain ⟨c0s, -⟩ := h.notOpen id c0 hc hop0
      by_cases hd : flag = 1 ∧ c0.discardPending = true
      · obtain ⟨-, -, hs4', -⟩ := hdisc hd
        constructor <;> omega
      · obtain ⟨hs4', -, -⟩ := hnd hd
        rw [hnil] at hs4'
        simp at hs4'
        constructor <;> omega
    · rw [if_neg hj] at hpc
      exact h.notOpen j pc (by unfold PageOf; exact hpc) hop
  · -- cl
    intro x hx j hxj
    rcases List.mem_append.mp hx with hx1 | hx1
    · rcases h.cl x hx1 j hxj with ⟨pc, hpc, hs'⟩ | ⟨hn, hcl2⟩
      · by_cases hj : j = id
        · have hpe : pc = c0 := Option.some.inj ((show (T.c.page.slots j).conn = some pc from hpc).symm.trans
            (by rw [hj]; exact hc))
          left
          refine ⟨c4, ?_, ?_⟩
          · show (P.slots j).conn = some c4
            rw [hPo j, if_pos hj]
          · show c4.seq = x.2
            rw [hs4, ← hpe]
            exact hs'
        · left
          refine ⟨pc, ?_, hs'⟩
          show (P.slots j).conn = some pc
          rw [hPo j, if_neg hj]
          exact hpc
      · by_cases hj : j = id
        · exfalso
          have hn1 : (T.c.page.slots j).conn = none := hn
          rw [hj, hc] at hn1
          cases hn1
        · right
          refine ⟨?_, ?_⟩
          · show (P.slots j).conn = none
            rw [hPo j, if_neg hj]
            exact hn
          · show (P.slots j).closing = true
            rw [hPcl j]
            exact hcl2
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- rq
    intro q hq' j cnt' hqj x hx n hxn
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.rq q (hsub q hq') j cnt' hqj x hx1 n hxn
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx1
      simp only [Relay.Ev.send.injEq] at hxn
      obtain ⟨hid, -⟩ := hxn
      rcases h.rep q (hsub q hq') j cnt' hqj with ⟨pc, hpc, hdp⟩ | ⟨hn, -⟩
      · have hpe : pc = c0 := Option.some.inj ((show (T.c.page.slots j).conn = some pc from hpc).symm.trans
          (by rw [← hid]; exact hc))
        rw [hpe] at hdp
        exact absurd hm (by rw [hnsd (Or.inl hdp)]; simp)
      · exfalso
        have hn1 : (T.c.page.slots j).conn = none := hn
        rw [← hid, hc] at hn1
        cases hn1
  · -- gensLt
    intro j c3 hc3
    exact h.gensLt j c3 hc3
  · -- gp
    intro x hx j hxj g
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.gp x hx1 j hxj g
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- openG
    intro j pc hpc hop
    change (P.slots j).conn = some pc at hpc
    show ∃ g, (pc.seq, g) ∈ T.c.genOf
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe] at hop ⊢
      have hop0 : c0.isOpen = true := by
        rw [← ho4]
        exact hop
      obtain ⟨g, hg'⟩ := h.openG id c0 hc hop0
      exact ⟨g, by rw [hs4]; exact hg'⟩
    · rw [if_neg hj] at hpc
      exact h.openG j pc hpc hop
  · -- mirror
    exact h.mirror
  · -- good
    exact h.good
  · -- seqG
    intro p g hpg
    show p < P.nextSeq
    rw [hnext]
    exact h.seqG p g hpg
  · -- seqQ
    intro x hx j hxj
    show x.2 < P.nextSeq
    rw [hnext]
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.seqQ x hx1 j hxj
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- disc
    intro x hx j hxj pc hpc hop
    change (P.slots j).conn = some pc at hpc
    show pc.discardPending = true
    rw [hPo j] at hpc
    rcases List.mem_append.mp hx with hx1 | hx1
    · by_cases hj : j = id
      · rw [if_pos hj] at hpc
        have hpe : pc = c4 := (Option.some.inj hpc).symm
        rw [hpe] at hop ⊢
        have hop0 : c0.isOpen = true := by
          rw [← ho4]
          exact hop
        by_cases hd : flag = 1 ∧ c0.discardPending = true
        · exfalso
          exact (h.discOnce _ hmemq id cnt (by rw [hd.1]) x hx1) (by rw [← hj]; exact hxj)
        · obtain ⟨-, -, hdp4⟩ := hnd hd
          rw [hdp4]
          exact h.disc x hx1 id (by rw [← hj]; exact hxj) c0 hc hop0
      · rw [if_neg hj] at hpc
        exact h.disc x hx1 j hxj pc hpc hop
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- rep
    intro q hq' j cnt' hqj
    show (∃ pc, (P.slots j).conn = some pc ∧ pc.discardPending = true) ∨
      ((P.slots j).conn = none ∧ (P.slots j).closing = true)
    rw [hPcl j]
    by_cases hj : j = id
    · rw [hj] at hqj ⊢
      left
      refine ⟨c4, by rw [hPo id, if_pos rfl], ?_⟩
      by_cases hd : flag = 1 ∧ c0.discardPending = true
      · exfalso
        have hcnt := h.discUniq id
        rw [hq] at hcnt
        have hhead : DiscRep id (Relay.Out.written id cnt flag, t) = true := by
          simp [DiscRep, hd.1]
        have hqb : DiscRep id q = true := by
          simp [DiscRep, hqj]
        have := two_discRep id _ rest q hq' hhead hqb
        omega
      · obtain ⟨-, -, hdp4⟩ := hnd hd
        rw [hdp4]
        rcases h.rep q (hsub q hq') id cnt' hqj with ⟨pc, hpc, hdp⟩ | ⟨hn, -⟩
        · have hpe : pc = c0 := Option.some.inj
            ((show (T.c.page.slots id).conn = some pc from hpc).symm.trans hc)
          rw [hpe] at hdp
          exact hdp
        · exfalso
          have hn1 : (T.c.page.slots id).conn = none := hn
          rw [hc] at hn1
          cases hn1
    · rcases h.rep q (hsub q hq') j cnt' hqj with ⟨pc, hpc, hdp⟩ | ⟨hn, hcl2⟩
      · left
        refine ⟨pc, ?_, hdp⟩
        rw [hPo j, if_neg hj]
        exact hpc
      · right
        refine ⟨?_, hcl2⟩
        rw [hPo j, if_neg hj]
        exact hn
  · -- recvG
    intro j pc hpc hr0
    change (P.slots j).conn = some pc at hpc
    show ∃ g, (pc.seq, g) ∈ T.c.genOf
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe] at hr0 ⊢
      obtain ⟨g, hg'⟩ := h.recvG id c0 hc (by rw [← hr4]; exact hr0)
      exact ⟨g, by rw [hs4]; exact hg'⟩
    · rw [if_neg hj] at hpc
      exact h.recvG j pc hpc hr0
  · -- failNone
    intro q hq' j e hqj
    exact h.failNone q (hsub q hq') j e hqj
  · -- closedNone
    intro q hq' j hqj
    exact h.closedNone q (hsub q hq') j hqj
  · -- closedClosing
    intro q hq' j hqj
    show (P.slots j).closing = true
    rw [hPcl j]
    exact h.closedClosing q (hsub q hq') j hqj
  · -- closedOrd
    exact List.Pairwise.sublist hsl h.closedOrd
  · -- closeClosing
    intro x hx j hxj
    show (P.slots j).closing = true
    rw [hPcl j]
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.closeClosing x hx1 j hxj
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- closedNoConn
    intro q hq' j hqj x hx
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.closedNoConn q (hsub q hq') j hqj x hx1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp
  · -- openRel
    intro j pc hpc hop c3 hc3
    change (P.slots j).conn = some pc at hpc
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe] at hop
      have hop0 : c0.isOpen = true := by
        rw [← ho4]
        exact hop
      exact h.openRel id c0 hc hop0 c3 (by rw [← hj]; exact hc3)
    · rw [if_neg hj] at hpc
      exact h.openRel j pc hpc hop c3 hc3
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    change (P.slots j).closing = false at hcl2
    rw [hPcl j] at hcl2
    change (P.slots j).conn = some pc at hpc
    show pc.isOpen = false
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [hj] at hqj hcl2
      rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe, ho4]
      exact h.okOpen q (hsub q hq') id hqj hcl2 c0 hc
    · rw [if_neg hj] at hpc
      exact h.okOpen q (hsub q hq') j hqj hcl2 pc hpc
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    rw [hPcl j] at hcl2
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.okNoDisc q (hsub q hq') j hqj hcl2 x hx1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp
  · -- discRel
    intro x hx j hxj
    rcases List.mem_append.mp hx with hx1 | hx1
    · rcases h.discRel x hx1 j hxj with hn | ⟨pc, hpc, hop⟩ | ⟨hn, hcl2⟩
      · exact Or.inl hn
      · by_cases hj : j = id
        · have hpe : pc = c0 := Option.some.inj
            ((show (T.c.page.slots j).conn = some pc from hpc).symm.trans (by rw [hj]; exact hc))
          refine Or.inr (Or.inl ⟨c4, ?_, ?_⟩)
          · show (P.slots j).conn = some c4
            rw [hPo j, if_pos hj]
          · show c4.isOpen = true
            rw [hpe] at hop
            rw [ho4]
            exact hop
        · refine Or.inr (Or.inl ⟨pc, ?_, hop⟩)
          show (P.slots j).conn = some pc
          rw [hPo j, if_neg hj]
          exact hpc
      · by_cases hj : j = id
        · exfalso
          have hn1 : (T.c.page.slots j).conn = none := hn
          rw [hj, hc] at hn1
          cases hn1
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · show (P.slots j).conn = none
            rw [hPo j, if_neg hj]
            exact hn
          · show (P.slots j).closing = true
            rw [hPcl j]
            exact hcl2
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- closingNone
    intro j hcl
    show (P.slots j).conn = none
    rw [hPcl j] at hcl
    rw [hPo j]
    by_cases hj : j = id
    · exfalso
      rw [hj, hcl0] at hcl
      cases hcl
    · rw [if_neg hj]
      exact h.closingNone j hcl
  · -- closedNoClose
    intro q hq' j hqj x hx
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.closedNoClose q (hsub q hq') j hqj x hx1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp
  · -- failOrd
    exact List.Pairwise.sublist hsl h.failOrd
  · -- connPend
    intro x hx j hxj q hq'
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.connPend x hx1 j hxj q (hsub q hq')
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp at hxj
  · -- okRel
    intro q hq' j hqj
    exact h.okRel q (hsub q hq') j hqj
  · -- okOrd
    exact List.Pairwise.sublist hsl h.okOrd
  · -- discOnce
    intro q hq' j cnt' hqj x hx
    rcases List.mem_append.mp hx with hx1 | hx1
    · exact h.discOnce q (hsub q hq') j cnt' hqj x hx1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hx1
      simp
  · -- discUniq
    intro id'
    exact discUniq_of_sub _ _ id' hsl (h.discUniq id')
  · -- wrMono
    intro q hq' j cnt' f' hqj pc hpc hgq
    change (P.slots j).conn = some pc at hpc
    show pc.written ≤ cnt'
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe] at hgq ⊢
      rw [hs4] at hgq
      have hqt : q.2 = t := (h.genFun c0.seq t q.2 hgen0 hgq).symm
      have hwo := h.wrOrd
      rw [hq] at hwo
      have hrel := (List.pairwise_cons.mp hwo).1 q hq'
      rw [hj] at hqj
      have hcc := hrel id cnt flag cnt' f' rfl hqj hqt.symm
      rw [hw4]
      exact hcc
    · rw [if_neg hj] at hpc
      exact h.wrMono q (hsub q hq') j cnt' f' hqj pc hpc hgq
  · -- wrOrd
    exact List.Pairwise.sublist hsl h.wrOrd
  · -- genFun
    exact h.genFun
  · -- wrSent
    intro q hq' j cnt' f' hqj pc hpc hgq
    change (P.slots j).conn = some pc at hpc
    show cnt' ≤ pc.sent
    rw [hPo j] at hpc
    by_cases hj : j = id
    · rw [if_pos hj] at hpc
      have hpe : pc = c4 := (Option.some.inj hpc).symm
      rw [hpe] at hgq ⊢
      rw [hs4] at hgq
      have hqt : q.2 = t := (h.genFun c0.seq t q.2 hgen0 hgq).symm
      rw [hj] at hqj
      by_cases hd : flag = 1 ∧ c0.discardPending = true
      · obtain ⟨-, -, hsent4, -⟩ := hdisc hd
        rw [hsent4]
        exact h.replyMax _ hmemq q (hsub q hq') id cnt cnt' f' (by rw [hd.1]) hqj hqt
      · obtain ⟨hsum4, -, -⟩ := hnd hd
        rw [hsum4]
        have hw := h.wrSent q (hsub q hq') id cnt' f' hqj c0 hc hgq
        omega
    · rw [if_neg hj] at hpc
      exact h.wrSent q (hsub q hq') j cnt' f' hqj pc hpc hgq
  · -- replyFrozen
    intro q hq' j cnt' hqj c3 hc3 hg3
    exact h.replyFrozen q (hsub q hq') j cnt' hqj c3 hc3 hg3
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    exact h.replyMax q (hsub q hq') r (hsub r hr) j c1 c2 f h1 h2 hg
  · -- noDeny
    intro x hx
    rcases List.mem_append.mp hx with h1 | h1
    · exact h.noDeny x h1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.mp h1
      simp

-- the page takes a WRITTEN frame: the connection's sent and written counts, the discard reset, and the SEND frames
-- its pump queues (the frame's own state change is inv_written_core)
theorem inv_tDoPage_written (T T' : TSys) (h : Inv T) (id t cnt flag : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.written id cnt flag, t) :: rest) (c0 : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c0) (hcl0 : (T.c.page.slots id).closing = false)
    (hT : tDoPage T = some T') : Inv T' := by
  have hmemq : (Relay.Out.written id cnt flag, t) ∈ T.c.toPage := by rw [hq]; simp
  have hgen0 : (c0.seq, t) ∈ T.c.genOf := by
    rcases h.apply _ hmemq id (by simp [isClosedOut]) (by simp [outIdT]) c0 hc with h1 | h1
    · rw [hcl0] at h1
      cases h1
    · exact h1
  have hw : c0.written ≤ cnt := h.wrMono _ hmemq id cnt flag rfl c0 hc hgen0
  have hacc : cnt ≤ c0.sent := h.wrSent _ hmemq id cnt flag rfl c0 hc hgen0
  have hPI : Page.PInv c0 := h.pi id c0 hc
  unfold tDoPage lift Client.doPage at hT
  simp only [hq] at hT
  generalize hG : Page.frame T.c.page (Relay.Out.written id cnt flag) = G at hT
  obtain ⟨st', obs⟩ := G
  have hfr := frame_written_eq T.c.page id cnt flag c0 hc hcl0
  rw [hG] at hfr
  have hcon := wr_frame_spec T.c.page id cnt flag c0 {c0 with written := cnt} rfl rfl rfl rfl rfl rfl rfl hw hacc hPI
  obtain ⟨c4, ns, hslot, hother, hnxt, hfilt, hs4, ho4, hw4, hr4, hPI4, hdisc, hnd, hnsd⟩ := hcon
  have hst : st' = (wrFrameC T.c.page id cnt flag {c0 with written := cnt}).1 := congrArg Prod.fst hfr
  have hob : obs = (wrFrameC T.c.page id cnt flag {c0 with written := cnt}).2 := congrArg Prod.snd hfr
  rw [← hob] at hfilt
  rw [← hst] at hslot hother hnxt
  simp only [Option.map_some, Option.some.injEq] at hT
  subst hT
  exact inv_written_core T h _ id t cnt flag rest hq c0 hc hcl0 ns st' c4 rfl
    (congrArg (fun l => T.c.toRelay ++ l) hfilt) rfl rfl rfl hslot hother hnxt hs4 ho4 hw4 hr4 hPI4 hdisc hnd hnsd

end Ind
