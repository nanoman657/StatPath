namespace Ind
open Timed

-- a queue without a SEND of an id has no SEND weight for the id
theorem qsumT_no_send : ∀ (L : List (Relay.Ev × Nat)) (id : Nat),
    (∀ y ∈ L, ∀ n, y.1 ≠ Relay.Ev.send id n) → qsumT id L = 0
  | [], _, _ => rfl
  | (e, m) :: L, id, h => by
    have h1 : qsumT id L = 0 := qsumT_no_send L id (fun y hy n => h y (List.mem_cons_of_mem _ hy) n)
    cases e with
    | send i n =>
      by_cases hi : i = id
      · exact absurd (by simp [hi]) (h (Relay.Ev.send i n, m) List.mem_cons_self n)
      · simp [qsumT, hi, h1]
    | _ => simp [qsumT, h1]

-- the rest of a queue whose head is a DISCARD of an id: no SEND and no DISCARD of that id (the barrier)
theorem rest_no_send_discard (T : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.discard id, p) :: rest) :
    ∀ y ∈ rest, (∀ n, y.1 ≠ Relay.Ev.send id n) ∧ y.1 ≠ Relay.Ev.discard id := by
  intro y hy
  have hb := h.barrier
  rw [hq] at hb
  have h1 := (List.pairwise_cons.mp hb).1 y hy
  constructor
  · intro n hyn
    rw [hyn] at h1
    exact h1 (by simp [FwdEv])
  · intro hyn
    rw [hyn] at h1
    exact h1 (by simp [FwdEv])

-- the DISCARD step of an open connection: its queue is emptied, and the page hears a reply with the written count
theorem discard_open_slot (cap : Nat) (s : Relay.St) (id : Nat) (cc : Relay.Conn) (hc : (s.slot id).conn = some cc)
    (ho : cc.isOpen = true) (hcl : s.closed.isSome = false) :
    ((Relay.step cap s (Relay.Ev.discard id)).1.slot id).conn = some { cc with queued := 0 } ∧
    (Relay.step cap s (Relay.Ev.discard id)).2 = [Relay.Out.written id cc.written 1] := by
  unfold Relay.step
  rw [if_neg (by simp [hcl])]
  unfold Relay.discardStep
  simp only [hc]
  simp [ho, Relay.setConn, Relay.setSlot, Relay.St.slot]-- a DISCARD at the head of the relay's queue, of an id whose connection is open: the connection's queue is emptied
-- and the page's queue gets the reply (a WRITTEN of flag 1 with the connection's written count)
theorem inv_relay_discard_open (T : TSys) (h : Inv T) (c' : Client.Sys) (clk' : Clock.Clk) (id p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (Relay.Ev.discard id, p) :: rest) (cc : Relay.Conn)
    (hcc : (T.c.rs.slot id).conn = some cc) (hopen : cc.isOpen = true)
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ [(Relay.Out.written id cc.written 1, Client.tagOf T.c.rs (Relay.Ev.discard id))])
    (hng : c'.rs.nextGen = T.c.rs.nextGen) (hqs : ∀ j, qs j ⟨c', clk'⟩ = qs j T)
    (hcN : ∀ j c'', ConnOf ⟨c', clk'⟩ j = some c'' → ∃ c, ConnOf T j = some c ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.peerClosed = c.peerClosed ∧
      (j = id → c''.queued = 0) ∧ (j ≠ id → c''.queued = c.queued))
    (hcN1 : ∀ j c, ConnOf T j = some c → ∃ c'', ConnOf ⟨c', clk'⟩ j = some c'' ∧ c''.gen = c.gen ∧
      c''.isOpen = c.isOpen ∧ c''.written = c.written ∧ c''.peerClosed = c.peerClosed ∧
      (j = id → c''.queued = 0) ∧ (j ≠ id → c''.queued = c.queued))
    (hnone1 : ∀ j, ConnOf T j = none → ConnOf ⟨c', clk'⟩ j = none)
    (hnone2 : ∀ j, ConnOf ⟨c', clk'⟩ j = none → ConnOf T j = none)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have hmem : (Relay.Ev.discard id, p) ∈ T.c.toRelay := by
    rw [hq]
    exact List.mem_cons_self
  have hrest : rest.Sublist T.c.toRelay := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hxrest : ∀ x ∈ c'.toRelay, x ∈ T.c.toRelay := fun x hx => by
    rw [hTR] at hx
    exact hrest.subset hx
  have hsubP : ∀ q ∈ c'.toPage, q ∈ T.c.toPage ∨
      q = (Relay.Out.written id cc.written 1, Client.tagOf T.c.rs (Relay.Ev.discard id)) := fun q hq' => by
    rw [hTP] at hq'
    rcases List.mem_append.mp hq' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (List.mem_singleton.mp h1)
  have hPO : ∀ j, PageOf ⟨c', clk'⟩ j = PageOf T j := fun j => by
    unfold PageOf
    rw [hpg]
  have hcl' : ∀ j, (c'.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpg]
  have hgen : Client.tagOf T.c.rs (Relay.Ev.discard id) = cc.gen := by
    simp [Client.tagOf, Relay.evId, hcc]
  -- the page's side of the reply: an open page connection with a pending discard, or a closing id
  have hrep : (∃ pc', PageOf T id = some pc' ∧ pc'.discardPending = true) ∨
      (PageOf T id = none ∧ (T.c.page.slots id).closing = true) := by
    rcases h.discRel _ hmem id rfl with hn | ⟨pc', hpc', hop'⟩ | ⟨hn, hcl2⟩
    · have hn' : (T.c.rs.slot id).conn = none := hn
      rw [hcc] at hn'
      cases hn'
    · exact Or.inl ⟨pc', hpc', h.disc _ hmem id rfl pc' hpc' hop'⟩
    · exact Or.inr ⟨hn, hcl2⟩
  -- the queue of the id: no SEND and no DISCARD of the id remains (the barrier), so the reply's sums are zero
  have hrs := rest_no_send_discard T h id p rest hq
  have hqsZ : qs id T = 0 := by
    unfold qs
    rw [hq]
    simp only [qsumT]
    have := qsumT_no_send rest id (fun y hy n => (hrs y hy).1 n)
    simp [this]
  -- the discard reply is alone of its id in the page's queue, and it is the last of the page's frames
  have hdiscOnceQ : ∀ q ∈ T.c.toPage, ∀ j cnt, q.1 = Relay.Out.written j cnt 1 → j ≠ id := by
    intro q hq' j cnt hqj hji
    rw [hji] at hqj
    exact absurd (h.discOnce q hq' id cnt hqj _ hmem) (by simp)
  -- the connection of the id is cc, whatever the connection of the id is named
  have hconnId : ∀ c, ConnOf T id = some c → c = cc := fun c hc => (Option.some.inj (hcc.symm.trans hc)).symm
  have hgenR : ∀ (q : Relay.Out × Nat), q = (Relay.Out.written id cc.written 1, Client.tagOf T.c.rs (Relay.Ev.discard id)) →
      q.2 = cc.gen := fun q hq' => by
    rw [hq', hgen]
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
    obtain ⟨c, hc, hg, -⟩ := hcN j c3 hc3
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
    obtain ⟨c, hc, hg, -, hw, -, hq0, hqne⟩ := hcN j c3 hc3
    have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
    have hgc' : (pc.seq, c.gen) ∈ T.c.genOf := by
      have h1 : (pc.seq, c3.gen) ∈ T.c.genOf := by
        rw [← hG]
        exact hgc
      rw [hg] at h1
      exact h1
    obtain ⟨hA, hB⟩ := h.acc j pc c hpc' hc hgc'
    have hq3 : c3.queued ≤ c.queued := by
      by_cases hj : j = id
      · rw [hq0 hj]
        exact Nat.zero_le _
      · exact Nat.le_of_eq (hqne hj)
    show c3.written + c3.queued + qs j ⟨c', clk'⟩ ≤ pc.sent ∧ pc.written ≤ c3.written
    rw [hqs j, hw]
    constructor <;> omega
  · -- wq
    intro j c3 hc3
    obtain ⟨c, hc, -, -, -, -, hq0, hqne⟩ := hcN j c3 hc3
    have hW := h.wq j c hc
    have hq3 : c3.queued ≤ c.queued := by
      by_cases hj : j = id
      · rw [hq0 hj]
        exact Nat.zero_le _
      · exact Nat.le_of_eq (hqne hj)
    show c3.queued + qs j ⟨c', clk'⟩ ≤ Relay.SEND_WINDOW
    rw [hqs j]
    omega
  · -- gen
    intro q hq' j hoj c3 hc3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -⟩ := hcN j c3 hc3
      rw [hg]
      exact h.gen q h1 j hoj c hc
    · subst h1
      have hjid : j = id := by
        simp [outIdT] at hoj
        exact hoj.symm
      obtain ⟨c, hc, hg, -⟩ := hcN j c3 hc3
      rw [hg, hgen]
      rw [hjid] at hc
      rw [hconnId c hc]
  · -- apply
    intro q hq' j hcl2 hoj pc hpc
    rcases hsubP q hq' with h1 | h1
    · have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
      show (c'.page.slots j).closing = true ∨ (pc.seq, q.2) ∈ c'.genOf
      rw [hcl' j, hG]
      exact h.apply q h1 j hcl2 hoj pc hpc'
    · subst h1
      have hjid : j = id := by
        simp [outIdT] at hoj
        exact hoj.symm
      have hpcT : PageOf T id = some pc := by
        rw [← hjid]
        exact (hPO j).symm.trans hpc
      rcases h.link id cc hcc with ⟨pc2, hpc2, hm2⟩ | ⟨hn2, -⟩
      · have hpe : pc2 = pc := Option.some.inj (hpc2.symm.trans hpcT)
        right
        show (pc.seq, Client.tagOf T.c.rs (Relay.Ev.discard id)) ∈ c'.genOf
        rw [hG, hgen, ← hpe]
        exact hm2
      · exact absurd (hpcT.symm.trans hn2) (by simp)
  · -- noOrphan
    intro q hq' j hcl2 hoj hpn
    rcases hsubP q hq' with h1 | h1
    · have hpn' : PageOf T j = none := (hPO j).symm.trans hpn
      show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact h.noOrphan q h1 j hcl2 hoj hpn'
    · subst h1
      have hjid : j = id := by
        simp [outIdT] at hoj
        exact hoj.symm
      have hpn' : PageOf T j = none := (hPO j).symm.trans hpn
      rcases hrep with ⟨pc', hpc', -⟩ | ⟨-, hcl3⟩
      · rw [hjid] at hpn'
        rw [hpc'] at hpn'
        cases hpn'
      · show (c'.page.slots j).closing = true
        rw [hcl' j, hjid]
        exact hcl3
  · -- written
    intro q hq' j cnt f hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -, hw, -, -, -⟩ := hcN j c3 hc3
      rw [hw]
      exact h.written q h1 j cnt f hqj c hc (hg.symm.trans hg3)
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt f := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      obtain ⟨c, hc, hg, -, hw, -, -, -⟩ := hcN id c3 hc3
      rw [hw, hconnId c hc]
      exact Nat.le_refl _
  · -- reset
    intro q hq' j cnt hqj pc hpc hdp hgq c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -, hw, -, hq0, hqne⟩ := hcN j c3 hc3
      by_cases hj : j = id
      · exact absurd hj (hdiscOnceQ q h1 j cnt hqj)
      · have hpc' : PageOf T j = some pc := (hPO j).symm.trans hpc
        have hgq' : (pc.seq, q.2) ∈ T.c.genOf := by
          rw [← hG]
          exact hgq
        obtain ⟨r1, r2, r3⟩ := h.reset q h1 j cnt hqj pc hpc' hdp hgq' c hc (hg.symm.trans hg3)
        show c3.queued = 0 ∧ qs j ⟨c', clk'⟩ = 0 ∧ c3.written = cnt
        rw [hqs j, hw, hqne hj]
        exact ⟨r1, r2, r3⟩
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt 1 := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      obtain ⟨c, hc, -, -, hw, -, hq0, -⟩ := hcN id c3 hc3
      show c3.queued = 0 ∧ qs id ⟨c', clk'⟩ = 0 ∧ c3.written = cc.written
      refine ⟨hq0 rfl, ?_, ?_⟩
      · rw [hqs id]
        exact hqsZ
      · rw [hw, hconnId c hc]
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
      rw [hcl' j]
      exact hcl2
  · -- rq
    intro q hq' j cnt hqj x hx n
    rcases hsubP q hq' with h1 | h1
    · exact h.rq q h1 j cnt hqj x (hxrest x hx) n
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt 1 := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      have hx' : x ∈ rest := by
        rw [← hTR]
        exact hx
      exact (hrs x hx').1 n
  · -- gensLt
    intro j c3 hc3
    obtain ⟨c, hc, hg, -⟩ := hcN j c3 hc3
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
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt 1 := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      rcases hrep with ⟨pc', hpc', hdp⟩ | ⟨hn, hcl2⟩
      · left
        exact ⟨pc', (hPO id).trans hpc', hdp⟩
      · right
        refine ⟨(hPO id).trans hn, ?_⟩
        show (c'.page.slots id).closing = true
        rw [hcl' id]
        exact hcl2
  · -- recvG
    intro j pc hpc hr0
    show ∃ g, (pc.seq, g) ∈ c'.genOf
    rw [hG]
    exact h.recvG j pc ((hPO j).symm.trans hpc) hr0
  · -- failNone
    intro q hq' j e hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.failNone q h1 j e hqj)
    · subst h1
      simp at hqj
  · -- closedNone
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · exact hnone1 j (h.closedNone q h1 j hqj)
    · subst h1
      simp at hqj
  · -- closedClosing
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · show (c'.page.slots j).closing = true
      rw [hcl' j]
      exact h.closedClosing q h1 j hqj
    · subst h1
      simp at hqj
  · -- closedOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.closedOrd, pairwise_le_one _ _ (by simp), fun a ha b hb id' hpa hob => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    have hid : id = id' := Option.some.inj hob
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
    · subst h1
      simp at hqj
  · -- openRel
    intro j pc hpc hop c3 hc3
    obtain ⟨c, hc, -, ho, -, -, -, -⟩ := hcN j c3 hc3
    rw [ho]
    exact h.openRel j pc ((hPO j).symm.trans hpc) hop c hc
  · -- okOpen
    intro q hq' j hqj hcl2 pc hpc
    rcases hsubP q hq' with h1 | h1
    · exact h.okOpen q h1 j hqj ((hcl' j).symm.trans hcl2) pc ((hPO j).symm.trans hpc)
    · subst h1
      simp at hqj
  · -- okNoDisc
    intro q hq' j hqj hcl2 x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.okNoDisc q h1 j hqj ((hcl' j).symm.trans hcl2) x (hxrest x hx)
    · subst h1
      simp at hqj
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
    · subst h1
      simp at hqj
  · -- failOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.failOrd, pairwise_le_one _ _ (by simp), fun a ha b hb id' e hpf hob => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    have hid : id = id' := Option.some.inj hob
    have h1 : (T.c.rs.slot id').conn = none := h.failNone a ha id' e hpf
    rw [← hid, hcc] at h1
    cases h1
  · -- connPend
    intro x hx j hxj q hq'
    rcases hsubP q hq' with h1 | h1
    · exact h.connPend x (hxrest x hx) j hxj q h1
    · subst h1
      intro hj'
      have hjid : id = j := Option.some.inj hj'
      have h3 : (T.c.rs.slot j).conn = none := h.connClean x (hxrest x hx) j hxj
      rw [← hjid, hcc] at h3
      cases h3
  · -- okRel
    intro q hq' j hqj
    rcases hsubP q hq' with h1 | h1
    · rcases h.okRel q h1 j hqj with hn | ⟨c, hc, hgc, hop⟩
      · exact Or.inl (hnone1 j hn)
      · obtain ⟨c'', hc'', hg, ho, -, -, -, -⟩ := hcN1 j c hc
        exact Or.inr ⟨c'', hc'', hg.trans hgc, ho.trans hop⟩
    · subst h1
      simp at hqj
  · -- okOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.okOrd, pairwise_le_one _ _ (by simp), fun a ha b hb id' _ hbo => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    simp at hbo
  · -- discOnce
    intro q hq' j cnt hqj x hx
    rcases hsubP q hq' with h1 | h1
    · exact h.discOnce q h1 j cnt hqj x (hxrest x hx)
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt 1 := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      have hx' : x ∈ rest := by
        rw [← hTR]
        exact hx
      exact (hrs x hx').2
  · -- discUniq
    intro id'
    show ((c'.toPage).filter (DiscRep id')).length ≤ 1
    rw [hTP, List.filter_append, List.length_append]
    by_cases hid : id' = id
    · rw [hid]
      have hold : (T.c.toPage.filter (DiscRep id)).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro x hx hxt
        obtain ⟨c, hc⟩ := discRep_spec id x hxt
        exact hdiscOnceQ x hx id c hc rfl
      rw [hold]
      simp [DiscRep]
    · have hrep0 : (List.filter (DiscRep id') [(Relay.Out.written id cc.written 1, Client.tagOf T.c.rs (Relay.Ev.discard id))]).length = 0 := by
        simp [DiscRep, Ne.symm hid]
      rw [hrep0, Nat.add_zero]
      exact h.discUniq id'
  · -- wrMono
    intro q hq' j cnt f hqj pc hpc hgq
    rcases hsubP q hq' with h1 | h1
    · exact h.wrMono q h1 j cnt f hqj pc ((hPO j).symm.trans hpc) (by rw [← hG]; exact hgq)
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt f := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      have hpc' : PageOf T id = some pc := (hPO id).symm.trans hpc
      have hg2 : (pc.seq, cc.gen) ∈ T.c.genOf := by
        rw [← hG, ← hgen]
        exact hgq
      obtain ⟨-, hB⟩ := h.acc id pc cc hpc' hcc hg2
      exact hB
  · -- wrOrd
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.wrOrd, pairwise_le_one _ _ (by simp), fun a ha b hb id' c1 f1 c2 f2 hap hbw hag => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    have hbw' : Relay.Out.written id cc.written 1 = Relay.Out.written id' c2 f2 := hbw
    obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hbw'
    exact h.written a ha id c1 f1 hap cc hcc ((hag.trans hgen).symm)
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
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt f := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      have hpc' : PageOf T id = some pc := (hPO id).symm.trans hpc
      have hg2 : (pc.seq, cc.gen) ∈ T.c.genOf := by
        rw [← hG, ← hgen]
        exact hgq
      obtain ⟨hA, -⟩ := h.acc id pc cc hpc' hcc hg2
      omega
  · -- replyFrozen
    intro q hq' j cnt hqj c3 hc3 hg3
    rcases hsubP q hq' with h1 | h1
    · obtain ⟨c, hc, hg, -, hw, -, hq0, hqne⟩ := hcN j c3 hc3
      by_cases hj : j = id
      · exact absurd hj (hdiscOnceQ q h1 j cnt hqj)
      · obtain ⟨r1, r2⟩ := h.replyFrozen q h1 j cnt hqj c hc (hg.symm.trans hg3)
        rw [hqne hj, hw]
        exact ⟨r1, r2⟩
    · subst h1
      have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j cnt 1 := hqj
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
      obtain ⟨c, hc, -, -, hw, -, hq0, -⟩ := hcN id c3 hc3
      exact ⟨hq0 rfl, by rw [hw, hconnId c hc]⟩
  · -- replyMax
    intro q hq' r hr j c1 c2 f h1 h2 hg
    rcases hsubP q hq' with hq1 | hq1
    · rcases hsubP r hr with hr1 | hr1
      · exact h.replyMax q hq1 r hr1 j c1 c2 f h1 h2 hg
      · subst hr1
        have hr2 : Relay.Out.written id cc.written 1 = Relay.Out.written j c2 f := h2
        obtain ⟨rfl, -, -⟩ := Relay.Out.written.inj hr2
        exact absurd rfl (hdiscOnceQ q hq1 id c1 h1)
    · subst hq1
      rcases hsubP r hr with hr1 | hr1
      · have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j c1 1 := h1
        obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
        exact h.written r hr1 id c2 f h2 cc hcc (hgen.symm.trans hg.symm)
      · subst hr1
        have hqj' : Relay.Out.written id cc.written 1 = Relay.Out.written j c1 1 := h1
        have hr2 : Relay.Out.written id cc.written 1 = Relay.Out.written j c2 f := h2
        obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj hqj'
        obtain ⟨-, rfl, -⟩ := Relay.Out.written.inj hr2
        exact Nat.le_refl _
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

-- a DISCARD leaves the other ids' slots, and the relay's nextGen, alone
theorem discard_slot_other (cap : Nat) (s : Relay.St) (id j : Nat) (hj : j ≠ id) :
    (Relay.step cap s (Relay.Ev.discard id)).1.slot j = s.slot j := by
  unfold Relay.step
  split
  · rfl
  · unfold Relay.discardStep
    rcases hc : (s.slot id).conn with _ | c
    · simp only [hc]
      split
      · rfl
      · rfl
    · simp only [hc]
      split
      · rfl
      · unfold Relay.setConn Relay.setSlot Relay.St.slot
        simp [hj]

theorem discard_nextGen (cap : Nat) (s : Relay.St) (id : Nat) :
    (Relay.step cap s (Relay.Ev.discard id)).1.nextGen = s.nextGen := by
  unfold Relay.step
  split
  · rfl
  · unfold Relay.discardStep
    rcases hc : (s.slot id).conn with _ | c
    · simp only [hc]
      split
      · rfl
      · rfl
    · simp only [hc]
      split
      · rfl
      · rfl

-- a DISCARD of a connection that is not open (or of none) either changes nothing, or closes the session
theorem discard_nonopen_form (cap : Nat) (s : Relay.St) (id : Nat)
    (hno : ∀ cc, (s.slot id).conn = some cc → cc.isOpen = false) :
    Relay.step cap s (Relay.Ev.discard id) = (s, []) ∨
      ∃ code, Relay.step cap s (Relay.Ev.discard id) = Relay.protoClose s code := by
  unfold Relay.step
  split
  · left
    rfl
  · unfold Relay.discardStep
    rcases hc : (s.slot id).conn with _ | c
    · simp only [hc]
      split
      · left
        rfl
      · right
        exact ⟨1002, rfl⟩
    · have hco := hno c hc
      simp only [hc, hco]
      right
      exact ⟨1002, rfl⟩

theorem discard_nonopen (cap : Nat) (s : Relay.St) (id : Nat)
    (hno : ∀ cc, (s.slot id).conn = some cc → cc.isOpen = false) :
    (∀ j, (Relay.step cap s (Relay.Ev.discard id)).1.slot j = s.slot j) ∧
    (∀ o ∈ (Relay.step cap s (Relay.Ev.discard id)).2, outIdT o = none) := by
  rcases discard_nonopen_form cap s id hno with h1 | ⟨code, h1⟩
  · rw [h1]
    exact ⟨fun j => rfl, fun o ho => absurd ho (List.not_mem_nil)⟩
  · rw [h1]
    refine ⟨fun j => protoClose_slot s code j, fun o ho => ?_⟩
    unfold Relay.protoClose at ho
    simp at ho
    subst ho
    rfl

-- the clock's step for a relay that is closed, and for a DISCARD of an open relay
theorem stepK_closed_gen (cap : Nat) (k : Clock.Clk) (s : Relay.St) (e : Relay.Ev) (hc : s.closed.isSome = true) :
    Clock.stepK cap k s e = (k, s, []) := by
  unfold Clock.stepK
  simp [hc]

theorem stepK_discard_formula (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id : Nat) (hc : s.closed.isSome = false) :
    Clock.stepK cap k s (Relay.Ev.discard id) =
      (Clock.clearGone (Clock.discardK k s id) (Relay.step cap s (Relay.Ev.discard id)).1 id,
        (Relay.step cap s (Relay.Ev.discard id)).1, (Relay.step cap s (Relay.Ev.discard id)).2) := by
  unfold Clock.stepK
  simp [hc]

theorem discard_open_conn (cap : Nat) (s : Relay.St) (id : Nat) (cc : Relay.Conn) (hc : (s.slot id).conn = some cc)
    (ho : cc.isOpen = true) (hcl : s.closed.isSome = false) :
    ((Relay.step cap s (Relay.Ev.discard id)).1.slot id).conn = some { cc with queued := 0 } :=
  (discard_open_slot cap s id cc hc ho hcl).1

theorem discard_open_outs (cap : Nat) (s : Relay.St) (id : Nat) (cc : Relay.Conn) (hc : (s.slot id).conn = some cc)
    (ho : cc.isOpen = true) (hcl : s.closed.isSome = false) :
    (Relay.step cap s (Relay.Ev.discard id)).2 = [Relay.Out.written id cc.written 1] :=
  (discard_open_slot cap s id cc hc ho hcl).2

-- a DISCARD at the head of the relay's queue
theorem inv_tDoRelay_discard (T T' : TSys) (h : Inv T) (id p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.discard id, p) :: rest) (hT : tDoRelay T = some T') : Inv T' := by
  unfold tDoRelay at hT
  simp only [hq] at hT
  simp only [Option.some.injEq] at hT
  subst hT
  by_cases hcl : T.c.rs.closed.isSome = true
  · rw [stepK_closed_gen Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) hcl]
    refine inv_relay_keep T h _ _ (Relay.Ev.discard id) p rest hq [] ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    · have hM := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) h.mirror
      rw [stepK_closed_gen Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) hcl] at hM
      exact hM
    · have hG := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) h.good
      rw [stepK_closed_gen Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) hcl] at hG
      exact hG
  · have hcl' : T.c.rs.closed.isSome = false := by simpa using hcl
    have hS := stepK_discard_formula Relay.DEFAULT_CAP T.clk T.c.rs id hcl'
    by_cases hop : ∃ cc, (T.c.rs.slot id).conn = some cc ∧ cc.isOpen = true
    · obtain ⟨cc, hcc, ho⟩ := hop
      rw [hS]
      refine inv_relay_discard_open T h _ _ id p rest hq cc hcc ho ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · show T.c.toPage ++ ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).2.map
          (fun o => (o, Client.tagOf T.c.rs (Relay.Ev.discard id)))) = _
        rw [discard_open_outs Relay.DEFAULT_CAP T.c.rs id cc hcc ho hcl']
        rfl
      · show (Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.nextGen = T.c.rs.nextGen
        exact discard_nextGen _ _ _
      · intro j
        show qsumT j rest = qs j T
        unfold qs
        rw [hq]
        simp [qsumT]
      · intro j c'' hc''
        change ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = some c'' at hc''
        by_cases hj : j = id
        · rw [hj, discard_open_conn Relay.DEFAULT_CAP T.c.rs id cc hcc ho hcl'] at hc''
          have hcc2 : c'' = { cc with queued := 0 } := (Option.some.inj hc'').symm
          refine ⟨cc, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun h' => absurd hj h'⟩
          · show (T.c.rs.slot j).conn = some cc
            rw [hj]
            exact hcc
          · rw [hcc2]
          · rw [hcc2]
          · rw [hcc2]
          · rw [hcc2]
          · rw [hcc2]
        · rw [discard_slot_other Relay.DEFAULT_CAP T.c.rs id j hj] at hc''
          exact ⟨c'', hc'', rfl, rfl, rfl, rfl, fun h' => absurd h' hj, fun _ => rfl⟩
      · intro j c hc'
        by_cases hj : j = id
        · have hcEq : c = cc := by
            have h1 : (T.c.rs.slot j).conn = some c := hc'
            rw [hj, hcc] at h1
            exact (Option.some.inj h1).symm
          subst hcEq
          refine ⟨{ c with queued := 0 }, ?_, rfl, rfl, rfl, rfl, fun _ => rfl, fun h' => absurd hj h'⟩
          show ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = some { c with queued := 0 }
          rw [hj]
          exact discard_open_conn Relay.DEFAULT_CAP T.c.rs id c hcc ho hcl'
        · refine ⟨c, ?_, rfl, rfl, rfl, rfl, fun h' => absurd h' hj, fun _ => rfl⟩
          show ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = some c
          rw [discard_slot_other Relay.DEFAULT_CAP T.c.rs id j hj]
          exact hc'
      · intro j hn
        have hn' : (T.c.rs.slot j).conn = none := hn
        show ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = none
        by_cases hj : j = id
        · rw [hj, hcc] at hn'
          cases hn'
        · rw [discard_slot_other Relay.DEFAULT_CAP T.c.rs id j hj]
          exact hn'
      · intro j hn
        change ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = none at hn
        show (T.c.rs.slot j).conn = none
        by_cases hj : j = id
        · rw [hj, discard_open_conn Relay.DEFAULT_CAP T.c.rs id cc hcc ho hcl'] at hn
          cases hn
        · rw [discard_slot_other Relay.DEFAULT_CAP T.c.rs id j hj] at hn
          exact hn
      · have hM := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) h.mirror
        rw [stepK_discard_formula Relay.DEFAULT_CAP T.clk T.c.rs id hcl'] at hM
        exact hM
      · have hG := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) h.good
        rw [stepK_discard_formula Relay.DEFAULT_CAP T.clk T.c.rs id hcl'] at hG
        exact hG
    · -- no open connection of the id: the relay changes no slot, and frames no id
      have hno : ∀ cc', (T.c.rs.slot id).conn = some cc' → cc'.isOpen = false := fun cc' hcc' => by
        cases hb : cc'.isOpen with
        | false => rfl
        | true => exact absurd ⟨cc', hcc', hb⟩ hop
      obtain ⟨hslot, houts⟩ := discard_nonopen Relay.DEFAULT_CAP T.c.rs id hno
      rw [hS]
      refine inv_relay_keep T h _ _ (Relay.Ev.discard id) p rest hq
        ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).2.map
          (fun o => (o, Client.tagOf T.c.rs (Relay.Ev.discard id)))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · rfl
      · intro q hq'
        rw [List.mem_map] at hq'
        obtain ⟨o, ho, rfl⟩ := hq'
        exact houts o ho
      · show (Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.nextGen = T.c.rs.nextGen
        exact discard_nextGen _ _ _
      · intro j
        show qsumT j rest = qs j T
        unfold qs
        rw [hq]
        simp [qsumT]
      · intro j c hc'
        refine ⟨c, ?_, rfl, rfl, rfl, rfl, rfl⟩
        show ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = some c
        rw [hslot j]
        exact hc'
      · intro j c'' hc''
        refine ⟨c'', ?_, rfl, rfl, rfl, rfl, rfl⟩
        change ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = some c'' at hc''
        rw [hslot j] at hc''
        exact hc''
      · intro j hn
        show ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = none
        rw [hslot j]
        exact hn
      · intro j hn
        change ((Relay.step Relay.DEFAULT_CAP T.c.rs (Relay.Ev.discard id)).1.slot j).conn = none at hn
        rw [hslot j] at hn
        exact hn
      · have hM := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) h.mirror
        rw [stepK_discard_formula Relay.DEFAULT_CAP T.clk T.c.rs id hcl'] at hM
        exact hM
      · have hG := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.discard id) h.good
        rw [stepK_discard_formula Relay.DEFAULT_CAP T.clk T.c.rs id hcl'] at hG
        exact hG

end Ind
