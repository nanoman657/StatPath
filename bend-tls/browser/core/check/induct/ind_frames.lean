namespace Ind
open Timed

-- a client record whose queue is a sublist of the old one, with the rest unchanged: the invariant holds (every
-- field that concerns the queue holds for the shorter queue; the others do not read it)
theorem inv_shrink (c : Client.Sys) (clk : Clock.Clk) (h : Inv ⟨c, clk⟩) (c' : Client.Sys)
    (hrs : c'.rs = c.rs) (hp : c'.page = c.page) (hr : c'.toRelay = c.toRelay) (hg : c'.genOf = c.genOf)
    (hs : c'.toPage.Sublist c.toPage) : Inv ⟨c', clk⟩ := by
  obtain ⟨rs', pg', tr', tp', gg', bd', pr', sk'⟩ := c'
  dsimp only at hrs hp hr hg hs
  subst hrs hp hr hg
  exact
    { pi := h.pi, link := h.link, acc := h.acc, wq := h.wq,
      gen := fun q hq => h.gen q (hs.subset hq), apply := fun q hq => h.apply q (hs.subset hq),
      noOrphan := fun q hq => h.noOrphan q (hs.subset hq), written := fun q hq => h.written q (hs.subset hq),
      reset := fun q hq => h.reset q (hs.subset hq), barrier := h.barrier, connClean := h.connClean,
      notOpen := h.notOpen, cl := h.cl, rq := fun q hq => h.rq q (hs.subset hq), gensLt := h.gensLt,
      gp := h.gp, openG := h.openG, mirror := h.mirror, good := h.good, seqG := h.seqG, seqQ := h.seqQ,
      disc := h.disc, rep := fun q hq => h.rep q (hs.subset hq), recvG := h.recvG,
      failNone := fun q hq => h.failNone q (hs.subset hq), closedNone := fun q hq => h.closedNone q (hs.subset hq),
      closedClosing := fun q hq => h.closedClosing q (hs.subset hq),
      closedOrd := List.Pairwise.sublist hs h.closedOrd, closeClosing := h.closeClosing,
      closedNoConn := fun q hq => h.closedNoConn q (hs.subset hq), openRel := h.openRel,
      okOpen := fun q hq => h.okOpen q (hs.subset hq), okNoDisc := fun q hq => h.okNoDisc q (hs.subset hq),
      discRel := h.discRel, closingNone := h.closingNone,
      closedNoClose := fun q hq => h.closedNoClose q (hs.subset hq), failOrd := List.Pairwise.sublist hs h.failOrd }

-- Page.frame does nothing to the page for a frame that does not apply (and is not a CLOSED frame)
theorem frame_none (st : Page.State) (o : Relay.Out) (hn : Page.applies st o = none)
    (hc : ∀ id, o ≠ Relay.Out.closed id) : Page.frame st o = (st, []) := by
  cases o with
  | closed id => exact absurd rfl (hc id)
  | wsclose _ => rfl
  | ok id => unfold Page.frame; rw [hn]
  | data id n => unfold Page.frame; rw [hn]
  | eof id => unfold Page.frame; rw [hn]
  | written id cnt f => unfold Page.frame; rw [hn]
  | fail id e => unfold Page.frame; rw [hn]

-- a frame of the page's queue that the page ignores: the queue loses its head, the page and the relay do not change
theorem inv_tDoPage_ignored (T T' : TSys) (h : Inv T) (o : Relay.Out) (t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (o, t) :: rest) (hn : Page.applies T.c.page o = none)
    (hc : ∀ id, o ≠ Relay.Out.closed id) (hT : tDoPage T = some T') : Inv T' := by
  unfold tDoPage lift Client.doPage at hT
  simp only [hq, frame_none T.c.page o hn hc, Option.map_some, Option.some.injEq, List.filterMap_nil,
    List.append_nil] at hT
  subst hT
  exact inv_shrink T.c T.clk h _ rfl rfl rfl rfl (by simp [hq])

end Ind

namespace Ind
open Timed

-- the page takes a CLOSED frame of an id: the id's closing flag goes, and the queue loses the frame. Nothing else in
-- the composed state changes, and the frame's id has no connection, no CONNECT or CLOSE queued, and no other frame
theorem frame_closed (st : Page.State) (id : Nat) :
    Page.frame st (Relay.Out.closed id) = (Page.setSlot st id { st.slots id with closing := false }, []) := rfl

theorem inv_closed_core (T : TSys) (h : Inv T) (c' : Client.Sys) (id t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.closed id, t) :: rest) (P : Page.State)
    (hrs : c'.rs = T.c.rs) (hr : c'.toRelay = T.c.toRelay) (hg : c'.genOf = T.c.genOf) (hs : c'.toPage = rest)
    (hp : c'.page = P) (hconn : ∀ j, (P.slots j).conn = (T.c.page.slots j).conn)
    (hcl1 : (P.slots id).closing = false)
    (hcl2 : ∀ j, j ≠ id → (P.slots j).closing = (T.c.page.slots j).closing)
    (hnext : P.nextSeq = T.c.page.nextSeq) :
    Inv ⟨c', T.clk⟩ := by
  obtain ⟨rs', pg', tr', tp', gg', bd', pr', sk'⟩ := c'
  dsimp only at hrs hr hg hs hp
  subst hrs hr hg
  subst tp'
  subst hp
  have hmemq : (Relay.Out.closed id, t) ∈ T.c.toPage := by rw [hq]; simp
  have hcn : ConnOf T id = none := h.closedNone _ hmemq id rfl
  have hnoC : ∀ x ∈ T.c.toRelay, x.1 ≠ Relay.Ev.connect id := h.closedNoConn _ hmemq id rfl
  have hnoCl : ∀ x ∈ T.c.toRelay, x.1 ≠ Relay.Ev.close id := h.closedNoClose _ hmemq id rfl
  have hord := h.closedOrd
  rw [hq] at hord
  have hrest := (List.pairwise_cons.mp hord).1
  have hnoF : ∀ r ∈ rest, outIdT r.1 ≠ some id := fun r hr' hEq => hrest r hr' id rfl hEq
  have hsub : ∀ q ∈ rest, q ∈ T.c.toPage := fun q hq' => by
    rw [hq]
    exact List.mem_cons_of_mem _ hq'
  have hsl : rest.Sublist T.c.toPage := by
    rw [hq]
    exact List.sublist_cons_self _ _
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_ }
  · intro j pc hpc
    change (pg'.slots j).conn = some pc at hpc
    rw [hconn j] at hpc
    exact h.pi j pc (by unfold PageOf; exact hpc)
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj
      rw [hcn] at hcc'
      cases hcc'
    · rcases h.link j cc hcc' with ⟨pc, hpc, hg'⟩ | ⟨hpn, hcl3⟩
      · refine Or.inl ⟨pc, ?_, hg'⟩
        change (pg'.slots j).conn = some pc
        rw [hconn j]
        exact hpc
      · refine Or.inr ⟨?_, ?_⟩
        · change (pg'.slots j).conn = none
          rw [hconn j]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl2 j hj]
          exact hcl3
  · intro j pc cc hpc hcc hg'
    have hpc' : PageOf T j = some pc := by
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn j] at hpc
      exact hpc
    have hcc' : ConnOf T j = some cc := hcc
    exact h.acc j pc cc hpc' hcc' hg'
  · intro j cc hcc
    exact h.wq j cc hcc
  · intro q hq' j hoj cc hcc
    exact h.gen q (hsub q hq') j hoj cc hcc
  · intro q hq' j hnc hoj pc hpc
    by_cases hj : j = id
    · subst hj
      exact absurd hoj (hnoF q hq')
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j] at hpc
        exact hpc
      show (pg'.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
      rw [hcl2 j hj]
      exact h.apply q (hsub q hq') j hnc hoj pc hpc'
  · intro q hq' j hnc hoj hpn
    by_cases hj : j = id
    · subst hj
      exact absurd hoj (hnoF q hq')
    · have hpn' : PageOf T j = none := by
        change (pg'.slots j).conn = none at hpn
        rw [hconn j] at hpn
        exact hpn
      show (pg'.slots j).closing = true
      rw [hcl2 j hj]
      exact h.noOrphan q (hsub q hq') j hnc hoj hpn'
  · intro q hq' j cnt f hq1 cc hcc hg'
    exact h.written q (hsub q hq') j cnt f hq1 cc hcc hg'
  · intro q hq' j cnt hq1 pc hpc hdp hg' cc hcc hgg
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hq1]; rfl) (hnoF q hq')
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j] at hpc
        exact hpc
      exact h.reset q (hsub q hq') j cnt hq1 pc hpc' hdp hg' cc hcc hgg
  · exact h.barrier
  · exact h.connClean
  · intro j pc hpc hop
    have hpc' : PageOf T j = some pc := by
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn j] at hpc
      exact hpc
    exact h.notOpen j pc hpc' hop
  · intro q hq' j hqc
    by_cases hj : j = id
    · subst hj
      exact absurd hqc (hnoC q hq')
    · rcases h.cl q hq' j hqc with ⟨pc, hpc, hs'⟩ | ⟨hpn, hcl3⟩
      · refine Or.inl ⟨pc, ?_, hs'⟩
        change (pg'.slots j).conn = some pc
        rw [hconn j]
        exact hpc
      · refine Or.inr ⟨?_, ?_⟩
        · change (pg'.slots j).conn = none
          rw [hconn j]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl2 j hj]
          exact hcl3
  · intro q hq' j cnt hq1 x hx n
    exact h.rq q (hsub q hq') j cnt hq1 x hx n
  · exact h.gensLt
  · exact h.gp
  · intro j pc hpc hop
    have hpc' : PageOf T j = some pc := by
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn j] at hpc
      exact hpc
    obtain ⟨g, hg'⟩ := h.openG j pc hpc' hop
    exact ⟨g, hg'⟩
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < pg'.nextSeq
    rw [hnext]
    exact h.seqG p g hm
  · intro q hq' j hqc
    show q.2 < pg'.nextSeq
    rw [hnext]
    exact h.seqQ q hq' j hqc
  · intro q hq' j hd pc hp hop
    have hp' : PageOf T j = some pc := by
      change (pg'.slots j).conn = some pc at hp
      rw [hconn j] at hp
      exact hp
    exact h.disc q hq' j hd pc hp' hop
  · intro q hq' j cnt hq1
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hq1]; rfl) (hnoF q hq')
    · rcases h.rep q (hsub q hq') j cnt hq1 with ⟨pc, hpc, hpd⟩ | ⟨hpn, hcl3⟩
      · refine Or.inl ⟨pc, ?_, hpd⟩
        change (pg'.slots j).conn = some pc
        rw [hconn j]
        exact hpc
      · refine Or.inr ⟨?_, ?_⟩
        · change (pg'.slots j).conn = none
          rw [hconn j]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl2 j hj]
          exact hcl3
  · intro j pc hp hr'
    have hp' : PageOf T j = some pc := by
      change (pg'.slots j).conn = some pc at hp
      rw [hconn j] at hp
      exact hp
    exact h.recvG j pc hp' hr'
  · intro q hq' j e hfl
    exact h.failNone q (hsub q hq') j e hfl
  · intro q hq' j hfl
    exact h.closedNone q (hsub q hq') j hfl
  · intro q hq' j hfl
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hfl]; rfl) (hnoF q hq')
    · change (pg'.slots j).closing = true
      rw [hcl2 j hj]
      exact h.closedClosing q (hsub q hq') j hfl
  · exact List.Pairwise.sublist hsl h.closedOrd
  · intro x hx j hxj
    by_cases hj : j = id
    · subst hj
      exact absurd hxj (hnoCl x hx)
    · change (pg'.slots j).closing = true
      rw [hcl2 j hj]
      exact h.closeClosing x hx j hxj
  · intro q hq' j hfl x hx hxe
    exact h.closedNoConn q (hsub q hq') j hfl x hx hxe
  · intro j pc hpc hop cc hcc
    have hpc' : PageOf T j = some pc := by
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn j] at hpc
      exact hpc
    exact h.openRel j pc hpc' hop cc hcc
  · intro q hq' j hfl hcl3 pc hpc
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hfl]; rfl) (hnoF q hq')
    · have hcl4 : (T.c.page.slots j).closing = false := by
        change (pg'.slots j).closing = false at hcl3
        rw [hcl2 j hj] at hcl3
        exact hcl3
      have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j] at hpc
        exact hpc
      exact h.okOpen q (hsub q hq') j hfl hcl4 pc hpc'
  · intro q hq' j hfl hcl3 x hx
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hfl]; rfl) (hnoF q hq')
    · have hcl4 : (T.c.page.slots j).closing = false := by
        change (pg'.slots j).closing = false at hcl3
        rw [hcl2 j hj] at hcl3
        exact hcl3
      exact h.okNoDisc q (hsub q hq') j hfl hcl4 x hx
  · intro x hx j hxd
    by_cases hj : j = id
    · subst hj
      exact Or.inl hcn
    · rcases h.discRel x hx j hxd with h0 | ⟨pc, hp, hop⟩ | ⟨hpn, hcl3⟩
      · exact Or.inl h0
      · have hp' : (pg'.slots j).conn = some pc := by
          rw [hconn j]
          exact hp
        exact Or.inr (Or.inl ⟨pc, hp', hop⟩)
      · refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · change (pg'.slots j).conn = none
          rw [hconn j]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl2 j hj]
          exact hcl3
  · intro j hcl3
    by_cases hj : j = id
    · subst hj
      rw [hcl1] at hcl3
      cases hcl3
    · change (pg'.slots j).conn = none
      rw [hconn j]
      exact h.closingNone j (by rw [← hcl2 j hj]; exact hcl3)
  · intro q hq' j hfl x hx hxe
    exact h.closedNoClose q (hsub q hq') j hfl x hx hxe
  · exact List.Pairwise.sublist hsl h.failOrd

theorem inv_tDoPage_closed (T T' : TSys) (h : Inv T) (id t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.closed id, t) :: rest) (hT : tDoPage T = some T') : Inv T' := by
  unfold tDoPage lift Client.doPage at hT
  simp only [hq, frame_closed, Option.map_some, Option.some.injEq] at hT
  subst hT
  refine inv_closed_core T h _ id t rest hq (Page.setSlot T.c.page id { T.c.page.slots id with closing := false }) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp
  · simp
  · intro j
    by_cases hj : j = id
    · subst hj
      simp [Page.setSlot]
    · simp [Page.setSlot, hj]
  · simp [Page.setSlot]
  · intro j hj
    simp [Page.setSlot, hj]
  · rfl

end Ind

namespace Ind
open Timed

-- the page takes a FAIL frame of an id that has a connection, not closing: the connection goes (the id's errors
-- are the die's, all to the callers, none on the queue)
theorem frame_fail_some (st : Page.State) (id e : Nat) (c : Page.PConn) (hc : (st.slots id).conn = some c)
    (hcl : (st.slots id).closing = false) :
    (Page.frame st (Relay.Out.fail id e)).1 =
        Page.setSlot st id { st.slots id with conn := none, lastErr := some e } ∧
    ((Page.frame st (Relay.Out.fail id e)).2.filterMap
        (fun o => match o with | .toRelay e p => some (e, p) | _ => none)) = [] := by
  have hap : Page.applies st (Relay.Out.fail id e) = some c.seq := by
    unfold Page.applies
    simp [hcl, hc]
  unfold Page.frame
  simp only [hap, hc]
  constructor
  · unfold Page.die
    simp [Page.setSlot]
  · unfold Page.die
    cases ho : c.isOpen <;> cases hop : c.op <;> cases hd : c.discardPending <;>
      simp [Page.setSlot, hc, ho, hop, hd, List.filterMap_map]

-- the page takes a FAIL frame of an id that has a connection, not closing: the queue loses the frame, the page
-- loses the connection of the id, and the relay has none of the id (the frame says so)
theorem inv_fail_core (T : TSys) (h : Inv T) (c' : Client.Sys) (id e t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.fail id e, t) :: rest) (c : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c) (hcl0 : (T.c.page.slots id).closing = false) (P : Page.State)
    (hrs : c'.rs = T.c.rs) (hr : c'.toRelay = T.c.toRelay) (hg : c'.genOf = T.c.genOf) (hs : c'.toPage = rest)
    (hp : c'.page = P) (hconn : ∀ j, j ≠ id → (P.slots j).conn = (T.c.page.slots j).conn)
    (hconn0 : (P.slots id).conn = none) (hcl : ∀ j, (P.slots j).closing = (T.c.page.slots j).closing)
    (hnext : P.nextSeq = T.c.page.nextSeq) :
    Inv ⟨c', T.clk⟩ := by
  obtain ⟨rs', pg', tr', tp', gg', bd', pr', sk'⟩ := c'
  dsimp only at hrs hr hg hs hp
  subst hrs hr hg
  subst tp'
  subst hp
  have hmemq : (Relay.Out.fail id e, t) ∈ T.c.toPage := by rw [hq]; simp
  have hcn : ConnOf T id = none := h.failNone _ hmemq id e rfl
  have hord := h.failOrd
  rw [hq] at hord
  have hrest := (List.pairwise_cons.mp hord).1
  have hnoF : ∀ r ∈ rest, outIdT r.1 ≠ some id := fun r hr' hEq => hrest r hr' id e rfl hEq
  have hsub : ∀ q ∈ rest, q ∈ T.c.toPage := fun q hq' => by
    rw [hq]
    exact List.mem_cons_of_mem _ hq'
  have hsl : rest.Sublist T.c.toPage := by
    rw [hq]
    exact List.sublist_cons_self _ _
  have hPid : PageOf T id = some c := hc
  refine
    { pi := ?_, link := ?_, acc := ?_, wq := ?_, gen := ?_, apply := ?_, noOrphan := ?_, written := ?_,
      reset := ?_, barrier := ?_, connClean := ?_, notOpen := ?_, cl := ?_, rq := ?_, gensLt := ?_, gp := ?_,
      openG := ?_, mirror := ?_, good := ?_, seqG := ?_, seqQ := ?_, disc := ?_, rep := ?_, recvG := ?_,
      failNone := ?_, closedNone := ?_, closedClosing := ?_, closedOrd := ?_, closeClosing := ?_,
      closedNoConn := ?_, openRel := ?_, okOpen := ?_, okNoDisc := ?_, discRel := ?_, closingNone := ?_,
      closedNoClose := ?_, failOrd := ?_ }
  · intro j pc hpc
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · change (pg'.slots j).conn = some pc at hpc
      rw [hconn j hj] at hpc
      exact h.pi j pc (by unfold PageOf; exact hpc)
  · intro j cc hcc
    have hcc' : ConnOf T j = some cc := hcc
    by_cases hj : j = id
    · subst hj
      rw [hcn] at hcc'
      cases hcc'
    · rcases h.link j cc hcc' with ⟨pc, hpc, hg'⟩ | ⟨hpn, hcl3⟩
      · refine Or.inl ⟨pc, ?_, hg'⟩
        change (pg'.slots j).conn = some pc
        rw [hconn j hj]
        exact hpc
      · refine Or.inr ⟨?_, ?_⟩
        · change (pg'.slots j).conn = none
          rw [hconn j hj]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl j]
          exact hcl3
  · intro j pc cc hpc hcc hg'
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      have hcc' : ConnOf T j = some cc := hcc
      exact h.acc j pc cc hpc' hcc' hg'
  · intro j cc hcc
    exact h.wq j cc hcc
  · intro q hq' j hoj cc hcc
    exact h.gen q (hsub q hq') j hoj cc hcc
  · intro q hq' j hnc hoj pc hpc
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      show (pg'.slots j).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
      rw [hcl j]
      exact h.apply q (hsub q hq') j hnc hoj pc hpc'
  · intro q hq' j hnc hoj hpn
    by_cases hj : j = id
    · subst hj
      exact absurd hoj (hnoF q hq')
    · have hpn' : PageOf T j = none := by
        change (pg'.slots j).conn = none at hpn
        rw [hconn j hj] at hpn
        exact hpn
      show (pg'.slots j).closing = true
      rw [hcl j]
      exact h.noOrphan q (hsub q hq') j hnc hoj hpn'
  · intro q hq' j cnt f hq1 cc hcc hg'
    exact h.written q (hsub q hq') j cnt f hq1 cc hcc hg'
  · intro q hq' j cnt hq1 pc hpc hdp hg' cc hcc hgg
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      exact h.reset q (hsub q hq') j cnt hq1 pc hpc' hdp hg' cc hcc hgg
  · exact h.barrier
  · exact h.connClean
  · intro j pc hpc hop
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      exact h.notOpen j pc hpc' hop
  · intro q hq' j hqc
    by_cases hj : j = id
    · subst hj
      exfalso
      rcases h.cl q hq' j hqc with ⟨pc, hpc, hs'⟩ | ⟨hpn, _⟩
      · have hpe : pc = c := by
          rw [hPid] at hpc
          exact (Option.some.inj hpc).symm
        subst hpe
        have hA := h.apply (Relay.Out.fail j e, t) hmemq j (by simp [isClosedOut]) (by simp [outIdT]) pc hPid
        rcases hA with hcl3 | hmg
        · rw [hcl0] at hcl3
          cases hcl3
        · exact h.gp q hq' j hqc t (by rw [← hs']; exact hmg)
      · rw [hPid] at hpn
        cases hpn
    · rcases h.cl q hq' j hqc with ⟨pc, hpc, hs'⟩ | ⟨hpn, hcl3⟩
      · refine Or.inl ⟨pc, ?_, hs'⟩
        change (pg'.slots j).conn = some pc
        rw [hconn j hj]
        exact hpc
      · refine Or.inr ⟨?_, ?_⟩
        · change (pg'.slots j).conn = none
          rw [hconn j hj]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl j]
          exact hcl3
  · intro q hq' j cnt hq1 x hx n
    exact h.rq q (hsub q hq') j cnt hq1 x hx n
  · exact h.gensLt
  · exact h.gp
  · intro j pc hpc hop
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      obtain ⟨g, hg'⟩ := h.openG j pc hpc' hop
      exact ⟨g, hg'⟩
  · exact h.mirror
  · exact h.good
  · intro p g hm
    show p < pg'.nextSeq
    rw [hnext]
    exact h.seqG p g hm
  · intro q hq' j hqc
    show q.2 < pg'.nextSeq
    rw [hnext]
    exact h.seqQ q hq' j hqc
  · intro q hq' j hd pc hp hop
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hp
      rw [hconn0] at hp
      cases hp
    · have hp' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hp
        rw [hconn j hj] at hp
        exact hp
      exact h.disc q hq' j hd pc hp' hop
  · intro q hq' j cnt hq1
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hq1]; rfl) (hnoF q hq')
    · rcases h.rep q (hsub q hq') j cnt hq1 with ⟨pc, hpc, hpd⟩ | ⟨hpn, hcl3⟩
      · refine Or.inl ⟨pc, ?_, hpd⟩
        change (pg'.slots j).conn = some pc
        rw [hconn j hj]
        exact hpc
      · refine Or.inr ⟨?_, ?_⟩
        · change (pg'.slots j).conn = none
          rw [hconn j hj]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl j]
          exact hcl3
  · intro j pc hp hr'
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hp
      rw [hconn0] at hp
      cases hp
    · have hp' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hp
        rw [hconn j hj] at hp
        exact hp
      exact h.recvG j pc hp' hr'
  · intro q hq' j e' hfl
    exact h.failNone q (hsub q hq') j e' hfl
  · intro q hq' j hfl
    exact h.closedNone q (hsub q hq') j hfl
  · intro q hq' j hfl
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hfl]; rfl) (hnoF q hq')
    · change (pg'.slots j).closing = true
      rw [hcl j]
      exact h.closedClosing q (hsub q hq') j hfl
  · exact List.Pairwise.sublist hsl h.closedOrd
  · intro x hx j hxj
    change (pg'.slots j).closing = true
    rw [hcl j]
    exact h.closeClosing x hx j hxj
  · intro q hq' j hfl x hx hxe
    exact h.closedNoConn q (hsub q hq') j hfl x hx hxe
  · intro j pc hpc hop cc hcc
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).conn = some pc at hpc
      rw [hconn0] at hpc
      cases hpc
    · have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      have hcc' : ConnOf T j = some cc := hcc
      exact h.openRel j pc hpc' hop cc hcc'
  · intro q hq' j hfl hcl3 pc hpc
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hfl]; rfl) (hnoF q hq')
    · have hcl4 : (T.c.page.slots j).closing = false := by
        change (pg'.slots j).closing = false at hcl3
        rw [hcl j] at hcl3
        exact hcl3
      have hpc' : PageOf T j = some pc := by
        change (pg'.slots j).conn = some pc at hpc
        rw [hconn j hj] at hpc
        exact hpc
      exact h.okOpen q (hsub q hq') j hfl hcl4 pc hpc'
  · intro q hq' j hfl hcl3 x hx
    by_cases hj : j = id
    · subst hj
      exact absurd (show outIdT q.1 = some j by rw [hfl]; rfl) (hnoF q hq')
    · have hcl4 : (T.c.page.slots j).closing = false := by
        change (pg'.slots j).closing = false at hcl3
        rw [hcl j] at hcl3
        exact hcl3
      exact h.okNoDisc q (hsub q hq') j hfl hcl4 x hx
  · intro x hx j hxd
    by_cases hj : j = id
    · subst hj
      exact Or.inl hcn
    · rcases h.discRel x hx j hxd with h0 | ⟨pc, hp, hop⟩ | ⟨hpn, hcl3⟩
      · exact Or.inl h0
      · have hp' : (pg'.slots j).conn = some pc := by
          rw [hconn j hj]
          exact hp
        exact Or.inr (Or.inl ⟨pc, hp', hop⟩)
      · refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · change (pg'.slots j).conn = none
          rw [hconn j hj]
          exact hpn
        · change (pg'.slots j).closing = true
          rw [hcl j]
          exact hcl3
  · intro j hcl3
    by_cases hj : j = id
    · subst hj
      change (pg'.slots j).closing = true at hcl3
      rw [hcl j, hcl0] at hcl3
      cases hcl3
    · change (pg'.slots j).conn = none
      rw [hconn j hj]
      exact h.closingNone j (by rw [← hcl j]; exact hcl3)
  · intro q hq' j hfl x hx hxe
    exact h.closedNoClose q (hsub q hq') j hfl x hx hxe
  · exact List.Pairwise.sublist hsl h.failOrd

theorem inv_tDoPage_fail (T T' : TSys) (h : Inv T) (id e t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (Relay.Out.fail id e, t) :: rest) (c : Page.PConn)
    (hc : (T.c.page.slots id).conn = some c) (hcl0 : (T.c.page.slots id).closing = false)
    (hT : tDoPage T = some T') : Inv T' := by
  unfold tDoPage lift Client.doPage at hT
  simp only [hq] at hT
  generalize hG : Page.frame T.c.page (Relay.Out.fail id e) = G at hT
  obtain ⟨st', obs⟩ := G
  have hfr := frame_fail_some T.c.page id e c hc hcl0
  rw [hG] at hfr
  dsimp only at hfr
  obtain ⟨hst, hob⟩ := hfr
  subst hst
  simp only [hob, Option.map_some, Option.some.injEq, List.append_nil] at hT
  subst hT
  refine inv_fail_core T h _ id e t rest hq c hc hcl0
    (Page.setSlot T.c.page id { T.c.page.slots id with conn := none, lastErr := some e }) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp
  · simp
  · intro j hj
    simp [Page.setSlot, hj]
  · simp [Page.setSlot]
  · intro j
    by_cases hj : j = id
    · subst hj
      simp [Page.setSlot]
    · simp [Page.setSlot, hj]
  · simp [Page.setSlot]

end Ind
