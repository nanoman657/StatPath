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
      discRel := h.discRel }

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
