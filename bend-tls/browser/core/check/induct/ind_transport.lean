
namespace Ind
open Timed

-- a flush-like step: the page, the queue of the page's frames and the page-to-relay map are kept; the relay's
-- connections are flushed; the frames appended are WRITTEN frames of connections that now carry those counts
theorem inv_flush (T T' : TSys) (h : Inv T) (hpage : T'.c.page = T.c.page) (hTR : T'.c.toRelay = T.c.toRelay)
    (hG : T'.c.genOf = T.c.genOf) (hF : Flushed T.c.rs T'.c.rs) (hng : T'.c.rs.nextGen = T.c.rs.nextGen)
    (new : List (Relay.Out × Nat))
    (hTP : T'.c.toPage = T.c.toPage ++ new)
    (hnew : ∀ q ∈ new, ∃ j cnt d, q.1 = Relay.Out.written j cnt 0 ∧ (T'.c.rs.slot j).conn = some d ∧
      cnt ≤ d.written ∧ q.2 = d.gen)
    (hclk : Clock.Mirror T'.clk T'.c.rs) (hgood : Clock.Good T'.clk) : Inv T' := by
  have hknown : ∀ j, (T'.c.rs.slot j).known = (T.c.rs.slot j).known := fun j => (hF j).1
  have hfwd : ∀ j c, ConnOf T j = some c → ∃ c', ConnOf T' j = some c' ∧ c'.gen = c.gen ∧ c'.isOpen = c.isOpen ∧
      c.written ≤ c'.written ∧ c'.written + c'.queued = c.written + c.queued ∧ c'.queued ≤ c.queued :=
    fun j c hc => (hF j).2.1 c hc
  have hback : ∀ j c', ConnOf T' j = some c' → ∃ c, ConnOf T j = some c ∧ c.gen = c'.gen :=
    fun j c' hc' => flushed_back hF j c' hc'
  have hnone : ∀ j, ConnOf T j = none → ConnOf T' j = none := fun j hn => (hF j).2.2 hn
  have hnone' : ∀ j, ConnOf T' j = none → ConnOf T j = none := by
    intro j hn
    cases hc : ConnOf T j with
    | none => rfl
    | some c =>
      obtain ⟨c', hc', _⟩ := hfwd j c hc
      rw [hn] at hc'
      cases hc'
  have hpg : ∀ j, PageOf T' j = PageOf T j := fun j => by simp only [PageOf, hpage]
  have hcl : ∀ j, (T'.c.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpage]
  have hqs : ∀ j, qs j T' = qs j T := fun j => by simp only [qs, hTR]
  have hmem : ∀ q, q ∈ T'.c.toPage ↔ q ∈ T.c.toPage ∨ q ∈ new := fun q => by
    rw [hTP, List.mem_append]
  -- a new frame names its id and the connection it reports
  have hnewId : ∀ q ∈ new, ∀ id, outIdT q.1 = some id → ∃ cnt d, q.1 = Relay.Out.written id cnt 0 ∧
      (T'.c.rs.slot id).conn = some d ∧ cnt ≤ d.written ∧ q.2 = d.gen := by
    intro q hq id hid
    obtain ⟨j, cnt, d, hqj, hd, hcnt, hg⟩ := hnew q hq
    rw [hqj] at hid
    simp only [outIdT] at hid
    have hji : j = id := Option.some.inj hid
    subst hji
    exact ⟨cnt, d, hqj, hd, hcnt, hg⟩
  have hreply : ∀ id, ReplyWait T' id ↔ ReplyWait T id := by
    intro id
    constructor
    · rintro ⟨q, hq, cnt, hqc⟩
      rcases (hmem q).mp hq with h0 | h1
      · exact ⟨q, h0, cnt, hqc⟩
      · obtain ⟨j, cnt', d, hqj, _⟩ := hnew q h1
        rw [hqj] at hqc
        cases hqc
    · rintro ⟨q, hq, cnt, hqc⟩
      exact ⟨q, (hmem q).mpr (Or.inl hq), cnt, hqc⟩
  have hdisc : ∀ id, DiscWait T' id ↔ DiscWait T id := by
    intro id; unfold DiscWait; rw [hTR]
  have hconnw : ∀ id, ConnWait T' id ↔ ConnWait T id := by
    intro id; unfold ConnWait; rw [hTR]
  constructor
  case pi =>
    intro id pc hp
    rw [hpg] at hp
    exact h.pi id pc hp
  case link =>
    intro id c hc
    obtain ⟨c0, hc0, hg⟩ := hback id c hc
    rcases h.link id c0 hc0 with ⟨pc, hp, hl⟩ | ⟨hp, hcls⟩
    · left
      refine ⟨pc, by rw [hpg]; exact hp, ?_⟩
      rw [hG, ← hg]; exact hl
    · right
      exact ⟨by rw [hpg]; exact hp, by rw [hcl]; exact hcls⟩
  case acc =>
    intro id pc c hp hc hl
    rw [hpg] at hp
    rw [hG] at hl
    obtain ⟨c0, hc0, hg⟩ := hback id c hc
    obtain ⟨c', hc', hgc, hoc, hwc, htc, hqc⟩ := hfwd id c0 hc0
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst hcc
    have hl0 : (pc.seq, c0.gen) ∈ T.c.genOf := by rw [hg]; exact hl
    obtain ⟨ha1, ha2⟩ := h.acc id pc c0 hp hc0 hl0
    rw [hqs]
    constructor
    · omega
    · omega
  case wq =>
    intro id c hc
    obtain ⟨c0, hc0, _⟩ := hback id c hc
    obtain ⟨c', hc', _, _, _, _, hqc⟩ := hfwd id c0 hc0
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst hcc
    rw [hqs]
    have := h.wq id c0 hc0
    omega
  case gen =>
    intro q hq id hid c hc
    rcases (hmem q).mp hq with h0 | h1
    · obtain ⟨c0, hc0, hg⟩ := hback id c hc
      have := h.gen q h0 id hid c0 hc0
      exact hg.symm.trans this
    · obtain ⟨cnt, d, _, hd, _, hg⟩ := hnewId q h1 id hid
      have hcd : c = d := Option.some.inj (hc.symm.trans hd)
      rw [hcd]; exact hg.symm
  case apply =>
    intro q hq id hcl' hid pc hpc
    rw [hpg] at hpc
    rcases (hmem q).mp hq with h0 | h1
    · rcases h.apply q h0 id hcl' hid pc hpc with h2 | h2
      · left; rw [hcl]; exact h2
      · right; rw [hG]; exact h2
    · obtain ⟨cnt, d, _, hd, _, hg⟩ := hnewId q h1 id hid
      obtain ⟨c0, hc0, hgc⟩ := hback id d hd
      rcases h.link id c0 hc0 with ⟨pc', hp', hl⟩ | ⟨hp', _⟩
      · have hpp : pc' = pc := Option.some.inj (hp'.symm.trans hpc)
        subst hpp
        right
        rw [hG, hg, ← hgc]
        exact hl
      · rw [hp'] at hpc; cases hpc
  case noOrphan =>
    intro q hq id hcl' hid hpn
    rw [hpg] at hpn
    rw [hcl]
    rcases (hmem q).mp hq with h0 | h1
    · exact h.noOrphan q h0 id hcl' hid hpn
    · obtain ⟨cnt, d, _, hd, _, _⟩ := hnewId q h1 id hid
      obtain ⟨c0, hc0, _⟩ := hback id d hd
      rcases h.link id c0 hc0 with ⟨pc', hp', _⟩ | ⟨_, hcls⟩
      · rw [hp'] at hpn; cases hpn
      · exact hcls
  case written =>
    intro q hq id cnt f hqf c hc hg
    rcases (hmem q).mp hq with h0 | h1
    · obtain ⟨c0, hc0, hgc⟩ := hback id c hc
      have h1 := h.written q h0 id cnt f hqf c0 hc0 (hgc.trans hg)
      obtain ⟨c', hc', _, _, hw, _, _⟩ := hfwd id c0 hc0
      have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst hcc
      exact Nat.le_trans h1 hw
    · obtain ⟨j, cnt', d, hqj, hd, hcnt, _⟩ := hnew q h1
      rw [hqj] at hqf
      have hw' := Relay.Out.written.inj hqf
      obtain ⟨hji, hcn, _⟩ := hw'
      subst hji
      have hcd : c = d := Option.some.inj (hc.symm.trans hd)
      rw [hcd, ← hcn]; exact hcnt
  case reset =>
    intro q hq id cnt hqf pc hpc hpd hl c hc hg
    rcases (hmem q).mp hq with h0 | h1
    · rw [hpg] at hpc
      obtain ⟨c0, hc0, hgc⟩ := hback id c hc
      obtain ⟨hq0, hqs0, hw0⟩ := h.reset q h0 id cnt hqf pc hpc hpd (by rw [hG] at hl; exact hl) c0 hc0 (hgc.trans hg)
      obtain ⟨c', hc', _, _, _, ht, hqc⟩ := hfwd id c0 hc0
      have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst hcc
      refine ⟨by omega, by rw [hqs]; exact hqs0, by omega⟩
    · obtain ⟨j, cnt', d, hqj, _⟩ := hnew q h1
      rw [hqj] at hqf
      cases hqf
  case barrier =>
    show List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) T'.c.toRelay
    rw [hTR]; exact h.barrier
  case connClean =>
    intro q hq id hqc
    rw [hTR] at hq
    exact hnone id (h.connClean q hq id hqc)
  case notOpen =>
    intro id pc hp hpo
    rw [hpg] at hp
    exact h.notOpen id pc hp hpo
  case cl =>
    intro q hq id hqc
    rw [hTR] at hq
    rw [hpg, hcl]
    exact h.cl q hq id hqc
  case rq =>
    intro q hq id cnt hqf x hx n
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.rq q h0 id cnt hqf x hx n
    · obtain ⟨j, cnt', d, hqj, _⟩ := hnew q h1
      rw [hqj] at hqf
      have := (Relay.Out.written.inj hqf).2.2
      omega
  case gensLt =>
    intro id c hc
    obtain ⟨c0, hc0, hg⟩ := hback id c hc
    rw [hng]
    have := h.gensLt id c0 hc0
    omega
  case gp =>
    intro q hq id hid g
    rw [hTR] at hq
    rw [hG]
    exact h.gp q hq id hid g
  case mirror => exact hclk
  case good => exact hgood
  case openG =>
    intro id pc hp hpo
    rw [hpg] at hp
    obtain ⟨g, hg⟩ := h.openG id pc hp hpo
    exact ⟨g, by rw [hG]; exact hg⟩

  case seqG =>
    intro p g hm
    rw [hG] at hm
    rw [hpage]
    exact h.seqG p g hm
  case seqQ =>
    intro q hq id hid
    rw [hTR] at hq
    rw [hpage]
    exact h.seqQ q hq id hid

  case disc =>
    intro q hq id hd pc hp hop
    rw [hTR] at hq
    rw [hpg] at hp
    exact h.disc q hq id hd pc hp hop
  case rep =>
    intro q hq id cnt hq1
    rcases (hmem q).mp hq with h0 | h1
    · rw [hpg, hpage]
      exact h.rep q h0 id cnt hq1
    · obtain ⟨j, cnt', d, hqj, _⟩ := hnew q h1
      rw [hqj] at hq1
      have := (Relay.Out.written.inj hq1).2.2
      omega
  case recvG =>
    intro id pc hp hr
    rw [hpg] at hp
    obtain ⟨g, hg⟩ := h.recvG id pc hp hr
    exact ⟨g, by rw [hG]; exact hg⟩

  case failNone =>
    intro q hq id e hfl
    rcases (hmem q).mp hq with h0 | h1
    · exact hnone id (h.failNone q h0 id e hfl)
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl
  case closedNone =>
    intro q hq id hfl
    rcases (hmem q).mp hq with h0 | h1
    · exact hnone id (h.closedNone q h0 id hfl)
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl
  case closedClosing =>
    intro q hq id hfl
    rw [hcl id]
    rcases (hmem q).mp hq with h0 | h1
    · exact h.closedClosing q h0 id hfl
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl
  case closedOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.closedOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b hb id hid _
      obtain ⟨j, cnt, d, hqj, _⟩ := hnew a ha
      rw [hqj] at hid
      cases hid
    · intro a ha b hb id hid hob
      obtain ⟨j, cnt, d, hqj, hd, _, _⟩ := hnew b hb
      rw [hqj] at hob
      have hji : j = id := by simpa [outIdT] using hob
      obtain ⟨c0, hc0, _⟩ := hback j d hd
      have hcn := h.closedNone a ha id hid
      rw [hji, hcn] at hc0
      cases hc0
  case closeClosing =>
    intro x hx id hxe
    rw [hTR] at hx
    rw [hcl id]
    exact h.closeClosing x hx id hxe
  case closedNoConn =>
    intro q hq id hfl x hx hxe
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.closedNoConn q h0 id hfl x hx hxe
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl
  case openRel =>
    intro id pc hp hop c hc
    rw [hpg] at hp
    obtain ⟨c0, hc0, hg⟩ := hback id c hc
    obtain ⟨c', hc', _, hio, _⟩ := hfwd id c0 hc0
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [← hcc, hio]
    exact h.openRel id pc hp hop c0 hc0
  case okOpen =>
    intro q hq id hfl hcl2 pc hp
    rw [hcl id] at hcl2
    rw [hpg] at hp
    rcases (hmem q).mp hq with h0 | h1
    · exact h.okOpen q h0 id hfl hcl2 pc hp
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl
  case okNoDisc =>
    intro q hq id hfl hcl2 x hx
    rw [hTR] at hx
    rw [hcl id] at hcl2
    rcases (hmem q).mp hq with h0 | h1
    · exact h.okNoDisc q h0 id hfl hcl2 x hx
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl
  case discRel =>
    intro x hx id hxd
    rw [hTR] at hx
    rcases h.discRel x hx id hxd with h0 | ⟨pc, hp, hop⟩ | ⟨hpn, hcl2⟩
    · exact Or.inl (hnone id h0)
    · exact Or.inr (Or.inl ⟨pc, by rw [hpg]; exact hp, hop⟩)
    · exact Or.inr (Or.inr ⟨by rw [hpg]; exact hpn, by rw [hcl id]; exact hcl2⟩)

  case closingNone =>
    intro j hcl2
    rw [hpage]
    rw [hcl j] at hcl2
    exact h.closingNone j hcl2
  case closedNoClose =>
    intro q hq id hfl x hx hxe
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.closedNoClose q h0 id hfl x hx hxe
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hfl
      cases hfl

end Ind
