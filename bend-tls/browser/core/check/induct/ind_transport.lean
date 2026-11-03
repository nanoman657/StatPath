
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
    (hnewLow : ∀ q ∈ new, ∀ j cnt, q.1 = Relay.Out.written j cnt 0 →
      ∃ c, ConnOf T j = some c ∧ c.gen = q.2 ∧ c.written ≤ cnt)
    (hnewUniq : ∀ a ∈ new, ∀ b ∈ new, ∀ j c1 c2 f1 f2, a.1 = Relay.Out.written j c1 f1 →
      b.1 = Relay.Out.written j c2 f2 → a = b)
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

  case connPend =>
    intro x hx id hxi q hq
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.connPend x hx id hxi q h0
    · obtain ⟨j, cnt, d, hqj, hd, _⟩ := hnew q h1
      intro hq2
      rw [hqj] at hq2
      have hji : j = id := by simpa [outIdT] using hq2
      have hn := hnone id (h.connClean x hx id hxi)
      rw [hji] at hd
      unfold ConnOf at hn
      rw [hd] at hn
      cases hn
  case okRel =>
    intro q hq id hqi
    rcases (hmem q).mp hq with h0 | h1
    · rcases h.okRel q h0 id hqi with hn0 | ⟨c, hc, hg, ho⟩
      · exact Or.inl (hnone id hn0)
      · obtain ⟨c', hc', hg', ho', _⟩ := hfwd id c hc
        exact Or.inr ⟨c', hc', hg'.trans hg, ho'.trans ho⟩
    · obtain ⟨j, cnt, d, hqj, _⟩ := hnew q h1
      rw [hqj] at hqi
      cases hqi
  case okOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.okOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b _ id hid
      obtain ⟨j, cnt, d, hqj, _⟩ := hnew a ha
      rw [hqj] at hid
      cases hid
    · intro a _ b hb id _ hbid
      obtain ⟨j, cnt, d, hqj, _⟩ := hnew b hb
      rw [hqj] at hbid
      cases hbid

  case discOnce =>
    intro q hq id cnt hqj x hx
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.discOnce q h0 id cnt hqj x hx
    · obtain ⟨j, cnt', d, hq', -⟩ := hnew q h1
      rw [hq'] at hqj
      cases hqj
  case discUniq =>
    intro id
    have hn : new.filter (DiscRep id) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx hxt
      obtain ⟨j, cnt', d, hx', -⟩ := hnew x hx
      rw [discRep_flag0 id j cnt' x hx'] at hxt
      exact absurd hxt (by decide)
    rw [hTP, List.filter_append, hn, List.append_nil]
    exact h.discUniq id
  case wrMono =>
    intro q hq id cnt f hqj pc hpc hg
    have hpc' : PageOf T id = some pc := by rw [← hpg id]; exact hpc
    have hg' : (pc.seq, q.2) ∈ T.c.genOf := by rw [hG] at hg; exact hg
    rcases (hmem q).mp hq with h0 | h1
    · exact h.wrMono q h0 id cnt f hqj pc hpc' hg'
    · obtain ⟨j, cnt', d, hq', -⟩ := hnew q h1
      rw [hq'] at hqj
      obtain ⟨hjj, hcc, -⟩ := Relay.Out.written.inj hqj
      obtain ⟨c, hc, hgc, hlow⟩ := hnewLow q h1 j cnt' hq'
      have hacc := h.acc j pc c (by rw [hjj]; exact hpc') hc (by rw [hgc]; exact hg')
      exact Nat.le_trans hacc.2 (by rw [← hcc]; exact hlow)
  case wrOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.wrOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b hb id c1 f1 c2 f2 ha1 hb1 _
      have hab := hnewUniq a ha b hb id c1 c2 f1 f2 ha1 hb1
      rw [hab] at ha1
      have hc12 := (Relay.Out.written.inj (ha1.symm.trans hb1)).2.1
      exact Nat.le_of_eq hc12
    · intro a ha b hb id c1 f1 c2 f2 ha1 hb1 hgab
      obtain ⟨j, cnt, d, hb', -⟩ := hnew b hb
      rw [hb'] at hb1
      obtain ⟨hjj, hcc, -⟩ := Relay.Out.written.inj hb1
      obtain ⟨c, hc, hgc, hlow⟩ := hnewLow b hb j cnt hb'
      have hc' : ConnOf T id = some c := by rw [← hjj]; exact hc
      have hgcg : c.gen = a.2 := hgc.trans hgab.symm
      have hw := h.written a ha id c1 f1 ha1 c hc' hgcg
      exact Nat.le_trans hw (by rw [hcc] at hlow; exact hlow)
  case genFun =>
    intro p g1 g2 h1 h2
    rw [hG] at h1 h2
    exact h.genFun p g1 g2 h1 h2
  case wrSent =>
    intro q hq id cnt f hqj pc hpc hgq
    rw [hpg] at hpc
    rw [hG] at hgq
    rcases (hmem q).mp hq with h0 | h1
    · exact h.wrSent q h0 id cnt f hqj pc hpc hgq
    · obtain ⟨j, cnt', d, hq', hd, hle, hgd⟩ := hnew q h1
      obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj (hq'.symm.trans hqj)
      obtain ⟨c, hc, hcg⟩ := hback j d hd
      obtain ⟨d', hd', -, -, -, hsum, -⟩ := hfwd j c hc
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      rw [hdd] at hsum
      obtain ⟨hacc1, -⟩ := h.acc j pc c hpc hc (by rw [hcg, ← hgd]; exact hgq)
      omega
  case replyFrozen =>
    intro q hq id cnt hqj c hc hcg
    rcases (hmem q).mp hq with h0 | h1
    · obtain ⟨c0, hc0, hc0g⟩ := hback id c hc
      obtain ⟨d', hd', -, -, hwl, hsum, hqle⟩ := hfwd id c0 hc0
      have hdd : d' = c := Option.some.inj (hd'.symm.trans hc)
      rw [hdd] at hsum hwl hqle
      obtain ⟨h1q, h2q⟩ := h.replyFrozen q h0 id cnt hqj c0 hc0 (hc0g.trans hcg)
      constructor <;> omega
    · obtain ⟨j, cnt', d, hq', -⟩ := hnew q h1
      obtain ⟨-, -, h01⟩ := Relay.Out.written.inj (hq'.symm.trans hqj)
      exact absurd h01 (by decide)
  case replyMax =>
    intro q hq r hr id c1 c2 f h1 h2 hg
    rcases (hmem q).mp hq with h0 | h1'
    · rcases (hmem r).mp hr with h0' | h1''
      · exact h.replyMax q h0 r h0' id c1 c2 f h1 h2 hg
      · obtain ⟨j, cnt', d, hr', hd, hle, hgd⟩ := hnew r h1''
        obtain ⟨rfl, rfl, -⟩ := Relay.Out.written.inj (hr'.symm.trans h2)
        obtain ⟨c0, hc0, hc0g⟩ := hback j d hd
        have hrf := h.replyFrozen q h0 j c1 h1 c0 hc0 (hc0g.trans (hgd.symm.trans hg))
        obtain ⟨d', hd', -, -, -, hsum, -⟩ := hfwd j c0 hc0
        have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
        rw [hdd] at hsum
        obtain ⟨hr1, hr2⟩ := hrf
        omega
    · obtain ⟨j, cnt', d, hq', -⟩ := hnew q h1'
      obtain ⟨-, -, h01⟩ := Relay.Out.written.inj (hq'.symm.trans h1)
      exact absurd h01 (by decide)
  case closeUniq =>
    intro id
    rw [hTR]
    exact h.closeUniq id
  case connSeq =>
    intro s
    rw [hTR]
    exact h.connSeq s
  case connAux =>
    refine ⟨⟨by rw [hpage]; exact h.connAux.1.1, fun q hq id hqid => h.connAux.1.2 q (by rw [hTR] at hq; exact hq) id hqid⟩, ?_⟩
    intro q hq id cnt f hqf
    rcases (hmem q).mp hq with h1 | h1
    · rw [hng]
      exact h.connAux.2 q h1 id cnt f hqf
    · obtain ⟨j, cnt', d, -, hd, -, hgd⟩ := hnew q h1
      obtain ⟨c0, hc0, hg0⟩ := hback j d hd
      have hlt := h.gensLt j c0 hc0
      rw [hng, hgd, ← hg0]
      exact hlt
  case noDeny =>
    intro x hx
    rw [hTR] at hx
    exact h.noDeny x hx
  case failOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.failOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b hb id e hid _
      obtain ⟨j, cnt, d, hqj, _⟩ := hnew a ha
      rw [hqj] at hid
      cases hid
    · intro a ha b hb id e hid hob
      obtain ⟨j, cnt, d, hqj, hd, _, _⟩ := hnew b hb
      rw [hqj] at hob
      have hji : j = id := by simpa [outIdT] using hob
      obtain ⟨c0, hc0, _⟩ := hback j d hd
      have hcn := h.failNone a ha id e hid
      rw [hji, hcn] at hc0
      cases hc0

end Ind
