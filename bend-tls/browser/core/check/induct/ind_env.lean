
namespace Ind
open Timed

-- a socket event (or a drain): the page, the queue and the page-to-relay map are kept; each relay connection keeps
-- its generation and its total and may open, or it fails (then none); the frames appended name a connection they
-- came from (their generation), and a WRITTEN frame has flag 0 and reports a count no more than the connection's
theorem inv_env_gen (T T' : TSys) (h : Inv T) (hpage : T'.c.page = T.c.page) (hTR : T'.c.toRelay = T.c.toRelay)
    (hG : T'.c.genOf = T.c.genOf) (hng : T'.c.rs.nextGen = T.c.rs.nextGen)
    (hknown : ∀ j, (T'.c.rs.slot j).known = (T.c.rs.slot j).known)
    (hconn : ∀ j c, ConnOf T j = some c → ConnOf T' j = none ∨ ∃ c', ConnOf T' j = some c' ∧ c'.gen = c.gen ∧
      (c.isOpen = true → c'.isOpen = true) ∧ c.written ≤ c'.written ∧
      c'.written + c'.queued ≤ c.written + c.queued ∧ c'.queued ≤ c.queued)
    (hnone : ∀ j, ConnOf T j = none → ConnOf T' j = none)
    (hback : ∀ j c', ConnOf T' j = some c' → ∃ c, ConnOf T j = some c ∧ c.gen = c'.gen)
    (new : List (Relay.Out × Nat)) (hTP : T'.c.toPage = T.c.toPage ++ new)
    (hnew : ∀ q ∈ new, isClosedOut q.1 = false ∧ ∃ j c, outIdT q.1 = some j ∧ ConnOf T j = some c ∧ q.2 = c.gen ∧
      (∀ cnt d, q.1 = Relay.Out.written j cnt 0 → ConnOf T' j = some d → cnt ≤ d.written) ∧
      (∀ cnt f, q.1 = Relay.Out.written j cnt f → f = 0))
    (hclk : Clock.Mirror T'.clk T'.c.rs) (hgood : Clock.Good T'.clk)
    (hfailN : ∀ q ∈ new, ∀ id e, q.1 = Relay.Out.fail id e → ConnOf T' id = none)
    (hokN : ∀ q ∈ new, ∀ id, q.1 = Relay.Out.ok id → ∃ c, ConnOf T id = some c ∧ c.isOpen = false)
    (hnewFO : List.Pairwise (fun p q => ∀ id e, p.1 = Relay.Out.fail id e → outIdT q.1 = some id → isClosedOut q.1 = true) new)
    (hokO : ∀ q ∈ new, ∀ id, q.1 = Relay.Out.ok id → ∃ c, ConnOf T' id = some c ∧ c.gen = q.2 ∧ c.isOpen = true)
    (hokU : List.Pairwise (fun p q => ∀ id, p.1 = Relay.Out.ok id → q.1 ≠ Relay.Out.ok id) new)
    (hnewLow : ∀ q ∈ new, ∀ j cnt, q.1 = Relay.Out.written j cnt 0 →
      ∃ c, ConnOf T j = some c ∧ c.gen = q.2 ∧ c.written ≤ cnt)
    (hnewUniq : ∀ a ∈ new, ∀ b ∈ new, ∀ j c1 c2 f1 f2, a.1 = Relay.Out.written j c1 f1 →
      b.1 = Relay.Out.written j c2 f2 → a = b)
    (hnewUp : ∀ q ∈ new, ∀ j cnt, q.1 = Relay.Out.written j cnt 0 → ∀ c, ConnOf T j = some c → q.2 = c.gen →
      cnt ≤ c.written + c.queued) : Inv T' := by
  -- a WRITTEN frame of a socket event is flag 0 at its own id
  have hnewFlag : ∀ q ∈ new, ∀ id cnt f, q.1 = Relay.Out.written id cnt f → f = 0 := by
    intro q hq id cnt f hqf
    obtain ⟨-, j, c, hoj, -, -, -, hf⟩ := hnew q hq
    have hjid : j = id := by
      rw [hqf] at hoj
      simp [outIdT] at hoj
      exact hoj.symm
    exact hf cnt f (by rw [hqf, hjid])
  have hmem : ∀ q, q ∈ T'.c.toPage ↔ q ∈ T.c.toPage ∨ q ∈ new := fun q => by
    rw [hTP, List.mem_append]
  have hpg : ∀ j, PageOf T' j = PageOf T j := fun j => by simp only [PageOf, hpage]
  have hcl : ∀ j, (T'.c.page.slots j).closing = (T.c.page.slots j).closing := fun j => by rw [hpage]
  have hqs : ∀ j, qs j T' = qs j T := fun j => by simp only [qs, hTR]
  have hpost2 : ∀ j c0 c, ConnOf T j = some c0 → ConnOf T' j = some c →
      c.gen = c0.gen ∧ (c0.isOpen = true → c.isOpen = true) ∧ c0.written ≤ c.written ∧
      c.written + c.queued ≤ c0.written + c0.queued ∧ c.queued ≤ c0.queued := by
    intro j c0 c hc0 hc
    rcases hconn j c0 hc0 with hn | ⟨c', hc', hg, ho, hw, ht, hq⟩
    · rw [hc] at hn; cases hn
    · have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst hcc
      exact ⟨hg, ho, hw, ht, hq⟩
  have hdisc : ∀ id, DiscWait T' id ↔ DiscWait T id := by
    intro id; unfold DiscWait; rw [hTR]
  have hconnw : ∀ id, ConnWait T' id ↔ ConnWait T id := by
    intro id; unfold ConnWait; rw [hTR]
  have hreply : ∀ id, ReplyWait T' id ↔ ReplyWait T id := by
    intro id
    constructor
    · rintro ⟨q, hq, cnt, hqc⟩
      rcases (hmem q).mp hq with h0 | h1
      · exact ⟨q, h0, cnt, hqc⟩
      · obtain ⟨_, j, c, hj, _, _, _, hz⟩ := hnew q h1
        have hjid : j = id := Option.some.inj (hj.symm.trans (by rw [hqc]; rfl))
        subst hjid
        have := hz cnt 1 hqc
        omega
    · rintro ⟨q, hq, cnt, hqc⟩
      exact ⟨q, (hmem q).mpr (Or.inl hq), cnt, hqc⟩
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
    obtain ⟨c0, hc0, _⟩ := hback id c hc
    obtain ⟨hg, _, hw, ht, hq⟩ := hpost2 id c0 c hc0 hc
    have hl0 : (pc.seq, c0.gen) ∈ T.c.genOf := by rw [← hg]; exact hl
    obtain ⟨ha1, ha2⟩ := h.acc id pc c0 hp hc0 hl0
    rw [hqs]
    constructor
    · omega
    · omega
  case wq =>
    intro id c hc
    obtain ⟨c0, hc0, _⟩ := hback id c hc
    obtain ⟨_, _, _, _, hq⟩ := hpost2 id c0 c hc0 hc
    rw [hqs]
    have := h.wq id c0 hc0
    omega
  case gen =>
    intro q hq id hid c hc
    rcases (hmem q).mp hq with h0 | h1
    · obtain ⟨c0, hc0, hg⟩ := hback id c hc
      exact hg.symm.trans (h.gen q h0 id hid c0 hc0)
    · obtain ⟨_, j, c0, hj, hc0, hgq, _, _⟩ := hnew q h1
      have hjid : j = id := Option.some.inj (hj.symm.trans hid)
      subst hjid
      obtain ⟨hg, _⟩ := hpost2 j c0 c hc0 hc
      exact hg.trans hgq.symm
  case apply =>
    intro q hq id hcl' hid pc hpc
    rw [hpg] at hpc
    rcases (hmem q).mp hq with h0 | h1
    · rcases h.apply q h0 id hcl' hid pc hpc with h2 | h2
      · left; rw [hcl]; exact h2
      · right; rw [hG]; exact h2
    · obtain ⟨_, j, c0, hj, hc0, hgq, _, _⟩ := hnew q h1
      have hjid : j = id := Option.some.inj (hj.symm.trans hid)
      subst hjid
      rcases h.link j c0 hc0 with ⟨pc', hp', hl⟩ | ⟨hp', _⟩
      · have hpp : pc' = pc := Option.some.inj (hp'.symm.trans hpc)
        subst hpp
        right
        rw [hG, hgq]
        exact hl
      · rw [hp'] at hpc
        cases hpc
  case noOrphan =>
    intro q hq id hcl' hid hpn
    rw [hpg] at hpn
    rw [hcl]
    rcases (hmem q).mp hq with h0 | h1
    · exact h.noOrphan q h0 id hcl' hid hpn
    · obtain ⟨_, j, c0, hj, hc0, _, _, _⟩ := hnew q h1
      have hjid : j = id := Option.some.inj (hj.symm.trans hid)
      subst hjid
      rcases h.link j c0 hc0 with ⟨pc', hp', _⟩ | ⟨_, hcls⟩
      · rw [hp'] at hpn
        cases hpn
      · exact hcls
  case written =>
    intro q hq id cnt f hqf c hc hg
    rcases (hmem q).mp hq with h0 | h1
    · obtain ⟨c0, hc0, hgc⟩ := hback id c hc
      have h1 := h.written q h0 id cnt f hqf c0 hc0 (hgc.trans hg)
      obtain ⟨_, _, hw, _, _⟩ := hpost2 id c0 c hc0 hc
      exact Nat.le_trans h1 hw
    · obtain ⟨_, j, c0, hj, _, _, hwc, hz⟩ := hnew q h1
      have hjid : j = id := Option.some.inj (hj.symm.trans (by rw [hqf]; rfl))
      subst hjid
      have hf := hz cnt f hqf
      subst hf
      exact hwc cnt c hqf hc
  case reset =>
    intro q hq id cnt hqf pc hpc hpd hl c hc hg
    rcases (hmem q).mp hq with h0 | h1
    · rw [hpg] at hpc
      obtain ⟨c0, hc0, hgc⟩ := hback id c hc
      obtain ⟨hq0, hqs0, hw0⟩ := h.reset q h0 id cnt hqf pc hpc hpd (by rw [hG] at hl; exact hl) c0 hc0 (hgc.trans hg)
      obtain ⟨_, _, hw', ht', hq'⟩ := hpost2 id c0 c hc0 hc
      refine ⟨by omega, by rw [hqs]; exact hqs0, by omega⟩
    · obtain ⟨_, j, c0, hj, _, _, _, hz⟩ := hnew q h1
      have hjid : j = id := Option.some.inj (hj.symm.trans (by rw [hqf]; rfl))
      subst hjid
      have := hz cnt 1 hqf
      omega
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
    · obtain ⟨_, j, c, hj, _, _, _, hz⟩ := hnew q h1
      rw [hqf] at hj
      have hji : j = id := by simp [outIdT] at hj; omega
      subst hji
      exact absurd (hz cnt 1 hqf) (by decide)
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
    · obtain ⟨_, j, c, hj, _, _, _, hz⟩ := hnew q h1
      rw [hq1] at hj
      have hji : j = id := by simp [outIdT] at hj; omega
      subst hji
      exact absurd (hz cnt 1 hq1) (by decide)
  case recvG =>
    intro id pc hp hr
    rw [hpg] at hp
    obtain ⟨g, hg⟩ := h.recvG id pc hp hr
    exact ⟨g, by rw [hG]; exact hg⟩

  case failNone =>
    intro q hq id e hfl
    rcases (hmem q).mp hq with h0 | h1
    · exact hnone id (h.failNone q h0 id e hfl)
    · exact hfailN q h1 id e hfl
  case closedNone =>
    intro q hq id hfl
    rcases (hmem q).mp hq with h0 | h1
    · exact hnone id (h.closedNone q h0 id hfl)
    · obtain ⟨hcl0, _⟩ := hnew q h1
      rw [hfl] at hcl0
      simp [isClosedOut] at hcl0
  case closedClosing =>
    intro q hq id hfl
    rw [hcl id]
    rcases (hmem q).mp hq with h0 | h1
    · exact h.closedClosing q h0 id hfl
    · obtain ⟨hcl0, _⟩ := hnew q h1
      rw [hfl] at hcl0
      simp [isClosedOut] at hcl0
  case closedOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.closedOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b hb id hid _
      obtain ⟨hcl0, _⟩ := hnew a ha
      rw [hid] at hcl0
      simp [isClosedOut] at hcl0
    · intro a ha b hb id hid hob
      obtain ⟨_, j, c, hj, hcj, _, _, _⟩ := hnew b hb
      rw [hj] at hob
      have hji : j = id := by simpa using hob
      have hcn := h.closedNone a ha id hid
      rw [hji, hcn] at hcj
      cases hcj
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
    · obtain ⟨hcl0, _⟩ := hnew q h1
      rw [hfl] at hcl0
      simp [isClosedOut] at hcl0
  case openRel =>
    intro id pc hp hop c hc
    rw [hpg] at hp
    obtain ⟨c0, hc0, hg⟩ := hback id c hc
    rcases hconn id c0 hc0 with hn | ⟨c', hc', _, hio, _⟩
    · rw [hc] at hn
      cases hn
    · have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
      rw [← hcc]
      exact hio (h.openRel id pc hp hop c0 hc0)
  case okOpen =>
    intro q hq id hfl hcl2 pc hp
    rw [hcl id] at hcl2
    rw [hpg] at hp
    rcases (hmem q).mp hq with h0 | h1
    · exact h.okOpen q h0 id hfl hcl2 pc hp
    · obtain ⟨c0, hc0, hfalse⟩ := hokN q h1 id hfl
      cases hpo' : pc.isOpen with
      | false => rfl
      | true =>
        have hcb := h.openRel id pc hp hpo' c0 hc0
        rw [hfalse] at hcb
        cases hcb
  case okNoDisc =>
    intro q hq id hfl hcl2 x hx
    rw [hTR] at hx
    rw [hcl id] at hcl2
    rcases (hmem q).mp hq with h0 | h1
    · exact h.okNoDisc q h0 id hfl hcl2 x hx
    · obtain ⟨c0, hc0, hfalse⟩ := hokN q h1 id hfl
      intro hxd
      rcases h.discRel x hx id hxd with h0 | ⟨pc, hp, hop⟩ | ⟨hpn, hcl3⟩
      · rw [hc0] at h0
        cases h0
      · have hcb := h.openRel id pc hp hop c0 hc0
        rw [hfalse] at hcb
        cases hcb
      · rw [hcl3] at hcl2
        cases hcl2
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
    · obtain ⟨hcl0, _⟩ := hnew q h1
      rw [hfl] at hcl0
      simp [isClosedOut] at hcl0

  case connPend =>
    intro x hx id hxi q hq
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.connPend x hx id hxi q h0
    · obtain ⟨_, j, c, hj, hcj, _⟩ := hnew q h1
      intro hq2
      rw [hj] at hq2
      have hji : j = id := by simpa [outIdT] using hq2
      rw [hji, h.connClean x hx id hxi] at hcj
      cases hcj
  case okRel =>
    intro q hq id hqi
    rcases (hmem q).mp hq with h0 | h1
    · rcases h.okRel q h0 id hqi with hn0 | ⟨c, hc, hg, ho⟩
      · exact Or.inl (hnone id hn0)
      · rcases hconn id c hc with hn1 | ⟨c', hc', hg', ho', _⟩
        · exact Or.inl hn1
        · exact Or.inr ⟨c', hc', hg'.trans hg, ho' ho⟩
    · exact Or.inr (hokO q h1 id hqi)
  case okOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.okOrd, hokU, ?_⟩
    intro a ha b hb id hai hbi
    obtain ⟨c, hc, hco⟩ := hokN b hb id hbi
    rcases h.okRel a ha id hai with hn | ⟨c', hc', _, ho'⟩
    · rw [hc] at hn
      cases hn
    · rw [hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc, hco] at ho'
      cases ho'

  case wrSent =>
    intro q hq id cnt f hqj pc hpc hgq
    have hpc0 : PageOf T id = some pc := by
      unfold PageOf at hpc ⊢
      rw [hpage] at hpc
      exact hpc
    rw [hG] at hgq
    rcases (hmem q).mp hq with h0 | h1
    · exact h.wrSent q h0 id cnt f hqj pc hpc0 hgq
    · obtain ⟨-, j, c, hoj, hcon, hgc, -, -⟩ := hnew q h1
      have hjid : j = id := by
        rw [hqj] at hoj
        simp [outIdT] at hoj
        exact hoj.symm
      have hf0 : f = 0 := hnewFlag q h1 id cnt f hqj
      have hu := hnewUp q h1 id cnt (by rw [hqj, hf0]) c (by rw [← hjid]; exact hcon) (by rw [← hgc]) 
      obtain ⟨hacc1, -⟩ := h.acc id pc c hpc0 (by rw [← hjid]; exact hcon) (by rw [← hgc]; exact hgq)
      omega
  case replyFrozen =>
    intro q hq id cnt hqj c' hc' hcg'
    rcases (hmem q).mp hq with h0 | h1
    · obtain ⟨c0, hc0, hc0g⟩ := hback id c' hc'
      obtain ⟨h1q, h2q⟩ := h.replyFrozen q h0 id cnt hqj c0 hc0 (hc0g.trans hcg')
      rcases hconn id c0 hc0 with hn | ⟨c'', hc'', -, -, hwl, hsum, hql⟩
      · rw [hn] at hc'
        cases hc'
      · have hcc : c'' = c' := Option.some.inj (hc''.symm.trans hc')
        rw [hcc] at hwl hsum hql
        constructor <;> omega
    · exact absurd (hnewFlag q h1 id cnt 1 hqj) (by decide)
  case replyMax =>
    intro q hq r hr id c1 c2 f h1 h2 hg
    rcases (hmem q).mp hq with h0 | h1'
    · rcases (hmem r).mp hr with h0' | h1''
      · exact h.replyMax q h0 r h0' id c1 c2 f h1 h2 hg
      · obtain ⟨-, j, c, hoj, hcon, hgc, -, -⟩ := hnew r h1''
        have hjid : j = id := by
          rw [h2] at hoj
          simp [outIdT] at hoj
          exact hoj.symm
        have hf0 : f = 0 := hnewFlag r h1'' id c2 f h2
        have hu := hnewUp r h1'' id c2 (by rw [h2, hf0]) c (by rw [← hjid]; exact hcon) hgc
        have hrf := h.replyFrozen q h0 id c1 h1 c (by rw [← hjid]; exact hcon) (hgc.symm.trans hg)
        obtain ⟨hq0, hq1⟩ := hrf
        omega
    · exact absurd (hnewFlag q h1' id c1 1 h1) (by decide)
  case closeUniq =>
    intro id
    rw [hTR]
    exact h.closeUniq id
  case connSeq =>
    intro s
    rw [hTR]
    exact h.connSeq s
  case noDeny =>
    intro x hx
    rw [hTR] at hx
    exact h.noDeny x hx
  case discOnce =>
    intro q hq id cnt hqj x hx
    rw [hTR] at hx
    rcases (hmem q).mp hq with h0 | h1
    · exact h.discOnce q h0 id cnt hqj x hx
    · cases hnewFlag q h1 id cnt 1 hqj
  case discUniq =>
    intro id
    have hn : new.filter (DiscRep id) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx hxt
      obtain ⟨c, hc⟩ := discRep_spec id x hxt
      exact absurd (hnewFlag x hx id c 1 hc) (by decide)
    rw [hTP, List.filter_append, hn, List.append_nil]
    exact h.discUniq id
  case wrMono =>
    intro q hq id cnt f hqj pc hpc hg
    have hpc' : PageOf T id = some pc := by
      have h1 := hpc
      unfold PageOf at h1 ⊢
      rw [hpage] at h1
      exact h1
    have hg' : (pc.seq, q.2) ∈ T.c.genOf := by rw [hG] at hg; exact hg
    rcases (hmem q).mp hq with h0 | h1
    · exact h.wrMono q h0 id cnt f hqj pc hpc' hg'
    · have hf0 : f = 0 := hnewFlag q h1 id cnt f hqj
      obtain ⟨c', hc', hgc', hlow⟩ := hnewLow q h1 id cnt (by rw [hqj, hf0])
      have hacc := h.acc id pc c' hpc' hc' (by rw [hgc']; exact hg')
      exact Nat.le_trans hacc.2 hlow
  case wrOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.wrOrd, pairwise_of_forall _ new ?_, ?_⟩
    · intro a ha b hb id c1 f1 c2 f2 ha1 hb1 _
      have hab := hnewUniq a ha b hb id c1 c2 f1 f2 ha1 hb1
      rw [hab] at ha1
      have hc12 := (Relay.Out.written.inj (ha1.symm.trans hb1)).2.1
      exact Nat.le_of_eq hc12
    · intro a ha b hb id c1 f1 c2 f2 ha1 hb1 hgab
      have hf0 : f2 = 0 := hnewFlag b hb id c2 f2 hb1
      obtain ⟨c, hc, hgc, hlow⟩ := hnewLow b hb id c2 (by rw [hb1, hf0])
      have hgcg : c.gen = a.2 := hgc.trans hgab.symm
      have hw := h.written a ha id c1 f1 ha1 c hc hgcg
      exact Nat.le_trans hw hlow
  case genFun =>
    intro p g1 g2 h1 h2
    rw [hG] at h1 h2
    exact h.genFun p g1 g2 h1 h2
  case failOrd =>
    rw [hTP]
    refine List.pairwise_append.mpr ⟨h.failOrd, hnewFO, ?_⟩
    intro a ha b hb id e hid hob
    obtain ⟨_, j, c, hj, hcj, _, _, _⟩ := hnew b hb
    rw [hj] at hob
    have hji : j = id := by simpa using hob
    have hcn := h.failNone a ha id e hid
    rw [hji, hcn] at hcj
    cases hcj

end Ind
