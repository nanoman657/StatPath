
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
    (hclk : Clock.Mirror T'.clk T'.c.rs) (hgood : Clock.Good T'.clk) : Inv T' := by
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

end Ind
