
namespace Ind
open Timed

-- a socket event of the composed system keeps the invariant (the state is given by the clocked step's result)
theorem inv_sock (T T' : TSys) (h : Inv T) (id g : Nat) (kk : Relay.Sk)
    (hp : T'.c.page = T.c.page) (hr : T'.c.toRelay = T.c.toRelay) (hg : T'.c.genOf = T.c.genOf)
    (hrs : T'.c.rs = (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.1)
    (hto : T'.c.toPage = T.c.toPage ++ (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.2.map
      (fun o => (o, Client.tagOf T.c.rs (.sock id g kk))))
    (hck : T'.clk = (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).1) : Inv T' := by
  have hng : T'.c.rs.nextGen = T.c.rs.nextGen := by
    rw [hrs]; exact stepK_sock_nextGen Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  have hspec := stepK_sock_spec Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  have hmir := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk) h.mirror
  have hgood := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk) h.good
  have hFailS : ∀ o ∈ (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.2,
      ∀ id' e', o = Relay.Out.fail id' e' →
        ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.1.slot id').conn = none :=
    fun o ho id' e' hoe => stepK_sock_fail_fact Relay.DEFAULT_CAP T.clk T.c.rs id g kk o id' e' ho hoe
  have hOkS : ∀ o ∈ (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.2,
      ∀ id', o = Relay.Out.ok id' → ∃ c0, (T.c.rs.slot id').conn = some c0 ∧ c0.isOpen = false :=
    fun o ho id' hoe => stepK_sock_ok_fact Relay.DEFAULT_CAP T.clk T.c.rs id g kk o id' ho hoe
  have hFO0 := stepK_sock_outs_pw Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  have hOkPost : ∀ o ∈ (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.2, ∀ id', o = Relay.Out.ok id' →
      id' = id ∧ ∃ c0, (T.c.rs.slot id).conn = some c0 ∧
        ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk)).2.1.slot id).conn = some { c0 with isOpen := true } :=
    fun o ho id' hoe => stepK_sock_ok_post Relay.DEFAULT_CAP T.clk T.c.rs id g kk o id' ho hoe
  have hOkPW := stepK_sock_okpw Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  have hWr := stepK_sock_wr Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  have hWrLe := stepK_sock_wr_le Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  have hUniq := stepK_sock_one_wr Relay.DEFAULT_CAP T.clk T.c.rs id g kk
  generalize Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk) = S at hrs hto hck hspec hmir hgood hFailS hOkS hFO0 hOkPost hOkPW hWr hWrLe hUniq
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hspec
  have hid : ∀ j, j ≠ id → (T'.c.rs.slot j) = (T.c.rs.slot j) := fun j hj => by rw [hrs, p1 j hj]
  have hknown : ∀ j, (T'.c.rs.slot j).known = (T.c.rs.slot j).known := by
    intro j
    by_cases hj : j = id
    · subst hj; rw [hrs]; exact p2
    · rw [hid j hj]
  refine inv_env_gen T T' h hp hr hg hng hknown ?_ ?_ ?_ _ hto ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j c hc
    by_cases hj : j = id
    · subst hj
      unfold ConnOf at hc ⊢
      rw [hrs]
      exact p4 c hc
    · right
      refine ⟨c, ?_, rfl, fun h' => h', Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
      unfold ConnOf at hc ⊢
      rw [hid j hj]; exact hc
  · intro j hc
    unfold ConnOf at hc ⊢
    by_cases hj : j = id
    · subst hj; rw [hrs]; exact p3 hc
    · rw [hid j hj]; exact hc
  · intro j c' hc'
    unfold ConnOf at hc' ⊢
    by_cases hj : j = id
    · subst hj
      rw [hrs] at hc'
      cases hpre : (T.c.rs.slot j).conn with
      | none => rw [p3 hpre] at hc'; cases hc'
      | some c =>
        rcases p4 c hpre with hn | ⟨c'', hc'', hgen, _⟩
        · rw [hn] at hc'; cases hc'
        · have hcc : c'' = c' := Option.some.inj (hc''.symm.trans hc')
          subst hcc
          exact ⟨c, rfl, hgen.symm⟩
    · rw [hid j hj] at hc'
      exact ⟨c', hc', rfl⟩
  · intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    obtain ⟨hcl, hidn, hflag, hcnt⟩ := p5 o ho
    cases hpre : (T.c.rs.slot id).conn with
    | none =>
      have := p6 hpre
      rw [this] at ho
      simp at ho
    | some c =>
      refine ⟨hcl, id, c, hidn, by unfold ConnOf; exact hpre, ?_, ?_, ?_⟩
      · show Client.tagOf T.c.rs (.sock id g kk) = c.gen
        simp [Client.tagOf, Relay.evId, hpre]
      · intro cnt d hod hd
        unfold ConnOf at hd
        rw [hrs] at hd
        exact hcnt cnt d hod hd
      · intro cnt f hof
        exact hflag cnt f hof
  · rw [hck, hrs]; exact hmir
  · rw [hck]; exact hgood
  · intro q hq id' e' hfl
    rw [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    have hfl' : o = Relay.Out.fail id' e' := hfl
    show (T'.c.rs.slot id').conn = none
    rw [hrs]
    exact hFailS o ho id' e' hfl'
  · intro q hq id' hfl
    rw [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    have hfl' : o = Relay.Out.ok id' := hfl
    exact hOkS o ho id' hfl'
  · exact List.Pairwise.map _ (fun a b hab id' e h1 h2 => (hab id' e h1 h2).elim) hFO0
  · intro q hq id' hfl
    rw [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    have hfl' : o = Relay.Out.ok id' := hfl
    obtain ⟨hid, c0, hc0, hpost⟩ := hOkPost o ho id' hfl'
    refine ⟨{ c0 with isOpen := true }, ?_, ?_, rfl⟩
    · show (T'.c.rs.slot id').conn = some { c0 with isOpen := true }
      rw [hrs, hid]
      exact hpost
    · show c0.gen = Client.tagOf T.c.rs (Relay.Ev.sock id g kk)
      simp [Client.tagOf, Relay.evId, hc0]
  · exact List.Pairwise.map _ (fun a b hab id' h1 h2 => hab id' h1 h2) hOkPW
  · intro q hq j cnt hqj
    simp only [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    have hqj' : o = Relay.Out.written j cnt 0 := hqj
    obtain ⟨hjid, c0, hc0, hle⟩ := hWr o ho j cnt 0 hqj'
    refine ⟨c0, ?_, ?_, hle⟩
    · show (T.c.rs.slot j).conn = some c0
      rw [hjid]
      exact hc0
    · show c0.gen = Client.tagOf T.c.rs (Relay.Ev.sock id g kk)
      simp [Client.tagOf, Relay.evId, hc0]
  · intro a ha b hb j c1 c2 f1 f2 ha1 hb1
    simp only [List.mem_map] at ha hb
    obtain ⟨oa, hoa, rfl⟩ := ha
    obtain ⟨ob, hob, rfl⟩ := hb
    have hab : oa = ob := hUniq oa hoa ob hob j c1 c2 f1 f2 ha1 hb1
    rw [hab]
  · intro q hq j cnt hqj c hc hgc
    simp only [List.mem_map] at hq
    obtain ⟨o, ho, rfl⟩ := hq
    have hqj' : o = Relay.Out.written j cnt 0 := hqj
    obtain ⟨hjid, c0, hc0, hle⟩ := hWrLe o ho j cnt 0 hqj'
    unfold ConnOf at hc
    rw [hjid] at hc
    have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
    rw [hcc] at hle
    exact hle

end Ind
