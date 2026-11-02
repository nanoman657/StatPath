
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
  generalize Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (.sock id g kk) = S at hrs hto hck hspec hmir hgood
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hspec
  have hid : ∀ j, j ≠ id → (T'.c.rs.slot j) = (T.c.rs.slot j) := fun j hj => by rw [hrs, p1 j hj]
  have hknown : ∀ j, (T'.c.rs.slot j).known = (T.c.rs.slot j).known := by
    intro j
    by_cases hj : j = id
    · subst hj; rw [hrs]; exact p2
    · rw [hid j hj]
  refine inv_env_gen T T' h hp hr hg hng hknown ?_ ?_ ?_ _ hto ?_ ?_ ?_
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

end Ind
