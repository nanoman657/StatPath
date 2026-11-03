namespace Ind
open Timed

-- the page's fixed flag is set at the start and never changes: every page operation rebuilds the state with the
-- record update, so the flag is the one it had
theorem die_fixed (st : Page.State) (id : Nat) (c : Page.PConn) (e : Nat) :
    (Page.die st id c e).1.fixed = st.fixed := by
  unfold Page.die
  simp [Page.setSlot]

theorem doClose_fixed (st : Page.State) (id : Nat) : (Page.doClose st id).1.fixed = st.fixed := by
  unfold Page.doClose Page.die
  repeat' split
  all_goals first | rfl | simp [Page.setSlot]

theorem wake_fixed (st : Page.State) (id : Nat) : (Page.wake st id).1.fixed = st.fixed := by
  unfold Page.wake
  dsimp only
  split
  · rfl
  · show (Page.setSlot st id _).fixed = st.fixed
    rfl

theorem doSend_fixed (st : Page.State) (id n : Nat) : (Page.doSend st id n).1.fixed = st.fixed := by
  unfold Page.doSend
  repeat' split
  all_goals first | rfl | simp [Page.setSlot]

theorem doRecv_fixed (st : Page.State) (id max : Nat) : (Page.doRecv st id max).1.fixed = st.fixed := by
  unfold Page.doRecv
  repeat' split
  all_goals first | rfl | simp [Page.setSlot, wake_fixed]

theorem doDiscard_fixed (st : Page.State) (id : Nat) : (Page.doDiscard st id).1.fixed = st.fixed := by
  unfold Page.doDiscard
  repeat' split
  all_goals first | rfl | simp [Page.setSlot]

theorem frame_fixed (st : Page.State) (o : Relay.Out) : (Page.frame st o).1.fixed = st.fixed := by
  unfold Page.frame
  repeat' split
  all_goals first | rfl | simp [Page.setSlot, Page.die, doClose_fixed, wake_fixed]

theorem doConnect_fixed (st : Page.State) : (Page.doConnect st).1.fixed = st.fixed := by
  unfold Page.doConnect
  repeat' split
  all_goals first | rfl | simp [Page.setSlot]

theorem page_step_fixed (st : Page.State) (i : Page.In) : (Page.step st i).1.fixed = st.fixed := by
  cases i with
  | connect => exact doConnect_fixed st
  | close id => exact doClose_fixed st id
  | send id n => exact doSend_fixed st id n
  | recv id max => exact doRecv_fixed st id max
  | discard id => exact doDiscard_fixed st id
  | frame o => exact frame_fixed st o

-- the page of each transition: a page call and a page frame keep the flag, and the others leave the page alone
theorem tPageCall_fixed (T T' : TSys) (i : Page.In) (hT : tPageCall T i = some T') :
    T'.c.page.fixed = T.c.page.fixed := by
  unfold tPageCall lift Client.pageCall at hT
  simp only [Option.map_some, Option.some.injEq] at hT
  subst hT
  exact page_step_fixed _ _

theorem doPage_fixed (v c' : Client.Sys) (h : Client.doPage v = some c') : c'.page.fixed = v.page.fixed := by
  unfold Client.doPage at h
  cases hq : v.toPage with
  | nil => rw [hq] at h; cases h
  | cons x rest =>
    obtain ⟨o, t⟩ := x
    rw [hq] at h
    dsimp only at h
    cases hf : Page.frame v.page o with
    | mk st' obs =>
      rw [hf] at h
      dsimp only at h
      cases h
      have hfx := frame_fixed v.page o
      rw [hf] at hfx
      exact hfx

theorem tDoPage_fixed (T T' : TSys) (hT : tDoPage T = some T') : T'.c.page.fixed = T.c.page.fixed := by
  unfold tDoPage lift at hT
  cases hd : Client.doPage T.c with
  | none => simp [hd] at hT
  | some c' =>
    simp only [hd, Option.map_some, Option.some.injEq] at hT
    subst hT
    exact doPage_fixed T.c _ hd

theorem tDoRelay_page (T T' : TSys) (hT : tDoRelay T = some T') : T'.c.page = T.c.page := by
  unfold tDoRelay at hT
  cases hq : T.c.toRelay with
  | nil => rw [hq] at hT; cases hT
  | cons x rest =>
    obtain ⟨e, p⟩ := x
    rw [hq] at hT
    dsimp only at hT
    cases hT
    rfl

theorem tDoEnv_page (T T' : TSys) (e : Relay.Ev) (hT : tDoEnv T e = some T') : T'.c.page = T.c.page := by
  unfold tDoEnv at hT
  cases e with
  | sock id g k =>
    dsimp only at hT
    split at hT
    · cases hT
    · cases hT
      rfl
  | _ => cases hT

theorem tTick_page (T : TSys) (ms : Nat) : (tTick T ms).c.page = T.c.page := rfl

end Ind
