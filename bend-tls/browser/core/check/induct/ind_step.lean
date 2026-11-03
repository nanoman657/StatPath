namespace Ind
open Timed

-- one transition of the timed composition: a page call, the relay's step, the page's frame, a socket event of the
-- environment, or the time going on
def TStep (T T' : TSys) : Prop :=
  tPageCall T .connect = some T' ∨
  (∃ i, tPageCall T (.close i) = some T') ∨
  (∃ i, tPageCall T (.discard i) = some T') ∨
  (∃ i max, tPageCall T (.recv i max) = some T') ∨
  (∃ i n, tPageCall T (.send i n) = some T') ∨
  tDoRelay T = some T' ∨
  tDoPage T = some T' ∨
  (∃ e, tDoEnv T e = some T') ∨
  (∃ ms, tTick T ms = T')

-- the relay's head event, dispatched to its step lemma (a deny or a socket event is not queued: noDeny)
theorem inv_tDoRelay (T T' : TSys) (h : Inv T) (hT : tDoRelay T = some T') : Inv T' := by
  cases hq : T.c.toRelay with
  | nil =>
    unfold tDoRelay at hT
    rw [hq] at hT
    cases hT
  | cons x rest =>
    obtain ⟨e, p⟩ := x
    cases e with
    | connect id => exact inv_tDoRelay_connect T T' h id p rest hq hT
    | send id n => exact inv_tDoRelay_send T T' h id n p rest hq hT
    | discard id => exact inv_tDoRelay_discard T T' h id p rest hq hT
    | read id k => exact inv_tDoRelay_read T T' h id k p rest hq hT
    | close id => exact inv_tDoRelay_close T T' h id p rest hq hT
    | deny id =>
      exact ((h.noDeny (Relay.Ev.deny id, p) (by rw [hq]; exact List.mem_cons_self)).1 id rfl).elim
    | sock id g k =>
      exact ((h.noDeny (Relay.Ev.sock id g k, p) (by rw [hq]; exact List.mem_cons_self)).2 id g k rfl).elim

-- the page's frame at the head of the queue: a closed or a frame of a connection the page has, or an ignored one
theorem inv_tDoPage_head (T T' : TSys) (h : Inv T) (o : Relay.Out) (t : Nat) (rest : List (Relay.Out × Nat))
    (hq : T.c.toPage = (o, t) :: rest) (hT : tDoPage T = some T') : Inv T' := by
  have hmem : (o, t) ∈ T.c.toPage := by
    rw [hq]
    exact List.mem_cons_self
  cases o with
  | closed id => exact inv_tDoPage_closed T T' h id t rest hq hT
  | wsclose c =>
    exact inv_tDoPage_ignored T T' h (Relay.Out.wsclose c) t rest hq rfl (fun j h' => by cases h') hT
  | ok id =>
    by_cases hn : Page.applies T.c.page (Relay.Out.ok id) = none
    · exact inv_tDoPage_ignored T T' h (Relay.Out.ok id) t rest hq hn (fun j h' => by cases h') hT
    · unfold Page.applies at hn
      by_cases hcl : (T.c.page.slots id).closing = true
      · simp [hcl] at hn
      · have hcl0 : (T.c.page.slots id).closing = false := by simpa using hcl
        cases hc : (T.c.page.slots id).conn with
        | none => simp [hc] at hn
        | some c =>
          exact inv_tDoPage_ok T T' h id t rest hq c hc hcl0 (h.okOpen _ hmem id rfl hcl0 c hc) hT
  | data id n =>
    by_cases hn : Page.applies T.c.page (Relay.Out.data id n) = none
    · exact inv_tDoPage_ignored T T' h (Relay.Out.data id n) t rest hq hn (fun j h' => by cases h') hT
    · unfold Page.applies at hn
      by_cases hcl : (T.c.page.slots id).closing = true
      · simp [hcl] at hn
      · have hcl0 : (T.c.page.slots id).closing = false := by simpa using hcl
        cases hc : (T.c.page.slots id).conn with
        | none => simp [hc] at hn
        | some c => exact inv_tDoPage_data T T' h id n t rest hq c hc hcl0 hT
  | eof id =>
    by_cases hn : Page.applies T.c.page (Relay.Out.eof id) = none
    · exact inv_tDoPage_ignored T T' h (Relay.Out.eof id) t rest hq hn (fun j h' => by cases h') hT
    · unfold Page.applies at hn
      by_cases hcl : (T.c.page.slots id).closing = true
      · simp [hcl] at hn
      · have hcl0 : (T.c.page.slots id).closing = false := by simpa using hcl
        cases hc : (T.c.page.slots id).conn with
        | none => simp [hc] at hn
        | some c => exact inv_tDoPage_eof T T' h id t rest hq c hc hcl0 hT
  | written id cnt f =>
    by_cases hn : Page.applies T.c.page (Relay.Out.written id cnt f) = none
    · exact inv_tDoPage_ignored T T' h (Relay.Out.written id cnt f) t rest hq hn (fun j h' => by cases h') hT
    · unfold Page.applies at hn
      by_cases hcl : (T.c.page.slots id).closing = true
      · simp [hcl] at hn
      · have hcl0 : (T.c.page.slots id).closing = false := by simpa using hcl
        cases hc : (T.c.page.slots id).conn with
        | none => simp [hc] at hn
        | some c => exact inv_tDoPage_written T T' h id t cnt f rest hq c hc hcl0 hT
  | fail id e =>
    by_cases hn : Page.applies T.c.page (Relay.Out.fail id e) = none
    · exact inv_tDoPage_ignored T T' h (Relay.Out.fail id e) t rest hq hn (fun j h' => by cases h') hT
    · unfold Page.applies at hn
      by_cases hcl : (T.c.page.slots id).closing = true
      · simp [hcl] at hn
      · have hcl0 : (T.c.page.slots id).closing = false := by simpa using hcl
        cases hc : (T.c.page.slots id).conn with
        | none => simp [hc] at hn
        | some c => exact inv_tDoPage_fail T T' h id e t rest hq c hc hcl0 hT

theorem inv_tDoPage (T T' : TSys) (h : Inv T) (hT : tDoPage T = some T') : Inv T' := by
  cases hq : T.c.toPage with
  | nil =>
    unfold tDoPage lift Client.doPage at hT
    rw [hq] at hT
    cases hT
  | cons x rest =>
    obtain ⟨o, t⟩ := x
    exact inv_tDoPage_head T T' h o t rest hq hT

-- one transition keeps the invariant
theorem inv_step (T T' : TSys) (h : Inv T) (hfix : T.c.page.fixed = true) (hS : TStep T T') : Inv T' := by
  rcases hS with h1 | ⟨i, h2⟩ | ⟨i, h2⟩ | ⟨i, max, h2⟩ | ⟨i, n, h2⟩ | h2 | h2 | ⟨e, h2⟩ | ⟨ms, h2⟩
  · exact inv_tPageConnect T T' h h1
  · exact inv_tPageClose T T' h hfix i h2
  · exact inv_tPageDiscard T T' h i h2
  · exact inv_tPageRecv T T' h i max h2
  · exact inv_tPageSend T T' h i n h2
  · exact inv_tDoRelay T T' h h2
  · exact inv_tDoPage T T' h h2
  · exact inv_env T T' h e h2
  · subst h2
    exact inv_tick T ms h

theorem TStep_fixed (T T' : TSys) (hfix : T.c.page.fixed = true) (hS : TStep T T') : T'.c.page.fixed = true := by
  rcases hS with h1 | ⟨i, h2⟩ | ⟨i, h2⟩ | ⟨i, max, h2⟩ | ⟨i, n, h2⟩ | h2 | h2 | ⟨e, h2⟩ | ⟨ms, h2⟩
  · rw [tPageCall_fixed T T' _ h1, hfix]
  · rw [tPageCall_fixed T T' _ h2, hfix]
  · rw [tPageCall_fixed T T' _ h2, hfix]
  · rw [tPageCall_fixed T T' _ h2, hfix]
  · rw [tPageCall_fixed T T' _ h2, hfix]
  · rw [tDoRelay_page T T' h2, hfix]
  · rw [tDoPage_fixed T T' h2, hfix]
  · rw [tDoEnv_page T T' e h2, hfix]
  · subst h2
    rw [tTick_page, hfix]

-- the reachable states: the timed composition from its start, one transition at a time
inductive TReach : TSys → Prop
  | init (cps bps : Nat) : TReach (TSys.init true cps bps)
  | step {T T' : TSys} : TReach T → TStep T T' → TReach T'

theorem reach_inv (T : TSys) (hR : TReach T) : Inv T ∧ T.c.page.fixed = true := by
  induction hR with
  | init cps bps => exact ⟨inv_init cps bps, rfl⟩
  | step hR hS ih => exact ⟨inv_step _ _ ih.1 ih.2 hS, TStep_fixed _ _ ih.2 hS⟩

-- the window claim: in every reachable state the connection's queued bytes and the bytes the relay's queue holds for
-- the id are within the window; so the head SEND of an id is within the window of its connection (the relay's check
-- does not fire)
theorem window_queue (T : TSys) (hR : TReach T) (id : Nat) (c : Relay.Conn) (hc : ConnOf T id = some c) :
    c.queued + qs id T ≤ Relay.SEND_WINDOW :=
  (reach_inv T hR).1.wq id c hc

theorem window_head (T : TSys) (hR : TReach T) (id n p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest) (c : Relay.Conn) (hc : ConnOf T id = some c) :
    n ≤ Relay.SEND_WINDOW - c.queued := by
  have hW := window_queue T hR id c hc
  have hQ := qs_head_send T id n p rest hq
  omega

end Ind
