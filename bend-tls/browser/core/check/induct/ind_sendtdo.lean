namespace Ind
open Timed

-- a SEND at the head of the relay's queue, through the clock: each case of the relay's step keeps the invariant
theorem inv_tDoRelay_send (T T' : TSys) (h : Inv T) (id n p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest) (hT : tDoRelay T = some T') : Inv T' := by
  unfold tDoRelay at hT
  simp only [hq] at hT
  simp only [Option.some.injEq] at hT
  subst hT
  by_cases hcl : T.c.rs.closed.isSome = true
  · rw [stepK_closed_gen Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n) hcl]
    exact inv_send_keep T h id n p rest hq _ _ T.c.rs [] rfl rfl rfl rfl (by simp) rfl (fun _ => rfl) rfl
      h.mirror h.good
  · have hcl' : T.c.rs.closed.isSome = false := by simpa using hcl
    by_cases hok : Clock.sendOk Relay.DEFAULT_CAP T.c.rs id n = true
    · obtain ⟨cc, hcc, ho, hn, hw, hcap, hp⟩ := Clock.sendOk_spec Relay.DEFAULT_CAP T.c.rs id n hok
      obtain ⟨hR1, hR2⟩ := stepK_send_ok_rel Relay.DEFAULT_CAP T.clk T.c.rs id n hcl' hok
      generalize hm : (Clock.flushSim ((T.clk.chunks id) ++ [n]) 4294967295 T.clk.bud).1 = m at hR1 hR2
      have htag : Client.tagOf T.c.rs (Relay.Ev.send id n) = cc.gen := by
        simp [Client.tagOf, Relay.evId, hcc]
      have hOuts : ((Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n)).2.2.map
          (fun o => (o, Client.tagOf T.c.rs (Relay.Ev.send id n)))) = if 0 < min m (cc.queued + n)
          then [(Relay.Out.written id (cc.written + min m (cc.queued + n)) 0, cc.gen)] else [] := by
        rw [hR2, sendStepB_ok_outs Relay.DEFAULT_CAP T.c.rs id n m cc hcc ho hn hw hcap hp, htag]
        by_cases hz : 0 < min m (cc.queued + n) <;> simp [hz]
      have hng' : (Clock.stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n)).2.1.nextGen
          = T.c.rs.nextGen := by
        rw [hR1, sendStepB_nextGen]
      exact inv_send_ok_wrap Relay.DEFAULT_CAP T h id n p rest hq cc hcc ho hn hw hcap hp m _ _ _ hOuts rfl rfl rfl
        rfl hR1 hng' (Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n) h.mirror)
        (Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n) h.good)
    · have hnok : Clock.sendOk Relay.DEFAULT_CAP T.c.rs id n = false := by simpa using hok
      obtain ⟨hR1, hR2⟩ := stepK_send_notok_rel Relay.DEFAULT_CAP T.clk T.c.rs id n hcl' hnok
      have hM := Clock.mirror_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n) h.mirror
      have hGd := Clock.good_stepK Relay.DEFAULT_CAP T.clk T.c.rs (Relay.Ev.send id n) h.good
      rw [hR1] at hM
      rw [hR1, hR2]
      generalize hR : Relay.sendStepB Relay.DEFAULT_CAP T.c.rs id n 0 = R at hM ⊢
      cases hsl : (T.c.rs.slot id).conn with
      | none =>
        by_cases hk : (T.c.rs.slot id).known = true
        · rw [sendStepB_noop_none Relay.DEFAULT_CAP T.c.rs id n 0 hsl hk] at hR
          subst hR
          exact inv_send_keep T h id n p rest hq _ _ _ _ rfl rfl rfl rfl (by simp) rfl (fun _ => rfl) rfl hM hGd
        · have hk' : (T.c.rs.slot id).known = false := by simpa using hk
          rw [sendStepB_proto_none Relay.DEFAULT_CAP T.c.rs id n 0 hsl hk'] at hR
          subst hR
          exact inv_send_keep T h id n p rest hq _ _ _ _ rfl rfl rfl rfl (by simp [outIdT, Relay.protoClose])
            rfl (fun j => protoClose_slot _ _ j) rfl hM hGd
      | some c =>
        by_cases ho : c.isOpen = true
        · by_cases hn0 : n = 0
          · rw [sendStepB_noop_n0 Relay.DEFAULT_CAP T.c.rs id n 0 c hsl ho hn0] at hR
            subst hR
            exact inv_send_keep T h id n p rest hq _ _ _ _ rfl rfl rfl rfl (by simp) rfl (fun _ => rfl) rfl hM hGd
          · by_cases hwin : Relay.SEND_WINDOW - c.queued < n
            · rw [sendStepB_proto_win Relay.DEFAULT_CAP T.c.rs id n 0 c hsl ho hn0 hwin] at hR
              subst hR
              exact inv_send_keep T h id n p rest hq _ _ _ _ rfl rfl rfl rfl (by simp [outIdT, Relay.protoClose])
                rfl (fun j => protoClose_slot _ _ j) rfl hM hGd
            · have hw : n ≤ Relay.SEND_WINDOW - c.queued := by omega
              by_cases hcap : Relay.DEFAULT_CAP < c.written + c.queued + n
              · rw [sendStepB_fail_cap Relay.DEFAULT_CAP T.c.rs id n 0 c hsl ho hn0 hw hcap,
                  failConn_open _ _ _ _ ho] at hR
                subst hR
                exact inv_send_fail_wrap T h id n p rest hq c hsl 27 _ _ rfl rfl rfl rfl rfl rfl hM hGd
              · have hcap' : c.written + c.queued + n ≤ Relay.DEFAULT_CAP := by omega
                by_cases hpc : c.peerClosed = true
                · rw [sendStepB_fail_peer Relay.DEFAULT_CAP T.c.rs id n 0 c hsl ho hn0 hw hcap' hpc,
                    failConn_open _ _ _ _ ho] at hR
                  subst hR
                  exact inv_send_fail_wrap T h id n p rest hq c hsl 32 _ _ rfl rfl rfl rfl rfl rfl hM hGd
                · exfalso
                  have hpc' : c.peerClosed = false := by simpa using hpc
                  have htrue : Clock.sendOk Relay.DEFAULT_CAP T.c.rs id n = true := by
                    simp [Clock.sendOk, hsl, ho, hn0, hw, hcap', hpc']
                  rw [htrue] at hnok
                  cases hnok
        · have hc' : c.isOpen = false := by simpa using ho
          rw [sendStepB_proto_closed Relay.DEFAULT_CAP T.c.rs id n 0 c hsl hc'] at hR
          subst hR
          exact inv_send_keep T h id n p rest hq _ _ _ _ rfl rfl rfl rfl (by simp [outIdT, Relay.protoClose])
            rfl (fun j => protoClose_slot _ _ j) rfl hM hGd

end Ind
