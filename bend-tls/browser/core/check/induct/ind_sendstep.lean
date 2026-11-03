namespace Ind
open Timed

-- the SEND at the head of the queue takes its amount off the id's queue sum; the other ids keep theirs
theorem qs_pop_gen (T : TSys) (c' : Client.Sys) (clk' : Clock.Clk) (id n p : Nat)
    (rest : List (Relay.Ev × Nat)) (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest)
    (hTR : c'.toRelay = rest) (j : Nat) :
    qs j ⟨c', clk'⟩ + (if id = j then n else 0) = qs j T := by
  show qsumT j c'.toRelay + (if id = j then n else 0) = qsumT j T.c.toRelay
  rw [hTR, hq]
  simp [qsumT, Nat.add_comm]

-- the clock's relay step for a SEND: the socket takes the flushed bytes (sendOk), or the send is refused whole
theorem stepK_send_ok_rel (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id n : Nat)
    (hcl : s.closed.isSome = false) (hok : Clock.sendOk cap s id n = true) :
    (Clock.stepK cap k s (Relay.Ev.send id n)).2.1 =
      (Relay.sendStepB cap s id n (Clock.flushSim ((k.chunks id) ++ [n]) 4294967295 k.bud).1).1 ∧
    (Clock.stepK cap k s (Relay.Ev.send id n)).2.2 =
      (Relay.sendStepB cap s id n (Clock.flushSim ((k.chunks id) ++ [n]) 4294967295 k.bud).1).2 := by
  unfold Clock.stepK
  simp [hcl, hok]

theorem stepK_send_notok_rel (cap : Nat) (k : Clock.Clk) (s : Relay.St) (id n : Nat)
    (hcl : s.closed.isSome = false) (hok : Clock.sendOk cap s id n = false) :
    (Clock.stepK cap k s (Relay.Ev.send id n)).2.1 = (Relay.sendStepB cap s id n 0).1 ∧
    (Clock.stepK cap k s (Relay.Ev.send id n)).2.2 = (Relay.sendStepB cap s id n 0).2 := by
  unfold Clock.stepK
  simp [hcl, hok]

theorem sendStepB_nextGen (cap : Nat) (s : Relay.St) (id n m : Nat) :
    (Relay.sendStepB cap s id n m).1.nextGen = s.nextGen := by
  unfold Relay.sendStepB
  repeat' split
  all_goals rfl

-- the outputs and the id's connection of a SEND the socket takes (open, a whole send within the window and the cap)
theorem sendStepB_ok_outs (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hs : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - c.queued) (hcap : c.written + c.queued + n ≤ cap)
    (hp : c.peerClosed = false) :
    (Relay.sendStepB cap s id n m).2 =
      if 0 < min m (c.queued + n) then [Relay.Out.written id (c.written + min m (c.queued + n)) 0] else [] := by
  have h1 : ¬ (n > Relay.SEND_WINDOW - c.queued) := by omega
  have h2 : ¬ (c.written + c.queued + n > cap) := by omega
  unfold Relay.sendStepB
  simp [hs, ho, hn, h1, h2, hp]

theorem sendStepB_ok_conn (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hs : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - c.queued) (hcap : c.written + c.queued + n ≤ cap)
    (hp : c.peerClosed = false) :
    ((Relay.sendStepB cap s id n m).1.slot id).conn =
      some { c with queued := c.queued + n - min m (c.queued + n),
                    written := c.written + min m (c.queued + n) } := by
  simp only [Clock.sendStepB_succ cap s id n m c hs ho hn hw hcap hp]

-- the SEND's other cases: no connection (a no-op if the id is known, else a protocol close), a closed connection,
-- an empty send, a send past the window (a protocol close), and the two failures of an open connection
theorem sendStepB_noop_none (cap : Nat) (s : Relay.St) (id n m : Nat) (hc : (s.slot id).conn = none)
    (hk : (s.slot id).known = true) : Relay.sendStepB cap s id n m = (s, []) := by
  unfold Relay.sendStepB
  simp [hc, hk]

theorem sendStepB_proto_none (cap : Nat) (s : Relay.St) (id n m : Nat) (hc : (s.slot id).conn = none)
    (hk : (s.slot id).known = false) : Relay.sendStepB cap s id n m = Relay.protoClose s 1002 := by
  unfold Relay.sendStepB
  simp [hc, hk]

theorem sendStepB_proto_closed (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hc : (s.slot id).conn = some c) (ho : c.isOpen = false) :
    Relay.sendStepB cap s id n m = Relay.protoClose s 1002 := by
  unfold Relay.sendStepB
  simp [hc, ho]

theorem sendStepB_noop_n0 (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hc : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n = 0) :
    Relay.sendStepB cap s id n m = (s, []) := by
  unfold Relay.sendStepB
  simp [hc, ho, hn]

theorem sendStepB_proto_win (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hc : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : Relay.SEND_WINDOW - c.queued < n) :
    Relay.sendStepB cap s id n m = Relay.protoClose s 1002 := by
  unfold Relay.sendStepB
  simp [hc, ho, hn, hw]

theorem sendStepB_fail_cap (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hc : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - c.queued) (hcap : cap < c.written + c.queued + n) :
    Relay.sendStepB cap s id n m = Relay.failConn s id c 27 := by
  have h1 : ¬ (n > Relay.SEND_WINDOW - c.queued) := by omega
  have h2 : c.written + c.queued + n > cap := by omega
  unfold Relay.sendStepB
  simp [hc, ho, hn, h1, h2]

theorem sendStepB_fail_peer (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hc : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - c.queued) (hcap : c.written + c.queued + n ≤ cap)
    (hp : c.peerClosed = true) :
    Relay.sendStepB cap s id n m = Relay.failConn s id c 32 := by
  have h1 : ¬ (n > Relay.SEND_WINDOW - c.queued) := by omega
  have h2 : ¬ (c.written + c.queued + n > cap) := by omega
  unfold Relay.sendStepB
  simp [hc, ho, hn, h1, h2, hp]

theorem failConn_open (s : Relay.St) (id : Nat) (c : Relay.Conn) (e : Nat) (ho : c.isOpen = true) :
    Relay.failConn s id c e
      = (Relay.setConn s id none, [Relay.Out.written id c.written 0, Relay.Out.fail id e]) := by
  unfold Relay.failConn
  simp [ho]

-- a step that keeps the relay's slots and next generation, and takes the SEND off the queue
theorem inv_send_keep (T : TSys) (h : Inv T) (id n p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest) (c' : Client.Sys) (clk' : Clock.Clk)
    (s' : Relay.St) (outs : List (Relay.Out × Nat))
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ outs) (hnew : ∀ q ∈ outs, outIdT q.1 = none)
    (hcrs : c'.rs = s') (hslot : ∀ j, s'.slot j = T.c.rs.slot j) (hng : s'.nextGen = T.c.rs.nextGen)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  refine inv_relay_keep T h c' clk' (Relay.Ev.send id n) p rest hq outs hTR hpg hG hTP hnew ?_ ?_ ?_ ?_ ?_ ?_ hM hGd
  · rw [hcrs, hng]
  · exact fun j => by
      have := qs_pop_gen T c' clk' id n p rest hq hTR j
      omega
  · intro j c hc
    refine ⟨c, ?_, rfl, rfl, rfl, rfl, rfl⟩
    show (c'.rs.slot j).conn = some c
    rw [hcrs, hslot j]
    exact hc
  · intro j c'' hc''
    have hc3 : (c'.rs.slot j).conn = some c'' := hc''
    rw [hcrs, hslot j] at hc3
    exact ⟨c'', hc3, rfl, rfl, rfl, rfl, rfl⟩
  · intro j hn
    have hn3 : (T.c.rs.slot j).conn = none := hn
    show (c'.rs.slot j).conn = none
    rw [hcrs, hslot j]
    exact hn3
  · intro j hn
    have hn3 : (c'.rs.slot j).conn = none := hn
    rw [hcrs, hslot j] at hn3
    exact hn3

-- a SEND that the socket takes whole (or in part): the id's connection gets the written bytes and the queue's rest
theorem inv_send_ok_wrap (cap : Nat) (T : TSys) (h : Inv T) (id n p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest) (cc : Relay.Conn)
    (hcc : (T.c.rs.slot id).conn = some cc) (hopen : cc.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - cc.queued) (hcap : cc.written + cc.queued + n ≤ cap) (hp : cc.peerClosed = false)
    (m : Nat) (c' : Client.Sys) (clk' : Clock.Clk) (outs : List (Relay.Out × Nat))
    (hOuts : outs = if 0 < min m (cc.queued + n)
      then [(Relay.Out.written id (cc.written + min m (cc.queued + n)) 0, cc.gen)] else [])
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ outs)
    (hcrs : c'.rs = (Relay.sendStepB cap T.c.rs id n m).1)
    (hng : c'.rs.nextGen = T.c.rs.nextGen)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have hOc := sendStepB_ok_conn cap T.c.rs id n m cc hcc hopen hn hw hcap hp
  have hnewLen : outs.length ≤ 1 := by
    rw [hOuts]
    split <;> simp
  have hnew1 : ∀ q ∈ outs, q.1 = Relay.Out.written id (cc.written + min m (cc.queued + n)) 0 ∧ q.2 = cc.gen := by
    intro q hq'
    rw [hOuts] at hq'
    split at hq'
    · rw [List.mem_singleton] at hq'
      rw [hq']
      exact ⟨rfl, rfl⟩
    · simp at hq'
  refine inv_relay_send_ok T h c' clk' id n p rest hq cc hcc (min m (cc.queued + n)) (Nat.min_le_right _ _)
    outs hnewLen hnew1 hTR hpg hG hTP hng ?_ ?_ ?_ ?_ hM hGd
  · exact fun j => qs_pop_gen T c' clk' id n p rest hq hTR j
  · intro j c'' hc''
    have h1 : ((Relay.sendStepB cap T.c.rs id n m).1.slot j).conn = some c'' := by
      rw [← hcrs]
      exact hc''
    by_cases hj : j = id
    · have h2 := h1
      rw [hj, hOc] at h2
      have hc2 : c'' = { cc with queued := cc.queued + n - min m (cc.queued + n),
                                 written := cc.written + min m (cc.queued + n) } :=
        (Option.some.inj h2).symm
      subst hc2
      refine ⟨cc, by rw [hj]; exact hcc, rfl, rfl, rfl, fun _ => ⟨rfl, ?_⟩, fun hne => absurd hj hne⟩
      show cc.queued + n - min m (cc.queued + n) + min m (cc.queued + n) = cc.queued + n
      omega
    · rw [Relay.sendStepB_slot_ne cap T.c.rs id n m j hj] at h1
      exact ⟨c'', h1, rfl, rfl, rfl, fun hj' => absurd hj' hj, fun _ => ⟨rfl, rfl⟩⟩
  · intro j c hc
    have hc3 : (T.c.rs.slot j).conn = some c := hc
    by_cases hj : j = id
    · rw [hj] at hc3
      have hcEq : c = cc := Option.some.inj (hc3.symm.trans hcc)
      rw [hcEq]
      refine ⟨{ cc with queued := cc.queued + n - min m (cc.queued + n),
                        written := cc.written + min m (cc.queued + n) }, ?_, rfl, rfl, rfl,
        fun _ => ⟨rfl, ?_⟩, fun hne => absurd hj hne⟩
      · show ((c'.rs).slot j).conn = _
        rw [hcrs, hj]
        exact hOc
      · show cc.queued + n - min m (cc.queued + n) + min m (cc.queued + n) = cc.queued + n
        omega
    · refine ⟨c, ?_, rfl, rfl, rfl, fun h' => absurd h' hj, fun _ => ⟨rfl, rfl⟩⟩
      show (c'.rs.slot j).conn = some c
      rw [hcrs, Relay.sendStepB_slot_ne cap T.c.rs id n m j hj]
      exact hc3
  · intro j hn
    have hn3 : (T.c.rs.slot j).conn = none := hn
    show (c'.rs.slot j).conn = none
    rw [hcrs]
    by_cases hj : j = id
    · rw [hj, hcc] at hn3
      cases hn3
    · rw [Relay.sendStepB_slot_ne cap T.c.rs id n m j hj]
      exact hn3

-- a failing SEND of an open connection: the id's connection is gone; the page hears its written count and the failure
theorem inv_send_fail_wrap (T : TSys) (h : Inv T) (id n p : Nat) (rest : List (Relay.Ev × Nat))
    (hq : T.c.toRelay = (Relay.Ev.send id n, p) :: rest) (cc : Relay.Conn)
    (hcc : (T.c.rs.slot id).conn = some cc) (e : Nat) (c' : Client.Sys) (clk' : Clock.Clk)
    (hTR : c'.toRelay = rest) (hpg : c'.page = T.c.page) (hG : c'.genOf = T.c.genOf)
    (hTP : c'.toPage = T.c.toPage ++ [(Relay.Out.written id cc.written 0, Client.tagOf T.c.rs (Relay.Ev.send id n)),
      (Relay.Out.fail id e, Client.tagOf T.c.rs (Relay.Ev.send id n))])
    (hcrs : c'.rs = Relay.setConn T.c.rs id none) (hng : c'.rs.nextGen = T.c.rs.nextGen)
    (hM : Clock.Mirror clk' c'.rs) (hGd : Clock.Good clk') : Inv ⟨c', clk'⟩ := by
  have htag : Client.tagOf T.c.rs (Relay.Ev.send id n) = cc.gen := by
    simp [Client.tagOf, Relay.evId, hcc]
  rw [htag] at hTP
  have hconnN : ∀ j, ConnOf ⟨c', clk'⟩ j = if j = id then none else ConnOf T j := by
    intro j
    show (c'.rs.slot j).conn = _
    rw [hcrs, setConn_conn]
    rfl
  refine inv_relay_send_fail T h c' clk' id n p rest hq cc hcc e _ rfl hTR hpg hG hTP hng ?_ ?_ ?_ ?_ ?_ hM hGd
  · exact fun j => qs_pop_gen T c' clk' id n p rest hq hTR j
  · intro j c'' hc''
    have h1 : ConnOf ⟨c', clk'⟩ j = some c'' := hc''
    rw [hconnN j] at h1
    by_cases hj : j = id
    · rw [if_pos hj] at h1
      cases h1
    · rw [if_neg hj] at h1
      exact ⟨hj, c'', h1, rfl, rfl, rfl, rfl, rfl⟩
  · intro j c hc hj
    refine ⟨c, ?_, rfl, rfl, rfl, rfl, rfl⟩
    rw [hconnN j, if_neg hj]
    exact hc
  · intro j hn
    rw [hconnN j]
    split
    · rfl
    · exact hn
  · rw [hconnN id]
    simp

end Ind
