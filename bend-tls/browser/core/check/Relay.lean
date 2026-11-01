/-
Relay.lean: the relay's connection machine (relay/relay.ts), the page client (tcp_relay_client.js), the clock,
and the search of the two composed. The file is one program; `lean --run Relay.lean MODE` runs it:

  (no argument)     the relay: traces on stdin, one per "trace" line (see below), each answered by its frames
                    and a line "end" (the relay conformance test)
  page              the page client: traces of calls and frames on stdin, each answered by the frames sent and
                    the callbacks made, and "end" (the client conformance test)
  search old|fixed N  every interleaving of the page and the relay, up to N steps, over a small alphabet: the
                    first violation of "the page applies a frame to the connection that sent it", or none

The relay model. The machine has one slot per connection id. A slot holds the connection that the id is in use
for. Each connection has a generation: a CONNECT that the relay accepts starts a connection with the next
generation. Socket events carry the id and the generation of the socket they come from, so a late event from a
socket that has been closed (and whose id may have been reused) can be told apart from the events of the
connection that has the id now (the bug fixed in relay.ts; test/lifecycle.test.ts). A CLOSE is answered with
CLOSED once the id has been used (PROTOCOL.md).

Trace lines: "trace" starts a trace; then optionally "cap N" (the count limit, default 2^32 - 1) and "rate N"
(connects per second, default 100000), then events and clock steps, one per line:
  connect ID | deny ID | send ID N | discard ID | read ID K | close ID
  sock ID GEN open | sock ID GEN data N | sock ID GEN eof | sock ID GEN peerclose
  sock ID GEN error E | sock ID GEN drain A
  tick MS                                  (the clock goes on by MS, and the timer runs once)
  rate N | budget N                        (connects per second, and bytes per second, for the trace)
Output: one line per frame or session event, then "end":
  ok ID | data ID N | eof ID | written ID COUNT FLAG | fail ID ERRNO | closed ID | wsclose CODE

The page model (Page): the client's connections, as the client keeps them: its calls, the sends framed in SEND
frames of at most 65535 bytes and within the send window, the recv calls waiting in order, the discard, the
closing ids, and the callbacks. The client's observable behaviour is what the conformance test compares.

Theorems (no sorry; `lean Relay.lean` checks them): stale_noop, freed_sock_silent, sockStep_fail_frees,
ok_only_from_open, step_outs_id (a step names only its own id), freed_run (a freed id is named only by the CLOSED
that answers a CLOSE), counters_bounded (the counts stay within the count limit, the queue within the send window,
the credit within the read window), drain_empties and open_resolves and error_resolves (liveness, under fairness),
rate_run (THE RATE BOUND: from the start, no more connects are accepted than two seconds' burst plus the rate
for the time that has passed) and byte_run (THE BYTE BOUND: the bytes written and read are at most the budget's
burst plus the byte rate for the time that has passed, less the budget's debt).

The assumptions: a socket opens once and its events come after its open (the events Bun produces); the socket
delivers data only while the relay has credit and budget (the relay pauses it otherwise: the model does not
model the pausing, it takes the data as it comes); for liveness, the environment is fair: a socket that is offered a
byte takes one, and the timer keeps running.
-/

import Std.Data.HashSet

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Relay

def SEND_WINDOW : Nat := 131072
def READ_WINDOW : Nat := 131072
def CHUNK_MAX : Nat := 1048576
def DEFAULT_CAP : Nat := 4294967295

structure Conn where
  gen : Nat
  isOpen : Bool
  queued : Nat
  written : Nat
  rd : Nat
  gr : Nat
  peerClosed : Bool
  deriving Repr

structure Slot where
  known : Bool
  conn : Option Conn
  deriving Repr

structure St where
  nextGen : Nat
  slots : Nat → Slot
  closed : Option Nat

inductive Out where
  | ok (id : Nat)
  | data (id n : Nat)
  | eof (id : Nat)
  | written (id c f : Nat)
  | fail (id e : Nat)
  | closed (id : Nat)
  | wsclose (code : Nat)
  deriving DecidableEq, Repr

inductive Sk where
  | open_
  | data (n : Nat)
  | eof
  | peerclose
  | error (e : Nat)
  | drain (a : Nat)
  deriving Repr

inductive Ev where
  | connect (id : Nat)
  | deny (id : Nat)
  | send (id n : Nat)
  | discard (id : Nat)
  | read (id k : Nat)
  | close (id : Nat)
  | sock (id g : Nat) (k : Sk)
  deriving Repr

def St.slot (s : St) (id : Nat) : Slot := s.slots id

def setSlot (s : St) (id : Nat) (sl : Slot) : St :=
  { s with slots := fun i => if i = id then sl else s.slots i }

def setConn (s : St) (id : Nat) (c : Option Conn) : St :=
  setSlot s id { (s.slot id) with conn := c }

-- the session ends: the WebSocket is closed with the code, and nothing more is sent
def protoClose (s : St) (code : Nat) : St × List Out :=
  ({ s with closed := some code }, [Out.wsclose code])

-- the connection failed: the page hears how much of its send was taken (if the socket was open), then
-- the failure; the id is free
def failConn (s : St) (id : Nat) (c : Conn) (errno : Nat) : St × List Out :=
  (setConn s id none,
   (if c.isOpen then [Out.written id c.written 0] else []) ++ [Out.fail id errno])

-- the socket takes up to a bytes of the queue
def flushConn (s : St) (id : Nat) (c : Conn) (a : Nat) : St × List Out :=
  if !c.isOpen then (s, []) else
  let m := min a c.queued
  if m = 0 then (s, []) else
  let c' : Conn := { c with queued := c.queued - m, written := c.written + m }
  (setConn s id (some c'), [Out.written id c'.written 0])

-- a socket event; a socket with no connection, or of another generation, does nothing
def sockStep (cap : Nat) (s : St) (id g : Nat) (k : Sk) : St × List Out :=
  match (s.slot id).conn with
  | none => (s, [])
  | some c =>
    if c.gen ≠ g then (s, []) else
    match k with
    | .open_ =>
      if c.isOpen then (s, [])
      else (setConn s id (some { c with isOpen := true }), [Out.ok id])
    | .data n =>
      if c.rd > c.gr then failConn s id c 5
      else if n > CHUNK_MAX then failConn s id c 5
      else if c.rd + n > cap then failConn s id c 27
      else (setConn s id (some { c with rd := c.rd + n }), [Out.data id n])
    | .eof => (s, [Out.eof id])
    | .peerclose =>
      let c' : Conn := { c with peerClosed := true }
      if c'.queued > 0 then failConn s id c' 32
      else (setConn s id (some c'), [])
    | .error e => failConn s id c e
    | .drain a => flushConn s id c a

def sendStep (cap : Nat) (s : St) (id n : Nat) : St × List Out :=
  match (s.slot id).conn with
  | none => if (s.slot id).known then (s, []) else protoClose s 1002
  | some c =>
    if !c.isOpen then protoClose s 1002
    else if n = 0 then (s, [])
    else if n > SEND_WINDOW - c.queued then protoClose s 1002
    else if c.written + c.queued + n > cap then failConn s id c 27
    else if c.peerClosed then failConn s id c 32
    else
      -- the socket takes everything offered, so the queue is written at once
      let total := c.queued + n
      let c' : Conn := { c with queued := 0, written := c.written + total }
      (setConn s id (some c'), if total > 0 then [Out.written id c'.written 0] else [])

-- sendStep, with the flush's amount given: m bytes of the queue (with the new bytes) go to the socket, the rest
-- waits. The clock uses this: the budget and the socket decide m (Clock.stepK). With m = the whole queue,
-- it is sendStep.
def sendStepB (cap : Nat) (s : St) (id n m : Nat) : St × List Out :=
  match (s.slot id).conn with
  | none => if (s.slot id).known then (s, []) else protoClose s 1002
  | some c =>
    if !c.isOpen then protoClose s 1002
    else if n = 0 then (s, [])
    else if n > SEND_WINDOW - c.queued then protoClose s 1002
    else if c.written + c.queued + n > cap then failConn s id c 27
    else if c.peerClosed then failConn s id c 32
    else
      let total := c.queued + n
      let w := min m total
      let c' : Conn := { c with queued := total - w, written := c.written + w }
      (setConn s id (some c'), if w > 0 then [Out.written id c'.written 0] else [])

def discardStep (s : St) (id : Nat) : St × List Out :=
  match (s.slot id).conn with
  | none => if (s.slot id).known then (s, []) else protoClose s 1002
  | some c =>
    if !c.isOpen then protoClose s 1002
    else (setConn s id (some { c with queued := 0 }), [Out.written id c.written 1])

def readStep (s : St) (id k : Nat) : St × List Out :=
  match (s.slot id).conn with
  | none => if (s.slot id).known then (s, []) else protoClose s 1002
  | some c =>
    if !c.isOpen then protoClose s 1002
    else (setConn s id (some { c with gr := min (c.rd + READ_WINDOW) (c.gr + k) }), [])

def connectStep (s : St) (id : Nat) : St × List Out :=
  match (s.slot id).conn with
  | some _ => protoClose s 1002
  | none =>
    let c : Conn := { gen := s.nextGen, isOpen := false, queued := 0, written := 0,
                      rd := 0, gr := 0, peerClosed := false }
    ({ setSlot s id { known := true, conn := some c } with nextGen := s.nextGen + 1 }, [])

-- a CONNECT the relay refuses (the destination, or a limit): the id stays free
def denyStep (s : St) (id : Nat) : St × List Out :=
  match (s.slot id).conn with
  | some _ => protoClose s 1002
  | none => (s, [Out.fail id 13])

-- a CLOSE is answered with CLOSED once the id has been used (PROTOCOL.md): the connection, if any, is dropped
def closeStep (s : St) (id : Nat) : St × List Out :=
  let outs : List Out := if (s.slot id).known then [Out.closed id] else []
  match (s.slot id).conn with
  | none => (s, outs)
  | some _ => (setConn s id none, outs)

def step (cap : Nat) (s : St) (e : Ev) : St × List Out :=
  if s.closed.isSome then (s, []) else
  match e with
  | .connect id => connectStep s id
  | .deny id => denyStep s id
  | .send id n => sendStep cap s id n
  | .discard id => discardStep s id
  | .read id k => readStep s id k
  | .close id => closeStep s id
  | .sock id g k => sockStep cap s id g k

def run (cap : Nat) (s : St) : List Ev → St × List Out
  | [] => (s, [])
  | e :: es =>
    let r1 := step cap s e
    let r2 := run cap r1.1 es
    (r2.1, r1.2 ++ r2.2)

def init : St :=
  { nextGen := 1, slots := fun _ => { known := false, conn := none }, closed := none }

-- ================================================================================================
-- Theorems
-- ================================================================================================

-- ---- the slots ----

theorem not_closed_of (s : St) (h : s.closed = none) : ¬ (s.closed.isSome = true) := by
  simp [h]

theorem slot_setSlot_self (s : St) (id : Nat) (sl : Slot) : (setSlot s id sl).slot id = sl := by
  simp [setSlot, St.slot]

theorem slot_setSlot_ne (s : St) (id i : Nat) (sl : Slot) (h : i ≠ id) :
    (setSlot s id sl).slot i = s.slot i := by
  simp [setSlot, St.slot, h]

theorem slot_setConn_self (s : St) (id : Nat) (c : Option Conn) :
    (setConn s id c).slot id = { (s.slot id) with conn := c } := by
  simp [setConn, slot_setSlot_self]

theorem slot_setConn_ne (s : St) (id i : Nat) (c : Option Conn) (h : i ≠ id) :
    (setConn s id c).slot i = s.slot i := by
  simp [setConn, slot_setSlot_ne _ _ _ _ h]

-- ---- a socket event does nothing for an id with no connection, or with a connection of another
--      generation: the late events of a closed socket cannot touch the connection that reuses its id ----

theorem stale_noop (cap : Nat) (s : St) (id g : Nat) (k : Sk) (hc : s.closed = none)
    (hs : ∀ c, (s.slot id).conn = some c → c.gen ≠ g) :
    step cap s (.sock id g k) = (s, []) := by
  unfold step
  rw [if_neg (not_closed_of s hc)]
  dsimp only
  unfold sockStep
  cases h : (s.slot id).conn with
  | none => rfl
  | some c =>
    have hg : c.gen ≠ g := hs c h
    dsimp only
    rw [if_pos hg]

theorem freed_sock_silent (cap : Nat) (s : St) (id g : Nat) (k : Sk) (hc : s.closed = none)
    (hn : (s.slot id).conn = none) :
    step cap s (.sock id g k) = (s, []) :=
  stale_noop cap s id g k hc (fun c h => by rw [hn] at h; cases h)

-- ---- an OK comes only from the open of a connection that is not open yet ----

theorem ok_only_from_open (cap : Nat) (s : St) (id g : Nat) (k : Sk)
    (hf : Out.ok id ∈ (sockStep cap s id g k).2) :
    k = .open_ ∧ ∃ c, (s.slot id).conn = some c ∧ c.gen = g ∧ c.isOpen = false := by
  unfold sockStep at hf
  cases hsl : (s.slot id).conn with
  | none =>
    rw [hsl] at hf
    simp at hf
  | some c =>
    rw [hsl] at hf
    dsimp only at hf
    by_cases hg : c.gen ≠ g
    · rw [if_pos hg] at hf
      simp at hf
    · rw [if_neg hg] at hf
      cases k with
      | open_ =>
        dsimp only at hf
        by_cases ho : c.isOpen = true
        · rw [if_pos ho] at hf
          simp at hf
        · exact ⟨rfl, c, rfl, by simpa using hg, by simpa using ho⟩
      | data n =>
        dsimp only at hf
        repeat' split at hf
        all_goals simp [failConn, setConn] at hf
      | eof =>
        dsimp only at hf
        simp at hf
      | peerclose =>
        dsimp only at hf
        repeat' split at hf
        all_goals simp [failConn, setConn] at hf
      | error e =>
        dsimp only at hf
        simp [failConn] at hf
      | drain a =>
        dsimp only at hf
        simp only [flushConn] at hf
        repeat' split at hf
        all_goals simp at hf

-- ---- the invariant: every connection's counters respect the bounds the model proves ----

def ConnOk (cap : Nat) (s : St) (c : Conn) : Prop :=
  c.gen < s.nextGen ∧ c.written + c.queued ≤ cap ∧ c.queued ≤ SEND_WINDOW ∧
    c.rd ≤ cap ∧ c.gr ≤ c.rd + READ_WINDOW ∧ c.rd ≤ c.gr + CHUNK_MAX

def Inv (cap : Nat) (s : St) : Prop :=
  ∀ id c, (s.slot id).conn = some c → ConnOk cap s c

theorem inv_init (cap : Nat) : Inv cap init := by
  intro id c h
  simp [init, St.slot] at h

theorem inv_setConn (cap : Nat) (s : St) (id : Nat) (c : Conn) (hI : Inv cap s) (hc : ConnOk cap s c) :
    Inv cap (setConn s id (some c)) := by
  intro i c' hi
  by_cases h : i = id
  · subst h
    rw [slot_setConn_self] at hi
    simp at hi
    subst hi
    exact hc
  · rw [slot_setConn_ne s id i _ h] at hi
    exact hI i c' hi

theorem inv_setConn_none (cap : Nat) (s : St) (id : Nat) (hI : Inv cap s) :
    Inv cap (setConn s id none) := by
  intro i c' hi
  by_cases h : i = id
  · subst h
    rw [slot_setConn_self] at hi
    simp at hi
  · rw [slot_setConn_ne s id i _ h] at hi
    exact hI i c' hi

theorem inv_protoClose (cap : Nat) (s : St) (code : Nat) (hI : Inv cap s) :
    Inv cap (protoClose s code).1 := by
  intro i c' hi
  exact hI i c' hi

theorem inv_failConn (cap : Nat) (s : St) (id : Nat) (c : Conn) (errno : Nat) (hI : Inv cap s) :
    Inv cap (failConn s id c errno).1 :=
  inv_setConn_none cap s id hI

theorem inv_flushConn (cap : Nat) (s : St) (id : Nat) (c : Conn) (a : Nat) (hI : Inv cap s)
    (hc : ConnOk cap s c) :
    Inv cap (flushConn s id c a).1 := by
  unfold flushConn
  dsimp only
  by_cases h1 : (!c.isOpen) = true
  · rw [if_pos h1]
    exact hI
  · rw [if_neg h1]
    by_cases h2 : min a c.queued = 0
    · rw [if_pos h2]
      exact hI
    · rw [if_neg h2]
      apply inv_setConn cap s id _ hI
      unfold ConnOk at hc ⊢
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
      have hm : min a c.queued ≤ c.queued := Nat.min_le_right _ _
      refine ⟨g1, ?_, ?_, g4, g5, g6⟩ <;> (try dsimp only) <;> omega

theorem inv_sendStep (cap : Nat) (s : St) (id n : Nat) (hI : Inv cap s) :
    Inv cap (sendStep cap s id n).1 := by
  unfold sendStep
  cases hsl : (s.slot id).conn with
  | none =>
    dsimp only
    by_cases hk : (s.slot id).known = true
    · rw [if_pos hk]
      exact hI
    · rw [if_neg hk]
      exact inv_protoClose cap s _ hI
  | some c =>
    dsimp only
    have hc := hI id c hsl
    by_cases h1 : (!c.isOpen) = true
    · rw [if_pos h1]
      exact inv_protoClose cap s _ hI
    · rw [if_neg h1]
      by_cases hn : n = 0
      · rw [if_pos hn]
        exact hI
      · rw [if_neg hn]
        by_cases h2 : n > SEND_WINDOW - c.queued
        · rw [if_pos h2]
          exact inv_protoClose cap s _ hI
        · rw [if_neg h2]
          by_cases h3 : c.written + c.queued + n > cap
          · rw [if_pos h3]
            exact inv_failConn cap s id c 27 hI
          · rw [if_neg h3]
            by_cases h4 : c.peerClosed = true
            · rw [if_pos h4]
              exact inv_failConn cap s id c 32 hI
            · rw [if_neg h4]
              apply inv_setConn cap s id _ hI
              unfold ConnOk at hc ⊢
              obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
              refine ⟨g1, ?_, ?_, g4, g5, g6⟩ <;> (try dsimp only) <;> omega

theorem inv_sendStepB (cap : Nat) (s : St) (id n m : Nat) (hI : Inv cap s) :
    Inv cap (sendStepB cap s id n m).1 := by
  unfold sendStepB
  cases hsl : (s.slot id).conn with
  | none =>
    dsimp only
    by_cases hk : (s.slot id).known = true
    · rw [if_pos hk]
      exact hI
    · rw [if_neg hk]
      exact inv_protoClose cap s _ hI
  | some c =>
    dsimp only
    have hc := hI id c hsl
    by_cases h1 : (!c.isOpen) = true
    · rw [if_pos h1]
      exact inv_protoClose cap s _ hI
    · rw [if_neg h1]
      by_cases hn : n = 0
      · rw [if_pos hn]
        exact hI
      · rw [if_neg hn]
        by_cases h2 : n > SEND_WINDOW - c.queued
        · rw [if_pos h2]
          exact inv_protoClose cap s _ hI
        · rw [if_neg h2]
          by_cases h3 : c.written + c.queued + n > cap
          · rw [if_pos h3]
            exact inv_failConn cap s id c 27 hI
          · rw [if_neg h3]
            by_cases h4 : c.peerClosed = true
            · rw [if_pos h4]
              exact inv_failConn cap s id c 32 hI
            · rw [if_neg h4]
              apply inv_setConn cap s id _ hI
              unfold ConnOk at hc ⊢
              obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
              have hw : min m (c.queued + n) ≤ c.queued + n := Nat.min_le_right _ _
              refine ⟨g1, ?_, ?_, g4, g5, g6⟩ <;> (try dsimp only) <;> omega

theorem inv_discardStep (cap : Nat) (s : St) (id : Nat) (hI : Inv cap s) :
    Inv cap (discardStep s id).1 := by
  unfold discardStep
  cases hsl : (s.slot id).conn with
  | none =>
    dsimp only
    by_cases hk : (s.slot id).known = true
    · rw [if_pos hk]
      exact hI
    · rw [if_neg hk]
      exact inv_protoClose cap s _ hI
  | some c =>
    dsimp only
    have hc := hI id c hsl
    by_cases h1 : (!c.isOpen) = true
    · rw [if_pos h1]
      exact inv_protoClose cap s _ hI
    · rw [if_neg h1]
      apply inv_setConn cap s id _ hI
      unfold ConnOk at hc ⊢
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
      refine ⟨g1, ?_, ?_, g4, g5, g6⟩ <;> (try dsimp only) <;> omega

theorem inv_readStep (cap : Nat) (s : St) (id k : Nat) (hI : Inv cap s) :
    Inv cap (readStep s id k).1 := by
  unfold readStep
  cases hsl : (s.slot id).conn with
  | none =>
    dsimp only
    by_cases hk : (s.slot id).known = true
    · rw [if_pos hk]
      exact hI
    · rw [if_neg hk]
      exact inv_protoClose cap s _ hI
  | some c =>
    dsimp only
    have hc := hI id c hsl
    by_cases h1 : (!c.isOpen) = true
    · rw [if_pos h1]
      exact inv_protoClose cap s _ hI
    · rw [if_neg h1]
      apply inv_setConn cap s id _ hI
      unfold ConnOk at hc ⊢
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
      have m1 := Nat.min_le_left (c.rd + READ_WINDOW) (c.gr + k)
      have m2 : c.gr ≤ min (c.rd + READ_WINDOW) (c.gr + k) :=
        Nat.le_min.mpr ⟨by omega, by omega⟩
      refine ⟨g1, g2, g3, g4, ?_, ?_⟩ <;> (try dsimp only) <;> omega

theorem inv_closeStep (cap : Nat) (s : St) (id : Nat) (hI : Inv cap s) :
    Inv cap (closeStep s id).1 := by
  unfold closeStep
  cases hsl : (s.slot id).conn with
  | none => exact hI
  | some _ => exact inv_setConn_none cap s id hI

theorem inv_denyStep (cap : Nat) (s : St) (id : Nat) (hI : Inv cap s) :
    Inv cap (denyStep s id).1 := by
  unfold denyStep
  cases hsl : (s.slot id).conn with
  | none => exact hI
  | some _ => exact inv_protoClose cap s _ hI

theorem inv_connectStep (cap : Nat) (s : St) (id : Nat) (hI : Inv cap s) :
    Inv cap (connectStep s id).1 := by
  unfold connectStep
  cases hsl : (s.slot id).conn with
  | some _ => exact inv_protoClose cap s _ hI
  | none =>
    dsimp only
    intro i c' hi
    by_cases h : i = id
    · subst h
      simp [St.slot, setSlot] at hi
      subst hi
      unfold ConnOk
      dsimp only
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · have hi2 : (s.slot i).conn = some c' := by
        simpa [St.slot, setSlot, h] using hi
      have hc := hI i c' hi2
      unfold ConnOk at hc ⊢
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
      refine ⟨?_, g2, g3, g4, g5, g6⟩
      · dsimp only
        omega

theorem inv_sockStep (cap : Nat) (s : St) (id g : Nat) (k : Sk) (hI : Inv cap s) :
    Inv cap (sockStep cap s id g k).1 := by
  unfold sockStep
  cases hsl : (s.slot id).conn with
  | none => exact hI
  | some c =>
    dsimp only
    have hc := hI id c hsl
    by_cases hg : c.gen ≠ g
    · rw [if_pos hg]
      exact hI
    · rw [if_neg hg]
      cases k with
      | open_ =>
        dsimp only
        by_cases ho : c.isOpen = true
        · rw [if_pos ho]
          exact hI
        · rw [if_neg ho]
          apply inv_setConn cap s id _ hI
          exact hc
      | data n =>
        dsimp only
        by_cases h1 : c.rd > c.gr
        · rw [if_pos h1]
          exact inv_failConn cap s id c 5 hI
        · rw [if_neg h1]
          by_cases h2 : n > CHUNK_MAX
          · rw [if_pos h2]
            exact inv_failConn cap s id c 5 hI
          · rw [if_neg h2]
            by_cases h3 : c.rd + n > cap
            · rw [if_pos h3]
              exact inv_failConn cap s id c 27 hI
            · rw [if_neg h3]
              apply inv_setConn cap s id _ hI
              unfold ConnOk at hc ⊢
              obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hc
              refine ⟨g1, g2, g3, ?_, ?_, ?_⟩ <;> (try dsimp only) <;> omega
      | eof => exact hI
      | peerclose =>
        dsimp only
        by_cases h1 : c.queued > 0
        · rw [if_pos h1]
          exact inv_failConn cap s id _ 32 hI
        · rw [if_neg h1]
          apply inv_setConn cap s id _ hI
          exact hc
      | error e => exact inv_failConn cap s id c e hI
      | drain a => exact inv_flushConn cap s id c a hI hc

theorem inv_step (cap : Nat) (s : St) (e : Ev) (hI : Inv cap s) : Inv cap (step cap s e).1 := by
  unfold step
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
    exact hI
  · rw [if_neg hc]
    cases e with
    | connect id => exact inv_connectStep cap s id hI
    | deny id => exact inv_denyStep cap s id hI
    | send id n => exact inv_sendStep cap s id n hI
    | discard id => exact inv_discardStep cap s id hI
    | read id k => exact inv_readStep cap s id k hI
    | close id => exact inv_closeStep cap s id hI
    | sock id g k => exact inv_sockStep cap s id g k hI

theorem inv_run (cap : Nat) (es : List Ev) : ∀ (s : St), Inv cap s → Inv cap (run cap s es).1 := by
  induction es with
  | nil =>
    intro s hI
    exact hI
  | cons e es ih =>
    intro s hI
    unfold run
    dsimp only
    exact ih _ (inv_step cap s e hI)

-- the bounds the invariant gives, for every trace from the start
theorem counters_bounded (cap : Nat) (es : List Ev) (id : Nat) (c : Conn)
    (h : ((run cap init es).1.slot id).conn = some c) :
    c.written + c.queued ≤ cap ∧ c.rd ≤ cap ∧ c.queued ≤ SEND_WINDOW ∧
      c.gr ≤ c.rd + READ_WINDOW ∧ c.rd ≤ c.gr + CHUNK_MAX := by
  have hc := inv_run cap es init (inv_init cap) id c h
  unfold ConnOk at hc
  exact ⟨hc.2.1, hc.2.2.2.1, hc.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩

-- ---- liveness, under fairness: a socket that takes a byte when offered one empties the queue ----

theorem step_drain_one (cap : Nat) (s : St) (id g : Nat) (c : Conn) (q : Nat)
    (hc0 : s.closed = none) (hconn : (s.slot id).conn = some c) (hg : c.gen = g)
    (ho : c.isOpen = true) (hq : c.queued = q + 1) :
    (step cap s (.sock id g (.drain 1))).1 = setConn s id (some { c with queued := q, written := c.written + 1 }) := by
  unfold step
  rw [if_neg (not_closed_of s hc0)]
  dsimp only
  unfold sockStep
  rw [hconn]
  dsimp only
  rw [if_neg (show ¬ (c.gen ≠ g) from fun h => h hg)]
  unfold flushConn
  dsimp only
  rw [if_neg (show ¬ ((!c.isOpen) = true) by simp [ho])]
  have hm : min 1 c.queued = 1 := by omega
  rw [hm]
  simp [hq]

theorem drain_empties (cap : Nat) (q : Nat) : ∀ (s : St) (id g : Nat) (c : Conn),
    s.closed = none → (s.slot id).conn = some c → c.gen = g → c.isOpen = true → c.queued = q →
    ∃ c', ((run cap s (List.replicate q (Ev.sock id g (Sk.drain 1)))).1.slot id).conn = some c' ∧
      c'.queued = 0 ∧ c'.written = c.written + q ∧ c'.gen = g ∧ c'.isOpen = true := by
  induction q with
  | zero =>
    intro s id g c hc0 hconn hg ho hq
    refine ⟨c, ?_, hq, by simp, hg, ho⟩
    exact hconn
  | succ q ih =>
    intro s id g c hc0 hconn hg ho hq
    have hstep := step_drain_one cap s id g c q hc0 hconn hg ho hq
    have hrun : (run cap s (List.replicate (q + 1) (Ev.sock id g (Sk.drain 1)))).1 =
        (run cap (step cap s (Ev.sock id g (Sk.drain 1))).1
          (List.replicate q (Ev.sock id g (Sk.drain 1)))).1 := by
      simp [List.replicate_succ, run]
    rw [hrun, hstep]
    have hc0' : (setConn s id (some { c with queued := q, written := c.written + 1 })).closed = none := hc0
    have hslot : (setConn s id (some { c with queued := q, written := c.written + 1 })).slot id =
        { (s.slot id) with conn := some { c with queued := q, written := c.written + 1 } } :=
      slot_setConn_self s id _
    obtain ⟨c', h1, h2, h3, h4, h5⟩ := ih (setConn s id (some { c with queued := q, written := c.written + 1 }))
      id g { c with queued := q, written := c.written + 1 } hc0' (by rw [hslot]) hg ho rfl
    refine ⟨c', h1, h2, ?_, h4, h5⟩
    rw [h3]
    simp
    omega

-- a connecting connection leaves the connecting state when its socket opens, or when it fails
theorem open_resolves (cap : Nat) (s : St) (id g : Nat) (c : Conn)
    (hc0 : s.closed = none) (hconn : (s.slot id).conn = some c) (hg : c.gen = g) (hno : c.isOpen = false) :
    ((step cap s (.sock id g .open_)).1.slot id).conn = some { c with isOpen := true } := by
  unfold step
  rw [if_neg (not_closed_of s hc0)]
  dsimp only
  unfold sockStep
  rw [hconn]
  dsimp only
  rw [if_neg (show ¬ (c.gen ≠ g) from fun h => h hg)]
  rw [if_neg (show ¬ (c.isOpen = true) by simp [hno])]
  simp [setConn, setSlot, St.slot]

theorem error_resolves (cap : Nat) (s : St) (id g : Nat) (c : Conn) (e : Nat)
    (hc0 : s.closed = none) (hconn : (s.slot id).conn = some c) (hg : c.gen = g) :
    ((step cap s (.sock id g (.error e))).1.slot id).conn = none := by
  unfold step
  rw [if_neg (not_closed_of s hc0)]
  dsimp only
  unfold sockStep
  rw [hconn]
  dsimp only
  rw [if_neg (show ¬ (c.gen ≠ g) from fun h => h hg)]
  simp [failConn, setConn, setSlot, St.slot]

-- ---- the slots and the frames of the helpers ----

theorem flushConn_no_fail (s : St) (id : Nat) (c : Conn) (a x : Nat) :
    Out.fail id x ∉ (flushConn s id c a).2 := by
  unfold flushConn
  dsimp only
  repeat' split
  all_goals simp

theorem flushConn_slot_ne (s : St) (id : Nat) (c : Conn) (a i : Nat) (h : i ≠ id) :
    (flushConn s id c a).1.slot i = s.slot i := by
  unfold flushConn
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | exact slot_setConn_ne _ _ _ _ h

-- ---- a FAIL frees the id ----

theorem sockStep_fail_frees (cap : Nat) (s : St) (id g : Nat) (k : Sk) (x : Nat)
    (hf : Out.fail id x ∈ (sockStep cap s id g k).2) :
    ((sockStep cap s id g k).1.slot id).conn = none := by
  unfold sockStep at hf ⊢
  cases hsl : (s.slot id).conn with
  | none => simp [hsl] at hf
  | some c =>
    simp only [hsl] at hf ⊢
    by_cases hg : c.gen ≠ g
    · rw [if_pos hg] at hf
      simp at hf
    · rw [if_neg hg] at hf ⊢
      cases k with
      | open_ =>
        try dsimp only at hf ⊢
        by_cases ho : c.isOpen = true
        · rw [if_pos ho] at hf
          simp at hf
        · rw [if_neg ho] at hf
          simp at hf
      | data n =>
        try dsimp only at hf ⊢
        repeat' (first | split at hf | split)
        all_goals simp_all [failConn, setConn, setSlot, St.slot]
      | eof =>
        try dsimp only at hf ⊢
        simp at hf
      | peerclose =>
        try dsimp only at hf ⊢
        repeat' (first | split at hf | split)
        all_goals simp_all [failConn, setConn, setSlot, St.slot]
      | error e =>
        try dsimp only at hf ⊢
        simp_all [failConn, setConn, setSlot, St.slot]
      | drain a =>
        try dsimp only at hf ⊢
        exact absurd hf (flushConn_no_fail s id c a x)

-- ---- the id of an event, and the id of an output (a step names only the id of its event) ----

def evId : Ev → Nat
  | .connect id => id
  | .deny id => id
  | .send id _ => id
  | .discard id => id
  | .read id _ => id
  | .close id => id
  | .sock id _ _ => id

def outId : Out → Option Nat
  | .ok id => some id
  | .data id _ => some id
  | .eof id => some id
  | .written id _ _ => some id
  | .fail id _ => some id
  | .closed id => some id
  | .wsclose _ => none

-- the events that use an id without reusing it: everything but CONNECT and DENY
def IsFreeEv : Ev → Prop
  | .connect _ => False
  | .deny _ => False
  | _ => True

theorem flushConn_outs (s : St) (id : Nat) (c : Conn) (a : Nat) :
    (flushConn s id c a).2.all (fun o => (outId o).isNone || outId o == some id) = true := by
  unfold flushConn
  dsimp only
  repeat' split
  all_goals simp [outId]

theorem sockStep_outs_id (cap : Nat) (s : St) (id g : Nat) (k : Sk) :
    (sockStep cap s id g k).2.all (fun o => (outId o).isNone || outId o == some id) = true := by
  unfold sockStep
  cases hsl : (s.slot id).conn with
  | none => simp
  | some c =>
    simp only [hsl]
    by_cases hg : c.gen ≠ g
    · rw [if_pos hg]
      simp
    · rw [if_neg hg]
      cases k with
      | open_ =>
        try dsimp only
        by_cases ho : c.isOpen = true
        · rw [if_pos ho]
          simp
        · rw [if_neg ho]
          simp [outId]
      | data n =>
        try dsimp only
        repeat' split
        all_goals simp [failConn, setConn, outId]
      | eof =>
        simp [outId]
      | peerclose =>
        try dsimp only
        repeat' split
        all_goals simp [failConn, setConn, outId]
      | error e =>
        simp [failConn, outId]
      | drain a =>
        exact flushConn_outs s id c a

theorem step_outs_id (cap : Nat) (s : St) (e : Ev) :
    (step cap s e).2.all (fun o => (outId o).isNone || outId o == some (evId e)) = true := by
  unfold step
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
    simp
  · rw [if_neg hc]
    cases e with
    | connect id =>
      simp only [connectStep]
      repeat' split
      all_goals simp_all [protoClose, outId, evId]
    | deny id =>
      simp only [denyStep]
      repeat' split
      all_goals simp_all [protoClose, outId, evId]
    | send id n =>
      simp only [sendStep]
      repeat' split
      all_goals simp_all [protoClose, failConn, setConn, flushConn, outId, evId]
    | discard id =>
      simp only [discardStep]
      repeat' split
      all_goals simp_all [protoClose, outId, evId, setConn, setSlot]
    | read id k =>
      simp only [readStep]
      repeat' split
      all_goals simp_all [protoClose, outId, evId, setConn, setSlot]
    | close id =>
      simp only [closeStep]
      repeat' split
      all_goals simp_all [outId, evId]
    | sock id g k =>
      exact sockStep_outs_id cap s id g k

-- a socket event changes the slot of its own id only
theorem sockStep_slot_ne (cap : Nat) (s : St) (id g : Nat) (k : Sk) (i : Nat) (h : i ≠ id) :
    (sockStep cap s id g k).1.slot i = s.slot i := by
  unfold sockStep
  cases hsl : (s.slot id).conn with
  | none => rfl
  | some c =>
    simp only [hsl]
    repeat' split
    all_goals first
      | rfl
      | exact slot_setConn_ne _ _ _ _ h
      | exact flushConn_slot_ne _ _ _ _ _ h

-- a step changes the slot of its own id only
theorem step_slot_ne (cap : Nat) (s : St) (e : Ev) (i : Nat) (h : evId e ≠ i) :
    (step cap s e).1.slot i = s.slot i := by
  have h' : i ≠ evId e := fun x => h x.symm
  unfold step
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
  · rw [if_neg hc]
    cases e with
    | connect id =>
      simp only [connectStep]
      repeat' split
      all_goals simp_all [protoClose, evId, St.slot, setSlot, setConn]
    | deny id =>
      simp only [denyStep]
      repeat' split
      all_goals simp_all [protoClose, evId, St.slot, setSlot, setConn]
    | send id n =>
      simp only [sendStep]
      repeat' split
      all_goals simp_all [protoClose, failConn, evId, St.slot, setSlot, setConn, flushConn]
    | discard id =>
      simp only [discardStep]
      repeat' split
      all_goals simp_all [protoClose, evId, St.slot, setSlot, setConn]
    | read id k =>
      simp only [readStep]
      repeat' split
      all_goals simp_all [protoClose, evId, St.slot, setSlot, setConn]
    | close id =>
      simp only [closeStep]
      repeat' split
      all_goals simp_all [evId, St.slot, setSlot, setConn]
    | sock id g k =>
      exact sockStep_slot_ne cap s id g k i (fun x => h x.symm)

-- a free event for an id with no connection does nothing but (at most) close the session
theorem step_none_shape (cap : Nat) (s : St) (e : Ev) (hf : IsFreeEv e)
    (hn : (s.slot (evId e)).conn = none) :
    (step cap s e).1.slots = s.slots ∧
      ∀ o ∈ (step cap s e).2, o = Out.wsclose 1002 ∨ ∃ i, o = Out.closed i ∧ i = evId e := by
  unfold step
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
    simp
  · rw [if_neg hc]
    cases e with
    | connect id => exact hf.elim
    | deny id => exact hf.elim
    | send id n =>
      simp only [evId] at hn
      simp only [sendStep, hn]
      repeat' split
      all_goals simp [protoClose]
    | discard id =>
      simp only [evId] at hn
      simp only [discardStep, hn]
      repeat' split
      all_goals simp [protoClose]
    | read id k =>
      simp only [evId] at hn
      simp only [readStep, hn]
      repeat' split
      all_goals simp [protoClose]
    | close id =>
      simp only [evId] at hn
      simp only [closeStep, hn]
      split
      all_goals simp [evId]
    | sock id g k =>
      simp only [evId] at hn
      simp [sockStep, hn]

-- the frames of a trace never name an id that is free at its start, unless the trace connects or denies it
theorem freed_run (cap : Nat) (id : Nat) (es : List Ev) :
    ∀ (s : St), (s.slot id).conn = none → (∀ e ∈ es, evId e = id → IsFreeEv e) →
      ∀ o ∈ (run cap s es).2, outId o ≠ some id ∨ o = Out.closed id := by
  induction es with
  | nil =>
    intro s _ _ o ho
    simp [run] at ho
  | cons e es ih =>
    intro s hn hfree o ho
    have hrun : (run cap s (e :: es)).2 = (step cap s e).2 ++ (run cap (step cap s e).1 es).2 := by
      simp [run]
    rw [hrun] at ho
    rcases List.mem_append.mp ho with h1 | h2
    · by_cases heq : evId e = id
      · have hF := hfree e (by simp) heq
        have hn' : (s.slot (evId e)).conn = none := by rw [heq]; exact hn
        rcases (step_none_shape cap s e hF hn').2 o h1 with h | ⟨i, hi, hie⟩
        · subst h
          simp [outId]
        · subst hi
          right
          rw [hie, heq]
      · have key := List.all_eq_true.mp (step_outs_id cap s e) o h1
        cases ho' : outId o with
        | none => simp [ho']
        | some x =>
          simp only [ho', Option.isNone_some, Bool.false_or, beq_iff_eq, Option.some.injEq] at key
          simp [key, heq]
    · have hstate : ((step cap s e).1.slot id).conn = none := by
        by_cases heq : evId e = id
        · have hF := hfree e (by simp) heq
          have hn' : (s.slot (evId e)).conn = none := by rw [heq]; exact hn
          have hsl := (step_none_shape cap s e hF hn').1
          simp only [St.slot, hsl]
          exact hn
        · rw [step_slot_ne cap s e id heq]
          exact hn
      exact ih (step cap s e).1 hstate (fun e' he' => hfree e' (by simp [he']) ) o h2

-- ================================================================================================
-- The page client (tcp_relay_client.js) as a model: the page's observable behaviour, from its calls and
-- the frames of the relay. It is the same model the search below composes with the relay.
-- ================================================================================================

namespace Page

def MAX_BODY : Nat := 65535
def MAX_IDS : Nat := 256
def SEND_W : Nat := Relay.SEND_WINDOW
def READ_W : Nat := Relay.READ_WINDOW

-- one connection, as the page keeps it. seq: the number of its CONNECT (the page's own count).
structure PConn where
  seq : Nat
  isOpen : Bool
  tail : Nat           -- bytes given to sends so far
  sent : Nat           -- bytes framed as SEND
  written : Nat        -- bytes the relay has taken
  received : Nat       -- bytes received as DATA
  taken : Nat          -- bytes the page has taken
  eof : Bool
  op : Option (Nat × Nat)  -- the send in progress: its start and length
  discardPending : Bool
  readers : List Nat   -- the recv calls waiting for data: their maxima, in order
  deriving Repr

structure PSlot where
  conn : Option PConn
  -- closed by the page, and the relay's CLOSED not yet come (the fixed client): not reused, frames dropped
  closing : Bool
  -- the errno that ended the id's last connection (the page's answer for a call on an id with none)
  lastErr : Option Nat
  deriving Repr

structure State where
  slots : Nat → PSlot
  nextSeq : Nat
  -- true: the closed id is closing until CLOSED (the client of this protocol); false: reused at once
  fixed : Bool

inductive Obs where
  | toRelay (e : Relay.Ev) (seq : Nat)
  | cb (s : String)
  | thrown
  deriving Repr

-- the page's calls and the relay's frames
inductive In where
  | connect
  | close (id : Nat)
  | send (id n : Nat)
  | recv (id max : Nat)
  | discard (id : Nat)
  | frame (o : Relay.Out)
  deriving Repr

def emptySlot : PSlot := { conn := none, closing := false, lastErr := none }

def init (fixed : Bool) : State :=
  { slots := fun _ => emptySlot, nextSeq := 1, fixed := fixed }

def setSlot (st : State) (id : Nat) (sl : PSlot) : State :=
  { st with slots := fun i => if i = id then sl else st.slots i }

-- the errno a call on an id without a connection answers with
def missing (sl : PSlot) : Nat := sl.lastErr.getD 9

-- the send in progress, pumped: SEND frames of at most MAX_BODY, and no more than SEND_WINDOW beyond what
-- the relay has taken; fuel bounds the loop
def pump (id : Nat) (c : PConn) (fuel : Nat) : PConn × List Obs :=
  match fuel with
  | 0 => (c, [])
  | fuel + 1 =>
    if c.op.isNone || c.discardPending || !c.isOpen then (c, [])
    else
      let n := min MAX_BODY (min (SEND_W - (c.sent - c.written)) (c.tail - c.sent))
      if n = 0 then (c, [])
      else
        let (c', obs) := pump id { c with sent := c.sent + n } fuel
        (c', Obs.toRelay (Relay.Ev.send id n) 0 :: obs)

-- takes what it can for a recv call of max bytes: the data, the end, or nothing yet
def takeFor (id : Nat) (c : PConn) (max : Nat) : PConn × Option Obs × Bool :=
  -- returns the connection, the answer (none: the call waits), and whether it answered with an error
  if c.received > c.taken then
    let want := min max (c.received - c.taken)
    ({ c with taken := c.taken + want }, some (Obs.toRelay (Relay.Ev.read id want) 0), false)
  else (c, none, false)

-- a connection ends with errno: its waiting calls hear it, and the id is free (not closing)
def die (st : State) (id : Nat) (c : PConn) (errno : Nat) : State × List Obs :=
  let obsConnect := if c.isOpen then [] else [Obs.cb s!"connectErr {id} {errno}"]
  let obsOp := match c.op with
    | some _ => [Obs.cb s!"sendErr {id} {errno} {c.written}"]
    | none => []
  let obsDiscard := if c.discardPending then [Obs.cb s!"discardErr {id} {errno}"] else []
  let obsReaders := c.readers.map (fun _ => Obs.cb s!"recvErr {id} {errno}")
  let sl := st.slots id
  (setSlot st id { sl with conn := none, lastErr := some errno }, obsConnect ++ obsOp ++ obsDiscard ++ obsReaders)

-- the waiting calls take what has arrived, in order
def wake (st : State) (id : Nat) : State × List Obs := Id.run do
  let sl := st.slots id
  match sl.conn with
  | none => return (st, [])
  | some c0 =>
    let mut c := c0
    let mut keep : List Nat := []
    let mut obs : List Obs := []
    for mx in c0.readers do
      let (c', o, _) := takeFor id c mx
      match o with
      | some ob => obs := obs ++ [ob, Obs.cb s!"data {id} {c'.taken - c.taken}"]
                   c := c'
      | none =>
        if c.eof then obs := obs ++ [Obs.cb s!"eof {id}"]
        else keep := keep ++ [mx]
    let st' := setSlot st id { sl with conn := some { c with readers := keep } }
    return (st', obs)

-- ---- the calls ----

def doConnect (st : State) : State × List Obs :=
  match (List.range MAX_IDS).find? (fun id => (st.slots id).conn.isNone && !(st.slots id).closing) with
  | none => (st, [Obs.cb "connectErr -1 24"])
  | some id =>
    let seq := st.nextSeq
    let c : PConn := { seq := seq, isOpen := false, tail := 0, sent := 0, written := 0, received := 0,
                       taken := 0, eof := false, op := none, discardPending := false, readers := [] }
    let sl := st.slots id
    ({ setSlot st id { sl with conn := some c, lastErr := none } with nextSeq := seq + 1 },
     [Obs.toRelay (Relay.Ev.connect id) seq])

def doClose (st : State) (id : Nat) : State × List Obs :=
  match (st.slots id).conn with
  | none => (st, [])
  | some c =>
    let sl := st.slots id
    let st1 := setSlot st id { sl with closing := st.fixed }
    let (st2, obs) := die st1 id c 9
    (st2, obs ++ [Obs.toRelay (Relay.Ev.close id) 0])

def doSend (st : State) (id n : Nat) : State × List Obs :=
  match (st.slots id).conn with
  | none => (st, [Obs.cb s!"sendErr {id} {missing (st.slots id)} -"])
  | some c =>
    if !c.isOpen then (st, [Obs.cb s!"sendErr {id} 22 {c.written}"])
    else if c.op.isSome || c.discardPending then (st, [Obs.thrown])
    else
      let start := c.tail
      let c1 := { c with tail := c.tail + n }
      if n = 0 then
        (setSlot st id { (st.slots id) with conn := some c1 }, [Obs.cb s!"sent {id}"])
      else
        let c2 := { c1 with op := some (start, n) }
        let (c3, obs) := pump id c2 (c2.tail - c2.sent + 1)
        (setSlot st id { (st.slots id) with conn := some c3 }, obs)

def doRecv (st : State) (id max : Nat) : State × List Obs :=
  match (st.slots id).conn with
  | none => (st, [Obs.cb s!"recvErr {id} {missing (st.slots id)}"])
  | some c =>
    if c.received > c.taken then
      let (c', o, _) := takeFor id c max
      (setSlot st id { (st.slots id) with conn := some c' },
       (o.toList) ++ [Obs.cb s!"data {id} {c'.taken - c.taken}"])
    else if c.eof then (st, [Obs.cb s!"eof {id}"])
    else (setSlot st id { (st.slots id) with conn := some { c with readers := c.readers ++ [max] } }, [])

def doDiscard (st : State) (id : Nat) : State × List Obs :=
  match (st.slots id).conn with
  | some c =>
    if c.isOpen then
      (setSlot st id { (st.slots id) with conn := some { c with discardPending := true } },
       [Obs.toRelay (Relay.Ev.discard id) 0])
    else (st, [Obs.cb s!"discardErr {id} {missing (st.slots id)}"])
  | none => (st, [Obs.cb s!"discardErr {id} {missing (st.slots id)}"])

-- ---- the relay's frames ----

-- the page applies a frame to its connection of id only when the id is not closing
def applies (st : State) (o : Relay.Out) : Option Nat :=
  match o with
  | .closed _ => none
  | .ok id => if (st.slots id).closing then none else ((st.slots id).conn.map (fun c => c.seq))
  | .data id _ => if (st.slots id).closing then none else
      (match (st.slots id).conn with | some c => some c.seq | none => none)
  | .eof id => if (st.slots id).closing then none else
      (match (st.slots id).conn with | some c => some c.seq | none => none)
  | .written id _ _ => if (st.slots id).closing then none else
      (match (st.slots id).conn with | some c => some c.seq | none => none)
  | .fail id _ => if (st.slots id).closing then none else
      (match (st.slots id).conn with | some c => some c.seq | none => none)
  | .wsclose _ => none

def frame (st : State) (o : Relay.Out) : State × List Obs :=
  match o with
  | .closed id => (setSlot st id { (st.slots id) with closing := false }, [])
  | .wsclose _ => (st, [])
  | _ =>
    match applies st o with
    | none => (st, [])
    | some _ =>
      match o with
      | .ok id =>
        match (st.slots id).conn with
        | some c =>
          let wasOpen := c.isOpen
          (setSlot st id { (st.slots id) with conn := some { c with isOpen := true } },
           [Obs.toRelay (Relay.Ev.read id READ_W) 0] ++ (if wasOpen then [] else [Obs.cb s!"connected {id}"]))
        | none => (st, [])
      | .fail id e =>
        match (st.slots id).conn with
        | some c => die st id c e
        | none => (st, [])
      | .data id n =>
        match (st.slots id).conn with
        | some c =>
          let st1 := setSlot st id { (st.slots id) with conn := some { c with received := c.received + n } }
          wake st1 id
        | none => (st, [])
      | .eof id =>
        match (st.slots id).conn with
        | some c =>
          let st1 := setSlot st id { (st.slots id) with conn := some { c with eof := true } }
          wake st1 id
        | none => (st, [])
      | .written id cnt flag =>
        match (st.slots id).conn with
        | some c0 =>
          let c1 := { c0 with written := cnt }
          let (c2, obsOk) :=
            match c1.op with
            | some (start, len) =>
              if cnt >= start + len then ({ c1 with op := none }, [Obs.cb s!"sent {id}"])
              else (c1, [])
            | none => (c1, [])
          let (c3, obsD) :=
            if flag = 1 && c2.discardPending then
              ({ c2 with discardPending := false, op := none, sent := c2.written, tail := c2.written },
               [Obs.cb s!"discarded {id} {cnt}"])
            else (c2, [])
          let st1 := setSlot st id { (st.slots id) with conn := some c3 }
          let (c4, obsP) :=
            match (st1.slots id).conn with
            | some c => pump id c (c.tail - c.sent + 1)
            | none => (c3, [])
          (setSlot st1 id { (st1.slots id) with conn := some c4 }, obsOk ++ obsD ++ obsP)
        | none => (st, [])
      | _ => (st, [])

def step (st : State) (i : In) : State × List Obs :=
  match i with
  | .connect => doConnect st
  | .close id => doClose st id
  | .send id n => doSend st id n
  | .recv id max => doRecv st id max
  | .discard id => doDiscard st id
  | .frame o => frame st o

-- the frames the page sends, as text (the conformance test's rendering)
def renderEv : Relay.Ev → String
  | .connect id => s!"CONNECT {id}"
  | .close id => s!"CLOSE {id}"
  | .send id n => s!"SEND {id} {n}"
  | .read id k => s!"READ {id} {k}"
  | .discard id => s!"DISCARD {id}"
  | _ => "?"

def renderObs : Obs → List String
  | .toRelay e _ => [s!"out {renderEv e}"]
  | .cb s => [s]
  | .thrown => ["thrown"]

end Page

namespace Client

-- the composed system: the page, the relay, and the two queues between them. Each frame of the relay
-- carries the relay generation of the connection that sent it; each CONNECT of the page carries its sequence
-- number, and genOf records the generation the relay gave it.
structure Sys where
  rs : Relay.St
  page : Page.State
  toRelay : List (Relay.Ev × Nat)
  toPage : List (Relay.Out × Nat)
  genOf : List (Nat × Nat)
  bad : Bool

def cap : Nat := Relay.DEFAULT_CAP

def initSys (fixed : Bool) : Sys :=
  { rs := Relay.init, page := Page.init fixed, toRelay := [], toPage := [], genOf := [], bad := false }

-- the relay generation a frame of the relay's step belongs to (the connection before the step)
def tagOf (rs : Relay.St) (e : Relay.Ev) : Nat :=
  match e with
  | .connect _ => rs.nextGen
  | _ => match (rs.slot (Relay.evId e)).conn with
    | some c => c.gen
    | none => 0

-- the page's calls: their observations go to the queue of the page's frames
def pageCall (v : Sys) (i : Page.In) : Option Sys :=
  let (st', obs) := Page.step v.page i
  some { v with page := st', toRelay := v.toRelay ++ obs.filterMap (fun o => match o with
    | .toRelay e p => some (e, p) | _ => none) }

-- the relay takes the oldest frame of the page
def doRelay (v : Sys) : Option Sys :=
  match v.toRelay with
  | [] => none
  | (e, p) :: rest =>
    let t := tagOf v.rs e
    let r := Relay.step cap v.rs e
    let genOf' := match e with
      | .connect _ => if p > 0 then (p, v.rs.nextGen) :: v.genOf else v.genOf
      | _ => v.genOf
    some { v with rs := r.1, toRelay := rest, toPage := v.toPage ++ r.2.map (fun o => (o, t)), genOf := genOf' }

-- a socket of the relay does something: the environment
def doEnv (v : Sys) (e : Relay.Ev) : Option Sys :=
  let t := tagOf v.rs e
  let r := Relay.step cap v.rs e
  some { v with rs := r.1, toPage := v.toPage ++ r.2.map (fun o => (o, t)) }

-- the page takes the oldest frame of the relay. A frame that the page applies must belong to the
-- connection the page has: the generation of the page's connect must be the frame's.
def doPage (v : Sys) : Option Sys :=
  match v.toPage with
  | [] => none
  | (o, t) :: rest =>
    let v1 := { v with toPage := rest }
    let bad' := match Page.applies v.page o with
      | none => false
      | some seq =>
        match (v.genOf.find? (fun q => q.1 == seq)) with
        | some q => q.2 != t
        | none => true
    let (st', obs) := Page.frame v.page o
    some { v1 with page := st', bad := v.bad || bad',
                   toRelay := v1.toRelay ++ obs.filterMap (fun x => match x with
                     | .toRelay e p => some (e, p) | _ => none) }

-- the search over every interleaving up to a depth
def actions (v : Sys) : List (String × Option Sys) :=
  [ ("connect", pageCall v .connect), ("close 0", pageCall v (.close 0)), ("close 1", pageCall v (.close 1)),
    ("send 0 1", pageCall v (.send 0 1)), ("send 1 1", pageCall v (.send 1 1)),
    ("recv 0 1", pageCall v (.recv 0 1)), ("discard 0", pageCall v (.discard 0)),
    ("relay", doRelay v), ("page", doPage v) ] ++
  ((List.range 2).flatMap (fun id =>
    (List.range 3).flatMap (fun g =>
      [ (s!"sock {id} {g+1} open", Relay.Ev.sock id (g+1) Relay.Sk.open_),
        (s!"sock {id} {g+1} data 1", Relay.Ev.sock id (g+1) (Relay.Sk.data 1)),
        (s!"sock {id} {g+1} eof", Relay.Ev.sock id (g+1) Relay.Sk.eof),
        (s!"sock {id} {g+1} error 111", Relay.Ev.sock id (g+1) (Relay.Sk.error 111)),
        (s!"sock {id} {g+1} drain 1", Relay.Ev.sock id (g+1) (Relay.Sk.drain 1)) ]))).map
    (fun (name, e) => (name, doEnv v e))

def keyOf (v : Sys) : String :=
  let ids := List.range 2
  s!"{repr v.rs.nextGen}|{repr v.rs.closed}|{ids.map (fun i => repr (v.rs.slot i))}|" ++
  s!"{ids.map (fun i => repr (v.page.slots i))}|{v.page.nextSeq}|{repr v.toRelay}|{repr v.toPage}|" ++
  s!"{repr v.genOf}|{v.bad}"

-- the search: every interleaving up to depth steps, each state once; the first violation, with the steps
-- that reach it, or none
def search (fixed : Bool) (depth : Nat) : Option (List String) × Nat := Id.run do
  let init := initSys fixed
  let mut frontier : Array (Sys × List String) := #[(init, [])]
  let mut visited : Std.HashSet String := {}
  visited := visited.insert (keyOf init)
  let mut found : Option (List String) := none
  for _ in [0:depth] do
    if found.isSome then break
    let mut next : Array (Sys × List String) := #[]
    for (v, tr) in frontier do
      if found.isSome then break
      for (name, act) in actions v do
        match act with
        | none => pure ()
        | some v' =>
          let k := keyOf v'
          if !visited.contains k then
            visited := visited.insert k
            if v'.bad then
              if found.isNone then found := some (tr ++ [name])
            else next := next.push (v', tr ++ [name])
    frontier := next
  return (found, visited.size)

end Client

-- ================================================================================================
-- Time (relay/relay.ts: refill, the ticker, the budgets). The tokens and the budget are kept in thousandths
-- (a connect takes 1000 tokens; a byte takes 1000 of the budget), so the arithmetic is exact. The relay's
-- floating-point arithmetic agrees with it where the test's clock steps keep it exact (multiples of half a
-- second, at rates that divide them). The queue of each connection is kept as chunks (the SEND frames, head
-- first): the socket takes from the head chunk, and the budget is checked before each write.
-- ================================================================================================

namespace Clock

structure Clk where
  now : Nat            -- the time, in ms
  refilled : Nat       -- the time of the last refill
  tokens : Int         -- connect tokens, in thousandths of a token
  acc : Nat            -- connects accepted (a ghost count)
  cps : Nat            -- connects per second
  bps : Nat            -- bytes per second: the budget's rate
  bud : Int            -- the byte budget, in thousandths of a byte (it can go negative: a write may cross zero)
  used : Nat           -- bytes written and read (a ghost count)
  chunks : Nat → List Nat  -- each connection's queue, as the lengths of its chunks, head first (a ghost mirror)

def init (cps bps : Nat) : Clk :=
  { now := 0, refilled := 0, tokens := 2000 * (cps : Int), acc := 0, cps := cps, bps := bps,
    bud := 1000 * (bps : Int), used := 0, chunks := fun _ => [] }

-- refill (relay/relay.ts): the tokens and the budget for the time since the last refill, up to their caps
def refill (k : Clk) : Clk :=
  let dt : Int := (k.now : Int) - (k.refilled : Int)
  { k with refilled := k.now,
           tokens := min (2000 * (k.cps : Int)) (k.tokens + dt * (k.cps : Int)),
           bud := min (1000 * (k.bps : Int)) (k.bud + dt * (k.bps : Int)) }

-- the flush of a queue (relay/relay.ts: flush): while the budget is positive, write the head chunk as far as the
-- socket accepts (a is what it accepts in all, for this flush); a partial write ends it. Returns the bytes taken,
-- the chunks left, and the budget left.
def flushSim : List Nat → Nat → Int → Nat × List Nat × Int
  | [], _, b => (0, [], b)
  | h :: rest, a, b =>
    if b ≤ 0 then (0, h :: rest, b)
    else
      let w := min a h
      if w = 0 then (0, h :: rest, b)
      else if w < h then (w, (h - w) :: rest, b - 1000 * (w : Int))
      else
        let r := flushSim rest (a - w) (b - 1000 * (w : Int))
        (w + r.1, r.2.1, r.2.2)

-- the budget left is the budget less what was taken, in thousandths
theorem flushSim_budget (cs : List Nat) : ∀ (a : Nat) (b : Int),
    (flushSim cs a b).2.2 = b - 1000 * ((flushSim cs a b).1 : Int) := by
  induction cs with
  | nil =>
    intro a b
    simp [flushSim]
  | cons x rest ih =>
    intro a b
    unfold flushSim
    by_cases hb : b ≤ 0
    · rw [if_pos hb]
      try simp
    · rw [if_neg hb]
      by_cases hw : min a x = 0
      · rw [if_pos hw]
        try simp
      · rw [if_neg hw]
        by_cases hlt : min a x < x
        · rw [if_pos hlt]
          try simp
        · rw [if_neg hlt]
          show (flushSim rest (a - min a x) (b - 1000 * ((min a x : Nat) : Int))).2.2
            = b - 1000 * (((min a x) + (flushSim rest (a - min a x) (b - 1000 * ((min a x : Nat) : Int))).1 : Nat) : Int)
          rw [ih]
          push_cast
          omega

-- what the ticker does to one connection: its queue is flushed, as far as the budget and the socket take it
def flushOne (k : Clk) (s : Relay.St) (id : Nat) : Clk × Relay.St × List Relay.Out :=
  match (s.slot id).conn with
  | some c =>
    if c.isOpen then
      let m := flushSim (k.chunks id) 4294967295 k.bud
      if m.1 > 0 then
        let r := Relay.flushConn s id c m.1
        ({ k with bud := m.2.2, used := k.used + m.1,
                  chunks := fun i => if i = id then m.2.1 else k.chunks i }, r.1, r.2)
      else (k, s, [])
    else (k, s, [])
  | none => (k, s, [])

def flushIds (k : Clk) (s : Relay.St) : List Nat → Clk × Relay.St × List Relay.Out
  | [] => (k, s, [])
  | id :: ids =>
    let r1 := flushOne k s id
    let r2 := flushIds r1.1 r1.2.1 ids
    (r2.1, r2.2.1, r1.2.2 ++ r2.2.2)

-- the ticker: the time goes on, the tokens and the budget refill, and the queues are flushed
def tickK (k : Clk) (s : Relay.St) (ms : Nat) : Clk × Relay.St × List Relay.Out :=
  if s.closed.isSome then (k, s, []) else
  let k1 := refill { k with now := k.now + ms }
  flushIds k1 s (List.range 256)

-- after a step, the queue of an id with no connection is empty (its connection is gone)
def clearGone (k : Clk) (s : Relay.St) (id : Nat) : Clk :=
  match (s.slot id).conn with
  | none => { k with chunks := fun i => if i = id then [] else k.chunks i }
  | some _ => k

-- one event, with the clock. The connect tokens refuse a CONNECT of a free id while there is less than one token.
-- A SEND or a DRAIN takes the bytes the budget and the socket allow (flushSim); a DATA takes the budget.
def stepK (cap : Nat) (k : Clk) (s : Relay.St) (e : Relay.Ev) : Clk × Relay.St × List Relay.Out :=
  if s.closed.isSome then (k, s, []) else
  match e with
  | .connect id =>
    match (s.slot id).conn with
    | some _ =>
      let r := Relay.step cap s e
      (k, r.1, r.2)
    | none =>
      let k1 := refill k
      if k1.tokens < 1000 then (k1, s, [Relay.Out.fail id 11])
      else
        let r := Relay.step cap s e
        ({ k1 with tokens := k1.tokens - 1000, acc := k1.acc + 1 }, r.1, r.2)
  | .send id n =>
    let m := flushSim ((k.chunks id) ++ [n]) 4294967295 k.bud
    let r := Relay.sendStepB cap s id n m.1
    let ok := decide (n ≠ 0) && (s.slot id).conn.isSome && (r.1.slot id).conn.isSome && r.1.closed.isNone
    if ok then
      let k' := { k with bud := m.2.2, used := k.used + m.1,
                         chunks := fun i => if i = id then m.2.1 else k.chunks i }
      (clearGone k' r.1 id, r.1, r.2)
    else (clearGone k r.1 id, r.1, r.2)
  | .sock id g (.drain a) =>
    match (s.slot id).conn with
    | some c =>
      if c.gen = g && c.isOpen then
        let m := flushSim (k.chunks id) a k.bud
        let r := Relay.step cap s (.sock id g (.drain m.1))
        let k' := { k with bud := m.2.2, used := k.used + m.1,
                           chunks := fun i => if i = id then m.2.1 else k.chunks i }
        (clearGone k' r.1 id, r.1, r.2)
      else
        let r := Relay.step cap s e
        (clearGone k r.1 id, r.1, r.2)
    | none =>
      let r := Relay.step cap s e
      (clearGone k r.1 id, r.1, r.2)
  | .sock id _g (.data n) =>
    let r := Relay.step cap s e
    let delivered := decide (Relay.Out.data id n ∈ r.2)
    let k' := if delivered then { k with bud := k.bud - 1000 * (n : Int), used := k.used + n } else k
    (clearGone k' r.1 id, r.1, r.2)
  | .discard id =>
    let r := Relay.step cap s e
    (clearGone { k with chunks := fun i => if i = id then [] else k.chunks i } r.1 id, r.1, r.2)
  | _ =>
    let r := Relay.step cap s e
    (clearGone k r.1 (Relay.evId e), r.1, r.2)

-- what the connection tokens and the budget promise. Good k: the tokens are never negative and the rate bound holds;
-- the budget and the bytes used satisfy the same bound: the budget is at most the rate for the time that has passed,
-- less what was used (in thousandths).
def Good (k : Clk) : Prop :=
  0 ≤ k.tokens ∧ k.refilled ≤ k.now ∧ k.tokens + 1000 * (k.acc : Int) ≤ 2000 * (k.cps : Int) + (k.cps : Int) * (k.refilled : Int)
    ∧ k.bud + 1000 * (k.used : Int) ≤ 1000 * (k.bps : Int) + (k.bps : Int) * (k.refilled : Int)

theorem good_init (cps bps : Nat) : Good (init cps bps) := by
  unfold Good init
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega

-- refill keeps the invariant: the tokens and the budget gained are the rates for the time since the last refill
theorem good_refill (k : Clk) (h : Good k) : Good (refill k) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold Good refill
  simp only
  have hdt : ((k.now : Int) - (k.refilled : Int)) * (k.cps : Int)
      = (k.cps : Int) * (k.now : Int) - (k.cps : Int) * (k.refilled : Int) := by
    rw [Int.sub_mul, Int.mul_comm (k.now : Int), Int.mul_comm (k.refilled : Int)]
  have hdb : ((k.now : Int) - (k.refilled : Int)) * (k.bps : Int)
      = (k.bps : Int) * (k.now : Int) - (k.bps : Int) * (k.refilled : Int) := by
    rw [Int.sub_mul, Int.mul_comm (k.now : Int), Int.mul_comm (k.refilled : Int)]
  have hnn : 0 ≤ ((k.now : Int) - (k.refilled : Int)) * (k.cps : Int) := by
    apply Int.mul_nonneg
    · omega
    · exact Int.natCast_nonneg _
  have hnb : 0 ≤ ((k.now : Int) - (k.refilled : Int)) * (k.bps : Int) := by
    apply Int.mul_nonneg
    · omega
    · exact Int.natCast_nonneg _
  have hmin : min (2000 * (k.cps : Int)) (k.tokens + ((k.now : Int) - (k.refilled : Int)) * (k.cps : Int))
      ≤ k.tokens + ((k.now : Int) - (k.refilled : Int)) * (k.cps : Int) := Int.min_le_right _ _
  have hminb : min (1000 * (k.bps : Int)) (k.bud + ((k.now : Int) - (k.refilled : Int)) * (k.bps : Int))
      ≤ k.bud + ((k.now : Int) - (k.refilled : Int)) * (k.bps : Int) := Int.min_le_right _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Int.le_min.mpr
    refine ⟨?_, ?_⟩
    · have : (0 : Int) ≤ (k.cps : Int) := Int.natCast_nonneg _
      omega
    · omega
  · exact Nat.le_refl _
  · omega
  · omega

theorem good_tick (k : Clk) (h : Good k) (ms : Nat) : Good (refill { k with now := k.now + ms }) := by
  apply good_refill
  unfold Good at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only
  omega

-- a write or a read: the budget less the bytes, and the bytes used more: the sum is unchanged
theorem good_flushOne (k : Clk) (s : Relay.St) (id : Nat) (h : Good k) :
    Good (flushOne k s id).1 := by
  unfold flushOne
  cases hsl : (s.slot id).conn with
  | none => exact h
  | some c =>
    dsimp only
    by_cases hopen : c.isOpen = true
    · rw [if_pos hopen]
      by_cases hm : (flushSim (k.chunks id) 4294967295 k.bud).1 > 0
      · rw [if_pos hm]
        unfold Good at h ⊢
        obtain ⟨h1, h2, h3, h4⟩ := h
        have hb := flushSim_budget (k.chunks id) 4294967295 k.bud
        simp only
        omega
      · rw [if_neg hm]
        exact h
    · rw [if_neg hopen]
      exact h

theorem good_flushIds (k : Clk) (s : Relay.St) (ids : List Nat) (h : Good k) :
    Good (flushIds k s ids).1 := by
  induction ids generalizing k s with
  | nil => exact h
  | cons id ids ih =>
    unfold flushIds
    dsimp only
    apply ih
    exact good_flushOne k s id h

theorem good_tickK (k : Clk) (s : Relay.St) (ms : Nat) (h : Good k) :
    Good (tickK k s ms).1 := by
  unfold tickK
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
    exact h
  · rw [if_neg hc]
    exact good_flushIds _ _ _ (good_tick k h ms)

-- a change of the chunks only keeps the invariant (it reads the numbers only)
theorem good_chunks (k : Clk) (c : Nat → List Nat) (h : Good k) : Good { k with chunks := c } := by
  unfold Good at h ⊢
  exact h

-- a change of the budget and of the bytes used keeps the invariant when the budget's loss is the bytes gained
theorem good_upd (k : Clk) (b' : Int) (u' : Nat) (c : Nat → List Nat) (h : Good k)
    (hsum : b' + 1000 * (u' : Int) = k.bud + 1000 * (k.used : Int)) :
    Good { k with bud := b', used := u', chunks := c } := by
  unfold Good at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  show b' + 1000 * (u' : Int) ≤ 1000 * (k.bps : Int) + (k.bps : Int) * (k.refilled : Int)
  omega

theorem good_clearGone_eq (k : Clk) (s : Relay.St) (id : Nat) (h : Good k) : Good (clearGone k s id) := by
  unfold clearGone
  split
  · exact good_chunks k _ h
  · exact h

theorem good_stepK (cap : Nat) (k : Clk) (s : Relay.St) (e : Relay.Ev) (h : Good k) :
    Good (stepK cap k s e).1 := by
  unfold stepK
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
    exact h
  · rw [if_neg hc]
    cases e with
    | connect id =>
      dsimp only
      split
      · exact h
      · have hg := good_refill k h
        split
        · exact hg
        · unfold Good at hg ⊢
          obtain ⟨g1, g2, g3, g4⟩ := hg
          simp only
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · exact g2
          · push_cast
            omega
          · exact g4
    | send id n =>
      dsimp only
      have hb := flushSim_budget ((k.chunks id) ++ [n]) 4294967295 k.bud
      split
      · exact good_clearGone_eq _ _ _ (good_upd k _ _ _ h (by omega))
      · exact good_clearGone_eq _ _ _ h
    | discard id =>
      dsimp only
      exact good_clearGone_eq _ _ _ (good_chunks k _ h)
    | read id k' =>
      exact good_clearGone_eq _ _ _ h
    | close id =>
      exact good_clearGone_eq _ _ _ h
    | deny id =>
      exact good_clearGone_eq _ _ _ h
    | sock id _g kk =>
      cases kk with
      | open_ => exact good_clearGone_eq _ _ _ h
      | eof => exact good_clearGone_eq _ _ _ h
      | peerclose => exact good_clearGone_eq _ _ _ h
      | error x => exact good_clearGone_eq _ _ _ h
      | drain a =>
        dsimp only
        have hb := flushSim_budget (k.chunks id) a k.bud
        split
        · split
          · exact good_clearGone_eq _ _ _ (good_upd k _ _ _ h (by omega))
          · exact good_clearGone_eq _ _ _ h
        · exact good_clearGone_eq _ _ _ h
      | data n =>
        dsimp only
        split
        · exact good_clearGone_eq _ _ _ (good_upd k _ _ _ h (by omega))
        · exact good_clearGone_eq _ _ _ h

-- an item of a trace: an event of the relay, or a tick of the timer (ms later)
inductive Item where
  | ev (e : Relay.Ev)
  | tick (ms : Nat)

def runK (cap : Nat) (k : Clk) (s : Relay.St) : List Item → Clk × Relay.St × List Relay.Out
  | [] => (k, s, [])
  | it :: its =>
    let r := match it with
      | .ev e => stepK cap k s e
      | .tick ms => tickK k s ms
    let r2 := runK cap r.1 r.2.1 its
    (r2.1, r2.2.1, r.2.2 ++ r2.2.2)

theorem good_runK (cap : Nat) (items : List Item) : ∀ (k : Clk) (s : Relay.St), Good k →
    Good (runK cap k s items).1 := by
  induction items with
  | nil =>
    intro k s h
    exact h
  | cons it its ih =>
    intro k s h
    cases it with
    | ev e => exact ih _ _ (good_stepK cap k s e h)
    | tick ms => exact ih _ _ (good_tickK k s ms h)

-- THE RATE BOUND: from the start, for any trace of events and ticks, the connects accepted are at most the burst
-- of two seconds' worth plus the rate for the time that has passed.
theorem rate_run (cap cps bps : Nat) (items : List Item) :
    1000 * ((runK cap (init cps bps) Relay.init items).1.acc : Int)
      ≤ 2000 * ((runK cap (init cps bps) Relay.init items).1.cps : Int)
        + ((runK cap (init cps bps) Relay.init items).1.cps : Int) * ((runK cap (init cps bps) Relay.init items).1.refilled : Int) := by
  have h := good_runK cap items (init cps bps) Relay.init (good_init cps bps)
  unfold Good at h
  omega

-- THE BYTE BOUND: from the start, for any trace, the bytes written and read are at most the budget's burst plus
-- the byte rate for the time that has passed, less what the budget is in debt (the budget may go below zero by the
-- last write: a write starts only while the budget is positive).
theorem byte_run (cap cps bps : Nat) (items : List Item) :
    1000 * ((runK cap (init cps bps) Relay.init items).1.used : Int)
      ≤ 1000 * ((runK cap (init cps bps) Relay.init items).1.bps : Int)
        + ((runK cap (init cps bps) Relay.init items).1.bps : Int) * ((runK cap (init cps bps) Relay.init items).1.refilled : Int)
        - (runK cap (init cps bps) Relay.init items).1.bud := by
  have h := good_runK cap items (init cps bps) Relay.init (good_init cps bps)
  generalize (runK cap (init cps bps) Relay.init items).1 = k at h ⊢
  unfold Good at h
  obtain ⟨_, _, _, h4⟩ := h
  omega

end Clock

-- ================================================================================================
-- The executable: the trace on stdin, the frames on stdout
-- ================================================================================================

def parseEv (ws : List String) : Option Ev :=
  match ws with
  | ["connect", a] => a.toNat?.map Ev.connect
  | ["deny", a] => a.toNat?.map Ev.deny
  | ["send", a, b] => do
      let i ← a.toNat?
      let n ← b.toNat?
      pure (Ev.send i n)
  | ["discard", a] => a.toNat?.map Ev.discard
  | ["read", a, b] => do
      let i ← a.toNat?
      let k ← b.toNat?
      pure (Ev.read i k)
  | ["close", a] => a.toNat?.map Ev.close
  | ["sock", a, b, "open"] => do
      let i ← a.toNat?
      let g ← b.toNat?
      pure (Ev.sock i g Sk.open_)
  | ["sock", a, b, "data", c] => do
      let i ← a.toNat?
      let g ← b.toNat?
      let m ← c.toNat?
      pure (Ev.sock i g (Sk.data m))
  | ["sock", a, b, "eof"] => do
      let i ← a.toNat?
      let g ← b.toNat?
      pure (Ev.sock i g Sk.eof)
  | ["sock", a, b, "peerclose"] => do
      let i ← a.toNat?
      let g ← b.toNat?
      pure (Ev.sock i g Sk.peerclose)
  | ["sock", a, b, "error", c] => do
      let i ← a.toNat?
      let g ← b.toNat?
      let e ← c.toNat?
      pure (Ev.sock i g (Sk.error e))
  | ["sock", a, b, "drain", c] => do
      let i ← a.toNat?
      let g ← b.toNat?
      let x ← c.toNat?
      pure (Ev.sock i g (Sk.drain x))
  | _ => none

def showOut : Out → String
  | .ok id => s!"ok {id}"
  | .data id n => s!"data {id} {n}"
  | .eof id => s!"eof {id}"
  | .written id c f => s!"written {id} {c} {f}"
  | .fail id e => s!"fail {id} {e}"
  | .closed id => s!"closed {id}"
  | .wsclose c => s!"wsclose {c}"

end Relay

open Relay

partial def readLines (h : IO.FS.Stream) (acc : Array String) : IO (Array String) := do
  let line ← h.getLine
  if line.isEmpty then return acc
  readLines h (acc.push line.trimAscii.toString)

def emitTrace (cap cps bps : Nat) (items : Array Clock.Item) : IO Unit := do
  let (_, _, outs) := Clock.runK cap (Clock.init cps bps) init items.toList
  for o in outs do
    IO.println (showOut o)
  IO.println "end"

-- the traces on stdin: "trace" starts one; in it, "cap N" (the count limit), "rate N" (connects per second:
-- the default is far above any trace's), "tick MS" (the clock goes on), and the events, one per line
def traceMode : IO UInt32 := do
  let lines ← readLines (← IO.getStdin) #[]
  let mut cap := DEFAULT_CAP
  let mut cps := 100000
  let mut bps := 1000000000
  let mut items : Array Clock.Item := #[]
  let mut started := false
  let mut bad := false
  for l in lines do
    if bad || l.isEmpty then continue
    if l == "trace" then
      if started then emitTrace cap cps bps items
      cap := DEFAULT_CAP
      cps := 100000
      bps := 1000000000
      items := #[]
      started := true
    else
      let ws := l.splitOn " "
      match ws with
      | ["cap", n] =>
        match n.toNat? with
        | some k => cap := k
        | none => bad := true
      | ["rate", n] =>
        match n.toNat? with
        | some k => cps := k
        | none => bad := true
      | ["budget", n] =>
        match n.toNat? with
        | some k => bps := k
        | none => bad := true
      | ["tick", n] =>
        match n.toNat? with
        | some k => items := items.push (Clock.Item.tick k)
        | none => bad := true
      | _ =>
        match parseEv ws with
        | some e => items := items.push (Clock.Item.ev e)
        | none => bad := true
  if bad then
    IO.println "BAD"
    return 1
  if started then emitTrace cap cps bps items
  return 0

def parsePage (ws : List String) : Option Page.In :=
  match ws with
  | ["connect"] => some Page.In.connect
  | ["close", a] => a.toNat?.map Page.In.close
  | ["send", a, b] => do
      let i ← a.toNat?
      let n ← b.toNat?
      pure (Page.In.send i n)
  | ["recv", a, b] => do
      let i ← a.toNat?
      let m ← b.toNat?
      pure (Page.In.recv i m)
  | ["discard", a] => a.toNat?.map Page.In.discard
  | ["frame", "OK", a] => a.toNat?.map (fun i => Page.In.frame (Relay.Out.ok i))
  | ["frame", "FAIL", a, e] => do
      let i ← a.toNat?
      let x ← e.toNat?
      pure (Page.In.frame (Relay.Out.fail i x))
  | ["frame", "WRITTEN", a, c, f] => do
      let i ← a.toNat?
      let x ← c.toNat?
      let y ← f.toNat?
      pure (Page.In.frame (Relay.Out.written i x y))
  | ["frame", "DATA", a, n] => do
      let i ← a.toNat?
      let x ← n.toNat?
      pure (Page.In.frame (Relay.Out.data i x))
  | ["frame", "EOF", a] => a.toNat?.map (fun i => Page.In.frame (Relay.Out.eof i))
  | ["frame", "CLOSED", a] => a.toNat?.map (fun i => Page.In.frame (Relay.Out.closed i))
  | _ => none

-- one trace of the page's calls and frames, from the fixed client: each call's observations, then "end"
def pageTrace (lines : List String) : IO Bool := do
  let mut st := Page.init true
  for l in lines do
    match parsePage (l.splitOn " ") with
    | none => return false
    | some i =>
      let (st', obs) := Page.step st i
      st := st'
      for o in obs do
        for line in Page.renderObs o do
          IO.println line
  IO.println "end"
  return true

def pageMode : IO UInt32 := do
  let lines ← readLines (← IO.getStdin) #[]
  let mut cur : List String := []
  let mut ok := true
  for l in lines do
    if l.isEmpty then continue
    if l == "trace" then
      if !cur.isEmpty then ok := ok && (← pageTrace cur)
      cur := []
    else cur := cur ++ [l]
  if !cur.isEmpty then ok := ok && (← pageTrace cur)
  return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["search", mode, d] =>
    match d.toNat? with
    | some depth =>
      let (found, n) := Client.search (mode == "fixed") depth
      match found with
      | some tr =>
        IO.println s!"VIOLATION ({mode}): {tr.length} steps, {n} states searched"
        for x in tr do
          IO.println s!"  {x}"
        return 1
      | none =>
        IO.println s!"no violation ({mode}) within {depth} steps: {n} states searched"
        return 0
    | none =>
      IO.println "BAD"
      return 1
  | ["page"] => pageMode
  | _ => traceMode
