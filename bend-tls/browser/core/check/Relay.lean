/-
Relay.lean: the relay's connection machine (relay/relay.ts), the page client (tcp_relay_client.js), the clock,
and the search of the two composed. The file is one program; `lean --run Relay.lean MODE` runs it:

  (no argument)     the relay: traces on stdin, one per "trace" line (see below), each answered by its frames
                    and a line "end" (the relay conformance test)
  page              the page client: traces of calls and frames on stdin, each answered by the frames sent and
                    the callbacks made, and "end" (the client conformance test)
  search old|fixed N  every interleaving of the page and the relay, up to N steps, over a small alphabet: the
                    first violation of "the page applies a frame to the connection that sent it", or of
                    "the relay closes the WebSocket on a frame of the page", or none

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
for the time that has passed), byte_run (THE BYTE BOUND: the bytes written and read are at most the budget's
burst plus the byte rate for the time that has passed, less the budget's debt), mirror_run (THE MIRROR: from the
start, each connection's queue, as the clock holds it in chunks, adds up to the bytes the relay has queued for it,
so the bounds above are about the relay's own queues), and, for the page's send pump, pump_props (it frames no
more than the data given, in frames of 1 to MAX_BODY bytes, and stays within the window beyond what the relay has
taken), pump_reach, and pump_done (a send with the fuel doSend gives it ends with its data framed, or with the
window full: it does not stall).

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

-- the budgeted send changes only the slot of its own id
theorem sendStepB_slot_ne (cap : Nat) (s : St) (id n m j : Nat) (h : j ≠ id) :
    (sendStepB cap s id n m).1.slot j = s.slot j := by
  unfold sendStepB
  cases hsl : (s.slot id).conn with
  | none =>
    dsimp only
    split
    · rfl
    · rfl
  | some c =>
    dsimp only
    repeat' split
    all_goals first
      | rfl
      | exact slot_setConn_ne _ _ _ _ h
      | rfl

-- the queue of the id a step names: each connection keeps its queued bytes, or it ends, or it is new and empty
def QOK (s s' : St) (id : Nat) : Prop :=
  ∀ c', (s'.slot id).conn = some c' →
    (∃ c, (s.slot id).conn = some c ∧ c'.queued = c.queued) ∨ ((s.slot id).conn = none ∧ c'.queued = 0)

theorem qok_slot_eq (s s' : St) (id : Nat) (h : s'.slot id = s.slot id) : QOK s s' id := by
  intro c' hc'
  rw [h] at hc'
  exact Or.inl ⟨c', hc', rfl⟩

theorem qok_none (s s' : St) (id : Nat) (h : (s'.slot id).conn = none) : QOK s s' id := by
  intro c' hc'
  rw [h] at hc'
  cases hc'

-- a socket event, for the events that do not drain or discard: the queue is kept, or the connection ends
theorem qok_connect (cap : Nat) (s : St) (id : Nat) : QOK s (step cap s (Ev.connect id)).1 id := by
  by_cases hcl : s.closed.isSome = true
  · exact qok_slot_eq _ _ _ (by unfold step; rw [if_pos hcl])
  · cases hsl : (s.slot id).conn with
    | some c =>
      apply qok_slot_eq
      unfold step
      rw [if_neg hcl]
      simp only [connectStep, hsl]
      rfl
    | none =>
      intro c' hc'
      unfold step at hc'
      rw [if_neg hcl] at hc'
      simp only [connectStep, hsl] at hc'
      simp [St.slot, setSlot] at hc'
      subst hc'
      exact Or.inr ⟨hsl, rfl⟩

theorem qok_deny (cap : Nat) (s : St) (id : Nat) : QOK s (step cap s (Ev.deny id)).1 id := by
  apply qok_slot_eq
  unfold step
  by_cases hcl : s.closed.isSome = true
  · rw [if_pos hcl]
  · rw [if_neg hcl]
    simp only [denyStep]
    repeat' split
    all_goals first
      | rfl
      | simp [protoClose]

theorem qok_close (cap : Nat) (s : St) (id : Nat) : QOK s (step cap s (Ev.close id)).1 id := by
  by_cases hcl : s.closed.isSome = true
  · exact qok_slot_eq _ _ _ (by unfold step; rw [if_pos hcl])
  · cases hsl : (s.slot id).conn with
    | none =>
      apply qok_slot_eq
      unfold step
      rw [if_neg hcl]
      simp only [closeStep, hsl]
    | some c =>
      apply qok_none
      unfold step
      rw [if_neg hcl]
      simp only [closeStep, hsl]
      rw [slot_setConn_self]

theorem qok_read (cap : Nat) (s : St) (id k : Nat) : QOK s (step cap s (Ev.read id k)).1 id := by
  by_cases hcl : s.closed.isSome = true
  · exact qok_slot_eq _ _ _ (by unfold step; rw [if_pos hcl])
  · intro c' hc'
    unfold step at hc'
    rw [if_neg hcl] at hc'
    simp only [readStep] at hc'
    cases hsl : (s.slot id).conn with
    | none =>
      simp only [hsl] at hc'
      split at hc'
      · change (s.slot id).conn = some c' at hc'
        rw [hsl] at hc'
        cases hc'
      · change (s.slot id).conn = some c' at hc'
        rw [hsl] at hc'
        cases hc'
    | some c =>
      simp only [hsl] at hc'
      split at hc'
      · change (s.slot id).conn = some c' at hc'
        rw [hsl] at hc'
        cases hc'
        exact Or.inl ⟨c', by simp [hsl], rfl⟩
      · rw [slot_setConn_self] at hc'
        cases hc'
        exact Or.inl ⟨c, by simp [hsl], by simp⟩

theorem conn_setConn_self (s : St) (id : Nat) (c : Option Conn) :
    ((setConn s id c).slot id).conn = c := by
  simp [slot_setConn_self]

-- a socket event (not a drain): a connection that is still there keeps its queued bytes
theorem qkeep_sockStep (cap : Nat) (s : St) (id g : Nat) (k : Sk) (hk : ∀ a, k ≠ Sk.drain a) :
    ∀ c', ((sockStep cap s id g k).1.slot id).conn = some c' →
      ∃ c, (s.slot id).conn = some c ∧ c'.queued = c.queued := by
  intro c' hc'
  unfold sockStep at hc'
  cases hsl : (s.slot id).conn with
  | none => simp [hsl] at hc'
  | some c =>
    simp only [hsl] at hc'
    cases k
    all_goals (try exact False.elim (hk _ rfl))
    all_goals (try dsimp only at hc')
    all_goals (repeat' split at hc')
    all_goals (try dsimp only at hc')
    all_goals first
      | (simp [failConn, conn_setConn_self] at hc'; done)
      | (rw [conn_setConn_self] at hc'; cases hc'; exact ⟨_, rfl, rfl⟩)
      | (rw [hsl] at hc'; cases hc'; exact ⟨_, rfl, rfl⟩)

theorem qok_sockStep (cap : Nat) (s : St) (id g : Nat) (k : Sk) (hk : ∀ a, k ≠ Sk.drain a) :
    QOK s (sockStep cap s id g k).1 id := by
  intro c' hc'
  obtain ⟨c, hc, hq⟩ := qkeep_sockStep cap s id g k hk c' hc'
  exact Or.inl ⟨c, hc, hq⟩

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
    if !c.isOpen then (st, [Obs.cb s!"discardErr {id} {missing (st.slots id)}"])
    -- one discard at a time (tcp_relay_client.js discard): a second is refused with EBUSY (16), not sent
    else if c.discardPending then (st, [Obs.cb s!"discardErr {id} 16"])
    else
      (setSlot st id { (st.slots id) with conn := some { c with discardPending := true } },
       [Obs.toRelay (Relay.Ev.discard id) 0])
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

-- ---- the send pump: its invariants (the send window, frames of at most MAX_BODY, nothing past the data) ----

-- the page's invariant for a send: the relay has taken no more than was framed, the frames are no more than the
-- data given, and they are no more than the window beyond what the relay has taken
def PInv (c : PConn) : Prop := c.written ≤ c.sent ∧ c.sent ≤ c.tail ∧ c.sent ≤ c.written + SEND_W

-- the bytes a SEND observation frames (0 for any other)
def sendBytes : Obs → Nat
  | .toRelay (.send _ n) _ => n
  | _ => 0

theorem max_body_pos : 0 < MAX_BODY := by
  simp [MAX_BODY]

-- the pump keeps the written count and the data, frames what it says, and keeps the invariant
theorem pump_props (id : Nat) : ∀ (fuel : Nat) (c : PConn), PInv c →
    (pump id c fuel).1.written = c.written ∧ (pump id c fuel).1.tail = c.tail ∧
    c.sent ≤ (pump id c fuel).1.sent ∧ PInv (pump id c fuel).1 ∧
    ((pump id c fuel).2.map sendBytes).sum = (pump id c fuel).1.sent - c.sent ∧
    ∀ x ∈ (pump id c fuel).2, 0 < sendBytes x ∧ sendBytes x ≤ MAX_BODY := by
  intro fuel
  induction fuel with
  | zero =>
    intro c hI
    exact ⟨rfl, rfl, Nat.le_refl _, hI, by simp [pump], by simp [pump]⟩
  | succ f ih =>
    intro c hI
    obtain ⟨hw, hst, hwin⟩ := hI
    simp only [pump]
    by_cases hstop : (c.op.isNone || c.discardPending || !c.isOpen) = true
    · rw [if_pos hstop]
      exact ⟨rfl, rfl, Nat.le_refl _, ⟨hw, hst, hwin⟩, by simp, by simp⟩
    · rw [if_neg hstop]
      obtain ⟨n, hn⟩ : ∃ n, n = min MAX_BODY (min (SEND_W - (c.sent - c.written)) (c.tail - c.sent)) :=
        ⟨_, rfl⟩
      rw [← hn]
      by_cases hn0 : n = 0
      · rw [if_pos hn0]
        exact ⟨rfl, rfl, Nat.le_refl _, ⟨hw, hst, hwin⟩, by simp, by simp⟩
      · rw [if_neg hn0]
        have hnM : n ≤ MAX_BODY := by
          rw [hn]
          exact Nat.min_le_left _ _
        have hnW : n ≤ SEND_W - (c.sent - c.written) := by
          rw [hn]
          exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
        have hnT : n ≤ c.tail - c.sent := by
          rw [hn]
          exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
        have hI' : PInv { c with sent := c.sent + n } := by
          unfold PInv
          dsimp only
          omega
        obtain ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩ := ih { c with sent := c.sent + n } hI'
        rcases hpc : pump id { c with sent := c.sent + n } f with ⟨c', obs⟩
        rw [hpc] at hR1 hR2 hR3 hR4 hR5 hR6
        dsimp only at hR1 hR2 hR3 hR4 hR5 hR6 ⊢
        refine ⟨hR1, hR2, by omega, hR4, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, sendBytes]
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨Nat.pos_of_ne_zero hn0, hnM⟩
          · exact hR6 x hx

-- a send in progress, pumped: at each point the pump is done (the data is all framed, or the window is full), or
-- its fuel has run out with at least one byte framed for each unit of fuel
theorem pump_reach (id : Nat) : ∀ (fuel : Nat) (c : PConn), PInv c →
    c.op.isSome = true → c.discardPending = false → c.isOpen = true →
    (pump id c fuel).1.sent = c.tail ∨ (pump id c fuel).1.sent = (pump id c fuel).1.written + SEND_W ∨
      c.sent + fuel ≤ (pump id c fuel).1.sent := by
  intro fuel
  induction fuel with
  | zero =>
    intro c _ _ _ _
    right
    right
    simp [pump]
  | succ f ih =>
    intro c hI hop hd ho
    obtain ⟨hw, hst, hwin⟩ := hI
    have hsome : c.op ≠ none := by
      intro h
      simp [h] at hop
    have hstop : ¬ ((c.op.isNone || c.discardPending || !c.isOpen) = true) := by
      simp [Option.isNone_iff_eq_none, hsome, hd, ho]
    simp only [pump]
    rw [if_neg hstop]
    obtain ⟨n, hn⟩ : ∃ n, n = min MAX_BODY (min (SEND_W - (c.sent - c.written)) (c.tail - c.sent)) :=
      ⟨_, rfl⟩
    rw [← hn]
    by_cases hn0 : n = 0
    · rw [if_pos hn0]
      have hmb := max_body_pos
      dsimp only
      rw [hn0] at hn
      omega
    · rw [if_neg hn0]
      have hnM : n ≤ MAX_BODY := by
        rw [hn]
        exact Nat.min_le_left _ _
      have hnW : n ≤ SEND_W - (c.sent - c.written) := by
        rw [hn]
        exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
      have hnT : n ≤ c.tail - c.sent := by
        rw [hn]
        exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      have hI' : PInv { c with sent := c.sent + n } := by
        unfold PInv
        dsimp only
        omega
      have hP := pump_props id f { c with sent := c.sent + n } hI'
      have hR := ih { c with sent := c.sent + n } hI' hop hd ho
      rcases hpc : pump id { c with sent := c.sent + n } f with ⟨c', obs⟩
      rw [hpc] at hP hR
      dsimp only at hP hR ⊢
      obtain ⟨hP1, _⟩ := hP
      omega

-- THE NO-STALL PROPERTY: a send started with the fuel doSend gives it (the bytes still to send, plus one) ends with
-- all its data framed, or with the window full
theorem pump_done (id : Nat) (c : PConn) (hI : PInv c) (hop : c.op.isSome = true)
    (hd : c.discardPending = false) (ho : c.isOpen = true) :
    (pump id c (c.tail - c.sent + 1)).1.sent = c.tail ∨
      (pump id c (c.tail - c.sent + 1)).1.sent = (pump id c (c.tail - c.sent + 1)).1.written + SEND_W := by
  have hR := pump_reach id (c.tail - c.sent + 1) c hI hop hd ho
  have hP := pump_props id (c.tail - c.sent + 1) c hI
  obtain ⟨_, _, _, hPI, _, _⟩ := hP
  obtain ⟨_, hT, _⟩ := hPI
  omega

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
  -- the relay closed the WebSocket on a frame of the page: a protocol violation by the page's frames
  proto : Bool
  -- each socket (by generation): its id, and its state: 0 created, 1 opened, 2 failed before it opened
  sockSt : List (Nat × Nat × Nat)

def cap : Nat := Relay.DEFAULT_CAP

def initSys (fixed : Bool) : Sys :=
  { rs := Relay.init, page := Page.init fixed, toRelay := [], toPage := [], genOf := [], bad := false,
    proto := false, sockSt := [] }

-- the environment's socket events follow the model's assumption (README, the assumptions of the model): a socket
-- opens once, and its data, end and drain come after its open; an error may come before the open (a connect
-- error) or after it. A socket exists for every generation the relay has given.
def sockEntry (v : Sys) (g : Nat) : Option (Nat × Nat) :=
  (v.sockSt.find? (fun q => q.1 == g)).map (fun q => (q.2.1, q.2.2))

def envAllowed (v : Sys) (id g : Nat) (k : Relay.Sk) : Bool :=
  match sockEntry v g with
  | none => false
  | some (i, st) =>
    i == id && (match k with
      | .open_ => st == 0
      | .error _ => st ≤ 1
      | _ => st == 1)

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
    let closedByPage := r.2.any (fun o => match o with | .wsclose _ => true | _ => false)
    -- a CONNECT the relay accepts makes a socket, of the generation the relay gave it
    let sockSt' := match e with
      | .connect id => if r.1.nextGen > v.rs.nextGen then (v.rs.nextGen, id, 0) :: v.sockSt else v.sockSt
      | _ => v.sockSt
    some { v with rs := r.1, toRelay := rest, toPage := v.toPage ++ r.2.map (fun o => (o, t)), genOf := genOf',
                  proto := v.proto || closedByPage, sockSt := sockSt' }

-- a socket of the relay does something: the environment (only what the model's socket assumption allows)
def doEnv (v : Sys) (e : Relay.Ev) : Option Sys :=
  match e with
  | .sock id g k =>
    if !envAllowed v id g k then none else
    let t := tagOf v.rs e
    let r := Relay.step cap v.rs e
    let st' := match k with
      | .open_ => v.sockSt.map (fun q => if q.1 == g then (q.1, q.2.1, 1) else q)
      | .error _ => v.sockSt.map (fun q => if q.1 == g && q.2.2 == 0 then (q.1, q.2.1, 2) else q)
      | _ => v.sockSt
    some { v with rs := r.1, toPage := v.toPage ++ r.2.map (fun o => (o, t)), sockSt := st' }
  | _ =>
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
  s!"{repr v.genOf}|{v.bad}|{v.proto}|{repr v.sockSt}"

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
            if v'.bad || v'.proto then
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

-- the send the relay takes whole into the socket's queue: exactly the case where sendStepB's last branch runs
def sendOk (cap : Nat) (s : Relay.St) (id n : Nat) : Bool :=
  match (s.slot id).conn with
  | none => false
  | some c => c.isOpen && decide (n ≠ 0) && decide (n ≤ Relay.SEND_WINDOW - c.queued)
      && decide (c.written + c.queued + n ≤ cap) && !c.peerClosed

-- a discard empties the queue of an open connection (as discardStep does); of any other it changes nothing
def discardK (k : Clk) (s : Relay.St) (id : Nat) : Clk :=
  match (s.slot id).conn with
  | some c => if c.isOpen then { k with chunks := fun i => if i = id then [] else k.chunks i } else k
  | none => k

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
    if sendOk cap s id n then
      let m := flushSim ((k.chunks id) ++ [n]) 4294967295 k.bud
      let r := Relay.sendStepB cap s id n m.1
      let k' := { k with bud := m.2.2, used := k.used + m.1,
                         chunks := fun i => if i = id then m.2.1 else k.chunks i }
      (clearGone k' r.1 id, r.1, r.2)
    else
      let r := Relay.sendStepB cap s id n 0
      (clearGone k r.1 id, r.1, r.2)
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
    (clearGone (discardK k s id) r.1 id, r.1, r.2)
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

theorem good_discardK (k : Clk) (s : Relay.St) (id : Nat) (h : Good k) : Good (discardK k s id) := by
  unfold discardK
  split
  · split
    · exact good_chunks k _ h
    · exact h
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
      exact good_clearGone_eq _ _ _ (good_discardK k s id h)
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

-- what a flush takes, and what it leaves, add up to what was queued
theorem flushSim_sum : ∀ (cs : List Nat) (a : Nat) (b : Int),
    (flushSim cs a b).2.1.sum + (flushSim cs a b).1 = cs.sum := by
  intro cs
  induction cs with
  | nil =>
    intro a b
    simp [flushSim]
  | cons x rest ih =>
    intro a b
    unfold flushSim
    by_cases hb : b ≤ 0
    · rw [if_pos hb]
      simp
    · rw [if_neg hb]
      by_cases hw : min a x = 0
      · rw [if_pos hw]
        simp
      · rw [if_neg hw]
        by_cases hlt : min a x < x
        · rw [if_pos hlt]
          simp only [List.sum_cons]
          omega
        · rw [if_neg hlt]
          have ih' := ih (a - min a x) (b - 1000 * ((min a x : Nat) : Int))
          simp only [List.sum_cons]
          omega

-- the chunks left are positive when the chunks were
theorem flushSim_pos : ∀ (cs : List Nat) (a : Nat) (b : Int),
    (∀ x ∈ cs, 0 < x) → ∀ x ∈ (flushSim cs a b).2.1, 0 < x := by
  intro cs
  induction cs with
  | nil =>
    intro a b _ x hx
    simp [flushSim] at hx
  | cons h rest ih =>
    intro a b hpos x hx
    have hh : 0 < h := hpos h (by simp)
    have hrest : ∀ y ∈ rest, 0 < y := fun y hy => hpos y (by simp [hy])
    unfold flushSim at hx
    by_cases hb : b ≤ 0
    · rw [if_pos hb] at hx
      rcases List.mem_cons.mp hx with h1 | h1
      · subst h1; exact hh
      · exact hrest x h1
    · rw [if_neg hb] at hx
      by_cases hw : min a h = 0
      · rw [if_pos hw] at hx
        rcases List.mem_cons.mp hx with h1 | h1
        · subst h1; exact hh
        · exact hrest x h1
      · rw [if_neg hw] at hx
        by_cases hlt : min a h < h
        · rw [if_pos hlt] at hx
          rcases List.mem_cons.mp hx with h1 | h1
          · subst h1
            omega
          · exact hrest x h1
        · rw [if_neg hlt] at hx
          exact ih (a - min a h) (b - 1000 * ((min a h : Nat) : Int)) hrest x hx

-- what a flush takes is at most what is queued
theorem flushSim_le (cs : List Nat) (a : Nat) (b : Int) : (flushSim cs a b).1 ≤ cs.sum := by
  have := flushSim_sum cs a b
  omega

-- ---- the mirror: each connection's queue is the lengths of its chunks ----

-- for one id: no connection, no chunks; a connection, chunks that add up to its queued bytes; every chunk positive
def MirrorAt (k : Clk) (s : Relay.St) (id : Nat) : Prop :=
  ((s.slot id).conn = none → k.chunks id = []) ∧
  (∀ c, (s.slot id).conn = some c → (k.chunks id).sum = c.queued) ∧
  (∀ x ∈ k.chunks id, 0 < x)

def Mirror (k : Clk) (s : Relay.St) : Prop := ∀ id, MirrorAt k s id

theorem mirrorAt_of_eq (k k' : Clk) (s s' : Relay.St) (id : Nat)
    (hs : s'.slot id = s.slot id) (hk : k'.chunks id = k.chunks id) (h : MirrorAt k s id) :
    MirrorAt k' s' id := by
  unfold MirrorAt at h ⊢
  rw [hs, hk]
  exact h

theorem mirror_init (cps bps : Nat) : Mirror (init cps bps) Relay.init := by
  intro id
  unfold MirrorAt
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro c hc
    simp [Relay.init, Relay.St.slot] at hc
  · intro x hx
    simp [init] at hx

-- the ticker's flush of one id: the mirror holds for every id
theorem flushOne_other (k : Clk) (s : Relay.St) (id j : Nat) (h : j ≠ id) :
    (flushOne k s id).2.1.slot j = s.slot j ∧ (flushOne k s id).1.chunks j = k.chunks j := by
  unfold flushOne
  cases hsl : (s.slot id).conn with
  | none => exact ⟨rfl, rfl⟩
  | some c =>
    dsimp only
    by_cases ho : c.isOpen = true
    · rw [if_pos ho]
      by_cases hm : (flushSim (k.chunks id) 4294967295 k.bud).1 > 0
      · rw [if_pos hm]
        dsimp only
        exact ⟨Relay.flushConn_slot_ne _ _ _ _ _ h, by simp [h]⟩
      · rw [if_neg hm]
        exact ⟨rfl, rfl⟩
    · rw [if_neg ho]
      exact ⟨rfl, rfl⟩

-- a flush of an open connection's queue, of a positive amount that the queue holds: the connection after it
theorem flushConn_some (s : Relay.St) (id : Nat) (c : Relay.Conn) (a : Nat) (ho : c.isOpen = true)
    (ha : 0 < a) (hq : a ≤ c.queued) :
    (Relay.flushConn s id c a).1.slot id
      = { (s.slot id) with conn := some { c with queued := c.queued - a, written := c.written + a } } := by
  have hm : min a c.queued = a := Nat.min_eq_left hq
  have ha0 : a ≠ 0 := by omega
  unfold Relay.flushConn
  simp [ho, hm, ha0, Relay.setConn, Relay.setSlot, Relay.St.slot]

theorem mirror_flushOne (k : Clk) (s : Relay.St) (id : Nat) (h : Mirror k s) :
    Mirror (flushOne k s id).1 (flushOne k s id).2.1 := by
  intro j
  by_cases hj : j = id
  · subst hj
    have hm := h j
    unfold flushOne
    cases hsl : (s.slot j).conn with
    | none =>
      dsimp only
      unfold MirrorAt
      exact ⟨fun _ => hm.1 hsl, fun c hc => by simp [hsl] at hc, hm.2.2⟩
    | some c =>
      dsimp only
      by_cases ho : c.isOpen = true
      · rw [if_pos ho]
        have hsum := hm.2.1 c hsl
        by_cases hmt : (flushSim (k.chunks j) 4294967295 k.bud).1 > 0
        · rw [if_pos hmt]
          dsimp only
          have hle : (flushSim (k.chunks j) 4294967295 k.bud).1 ≤ c.queued := by
            have := flushSim_le (k.chunks j) 4294967295 k.bud
            rw [hsum] at this
            exact this
          have hsl2 := flushConn_some s j c _ ho hmt hle
          have hsum2 := flushSim_sum (k.chunks j) 4294967295 k.bud
          rw [hsum] at hsum2
          have hpos := flushSim_pos (k.chunks j) 4294967295 k.bud hm.2.2
          unfold MirrorAt
          refine ⟨?_, ?_, ?_⟩
          · intro hn
            simp only [hsl2] at hn
            simp at hn
          · intro c2 hc2
            simp only [hsl2] at hc2
            simp only [Option.some.injEq] at hc2
            subst hc2
            dsimp only
            simp only [↓reduceIte]
            omega
          · intro x hx
            dsimp only at hx
            simp only [↓reduceIte] at hx
            exact hpos x hx
        · rw [if_neg hmt]
          exact hm
      · rw [if_neg ho]
        exact hm
  · obtain ⟨hs, hc⟩ := flushOne_other k s id j hj
    exact mirrorAt_of_eq k (flushOne k s id).1 s (flushOne k s id).2.1 j hs hc (h j)


-- ---- the mirror holds through each step: each id's chunks are its queue ----

theorem flushSim_zero : ∀ (cs : List Nat) (a : Nat) (b : Int),
    (flushSim cs a b).1 = 0 → (flushSim cs a b).2.1 = cs := by
  intro cs
  induction cs with
  | nil =>
    intro a b _
    simp [flushSim]
  | cons x rest ih =>
    intro a b h
    unfold flushSim at h ⊢
    by_cases hb : b ≤ 0
    · rw [if_pos hb]
    · by_cases hw : min a x = 0
      · rw [if_neg hb, if_pos hw]
      · exfalso
        by_cases hlt : min a x < x
        · rw [if_neg hb, if_neg hw, if_pos hlt] at h
          dsimp only at h
          omega
        · rw [if_neg hb, if_neg hw, if_neg hlt] at h
          dsimp only at h
          omega

theorem clearGone_chunks_ne (k : Clk) (s : Relay.St) (id j : Nat) (h : j ≠ id) :
    (clearGone k s id).chunks j = k.chunks j := by
  unfold clearGone
  split <;> simp [h]

theorem clearGone_some (k : Clk) (s : Relay.St) (id : Nat) (c : Relay.Conn)
    (hs : (s.slot id).conn = some c) : clearGone k s id = k := by
  unfold clearGone
  simp [hs]

theorem discardK_chunks_ne (k : Clk) (s : Relay.St) (id j : Nat) (h : j ≠ id) :
    (discardK k s id).chunks j = k.chunks j := by
  unfold discardK
  split
  · split <;> simp [h]
  · rfl

-- a connection that keeps its queue (or ends, or is new and empty): the clearing step keeps the mirror
theorem mirrorAt_clearGone (k : Clk) (s s' : Relay.St) (id : Nat) (hM : MirrorAt k s id)
    (hQ : Relay.QOK s s' id) : MirrorAt (clearGone k s' id) s' id := by
  cases hs' : (s'.slot id).conn with
  | none =>
    have hk : clearGone k s' id = { k with chunks := fun i => if i = id then [] else k.chunks i } := by
      unfold clearGone
      simp [hs']
    rw [hk]
    unfold MirrorAt
    refine ⟨fun _ => by simp, fun c hc => ?_, fun x hx => ?_⟩
    · rw [hs'] at hc
      cases hc
    · simp at hx
  | some c' =>
    rw [clearGone_some k s' id c' hs']
    have hq := hQ c' hs'
    unfold MirrorAt at hM ⊢
    rcases hq with ⟨c, hc, hqe⟩ | ⟨hnone, hq0⟩
    · have hsum := hM.2.1 c hc
      refine ⟨fun h => ?_, fun c2 hc2 => ?_, hM.2.2⟩
      · rw [hs'] at h
        cases h
      · rw [hs'] at hc2
        cases hc2
        rw [hsum]
        exact hqe.symm
    · have hz := hM.1 hnone
      refine ⟨fun h => ?_, fun c2 hc2 => ?_, hM.2.2⟩
      · rw [hs'] at h
        cases h
      · rw [hs'] at hc2
        cases hc2
        rw [hz]
        simp [hq0]

-- the mirror of the other ids is unchanged, and the mirror of this id holds: the whole mirror holds
theorem mirror_of_parts (k k' : Clk) (s s' : Relay.St) (id : Nat) (hM : Mirror k s)
    (hs : ∀ j, j ≠ id → s'.slot j = s.slot j) (hk : ∀ j, j ≠ id → k'.chunks j = k.chunks j)
    (hid : MirrorAt k' s' id) : Mirror k' s' := by
  intro j
  by_cases hj : j = id
  · subst hj
    exact hid
  · exact mirrorAt_of_eq k k' s s' j (hs j hj) (hk j hj) (hM j)

-- an id with no connection has no chunks; a step that leaves it unconnected keeps that
theorem mirrorAt_qok_none (k : Clk) (s s' : Relay.St) (id : Nat) (hM : MirrorAt k s id)
    (hn : (s.slot id).conn = none) (hQ : Relay.QOK s s' id) : MirrorAt k s' id := by
  have hz := hM.1 hn
  unfold MirrorAt
  refine ⟨fun _ => hz, fun c2 hc2 => ?_, hM.2.2⟩
  rcases hQ c2 hc2 with ⟨c, hc, _⟩ | ⟨_, hq0⟩
  · rw [hn] at hc
    cases hc
  · rw [hz]
    simp [hq0]

theorem mirror_default (cap : Nat) (k : Clk) (s : Relay.St) (e : Relay.Ev) (hM : Mirror k s)
    (hQ : Relay.QOK s (Relay.step cap s e).1 (Relay.evId e)) :
    Mirror (clearGone k (Relay.step cap s e).1 (Relay.evId e)) (Relay.step cap s e).1 := by
  apply mirror_of_parts k _ s _ (Relay.evId e) hM
  · intro j hj
    exact Relay.step_slot_ne cap s e j (Ne.symm hj)
  · intro j hj
    exact clearGone_chunks_ne k _ _ j hj
  · exact mirrorAt_clearGone k s _ (Relay.evId e) (hM (Relay.evId e)) hQ

theorem connect_some_slot (cap : Nat) (s : Relay.St) (id : Nat) (c : Relay.Conn)
    (hc : ¬ (s.closed.isSome = true)) (hs : (s.slot id).conn = some c) :
    (Relay.step cap s (Relay.Ev.connect id)).1.slot id = s.slot id := by
  simp only [Relay.step, Relay.connectStep, hc, hs]
  try rfl

-- the connection's queue after a send the relay takes whole: the budget decides how much of it goes
theorem sendStepB_succ (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hs : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - c.queued) (hcap : c.written + c.queued + n ≤ cap)
    (hp : c.peerClosed = false) :
    (Relay.sendStepB cap s id n m).1.slot id
      = { (s.slot id) with conn := some { c with queued := c.queued + n - min m (c.queued + n),
                                                 written := c.written + min m (c.queued + n) } } := by
  have h1 : ¬ (n > Relay.SEND_WINDOW - c.queued) := by omega
  have h2 : ¬ (c.written + c.queued + n > cap) := by omega
  unfold Relay.sendStepB
  simp [hs, ho, hn, h1, h2, hp, Relay.slot_setConn_self]

-- a send that is not taken whole leaves the connection as it is, or ends it
theorem sendStepB_notok (cap : Nat) (s : Relay.St) (id n m : Nat) (hn : ¬ (sendOk cap s id n = true)) :
    Relay.QOK s (Relay.sendStepB cap s id n m).1 id := by
  unfold Relay.sendStepB
  cases hsl : (s.slot id).conn with
  | none =>
    dsimp only
    split
    all_goals exact Relay.qok_slot_eq _ _ _ rfl
  | some c =>
    dsimp only
    repeat' split
    all_goals first
      | exact Relay.qok_slot_eq _ _ _ rfl
      | (exfalso; apply hn; clear hn; simp_all [sendOk]; done)
      | (apply Relay.qok_none; simp [Relay.failConn, Relay.conn_setConn_self]; done)

theorem sendOk_spec (cap : Nat) (s : Relay.St) (id n : Nat) (h : sendOk cap s id n = true) :
    ∃ c, (s.slot id).conn = some c ∧ c.isOpen = true ∧ n ≠ 0 ∧ n ≤ Relay.SEND_WINDOW - c.queued
      ∧ c.written + c.queued + n ≤ cap ∧ c.peerClosed = false := by
  unfold sendOk at h
  cases hsl : (s.slot id).conn with
  | none => simp [hsl] at h
  | some c =>
    simp only [sendOk, hsl, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨ho, hn⟩, hw⟩, hcap⟩, hp⟩ := h
    exact ⟨c, rfl, ho, hn, hw, hcap, by simpa using hp⟩

-- the chunks, the bytes and the budget after a send that the relay takes whole
def sendK (k : Clk) (m : Nat × List Nat × Int) (id : Nat) : Clk :=
  { k with bud := m.2.2, used := k.used + m.1, chunks := fun i => if i = id then m.2.1 else k.chunks i }

theorem mirror_send_ok (cap : Nat) (k : Clk) (s : Relay.St) (id n : Nat) (hM : Mirror k s)
    (c : Relay.Conn) (hsl : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : n ≤ Relay.SEND_WINDOW - c.queued) (hcap : c.written + c.queued + n ≤ cap) (hp : c.peerClosed = false)
    (m : Nat × List Nat × Int) (hm : flushSim ((k.chunks id) ++ [n]) 4294967295 k.bud = m) :
    Mirror (clearGone (sendK k m id) (Relay.sendStepB cap s id n m.1).1 id) (Relay.sendStepB cap s id n m.1).1 := by
  have hsum := (hM id).2.1 c hsl
  have hpos0 : ∀ x ∈ (k.chunks id) ++ [n], 0 < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hM id).2.2 x hx
    · rw [List.mem_singleton.mp hx]
      exact Nat.pos_of_ne_zero hn
  have hsum2 : ((k.chunks id) ++ [n]).sum = c.queued + n := by
    rw [List.sum_append, hsum]
    simp
  have hsumM := flushSim_sum ((k.chunks id) ++ [n]) 4294967295 k.bud
  have hposM := flushSim_pos ((k.chunks id) ++ [n]) 4294967295 k.bud hpos0
  rw [hm] at hsumM hposM
  have hle : m.1 ≤ c.queued + n := by omega
  have hslot := sendStepB_succ cap s id n m.1 c hsl ho hn hw hcap hp
  rw [Nat.min_eq_left hle] at hslot
  have hconn : ((Relay.sendStepB cap s id n m.1).1.slot id).conn
      = some { c with queued := c.queued + n - m.1, written := c.written + m.1 } := by
    rw [hslot]
  rw [clearGone_some _ _ _ _ hconn]
  apply mirror_of_parts k _ s _ id hM
  · intro j hj
    exact Relay.sendStepB_slot_ne cap s id n m.1 j hj
  · intro j hj
    simp [sendK, hj]
  · have hk' : (sendK k m id).chunks id = m.2.1 := by
      simp [sendK]
    unfold MirrorAt
    rw [hk']
    refine ⟨fun h => ?_, fun c2 hc2 => ?_, hposM⟩
    · rw [hconn] at h
      cases h
    · rw [hconn] at hc2
      cases hc2
      dsimp only
      omega

theorem mirror_send_no (cap : Nat) (k : Clk) (s : Relay.St) (id n m : Nat) (hM : Mirror k s)
    (hno : ¬ (sendOk cap s id n = true)) :
    Mirror (clearGone k (Relay.sendStepB cap s id n m).1 id) (Relay.sendStepB cap s id n m).1 := by
  apply mirror_of_parts k _ s _ id hM
  · intro j hj
    exact Relay.sendStepB_slot_ne cap s id n m j hj
  · intro j hj
    exact clearGone_chunks_ne k _ _ j hj
  · exact mirrorAt_clearGone k s _ id (hM id) (sendStepB_notok cap s id n m hno)

theorem qok_sock (cap : Nat) (s : Relay.St) (id g : Nat) (k : Relay.Sk) (hk : ∀ a, k ≠ Relay.Sk.drain a) :
    Relay.QOK s (Relay.step cap s (Relay.Ev.sock id g k)).1 id := by
  by_cases hcl : s.closed.isSome = true
  · exact Relay.qok_slot_eq _ _ _ (by simp [Relay.step, hcl])
  · have h1 : (Relay.step cap s (Relay.Ev.sock id g k)).1 = (Relay.sockStep cap s id g k).1 := by
      simp [Relay.step, hcl]
    rw [h1]
    exact Relay.qok_sockStep cap s id g k hk

theorem qok_drain_none (cap : Nat) (s : Relay.St) (id g a : Nat) (hc : ¬ (s.closed.isSome = true))
    (hsl : (s.slot id).conn = none) :
    Relay.QOK s (Relay.step cap s (Relay.Ev.sock id g (Relay.Sk.drain a))).1 id :=
  Relay.qok_slot_eq _ _ _ (by simp [Relay.step, Relay.sockStep, hc, hsl])

theorem qok_drain_noop (cap : Nat) (s : Relay.St) (id g a : Nat) (c : Relay.Conn)
    (hc : ¬ (s.closed.isSome = true)) (hsl : (s.slot id).conn = some c)
    (hn : ¬ (c.gen = g ∧ c.isOpen = true)) :
    Relay.QOK s (Relay.step cap s (Relay.Ev.sock id g (Relay.Sk.drain a))).1 id := by
  apply Relay.qok_slot_eq
  by_cases hg : c.gen = g
  · have ho : c.isOpen = false := by
      cases hco : c.isOpen
      · rfl
      · exact absurd ⟨hg, hco⟩ hn
    simp [Relay.step, Relay.sockStep, hc, hsl, hg, ho, Relay.flushConn]
  · simp [Relay.step, Relay.sockStep, hc, hsl, hg]

theorem step_sock_drain_open (cap : Nat) (s : Relay.St) (id g a : Nat) (c : Relay.Conn)
    (hc : ¬ (s.closed.isSome = true)) (hsl : (s.slot id).conn = some c) (hg : c.gen = g) :
    (Relay.step cap s (Relay.Ev.sock id g (Relay.Sk.drain a))).1 = (Relay.flushConn s id c a).1 := by
  simp [Relay.step, Relay.sockStep, hc, hsl, hg]

-- an open connection's queue, flushed by the clock's amount: the connection keeps a queue of the chunks left
theorem mirrorAt_flushConn (k : Clk) (s : Relay.St) (id a : Nat) (c : Relay.Conn) (hM : MirrorAt k s id)
    (hsl : (s.slot id).conn = some c) (ho : c.isOpen = true) :
    (∃ c'', ((Relay.flushConn s id c (flushSim (k.chunks id) a k.bud).1).1.slot id).conn = some c'') ∧
    MirrorAt { k with chunks := fun i => if i = id then (flushSim (k.chunks id) a k.bud).2.1 else k.chunks i }
      (Relay.flushConn s id c (flushSim (k.chunks id) a k.bud).1).1 id := by
  have hsum := hM.2.1 c hsl
  have hle := flushSim_le (k.chunks id) a k.bud
  have hsum2 := flushSim_sum (k.chunks id) a k.bud
  have hpos := flushSim_pos (k.chunks id) a k.bud hM.2.2
  rw [hsum] at hle hsum2
  have hk' : ({ k with chunks := fun i => if i = id then (flushSim (k.chunks id) a k.bud).2.1 else k.chunks i }
      : Clk).chunks id = (flushSim (k.chunks id) a k.bud).2.1 := by
    simp
  by_cases hm : (flushSim (k.chunks id) a k.bud).1 = 0
  · have hz := flushSim_zero (k.chunks id) a k.bud hm
    have hf : (Relay.flushConn s id c (flushSim (k.chunks id) a k.bud).1).1 = s := by
      rw [hm]
      simp [Relay.flushConn, ho]
    rw [hf]
    refine ⟨⟨c, hsl⟩, ?_⟩
    unfold MirrorAt
    rw [hk', hz]
    refine ⟨fun h => ?_, fun c2 hc2 => ?_, hM.2.2⟩
    · rw [hsl] at h
      cases h
    · rw [hsl] at hc2
      cases hc2
      exact hsum
  · have hpos' : 0 < (flushSim (k.chunks id) a k.bud).1 := Nat.pos_of_ne_zero hm
    have hq : (flushSim (k.chunks id) a k.bud).1 ≤ c.queued := hle
    have hsl2 := flushConn_some s id c _ ho hpos' hq
    refine ⟨⟨_, by rw [hsl2]⟩, ?_⟩
    unfold MirrorAt
    rw [hsl2, hk']
    refine ⟨fun h => ?_, fun c2 hc2 => ?_, hpos⟩
    · simp at h
    · simp at hc2
      subst hc2
      dsimp only
      omega

theorem mirror_data (cap : Nat) (k : Clk) (s : Relay.St) (id g n : Nat) (hM : Mirror k s) (k' : Clk)
    (hk' : ∀ j, k'.chunks j = k.chunks j) :
    Mirror (clearGone k' (Relay.step cap s (Relay.Ev.sock id g (Relay.Sk.data n))).1 id)
      (Relay.step cap s (Relay.Ev.sock id g (Relay.Sk.data n))).1 := by
  apply mirror_of_parts k _ s _ id hM
  · intro j hj
    exact Relay.step_slot_ne cap s _ j (Ne.symm hj)
  · intro j hj
    rw [clearGone_chunks_ne _ _ _ _ hj, hk' j]
  · exact mirrorAt_clearGone k' s _ id (mirrorAt_of_eq k k' s s id rfl (hk' id) (hM id))
      (qok_sock cap s id g _ (fun a h => by cases h))

theorem mirror_discard (cap : Nat) (k : Clk) (s : Relay.St) (id : Nat) (hM : Mirror k s)
    (hc : ¬ (s.closed.isSome = true)) :
    Mirror (clearGone (discardK k s id) (Relay.step cap s (Relay.Ev.discard id)).1 id)
      (Relay.step cap s (Relay.Ev.discard id)).1 := by
  apply mirror_of_parts k _ s _ id hM
  · intro j hj
    exact Relay.step_slot_ne cap s _ j (Ne.symm hj)
  · intro j hj
    rw [clearGone_chunks_ne _ _ _ _ hj]
    exact discardK_chunks_ne k s id j hj
  · cases hsl : (s.slot id).conn with
    | none =>
      have hdk : discardK k s id = k := by
        unfold discardK
        simp [hsl]
      have hs' : (Relay.step cap s (Relay.Ev.discard id)).1.slot id = s.slot id := by
        simp only [Relay.step, Relay.discardStep, hc, hsl]
        repeat' split
        all_goals rfl
      rw [hdk]
      exact mirrorAt_clearGone k s _ id (hM id) (Relay.qok_slot_eq _ _ _ hs')
    | some c =>
      by_cases ho : c.isOpen = true
      · have hdk : discardK k s id = { k with chunks := fun i => if i = id then [] else k.chunks i } := by
          unfold discardK
          simp [hsl, ho]
        have hs' : (Relay.step cap s (Relay.Ev.discard id)).1.slot id
            = { (s.slot id) with conn := some { c with queued := 0 } } := by
          simp [Relay.step, Relay.discardStep, hc, hsl, ho, Relay.slot_setConn_self]
        have hconn : ((Relay.step cap s (Relay.Ev.discard id)).1.slot id).conn
            = some { c with queued := 0 } := by
          rw [hs']
        rw [hdk, clearGone_some _ _ _ _ hconn]
        unfold MirrorAt
        refine ⟨fun h => ?_, fun c2 hc2 => ?_, fun x hx => ?_⟩
        · rw [hconn] at h
          cases h
        · rw [hconn] at hc2
          cases hc2
          simp
        · simp at hx
      · have hdk : discardK k s id = k := by
          unfold discardK
          simp [hsl, ho]
        have hs' : (Relay.step cap s (Relay.Ev.discard id)).1.slot id = s.slot id := by
          have ho' : c.isOpen = false := by simpa using ho
          simp [Relay.step, Relay.discardStep, hc, hsl, ho']
          try rfl
        rw [hdk]
        exact mirrorAt_clearGone k s _ id (hM id) (Relay.qok_slot_eq _ _ _ hs')

theorem mirror_stepK (cap : Nat) (k : Clk) (s : Relay.St) (e : Relay.Ev) (hM : Mirror k s) :
    Mirror (stepK cap k s e).1 (stepK cap k s e).2.1 := by
  unfold stepK
  by_cases hc : s.closed.isSome = true
  · rw [if_pos hc]
    exact hM
  · rw [if_neg hc]
    cases e with
    | connect id =>
      dsimp only
      cases hsl : (s.slot id).conn with
      | some c =>
        dsimp only
        exact mirror_of_parts k k s _ id hM
          (fun j hj => Relay.step_slot_ne cap s (Relay.Ev.connect id) j (Ne.symm hj))
          (fun _ _ => rfl)
          (mirrorAt_of_eq k k s _ id (connect_some_slot cap s id c hc hsl) rfl (hM id))
      | none =>
        dsimp only
        split
        · exact fun j => mirrorAt_of_eq k _ s s j rfl rfl (hM j)
        · exact mirror_of_parts k _ s _ id hM
            (fun j hj => Relay.step_slot_ne cap s (Relay.Ev.connect id) j (Ne.symm hj))
            (fun _ _ => rfl)
            (mirrorAt_of_eq k _ _ _ id rfl rfl
              (mirrorAt_qok_none k s _ id (hM id) hsl (Relay.qok_connect cap s id)))
    | send id n =>
      dsimp only
      split
      next hok =>
        obtain ⟨c, hsl, ho, hn, hw, hcap, hp⟩ := sendOk_spec cap s id n hok
        exact mirror_send_ok cap k s id n hM c hsl ho hn hw hcap hp
          (flushSim ((k.chunks id) ++ [n]) 4294967295 k.bud) rfl
      next hno =>
        exact mirror_send_no cap k s id n 0 hM hno
    | discard id =>
      dsimp only
      exact mirror_discard cap k s id hM hc
    | read id k' =>
      dsimp only
      exact mirror_default cap k s (Relay.Ev.read id k') hM (Relay.qok_read cap s id k')
    | close id =>
      dsimp only
      exact mirror_default cap k s (Relay.Ev.close id) hM (Relay.qok_close cap s id)
    | deny id =>
      dsimp only
      exact mirror_default cap k s (Relay.Ev.deny id) hM (Relay.qok_deny cap s id)
    | sock id g kk =>
      cases kk with
      | open_ =>
        dsimp only
        exact mirror_default cap k s (Relay.Ev.sock id g Relay.Sk.open_) hM
          (qok_sock cap s id g Relay.Sk.open_ (fun a h => by cases h))
      | eof =>
        dsimp only
        exact mirror_default cap k s (Relay.Ev.sock id g Relay.Sk.eof) hM
          (qok_sock cap s id g Relay.Sk.eof (fun a h => by cases h))
      | peerclose =>
        dsimp only
        exact mirror_default cap k s (Relay.Ev.sock id g Relay.Sk.peerclose) hM
          (qok_sock cap s id g Relay.Sk.peerclose (fun a h => by cases h))
      | error x =>
        dsimp only
        exact mirror_default cap k s (Relay.Ev.sock id g (Relay.Sk.error x)) hM
          (qok_sock cap s id g (Relay.Sk.error x) (fun a h => by cases h))
      | data n =>
        dsimp only
        refine mirror_data cap k s id g n hM _ ?_
        intro j
        split <;> rfl
      | drain a =>
        dsimp only
        cases hsl : (s.slot id).conn with
        | none =>
          dsimp only
          exact mirror_default cap k s (Relay.Ev.sock id g (Relay.Sk.drain a)) hM
            (qok_drain_none cap s id g a hc hsl)
        | some c =>
          dsimp only
          by_cases hgo : c.gen = g ∧ c.isOpen = true
          · obtain ⟨hg, ho⟩ := hgo
            have hcond : (c.gen = g && c.isOpen) = true := by simp [hg, ho]
            rw [if_pos hcond]
            rw [step_sock_drain_open cap s id g (flushSim (k.chunks id) a k.bud).1 c hc hsl hg]
            obtain ⟨⟨c'', hc''⟩, _⟩ := mirrorAt_flushConn k s id a c (hM id) hsl ho
            rw [clearGone_some _ _ _ c'' hc'']
            apply mirror_of_parts k _ s _ id hM
            · intro j hj
              exact Relay.flushConn_slot_ne s id c _ j hj
            · intro j hj
              simp [hj]
            · exact mirrorAt_of_eq _ _ _ _ id rfl rfl (mirrorAt_flushConn k s id a c (hM id) hsl ho).2
          · have hcond : ¬ ((c.gen = g && c.isOpen) = true) := by
              intro h
              exact hgo (by simpa using h)
            rw [if_neg hcond]
            exact mirror_default cap k s (Relay.Ev.sock id g (Relay.Sk.drain a)) hM
              (qok_drain_noop cap s id g a c hc hsl hgo)

theorem mirror_flushIds (ids : List Nat) : ∀ (k : Clk) (s : Relay.St), Mirror k s →
    Mirror (flushIds k s ids).1 (flushIds k s ids).2.1 := by
  induction ids with
  | nil =>
    intro k s h
    exact h
  | cons id ids ih =>
    intro k s h
    exact ih _ _ (mirror_flushOne k s id h)

theorem mirror_tickK (k : Clk) (s : Relay.St) (ms : Nat) (hM : Mirror k s) :
    Mirror (tickK k s ms).1 (tickK k s ms).2.1 := by
  unfold tickK
  split
  · exact hM
  · dsimp only
    exact mirror_flushIds (List.range 256) _ _ (fun j => mirrorAt_of_eq k _ s s j rfl rfl (hM j))

theorem mirror_runK (cap : Nat) (items : List Item) : ∀ (k : Clk) (s : Relay.St), Mirror k s →
    Mirror (runK cap k s items).1 (runK cap k s items).2.1 := by
  induction items with
  | nil =>
    intro k s h
    exact h
  | cons it its ih =>
    intro k s h
    cases it with
    | ev e =>
      exact ih _ _ (mirror_stepK cap k s e h)
    | tick ms =>
      exact ih _ _ (mirror_tickK k s ms h)

-- THE MIRROR: from the start, for any trace, each connection's chunks add up to its queued bytes
theorem mirror_run (cps bps cap : Nat) (items : List Item) :
    Mirror (runK cap (init cps bps) Relay.init items).1 (runK cap (init cps bps) Relay.init items).2.1 :=
  mirror_runK cap items _ _ (mirror_init cps bps)

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

-- ================================================================================================
-- The window, one connection at a time. The relay refuses a SEND that would take its queue past SEND_WINDOW
-- with a protocol close (sendStep: n > SEND_WINDOW - queued). The page's pump frames a SEND only within the
-- window beyond what the relay has taken (Page.PInv). Pair states how the two counts of one connection relate:
-- the relay's accepted total, with the bytes of SEND frames in flight, is no more than what the page framed, and
-- the page has taken no more than the relay has. The lemmas below show that the relay's check then passes, and that
-- each operation on the connection keeps Pair. What makes Pair hold for a connection of the composed system (frames
-- in order; each frame applied to the connection that sent it) is not in this section.
-- ================================================================================================

namespace Window

structure Pair (pc : Page.PConn) (rc : Relay.Conn) (f : Nat) : Prop where
  total : rc.written + rc.queued + f ≤ pc.sent
  taken : pc.written ≤ rc.written

-- the relay's window check passes for a SEND of n, given the page's invariant and Pair (f: in-flight bytes, n ≤ f)
theorem window_ok (pc : Page.PConn) (rc : Relay.Conn) (f n : Nat) (hI : Page.PInv pc) (hP : Pair pc rc f)
    (hn : n ≤ f) : rc.queued + n ≤ Relay.SEND_WINDOW := by
  have hA := hP.total
  have hB := hP.taken
  obtain ⟨-, -, hC⟩ := hI
  unfold Page.SEND_W at hC
  omega

-- the relay's SEND of n, accepted into an open connection with room in the window and the count limit, takes
-- the bytes the flush allows (m of them) and no close (closed stays none)
theorem sendStepB_accept (cap : Nat) (s : Relay.St) (id n m : Nat) (c : Relay.Conn)
    (hs : (s.slot id).conn = some c) (ho : c.isOpen = true) (hn : n ≠ 0)
    (hw : c.queued + n ≤ Relay.SEND_WINDOW) (hcap : c.written + c.queued + n ≤ cap) (hp : c.peerClosed = false) :
    (Relay.sendStepB cap s id n m).1 = Relay.setConn s id (some { c with
        queued := c.queued + n - min m (c.queued + n), written := c.written + min m (c.queued + n) }) := by
  unfold Relay.sendStepB
  rw [hs]
  have h1 : ¬ (n > Relay.SEND_WINDOW - c.queued) := by omega
  have h2 : ¬ (c.written + c.queued + n > cap) := by omega
  simp [ho, hn, h1, h2, hp]

-- accepting a SEND of n (one of the in-flight bytes) keeps Pair, with n fewer in flight
theorem pair_accept (pc : Page.PConn) (c : Relay.Conn) (f n m : Nat) (hP : Pair pc c f) (hn : n ≤ f) :
    Pair pc { c with queued := c.queued + n - min m (c.queued + n), written := c.written + min m (c.queued + n) }
      (f - n) := by
  have hA := hP.total
  have hB := hP.taken
  have hw : min m (c.queued + n) ≤ c.queued + n := Nat.min_le_right _ _
  generalize min m (c.queued + n) = w at hw ⊢
  exact ⟨by simp only []; omega, by simp only []; omega⟩

-- the socket takes m bytes of the queue (flushConn): Pair is kept, the total is unchanged
theorem pair_flush (pc : Page.PConn) (c : Relay.Conn) (f a : Nat) (hP : Pair pc c f) :
    Pair pc { c with queued := c.queued - min a c.queued, written := c.written + min a c.queued } f := by
  have hA := hP.total
  have hB := hP.taken
  have hw : min a c.queued ≤ c.queued := Nat.min_le_right _ _
  generalize min a c.queued = w at hw ⊢
  exact ⟨by simp only []; omega, by simp only []; omega⟩

-- a discard of the queue (discardStep) with no SEND in flight keeps Pair
theorem pair_discard (pc : Page.PConn) (c : Relay.Conn) (hP : Pair pc c 0) :
    Pair pc { c with queued := 0 } 0 := by
  have hA := hP.total
  have hB := hP.taken
  exact ⟨by simp only []; omega, hB⟩

-- the page frames a SEND of n (pump): the bytes are sent and in flight
theorem pair_frame (pc : Page.PConn) (rc : Relay.Conn) (f n : Nat) (hP : Pair pc rc f) :
    Pair { pc with sent := pc.sent + n } rc (f + n) := by
  have hA := hP.total
  have hB := hP.taken
  exact ⟨by simp only []; omega, hB⟩

-- the relay's WRITTEN count, cnt, arrives: it is no more than the relay's own count now, and no less than the
-- page's (counts only grow along the frames of one connection)
theorem pair_written (pc : Page.PConn) (rc : Relay.Conn) (f cnt : Nat) (hP : Pair pc rc f)
    (hc : cnt ≤ rc.written) (_hm : pc.written ≤ cnt) : Pair { pc with written := cnt } rc f := by
  have hA := hP.total
  exact ⟨hA, hc⟩

-- the discard reset of the page (its WRITTEN with flag 1): the page's counts become the relay's, with nothing
-- queued or in flight
-- and the page's invariant (Page.PInv) survives the same WRITTEN frame: the counts stay in order and in the window
theorem pinv_written (pc : Page.PConn) (rc : Relay.Conn) (f cnt : Nat) (hI : Page.PInv pc) (hP : Pair pc rc f)
    (hc : cnt ≤ rc.written) (hm : pc.written ≤ cnt) : Page.PInv { pc with written := cnt } := by
  have hA := hP.total
  obtain ⟨-, hT, hW⟩ := hI
  unfold Page.PInv
  unfold Page.SEND_W at hW ⊢
  exact ⟨by simp only []; omega, hT, by simp only []; omega⟩

theorem pair_discard_reset (pc : Page.PConn) (rc : Relay.Conn) (cnt : Nat) (hP : Pair pc rc 0)
    (hq : rc.queued = 0) (hw : rc.written = cnt) :
    Pair { pc with sent := cnt, written := cnt } rc 0 := by
  have hA := hP.total
  exact ⟨by simp only []; omega, by simp only []; omega⟩

end Window

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
