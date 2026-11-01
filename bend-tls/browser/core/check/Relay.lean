/-
Relay.lean: the relay's connection machine (relay/relay.ts) as a Lean model, with theorems about it.

The machine has one slot per connection id. A slot holds the connection that the id is in use for. Each
connection has a generation: a CONNECT that the relay accepts starts a connection with the next generation.
Socket events carry the id and the generation of the socket they come from, so a late event from a socket
that has been closed (and whose id may have been reused) can be told apart from the events of the connection
that has the id now. That is the point of the generations: without it, a late failure of an old socket fails
the new connection (the bug fixed in relay.ts; test/lifecycle.test.ts).

The model is what the relay is tested against: relay_conformance.test.ts (in this folder) drives the relay with
random traces of page frames and socket events, and compares the frames it sends with the output of this program
on the same trace. The theorems are about the model: what it guarantees for every trace. The assumptions are
stated where they are used:
  * a socket opens once, and its events come after its open (the events Bun produces);
  * for liveness, the environment is fair: a socket that is offered a byte takes one, and the relay's
    budget refills (the model has no budget).

Input: traces, each starting with a "trace" line. In a trace, one event per line, after an optional "cap N"
line (the count limit; default 2^32 - 1):
  connect ID | deny ID | send ID N | discard ID | read ID K | close ID
  sock ID GEN open | sock ID GEN data N | sock ID GEN eof | sock ID GEN peerclose
  sock ID GEN error E | sock ID GEN drain A
Output: for each trace, one line per frame or session event, then a line "end":
  ok ID | data ID N | eof ID | written ID COUNT FLAG | fail ID ERRNO | wsclose CODE
-/

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

structure Slot where
  known : Bool
  conn : Option Conn

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
  | wsclose (code : Nat)
  deriving DecidableEq

inductive Sk where
  | open_
  | data (n : Nat)
  | eof
  | peerclose
  | error (e : Nat)
  | drain (a : Nat)

inductive Ev where
  | connect (id : Nat)
  | deny (id : Nat)
  | send (id n : Nat)
  | discard (id : Nat)
  | read (id k : Nat)
  | close (id : Nat)
  | sock (id g : Nat) (k : Sk)

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
    else if n > SEND_WINDOW - c.queued then protoClose s 1002
    else if c.written + c.queued + n > cap then failConn s id c 27
    else if c.peerClosed then failConn s id c 32
    else
      -- the socket takes everything offered, so the queue is written at once
      let total := c.queued + n
      let c' : Conn := { c with queued := 0, written := c.written + total }
      (setConn s id (some c'), if total > 0 then [Out.written id c'.written 0] else [])

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

def closeStep (s : St) (id : Nat) : St × List Out :=
  match (s.slot id).conn with
  | none => (s, [])
  | some _ => (setConn s id none, [])

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
    (step cap s e).1.slots = s.slots ∧ ((step cap s e).2 = [] ∨ (step cap s e).2 = [Out.wsclose 1002]) := by
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
      simp [closeStep, hn]
    | sock id g k =>
      simp only [evId] at hn
      simp [sockStep, hn]

-- the frames of a trace never name an id that is free at its start, unless the trace connects or denies it
theorem freed_run (cap : Nat) (id : Nat) (es : List Ev) :
    ∀ (s : St), (s.slot id).conn = none → (∀ e ∈ es, evId e = id → IsFreeEv e) →
      ∀ o ∈ (run cap s es).2, outId o ≠ some id := by
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
        rcases (step_none_shape cap s e hF hn').2 with h | h
        · rw [h] at h1
          simp at h1
        · rw [h] at h1
          simp at h1
          subst h1
          simp [outId]
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
  | .wsclose c => s!"wsclose {c}"

end Relay

open Relay

partial def readLines (h : IO.FS.Stream) (acc : Array String) : IO (Array String) := do
  let line ← h.getLine
  if line.isEmpty then return acc
  readLines h (acc.push line.trimAscii.toString)

def emitTrace (cap : Nat) (evs : Array Ev) : IO Unit := do
  let (_, outs) := run cap init evs.toList
  for o in outs do
    IO.println (showOut o)
  IO.println "end"

def main : IO UInt32 := do
  let lines ← readLines (← IO.getStdin) #[]
  let mut cap := DEFAULT_CAP
  let mut evs : Array Ev := #[]
  let mut started := false
  let mut bad := false
  for l in lines do
    if bad || l.isEmpty then continue
    if l == "trace" then
      if started then emitTrace cap evs
      cap := DEFAULT_CAP
      evs := #[]
      started := true
    else
      let ws := l.splitOn " "
      match ws with
      | ["cap", n] =>
        match n.toNat? with
        | some k => cap := k
        | none => bad := true
      | _ =>
        match parseEv ws with
        | some e => evs := evs.push e
        | none => bad := true
  if bad then
    IO.println "BAD"
    return 1
  if started then emitTrace cap evs
  return 0
