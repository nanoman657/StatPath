
-- ================================================================================================
-- The induction (guarded timed model, the fixed page). Inv is the invariant: each field is a claim about the
-- state, and the step lemmas below show that each transition keeps every field. WQ (the window) follows.
-- ================================================================================================
namespace Ind
open Timed

def ConnOf (T : TSys) (id : Nat) : Option Relay.Conn := (T.c.rs.slot id).conn
def PageOf (T : TSys) (id : Nat) : Option Page.PConn := (T.c.page.slots id).conn
def qs (id : Nat) (T : TSys) : Nat := qsumT id T.c.toRelay
def isClosedOut : Relay.Out → Bool
  | .closed _ => true
  | _ => false

-- the queue order: a frame that may not follow another frame of the same id (a SEND, READ or DISCARD after a CONNECT
-- of its id, and a SEND or DISCARD after a DISCARD of its id): the page frames these only on an open connection, and
-- it holds a SEND back while a discard is pending
def FwdEv : Relay.Ev → Relay.Ev → Prop
  | .connect a, .send b _ => a = b
  | .connect a, .read b _ => a = b
  | .connect a, .discard b => a = b
  | .connect a, .connect b => a = b
  | .discard a, .send b _ => a = b
  | .discard a, .discard b => a = b
  | .close a, .connect b => a = b
  | _, _ => False

-- a discard of the page is waiting in the queue, or the reply to one is, for this id
def DiscWait (T : TSys) (id : Nat) : Prop := ∃ q ∈ T.c.toRelay, q.1 = .discard id
def ReplyWait (T : TSys) (id : Nat) : Prop := ∃ q ∈ T.c.toPage, ∃ cnt, q.1 = .written id cnt 1
def ConnWait (T : TSys) (id : Nat) : Prop := ∃ q ∈ T.c.toRelay, q.1 = .connect id

-- a relation holding between every two members of a list holds along the list
theorem pairwise_of_forall {α : Type} (R : α → α → Prop) : ∀ (L : List α), (∀ a ∈ L, ∀ b ∈ L, R a b) → L.Pairwise R := by
  intro L
  induction L with
  | nil => intro _; exact List.Pairwise.nil
  | cons x xs ih =>
    intro h
    refine List.Pairwise.cons ?_ (ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])))
    intro b hb
    exact h x (by simp) b (by simp [hb])

structure Inv (T : TSys) : Prop where
  pi : ∀ id pc, PageOf T id = some pc → Page.PInv pc
  link : ∀ id c, ConnOf T id = some c →
    (∃ pc, PageOf T id = some pc ∧ (pc.seq, c.gen) ∈ T.c.genOf) ∨
    (PageOf T id = none ∧ (T.c.page.slots id).closing = true)
  acc : ∀ id pc c, PageOf T id = some pc → ConnOf T id = some c → (pc.seq, c.gen) ∈ T.c.genOf →
    c.written + c.queued + qs id T ≤ pc.sent ∧ pc.written ≤ c.written
  wq : ∀ id c, ConnOf T id = some c → c.queued + qs id T ≤ Relay.SEND_WINDOW
  gen : ∀ q ∈ T.c.toPage, ∀ id, outIdT q.1 = some id → ∀ c, ConnOf T id = some c → c.gen = q.2
  apply : ∀ q ∈ T.c.toPage, ∀ id, isClosedOut q.1 = false → outIdT q.1 = some id → ∀ pc, PageOf T id = some pc →
    (T.c.page.slots id).closing = true ∨ (pc.seq, q.2) ∈ T.c.genOf
  noOrphan : ∀ q ∈ T.c.toPage, ∀ id, isClosedOut q.1 = false → outIdT q.1 = some id →
    PageOf T id = none → (T.c.page.slots id).closing = true
  written : ∀ q ∈ T.c.toPage, ∀ id cnt f, q.1 = .written id cnt f → ∀ c, ConnOf T id = some c → c.gen = q.2 →
    cnt ≤ c.written
  reset : ∀ q ∈ T.c.toPage, ∀ id cnt, q.1 = .written id cnt 1 → ∀ pc, PageOf T id = some pc →
    pc.discardPending = true → (pc.seq, q.2) ∈ T.c.genOf → ∀ c, ConnOf T id = some c → c.gen = q.2 →
    c.queued = 0 ∧ qs id T = 0 ∧ c.written = cnt
  barrier : List.Pairwise (fun p q => ¬ FwdEv p.1 q.1) T.c.toRelay
  connClean : ∀ q ∈ T.c.toRelay, ∀ id, q.1 = .connect id → ConnOf T id = none
  notOpen : ∀ id pc, PageOf T id = some pc → pc.isOpen = false → pc.sent = 0 ∧ pc.written = 0
  cl : ∀ q ∈ T.c.toRelay, ∀ id, q.1 = .connect id →
    (∃ pc, PageOf T id = some pc ∧ pc.seq = q.2) ∨ (PageOf T id = none ∧ (T.c.page.slots id).closing = true)
  rq : ∀ q ∈ T.c.toPage, ∀ id cnt, q.1 = .written id cnt 1 → ∀ x ∈ T.c.toRelay, ∀ n, x.1 ≠ .send id n
  gensLt : ∀ id c, ConnOf T id = some c → c.gen < T.c.rs.nextGen
  gp : ∀ q ∈ T.c.toRelay, ∀ id, q.1 = .connect id → ∀ g, (q.2, g) ∉ T.c.genOf
  openG : ∀ id pc, PageOf T id = some pc → pc.isOpen = true → ∃ g, (pc.seq, g) ∈ T.c.genOf
  mirror : Clock.Mirror T.clk T.c.rs
  good : Clock.Good T.clk
  -- every sequence number the page has given is below its next one (for the genOf map and the queued CONNECTs)
  seqG : ∀ p g, (p, g) ∈ T.c.genOf → p < T.c.page.nextSeq
  seqQ : ∀ q ∈ T.c.toRelay, ∀ id, q.1 = .connect id → q.2 < T.c.page.nextSeq
  -- a queued discard of an open page connection finds it pending (the page keeps one discard at a time)
  disc : ∀ q ∈ T.c.toRelay, ∀ id, q.1 = .discard id → ∀ pc, PageOf T id = some pc → pc.isOpen = true → pc.discardPending = true
  -- a discard reply in the page's queue finds its connection pending its reset, or the id closing
  rep : ∀ q ∈ T.c.toPage, ∀ id cnt, q.1 = .written id cnt 1 →
    (∃ pc, PageOf T id = some pc ∧ pc.discardPending = true) ∨ (PageOf T id = none ∧ (T.c.page.slots id).closing = true)
  -- a connection that has received data has the generation the relay gave it
  recvG : ∀ id pc, PageOf T id = some pc → 0 < pc.received → ∃ g, (pc.seq, g) ∈ T.c.genOf
  -- the page's queue and the relay's, in the order they are kept (step 1 of the extension: see induct/README.md)
  failNone : ∀ q ∈ T.c.toPage, ∀ id e, q.1 = .fail id e → ConnOf T id = none
  closedNone : ∀ q ∈ T.c.toPage, ∀ id, q.1 = .closed id → ConnOf T id = none
  closedClosing : ∀ q ∈ T.c.toPage, ∀ id, q.1 = .closed id → (T.c.page.slots id).closing = true
  closedOrd : List.Pairwise (fun p q => ∀ id, p.1 = .closed id → outIdT q.1 = some id → False) T.c.toPage
  closeClosing : ∀ x ∈ T.c.toRelay, ∀ id, x.1 = .close id → (T.c.page.slots id).closing = true
  closedNoConn : ∀ q ∈ T.c.toPage, ∀ id, q.1 = .closed id → ∀ x ∈ T.c.toRelay, x.1 ≠ .connect id
  openRel : ∀ id pc, PageOf T id = some pc → pc.isOpen = true → ∀ c, ConnOf T id = some c → c.isOpen = true
  okOpen : ∀ q ∈ T.c.toPage, ∀ id, q.1 = .ok id → (T.c.page.slots id).closing = false → ∀ pc, PageOf T id = some pc → pc.isOpen = false
  okNoDisc : ∀ q ∈ T.c.toPage, ∀ id, q.1 = .ok id → (T.c.page.slots id).closing = false → ∀ x ∈ T.c.toRelay, x.1 ≠ .discard id
  discRel : ∀ x ∈ T.c.toRelay, ∀ id, x.1 = .discard id → ConnOf T id = none ∨ (∃ pc, PageOf T id = some pc ∧ pc.isOpen = true) ∨ (PageOf T id = none ∧ (T.c.page.slots id).closing = true)
  closingNone : ∀ id, (T.c.page.slots id).closing = true → (T.c.page.slots id).conn = none
  closedNoClose : ∀ q ∈ T.c.toPage, ∀ id, q.1 = .closed id → ∀ x ∈ T.c.toRelay, x.1 ≠ .close id
  failOrd : List.Pairwise (fun p q => ∀ id e, p.1 = .fail id e → outIdT q.1 = some id → isClosedOut q.1 = true) T.c.toPage

theorem inv_init (cps bps : Nat) : Inv (TSys.init true cps bps) := by
  constructor
  all_goals first
    | exact Clock.good_init cps bps
    | exact Clock.mirror_init cps bps
    | (intros; simp_all [PageOf, ConnOf, TSys.init, Client.initSys, Relay.init, Relay.St.slot, Page.init, Page.emptySlot,
        qs, qsumT, DiscWait, ReplyWait, ConnWait])

end Ind
