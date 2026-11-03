
namespace Timed
-- ---- the candidate invariant (guarded model): each component is a Bool check over the timed state ----
def gLink (v : TSys) (pc : Page.PConn) (c : Relay.Conn) : Bool := v.c.genOf.any (fun q => q.1 == pc.seq && q.2 == c.gen)

-- I2: a relay connection belongs to a page connection that the relay has taken, or the page has closed the id
def iLink (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.rs.slot id).conn with
  | some c => match (v.c.page.slots id).conn with
    | some pc => gLink v pc c
    | none => (v.c.page.slots id).closing
  | none => true

-- I3: the accounting of a linked pair (the relay has taken no more than the page framed; the page has taken no
-- more than the relay wrote)
def iAcc (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn, (v.c.rs.slot id).conn with
  | some pc, some c => !(gLink v pc c) ||
      (decide (c.written + c.queued + qsumT id v.c.toRelay ≤ pc.sent) && decide (pc.written ≤ c.written))
  | _, _ => true

-- I5: the frames pending for an id come from its relay connection (or there is none)
def iGen (v : TSys) : Bool := v.c.toPage.all fun q =>
  match outIdT q.1 with
  | some id => match (v.c.rs.slot id).conn with
    | some c => c.gen == q.2
    | none => true
  | none => true

-- I6: a frame the page would apply belongs to its connection (the page's is linked to the frame's generation)
def iApply (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .closed _ => true
  | _ => match outIdT q.1 with
    | some id => match (v.c.page.slots id).conn with
      | some pc => (v.c.page.slots id).closing || v.c.genOf.any (fun g => g.1 == pc.seq && g.2 == q.2)
      | none => (v.c.page.slots id).closing || true
    | none => true

-- I7: no frame waits for an id whose page has no connection and is not closing
def iNoOrphan (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .closed _ => true
  | _ => match outIdT q.1 with
    | some id => !((v.c.page.slots id).conn.isNone && !(v.c.page.slots id).closing)
    | none => true

-- I8: a WRITTEN frame's count is no more than the relay's count of its connection, now
def iWritten (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .written id cnt _ => match (v.c.rs.slot id).conn with
    | some c => !(c.gen == q.2) || decide (cnt ≤ c.written)
    | none => true
  | _ => true

-- I9: a reset (WRITTEN with the discard flag, for a page with a discard pending) finds the connection drained
def iReset (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .written id cnt 1 => match (v.c.page.slots id).conn with
    | some pc => !(pc.discardPending && v.c.genOf.any (fun g => g.1 == pc.seq && g.2 == q.2)) ||
        (match (v.c.rs.slot id).conn with
          | some c => !(c.gen == q.2) || (decide (c.queued = 0) && decide (qsumT id v.c.toRelay = 0) && decide (cnt = c.written))
          | none => true)
    | none => true
  | _ => true

-- I10: a CONNECT or a DISCARD of an id is never followed, in the queue, by a SEND of that id
-- a frame that may not follow another frame of the same id in the queue: a SEND, READ or DISCARD after a CONNECT
-- of its id, and a SEND or DISCARD after a DISCARD of its id (the page frames these only on an open connection,
-- and it holds a SEND back while a discard is pending)
def fwdB : Relay.Ev → Relay.Ev → Bool
  | .connect a, .send b _ => a == b
  | .connect a, .read b _ => a == b
  | .connect a, .discard b => a == b
  | .connect a, .connect b => a == b
  | .discard a, .send b _ => a == b
  | .discard a, .discard b => a == b
  | .close a, .connect b => a == b
  | _, _ => false
def pairOK : List (Relay.Ev × Nat) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !fwdB x.1 y.1) && pairOK xs
def iBarrier (v : TSys) : Bool := pairOK v.c.toRelay

-- I11: a CONNECT waiting in the queue finds no connection for its id
def iConnClean (v : TSys) : Bool := v.c.toRelay.all fun q =>
  match q.1 with
  | .connect id => (v.c.rs.slot id).conn.isNone
  | _ => true

-- I12: an open page connection's linked relay connection is open; I13: and the relay knows the id
def iOpen (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn, (v.c.rs.slot id).conn with
  | some pc, some c => !pc.isOpen || !(gLink v pc c) || (c.isOpen && (v.c.rs.slot id).known)
  | _, _ => true

-- I14: a frame that needs an open connection finds it open, or gone and known
def iNeedsOpen (v : TSys) : Bool := v.c.toRelay.all fun q =>
  let idOf : Option Nat := match q.1 with
    | .send id _ => some id | .discard id => some id | .read id _ => some id | _ => none
  match idOf with
  | some id => match (v.c.rs.slot id).conn with
    | some c => c.isOpen
    | none => (v.c.rs.slot id).known
  | none => true

-- I15: a discard the page has pending is waiting in the queue, or its reply is, or the relay has no connection for the
-- id (the relay answers nothing then). A DISCARD or a reply with no CONNECT of its id behind the DISCARD belongs to the
-- page's current connection, so the page has the discard pending.
def iPending (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn with
  | some pc =>
    let discWait := v.c.toRelay.any (fun q => match q.1 with | .discard i => i == id | _ => false)
    let replyWait := v.c.toPage.any (fun q => match q.1 with | .written i _ 1 => i == id | _ => false)
    let connWait := v.c.toRelay.any (fun q => match q.1 with | .connect i => i == id | _ => false)
    let gone := (v.c.rs.slot id).conn.isNone
    (!pc.discardPending || discWait || replyWait || gone) &&
      ((!(discWait && !connWait) && !replyWait) || pc.discardPending)
  | none => true

-- I16: a page connection that is not open has nothing counted on either side
def iNotOpen (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn with
  | some pc => pc.isOpen || (decide (pc.sent = 0) && decide (pc.written = 0))
  | none => true

-- I17, I18 come from the clock: the queues are the relay's, and the budget and the tokens keep their bounds
def iInv : List (String × (TSys → Bool)) :=
  [("PI", cPI), ("Link", iLink), ("Acc", iAcc), ("WQ", cWQ), ("Gen", iGen), ("Apply", iApply),
   ("NoOrphan", iNoOrphan), ("Written", iWritten), ("Reset", iReset), ("Barrier", iBarrier),
   ("ConnClean", iConnClean), ("Open", iOpen), ("NeedsOpen", iNeedsOpen), ("Pending", iPending),
   ("NotOpen", iNotOpen), ("Mirror", cMirror), ("Good", cGood)]


-- CL: a CONNECT waiting in the queue is for the page's connection of its id (or the id is closing, not connected)
def iCL (v : TSys) : Bool := v.c.toRelay.all fun q =>
  match q.1 with
  | .connect id => match (v.c.page.slots id).conn with
    | some pc => decide (pc.seq = q.2)
    | none => (v.c.page.slots id).closing
  | _ => true

-- KO: an OK frame's id is known to the relay (the relay said OK after it took the CONNECT)
def iKO (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .ok id => (v.c.rs.slot id).known
  | _ => true

-- K: an open page connection's id is known to the relay
def iKnown (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn with
  | some pc => !pc.isOpen || (v.c.rs.slot id).known
  | none => true


-- ConnKnown: a relay connection's id is known to the relay
def iConnKnown (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.rs.slot id).conn with
  | some _ => (v.c.rs.slot id).known
  | none => true

-- OpenG: an open page connection has its generation recorded in genOf
def iOpenG (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn with
  | some pc => !pc.isOpen || v.c.genOf.any (fun g => g.1 == pc.seq)
  | none => true


-- GensLt: every relay connection's generation is below the next one to give
def iGensLt (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.rs.slot id).conn with
  | some c => decide (c.gen < v.c.rs.nextGen)
  | none => true

-- GP: a CONNECT waiting in the queue has no generation recorded for its sequence number yet
def iGP (v : TSys) : Bool := v.c.toRelay.all fun q =>
  match q.1 with
  | .connect _ => !(v.c.genOf.any (fun g => g.1 == q.2))
  | _ => true


-- RQ: a reply to a discard (flag 1) is waiting for an id: no SEND of that id is in the queue
def iRQ (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .written id _ 1 => !(v.c.toRelay.any (fun x => match x.1 with | .send i _ => i == id | _ => false))
  | _ => true

-- candidate: a discard waiting in the queue for an id whose page connection is open has that connection pending
def iDisc (v : TSys) : Bool := v.c.toRelay.all fun q => match q.1 with
  | .discard id => match (v.c.page.slots id).conn with
    | some pc => !pc.isOpen || pc.discardPending
    | none => true
  | _ => true
-- candidate: the sequence numbers the page has given are below its next one
def iSeqG (v : TSys) : Bool := v.c.genOf.all fun q => decide (q.1 < v.c.page.nextSeq)
def iSeqQ (v : TSys) : Bool := v.c.toRelay.all fun q => match q.1 with
  | .connect _ => decide (q.2 < v.c.page.nextSeq)
  | _ => true

def iInv2 : List (String × (TSys → Bool)) := iInv ++ [("CL", iCL), ("KO", iKO), ("Known", iKnown), ("ConnKnown", iConnKnown), ("OpenG", iOpenG), ("GensLt", iGensLt), ("GP", iGP), ("RQ", iRQ)]

-- candidate: a discard reply in the page's queue belongs to a connection still pending its reset (or to a closing id)
def iRep (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .written id _ 1 => match (v.c.page.slots id).conn with
    | some pc => pc.discardPending
    | none => (v.c.page.slots id).closing
  | _ => true
-- candidate: a page connection that has received data has a generation the relay gave it
def iRecvG (v : TSys) : Bool := tIds.all fun id => match (v.c.page.slots id).conn with
  | some pc => !decide (0 < pc.received) || v.c.genOf.any (fun q => q.1 == pc.seq)
  | none => true
def iInv3 : List (String × (TSys → Bool)) := iInv2 ++ [("Disc", iDisc), ("SeqG", iSeqG), ("SeqQ", iSeqQ), ("Rep", iRep), ("RecvG", iRecvG)]
-- candidate: a fail frame in the page's queue finds the relay's connection of its id gone
def iFailNone (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .fail id _ => (v.c.rs.slot id).conn.isNone
  | _ => true
-- candidate: a closed frame in the page's queue finds the relay's connection of its id gone
def iClosedNone (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .closed id => (v.c.rs.slot id).conn.isNone
  | _ => true
-- candidate: after a closed frame of an id, the queue has no other frame of that id (except a closed one)
def closedOrdB : List (Relay.Out × Nat) → Bool
  | [] => true
  | q :: rest => (match q.1 with
      | .closed id => rest.all (fun r => match outIdT r.1 with
          | some j => j != id || (match r.1 with | .closed _ => true | _ => false)
          | none => true)
      | _ => true) && closedOrdB rest
def iClosedOrd (v : TSys) : Bool := closedOrdB v.c.toPage
-- candidate: an ok frame of an id in the page's queue finds no discard of that id in the relay's queue
def iOkNoDisc (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .ok id => (v.c.page.slots id).closing || v.c.toRelay.all (fun x => match x.1 with
      | .discard j => j != id
      | _ => true)
  | _ => true
-- candidate: a discard in the queue finds its id's relay connection gone, or its page connection open, or the page closing
def iDiscRel (v : TSys) : Bool := v.c.toRelay.all fun q => match q.1 with
  | .discard id => (v.c.rs.slot id).conn.isNone || (match (v.c.page.slots id).conn with
      | some pc => pc.isOpen
      | none => (v.c.page.slots id).closing)
  | _ => true
def iInv4 : List (String × (TSys → Bool)) := iInv3 ++ [("FailNone", iFailNone), ("ClosedNone", iClosedNone), ("ClosedOrd", iClosedOrd), ("OkNoDisc", iOkNoDisc), ("DiscRel", iDiscRel)]
-- candidate: a queued CLOSE means its id's page is closing
def iCloseClosing (v : TSys) : Bool := v.c.toRelay.all fun q => match q.1 with
  | .close id => (v.c.page.slots id).closing
  | _ => true
-- candidate: a CLOSED frame in the page's queue means its id's page is closing
def iClosedClosing (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .closed id => (v.c.page.slots id).closing
  | _ => true
-- candidate: a CLOSED frame in the page's queue means no CONNECT of its id is queued
def iClosedNoConn (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .closed id => v.c.toRelay.all (fun x => match x.1 with
      | .connect j => j != id
      | _ => true)
  | _ => true
def iInv5 : List (String × (TSys → Bool)) := iInv4 ++ [("CloseClosing", iCloseClosing), ("ClosedClosing", iClosedClosing), ("ClosedNoConn", iClosedNoConn)]
-- candidate: an open page connection has a relay connection that is open
def iOpenRel (v : TSys) : Bool := tIds.all fun id => match (v.c.page.slots id).conn with
  | some pc => !pc.isOpen || (match (v.c.rs.slot id).conn with
      | some c => c.isOpen
      | none => true)
  | none => true
-- candidate: an OK frame (page not closing) finds its page connection not open
def iOkOpen (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .ok id => (v.c.page.slots id).closing || (match (v.c.page.slots id).conn with
      | some pc => !pc.isOpen
      | none => true)
  | _ => true
def iInv6 : List (String × (TSys → Bool)) := iInv5 ++ [("OpenRel", iOpenRel), ("OkOpen", iOkOpen)]
-- candidate: a closing id has no page connection
def iClosingNone (v : TSys) : Bool := tIds.all fun id =>
  (v.c.page.slots id).closing == false || (v.c.page.slots id).conn.isNone
-- candidate: a CLOSED frame in the page's queue has no CLOSE of its id in the relay's queue
def iClosedNoClose (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .closed id => v.c.toRelay.all (fun x => match x.1 with
      | .close j => j != id
      | _ => true)
  | _ => true
-- candidate (strengthened): no frame of an id follows a CLOSED frame of that id in the page's queue
def closedOrdStrongB : List (Relay.Out × Nat) → Bool
  | [] => true
  | q :: rest => (match q.1 with
      | .closed id => rest.all (fun r => match outIdT r.1 with
          | some j => j != id
          | none => true)
      | _ => true) && closedOrdStrongB rest
def iClosedOrdStrong (v : TSys) : Bool := closedOrdStrongB v.c.toPage
def iInv7 : List (String × (TSys → Bool)) := iInv6 ++ [("ClosingNone", iClosingNone), ("ClosedNoClose", iClosedNoClose), ("ClosedOrdStrong", iClosedOrdStrong)]
-- candidate: no frame of an id follows a FAIL frame of that id in the page's queue
def failOrdB : List (Relay.Out × Nat) → Bool
  | [] => true
  | q :: rest => (match q.1 with
      | .fail id _ => rest.all (fun r => match outIdT r.1 with
          | some j => j != id || (match r.1 with | .closed _ => true | _ => false)
          | none => true)
      | _ => true) && failOrdB rest
def iFailOrd (v : TSys) : Bool := failOrdB v.c.toPage
def iInv8 : List (String × (TSys → Bool)) := iInv7 ++ [("FailOrd", iFailOrd)]
-- candidate: an OK frame in the page's queue finds its id's relay connection gone, or the same generation, open
def iOkRel (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .ok id => match (v.c.rs.slot id).conn with
      | some c => decide (c.gen = q.2) && c.isOpen
      | none => true
  | _ => true
def iInv9 : List (String × (TSys → Bool)) := iInv8 ++ [("OkRel", iOkRel)]
-- candidate: no two OK frames of the same id are queued in the page's queue
def okOrdB : List (Relay.Out × Nat) → Bool
  | [] => true
  | q :: rest => (match q.1 with
      | .ok id => rest.all (fun r => match r.1 with
          | .ok j => j != id
          | _ => true)
      | _ => true) && okOrdB rest
def iOkOrd (v : TSys) : Bool := okOrdB v.c.toPage
def iInv10 : List (String × (TSys → Bool)) := iInv9 ++ [("OkOrd", iOkOrd)]
-- candidate: while a CONNECT of an id waits in the relay's queue, no frame of that id is in the page's queue
def connPendB (v : TSys) : Bool := v.c.toRelay.all fun x => match x.1 with
  | .connect id => v.c.toPage.all fun q => outIdT q.1 != some id
  | _ => true
def iInv11 : List (String × (TSys → Bool)) := iInv10 ++ [("ConnPend", connPendB)]
-- candidate: a discard reply of an id is queued only when no DISCARD of that id waits in the relay's queue
def discOnceB (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .written id _ 1 => v.c.toRelay.all fun x => match x.1 with
    | .discard j => j != id
    | _ => true
  | _ => true
-- candidate: at most one discard reply of an id is queued
def discUniqB (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .written id c 1 => v.c.toPage.all fun r => match r.1 with
    | .written j c2 1 => j != id || decide (r = q)
    | _ => true
  | _ => true
def iInv12 : List (String × (TSys → Bool)) := iInv11 ++ [("DiscOnce", discOnceB)]
def iInv13 : List (String × (TSys → Bool)) := iInv12 ++ [("DiscUniq", discUniqB)]
-- candidate: a queued WRITTEN of a connection (its generation) has a count at least the page's written count
def wrMonoB (v : TSys) : Bool := v.c.toPage.all fun q => match q.1 with
  | .written id cnt _ => match (v.c.page.slots id).conn with
    | some pc => decide (!(v.c.genOf.any (fun g => g.1 == pc.seq && g.2 == q.2)) || pc.written ≤ cnt)
    | none => true
  | _ => true
-- candidate: queued WRITTENs of one id and generation are in nondecreasing order of count
def wrOrdB : List (Relay.Out × Nat) → Bool
  | [] => true
  | q :: rest => (match q.1 with
      | .written id c1 _ => rest.all (fun r => match r.1 with
          | .written j c2 _ => !(j == id && r.2 == q.2) || decide (c1 ≤ c2)
          | _ => true)
      | _ => true) && wrOrdB rest
def iInv14 : List (String × (TSys → Bool)) := iInv13 ++ [("WrMono", wrMonoB), ("WrOrd", fun v => wrOrdB v.c.toPage)]
def firstBadI (v : TSys) : Option String := (iInv14.find? (fun c => !c.2 v)).map (·.1)

def iSearch (fixed : Bool) (depth : Nat) : Option (String × List String) × Nat := Id.run do
  let init := TSys.init fixed 1 1
  let mut frontier : Array (TSys × List String) := #[(init, [])]
  let mut visited : Std.HashSet String := {}
  visited := visited.insert (tKey init)
  let mut found : Option (String × List String) := none
  match firstBadI init with
  | some n => found := some (n, [])
  | none => pure ()
  for _ in [0:depth] do
    if found.isSome then break
    let mut next : Array (TSys × List String) := #[]
    for (v, tr) in frontier do
      if found.isSome then break
      for (name, act) in tActions v do
        match act with
        | none => pure ()
        | some v' =>
          let k := tKey v'
          if !visited.contains k then
            visited := visited.insert k
            match firstBadI v' with
            | some n => if found.isNone then found := some (n, tr ++ [name])
            | none => next := next.push (v', tr ++ [name])
    frontier := next
  return (found, visited.size)
end Timed

namespace Timed
def showT (v : TSys) (id : Nat) : String :=
  let pcS := match (v.c.page.slots id).conn with
    | some pc => s!"page {id}: seq {pc.seq} open {pc.isOpen} disc {pc.discardPending} sent {pc.sent} written {pc.written}"
    | none => s!"page {id}: none closing {(v.c.page.slots id).closing}"
  let rcS := match (v.c.rs.slot id).conn with
    | some c => s!"relay {id}: gen {c.gen} open {c.isOpen} queued {c.queued} written {c.written}"
    | none => s!"relay {id}: none known {(v.c.rs.slot id).known}"
  s!"{pcS} | {rcS}"
def runWith (v : TSys) (names : List String) : List String := Id.run do
  let mut cur : Option TSys := some v
  let mut out : List String := []
  for n in names do
    match cur with
    | none => out := out ++ [s!"{n}: stopped"]; cur := none
    | some w =>
      match (tActions w).lookup n with
      | some (some w') =>
        cur := some w'
        let frames := s!"toRelay {w'.c.toRelay.map (fun q => match q.1 with | .send i k => s!"SEND{i}:{k}" | .discard i => s!"DISC{i}" | .connect i => s!"CONN{i}" | .read i _ => s!"READ{i}" | .close i => s!"CLOSE{i}" | _ => "?")} toPage {w'.c.toPage.map (fun q => match q.1 with | .written i c f => s!"W{i}:{c}/{f}" | .ok i => s!"OK{i}" | .fail i _ => s!"FAIL{i}" | .data i k => s!"DATA{i}:{k}" | .eof i => s!"EOF{i}" | .closed i => s!"CLOSED{i}" | _ => "?")}"
        out := out ++ [s!"{n}: {match firstBadI w' with | some c => "FAILS " ++ c | none => "ok"} | {frames}" ++ s!"\n    {showT w' 0}" ++ s!"\n    {showT w' 1}"]
      | _ => out := out ++ [s!"{n}: not enabled"]; cur := none
  return out
end Timed

