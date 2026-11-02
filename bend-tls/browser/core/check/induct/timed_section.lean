-- ================================================================================================
-- The timed composition: the page, the relay's connection machine with the clock (Clock.stepK, Clock.tickK), and
-- the frames between them. The untimed composition (Client.Sys) gives the relay an empty queue, so the window can
-- never be reached there; here the budget can hold bytes back, and they wait in the queue.
-- ================================================================================================
namespace Timed

structure TSys where
  c : Client.Sys
  clk : Clock.Clk

def TSys.init (fixed : Bool) (cps bps : Nat) : TSys := ⟨Client.initSys fixed, Clock.init cps bps⟩

def lift (v : TSys) (f : Client.Sys → Option Client.Sys) : Option TSys :=
  (f v.c).map (fun c' => ⟨c', v.clk⟩)

def tPageCall (v : TSys) (i : Page.In) : Option TSys := lift v (fun c => Client.pageCall c i)

def tDoPage (v : TSys) : Option TSys := lift v Client.doPage

-- the id a frame of the relay belongs to (closed has none: the page ignores it)
def outIdT : Relay.Out → Option Nat
  | .ok id => some id
  | .data id _ => some id
  | .eof id => some id
  | .written id _ _ => some id
  | .fail id _ => some id
  | .closed id => some id
  | .wsclose _ => none

-- the relay takes the oldest frame of the page, with the clock
def tDoRelay (v : TSys) : Option TSys :=
  match v.c.toRelay with
  | [] => none
  | (e, p) :: rest =>
    let t := Client.tagOf v.c.rs e
    let r := Clock.stepK Relay.DEFAULT_CAP v.clk v.c.rs e
    let genOf' := match e with
      | .connect _ => if p > 0 then (p, v.c.rs.nextGen) :: v.c.genOf else v.c.genOf
      | _ => v.c.genOf
    let closedByPage := r.2.2.any (fun o => match o with | .wsclose _ => true | _ => false)
    let sockSt' := match e with
      | .connect id => if r.2.1.nextGen > v.c.rs.nextGen then (v.c.rs.nextGen, id, 0) :: v.c.sockSt else v.c.sockSt
      | _ => v.c.sockSt
    let c' : Client.Sys :=
      { v.c with
        rs := r.2.1
        toRelay := rest
        toPage := v.c.toPage ++ r.2.2.map (fun o => (o, t))
        genOf := genOf'
        proto := v.c.proto || closedByPage
        sockSt := sockSt' }
    some ⟨c', r.1⟩

-- a socket event of the relay, as the environment may make it (Client.envAllowed), with the clock
def tDoEnv (v : TSys) (e : Relay.Ev) : Option TSys :=
  match e with
  | .sock id g k =>
    if !Client.envAllowed v.c id g k then none else
    let t := Client.tagOf v.c.rs e
    let r := Clock.stepK Relay.DEFAULT_CAP v.clk v.c.rs e
    let st' := match k with
      | .open_ => v.c.sockSt.map (fun q => if q.1 == g then (q.1, q.2.1, 1) else q)
      | .error _ => v.c.sockSt.map (fun q => if q.1 == g && q.2.2 == 0 then (q.1, q.2.1, 2) else q)
      | _ => v.c.sockSt
    let c' : Client.Sys :=
      { v.c with
        rs := r.2.1
        toPage := v.c.toPage ++ r.2.2.map (fun o => (o, t))
        sockSt := st' }
    some ⟨c', r.1⟩
  | _ => none

-- the time goes on: the tokens and the budget refill, and the queues are flushed; each frame is tagged with the
-- generation of its connection
def tTick (v : TSys) (ms : Nat) : TSys :=
  let r := Clock.tickK v.clk v.c.rs ms
  let tag : Relay.Out → Nat := fun o => match outIdT o with
    | some id => ((v.c.rs.slot id).conn.map (fun c => c.gen)).getD 0
    | none => 0
  let c' : Client.Sys := { v.c with rs := r.2.1, toPage := v.c.toPage ++ r.2.2.map (fun o => (o, tag o)) }
  ⟨c', r.1⟩

def tActions (v : TSys) : List (String × Option TSys) :=
  [("connect", tPageCall v .connect), ("close 0", tPageCall v (.close 0)), ("close 1", tPageCall v (.close 1)),
   ("send 0 1", tPageCall v (.send 0 1)), ("send 1 1", tPageCall v (.send 1 1)),
   ("send 0 2", tPageCall v (.send 0 2)), ("send 0 65535", tPageCall v (.send 0 65535)), ("send 0 131073", tPageCall v (.send 0 131073)),
   ("recv 0 1", tPageCall v (.recv 0 1)), ("discard 0", tPageCall v (.discard 0)),
   ("relay", tDoRelay v), ("page", tDoPage v), ("tick 1000", some (tTick v 1000))] ++
  ((List.range 2).flatMap (fun id =>
    (List.range 2).flatMap (fun g =>
      [ (s!"sock {id} {g+1} open", tDoEnv v (Relay.Ev.sock id (g+1) Relay.Sk.open_)),
        (s!"sock {id} {g+1} data 1", tDoEnv v (Relay.Ev.sock id (g+1) (Relay.Sk.data 1))),
        (s!"sock {id} {g+1} eof", tDoEnv v (Relay.Ev.sock id (g+1) Relay.Sk.eof)),
        (s!"sock {id} {g+1} drain 1", tDoEnv v (Relay.Ev.sock id (g+1) (Relay.Sk.drain 1))),
        (s!"sock {id} {g+1} drain 2", tDoEnv v (Relay.Ev.sock id (g+1) (Relay.Sk.drain 2))) ]))).map id

def tKey (v : TSys) : String :=
  Client.keyOf v.c ++ s!"|clk {v.clk.now} {v.clk.refilled} {v.clk.tokens} {v.clk.bud} {v.clk.used} {v.clk.acc}" ++
    s!"{(List.range 3).map (fun i => v.clk.chunks i)}"

-- ---- the candidate invariant, as checks (ids 0..2 for the search) ----
def qsumT (id : Nat) : List (Relay.Ev × Nat) → Nat
  | [] => 0
  | (e, _) :: rest => (match e with
      | .send i n => if i = id then n else 0
      | _ => 0) + qsumT id rest

def tIds : List Nat := List.range 3

def cWQ (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.rs.slot id).conn with
  | some c => decide (c.queued + qsumT id v.c.toRelay ≤ Relay.SEND_WINDOW)
  | none => true

def cP1 (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn, (v.c.rs.slot id).conn with
  | some pc, some c =>
    !pc.isOpen || (decide (c.written + c.queued + qsumT id v.c.toRelay ≤ pc.sent)
      && decide (pc.written ≤ c.written) && v.c.genOf.any (fun q => q.1 == pc.seq && q.2 == c.gen))
  | _, _ => true

def cPI (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn with
  | some pc => decide (pc.written ≤ pc.sent ∧ pc.sent ≤ pc.tail ∧ pc.sent ≤ pc.written + Relay.SEND_WINDOW)
  | none => true

def cTP1 (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .written id cnt _ => match (v.c.rs.slot id).conn with
    | some c => !(c.gen == q.2) || decide (cnt ≤ c.written)
    | none => true
  | _ => true

-- the clock's queues are the relay's (Clock.MirrorAt), and the tokens and the budget keep their bounds (Clock.Good)
def cMirror (v : TSys) : Bool := tIds.all fun id =>
  let chunks := v.clk.chunks id
  (match (v.c.rs.slot id).conn with
    | none => chunks.isEmpty
    | some c => decide (chunks.sum = c.queued)) && chunks.all (fun x => decide (0 < x))

def cGood (v : TSys) : Bool :=
  decide (0 ≤ v.clk.tokens) && decide (v.clk.refilled ≤ v.clk.now) &&
  decide (v.clk.tokens + 1000 * (v.clk.acc : Int) ≤ 2000 * (v.clk.cps : Int) + (v.clk.cps : Int) * (v.clk.refilled : Int)) &&
  decide (v.clk.bud + 1000 * (v.clk.used : Int) ≤ 1000 * (v.clk.bps : Int) + (v.clk.bps : Int) * (v.clk.refilled : Int))

-- a witness, not an invariant: it fails in a state where some relay queue holds bytes (so the search does reach
-- the queued case when this check is the one reported)
def cWitness (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.rs.slot id).conn with
  | some c => decide (c.queued = 0)
  | none => true

-- ORD: no SEND for an id sits behind a CONNECT for that id in the queue (frames are queued in the order framed)
def ordOK : List (Relay.Ev × Nat) → List Nat → Bool
  | [], _ => true
  | (e, _) :: rest, seen => match e with
    | .connect id => ordOK rest (id :: seen)
    | .send id _ => !(seen.contains id) && ordOK rest seen
    | _ => ordOK rest seen

def cORD (v : TSys) : Bool := ordOK v.c.toRelay []

-- DP: a WRITTEN frame that answers a DISCARD (flag 1), for the connection that is there now, finds the relay's queue
-- and the in-flight bytes of the id empty, and its count is the relay's count
def cDP (v : TSys) : Bool := v.c.toPage.all fun q =>
  match q.1 with
  | .written id cnt 1 => match (v.c.rs.slot id).conn with
    | some c => !(c.gen == q.2) || (decide (c.queued = 0) && decide (qsumT id v.c.toRelay = 0) && decide (cnt = c.written))
    | none => true
  | _ => true

-- P0: a page connection that is not open yet, whose CONNECT the relay has taken, has no counts on either side
def cP0 (v : TSys) : Bool := tIds.all fun id =>
  match (v.c.page.slots id).conn with
  | some pc => if pc.isOpen then true else
    match (v.c.rs.slot id).conn with
    | some c => !(v.c.genOf.any (fun q => q.1 == pc.seq && q.2 == c.gen)) ||
        (decide (c.written = 0) && decide (c.queued = 0) && decide (qsumT id v.c.toRelay = 0) &&
         decide (pc.sent = 0) && decide (pc.written = 0))
    | none => true
  | none => true

def checks : List (String × (TSys → Bool)) :=
  [("WQ", cWQ), ("P1", cP1), ("PI", cPI), ("TP1", cTP1), ("Mirror", cMirror), ("Good", cGood),
   ("ORD", cORD), ("DP", cDP), ("P0", cP0)]

def witnessChecks : List (String × (TSys → Bool)) := [("Witness", cWitness)]

def firstBadT (v : TSys) : Option String := (checks.find? (fun c => !c.2 v)).map (·.1)

def tSearch (fixed : Bool) (depth : Nat) : Option (String × List String) × Nat := Id.run do
  let init := TSys.init fixed 1 1
  let mut frontier : Array (TSys × List String) := #[(init, [])]
  let mut visited : Std.HashSet String := {}
  visited := visited.insert (tKey init)
  let mut found : Option (String × List String) := none
  match firstBadT init with
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
            match firstBadT v' with
            | some n => if found.isNone then found := some (n, tr ++ [name])
            | none => next := next.push (v', tr ++ [name])
    frontier := next
  return (found, visited.size)

end Timed

namespace Timed
-- run named actions from the start, and report the first failing check after each step
def runNamed (v : TSys) (names : List String) : List String := Id.run do
  let mut cur : Option TSys := some v
  let mut out : List String := []
  for n in names do
    match cur with
    | none => out := out ++ [s!"{n}: no such step"]; cur := none
    | some w =>
      match (tActions w).lookup n with
      | some (some w') =>
        cur := some w'
        let pcS := match (w'.c.page.slots 0).conn with
          | some pc => s!"page sent {pc.sent} written {pc.written} tail {pc.tail} open {pc.isOpen} disc {pc.discardPending}"
          | none => "page none"
        let rcS := match (w'.c.rs.slot 0).conn with
          | some c => s!"relay written {c.written} queued {c.queued}"
          | none => "relay none"
        out := out ++ [s!"{n}: {match firstBadT w' with | some c => "FAILS " ++ c | none => "ok"}{if w'.c.proto then " PROTO-CLOSED" else ""} | toRelay {w'.c.toRelay.map (fun q => match q.1 with | .send _ k => s!"SEND{k}" | .discard _ => "DISC" | .connect _ => "CONN" | .read _ _ => "READ" | .close _ => "CLOSE" | _ => "?")} toPage {w'.c.toPage.map (fun q => match q.1 with | .written _ c f => s!"W{c}/{f}" | .ok _ => "OK" | .fail _ _ => "FAIL" | .closed _ => "CLOSED" | _ => "?")} | {pcS} | {rcS}"]
      | _ => out := out ++ [s!"{n}: not enabled"]; cur := none
  return out
end Timed

def main (args : List String) : IO UInt32 := do
  if args.head? == some "trace" then
    let steps := ["connect", "relay", "sock 0 1 open", "page", "send 0 2", "discard 0", "discard 0", "relay",
                  "relay", "relay", "page", "page", "send 0 1", "discard 0", "relay", "page",
                  "relay", "tick 1000", "tick 1000", "relay", "page", "send 0 131073", "relay", "relay", "relay"]
    for line in Timed.runNamed (Timed.TSys.init true 1 1) steps do IO.println line
    return 0
  let depth := (args.head? >>= String.toNat?).getD 6
  let fixed := args.getD 1 "fixed" != "old"
  let (res, n) := Timed.tSearch fixed depth
  IO.println s!"states {n} fixed {fixed} depth {depth}"
  match res with
  | some (name, tr) =>
    IO.println s!"VIOLATED {name} after {tr.length} steps: {tr}"
    return 1
  | none =>
    IO.println "no violation"
    return 0
