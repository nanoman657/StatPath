/-
Transparency.lean: the relay forwards every byte unchanged and in order, in both directions (relay/relay.ts,
tcp_relay_client.js). The relay's only uses of a byte are to split a stream into pieces, to queue pieces, and to
write a prefix of the queue, and to concatenate. These theorems say those operations never change a byte, drop one,
or reorder them. So whatever the page sends in the clear, the relay sees, and whatever the destination sends, the
relay sees. Nothing here is secrecy: a page that encrypts its bytes first gives the relay ciphertext, and the theorems
say only that the relay passes it on unchanged. The bytes are abstract (any type); no sorry, no axioms beyond Lean's.
-/

namespace Transparency

variable {α : Type}

-- DATA: relay.ts sends a socket chunk as frames of at most k bytes:
--   for (let at = 0; at < chunk.length; at += MAX_BODY) sendFrame(DATA, chunk.subarray(at, min(len, at + MAX_BODY)))
-- framesN is that loop, with fuel n (the length of the chunk is always enough).
def framesN (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, x :: xs => (x :: xs).take k :: framesN k n ((x :: xs).drop k)

def frames (k : Nat) (l : List α) : List (List α) := framesN k l.length l

theorem framesN_flatten (k : Nat) (hk : 0 < k) : ∀ (n : Nat) (l : List α), l.length ≤ n →
    (framesN k n l).flatten = l := by
  intro n
  induction n with
  | zero => intro l hl; cases l with
    | nil => rfl
    | cons x xs => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => rfl
    | cons x xs =>
      simp only [framesN, List.flatten_cons]
      have hd : ((x :: xs).drop k).length ≤ n := by
        simp only [List.length_drop, List.length_cons] at hl ⊢; omega
      rw [ih _ hd, List.take_append_drop]

theorem frames_flatten (k : Nat) (hk : 0 < k) (l : List α) : (frames k l).flatten = l :=
  framesN_flatten k hk l.length l (Nat.le_refl _)

-- every piece is non-empty and at most k bytes, when k > 0: each DATA frame carries bytes, within MAX_BODY
theorem framesN_piece (k : Nat) (hk : 0 < k) : ∀ (n : Nat) (l : List α), ∀ f ∈ framesN k n l,
    0 < f.length ∧ f.length ≤ k := by
  intro n
  induction n with
  | zero => intro l f hf; simp [framesN] at hf
  | succ n ih =>
    intro l f hf
    cases l with
    | nil => simp [framesN] at hf
    | cons x xs =>
      simp only [framesN, List.mem_cons] at hf
      rcases hf with rfl | hf
      · simp only [List.length_take, List.length_cons]; omega
      · exact ih _ f hf

-- the page's SEND pieces: its pump sends a piece of n bytes from where the last one ended (tcp_relay_client.js:
-- encodeFrame(SEND, id, bytes.subarray(off, off + n)))
def sendPieces : List α → List Nat → List (List α)
  | _, [] => []
  | l, n :: ns => l.take n :: sendPieces (l.drop n) ns

theorem sendPieces_flatten : ∀ (ns : List Nat) (l : List α),
    (sendPieces l ns).flatten = l.take ns.sum := by
  intro ns
  induction ns with
  | nil => intro l; simp [sendPieces]
  | cons n ns ih =>
    intro l
    simp only [sendPieces, List.flatten_cons, ih, List.sum_cons]
    rw [List.take_add]

-- the DATA path: the page receives the socket's bytes, every chunk in order, and nothing else
theorem data_path (k : Nat) (hk : 0 < k) (cs : List (List α)) :
    ((cs.map (frames k)).flatten).flatten = cs.flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatten_append, frames_flatten k hk, ih]

-- the relay's queue for one connection, as bytes: wr is what the socket has taken, q is what waits in the queue,
-- acc is every byte the page has sent (the SEND bodies accepted, in order)
structure Queue (α : Type) where
  wr : List α
  q : List α
  acc : List α

def Queue.init : Queue α := ⟨[], [], []⟩

-- a SEND body is accepted (relay.ts: conn.queue.push(body), then flush)
def Queue.accept (s : Queue α) (b : List α) : Queue α :=
  { s with q := s.q ++ b, acc := s.acc ++ b }

-- the socket takes k bytes of the queue, in order (flush: the head chunk, as far as the socket accepts)
def Queue.write (s : Queue α) (k : Nat) : Queue α :=
  { s with wr := s.wr ++ s.q.take k, q := s.q.drop k }

-- the queue never changes a byte: what the socket has taken and what waits is exactly what the page sent
def Queue.Inv (s : Queue α) : Prop := s.wr ++ s.q = s.acc

theorem queue_inv_init : (Queue.init : Queue α).Inv := by
  simp [Queue.Inv, Queue.init]

theorem queue_inv_accept (s : Queue α) (b : List α) (h : s.Inv) : (s.accept b).Inv := by
  unfold Queue.Inv at *
  simp only [Queue.accept, ← h, List.append_assoc]

theorem queue_inv_write (s : Queue α) (k : Nat) (h : s.Inv) : (s.write k).Inv := by
  unfold Queue.Inv at *
  simp only [Queue.write]
  rw [← h, List.append_assoc, List.take_append_drop]

-- any sequence of accepts and writes keeps the invariant
inductive Op (α : Type) where
  | accept (b : List α)
  | write (k : Nat)

def Queue.run (s : Queue α) : List (Op α) → Queue α
  | [] => s
  | Op.accept b :: ops => Queue.run (s.accept b) ops
  | Op.write k :: ops => Queue.run (s.write k) ops

theorem queue_run_inv (ops : List (Op α)) : ∀ (s : Queue α), s.Inv → (s.run ops).Inv := by
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih =>
    intro s h
    cases op with
    | accept b => exact ih _ (queue_inv_accept s b h)
    | write k => exact ih _ (queue_inv_write s k h)

-- folding the accepts: the queue takes the pieces in order, and the socket's side is unchanged
theorem fold_accept (bs : List (List α)) : ∀ (s : Queue α),
    (bs.foldl (fun s b => s.accept b) s).wr = s.wr ∧
    (bs.foldl (fun s b => s.accept b) s).q = s.q ++ bs.flatten ∧
    (bs.foldl (fun s b => s.accept b) s).acc = s.acc ++ bs.flatten := by
  induction bs with
  | nil => intro s; simp
  | cons b bs ih =>
    intro s
    obtain ⟨h1, h2, h3⟩ := ih (s.accept b)
    simp only [List.foldl_cons, List.flatten_cons]
    refine ⟨by rw [h1]; simp [Queue.accept], ?_, ?_⟩
    · rw [h2]; simp [Queue.accept, List.append_assoc]
    · rw [h3]; simp [Queue.accept, List.append_assoc]

-- folding the writes keeps the invariant
theorem fold_write (ks : List Nat) : ∀ (s : Queue α), s.Inv →
    (ks.foldl (fun s k => s.write k) s).Inv := by
  induction ks with
  | nil => intro s h; exact h
  | cons k ks ih =>
    intro s h
    exact ih _ (queue_inv_write s k h)

-- a write never changes what the page has sent
theorem write_acc (s : Queue α) (k : Nat) : (s.write k).acc = s.acc := rfl

theorem fold_write_acc (ks : List Nat) : ∀ (s : Queue α),
    (ks.foldl (fun s k => s.write k) s).acc = s.acc := by
  induction ks with
  | nil => intro s; rfl
  | cons k ks ih => intro s; simp only [List.foldl_cons]; rw [ih, write_acc]

-- one run of the relay on the page's send: the page's pieces are accepted in order, then the socket takes bytes
-- in the schedule ks
def sendRun (D : List α) (ns ks : List Nat) : Queue α :=
  ks.foldl (fun s k => s.write k) ((sendPieces D ns).foldl (fun s b => s.accept b) Queue.init)

-- END TO END. The page sends the stream D in SEND pieces of the sizes ns. The relay queues them, and the socket takes
-- bytes in any schedule ks. What the socket has taken, with what is still queued, is the page's stream as far as it
-- was sent: nothing is changed, dropped or reordered, and the socket's bytes are a prefix of the page's stream.
theorem relay_send_transparent (D : List α) (ns ks : List Nat) :
    (sendRun D ns ks).wr ++ (sendRun D ns ks).q = D.take ns.sum ∧
      List.IsPrefix (sendRun D ns ks).wr D := by
  obtain ⟨h1, h2, h3⟩ := fold_accept (sendPieces D ns) (Queue.init : Queue α)
  have hwr : ((sendPieces D ns).foldl (fun s b => s.accept b) (Queue.init : Queue α)).wr = [] := by
    rw [h1]; rfl
  have hq : ((sendPieces D ns).foldl (fun s b => s.accept b) (Queue.init : Queue α)).q = D.take ns.sum := by
    rw [h2, sendPieces_flatten]; rfl
  have hacc : ((sendPieces D ns).foldl (fun s b => s.accept b) (Queue.init : Queue α)).acc = D.take ns.sum := by
    rw [h3, sendPieces_flatten]; rfl
  have hI : ((sendPieces D ns).foldl (fun s b => s.accept b) (Queue.init : Queue α)).Inv := by
    unfold Queue.Inv; rw [hwr, hq, hacc]; rfl
  have hT := fold_write ks _ hI
  have hA := fold_write_acc ks ((sendPieces D ns).foldl (fun s b => s.accept b) (Queue.init : Queue α))
  have hEq : (sendRun D ns ks).wr ++ (sendRun D ns ks).q = D.take ns.sum := by
    unfold sendRun at hT ⊢
    unfold Queue.Inv at hT
    rw [hT, hA, hacc]
  refine ⟨hEq, ?_⟩
  have hp : (sendRun D ns ks).wr <+: (sendRun D ns ks).wr ++ (sendRun D ns ks).q :=
    List.prefix_append _ _
  rw [hEq] at hp
  exact hp.trans (List.take_prefix _ _)


-- ---- the operation codes ----
-- PROTOCOL.md's table, as data. This is a closed-world statement about this table; transparency.test.ts checks that
-- the table is the one PROTOCOL.md prints, and that relay/relay.ts and tcp_relay_client.js use the same codes, so
-- LISTEN and ACCEPT are not in the protocol or in either side's code.
namespace Wire

def codes : List (Nat × String) :=
  [(15, "AUTH"), (16, "AUTHOK"), (1, "CONNECT"), (2, "SEND"), (3, "CLOSE"), (4, "DISCARD"), (5, "READ"),
   (10, "OK"), (11, "FAIL"), (12, "DATA"), (13, "EOF"), (14, "WRITTEN"), (17, "CLOSED")]

theorem codes_nodup : (codes.map Prod.fst).Nodup := by decide

theorem codes_fit_a_byte : ∀ c ∈ codes.map Prod.fst, c < 256 := by decide

theorem no_listen_or_accept : ∀ p ∈ codes, p.2 ≠ "LISTEN" ∧ p.2 ≠ "ACCEPT" := by decide

theorem codes_6_to_9_unused : ∀ c ∈ [0, 6, 7, 8, 9], c ∉ codes.map Prod.fst := by decide

end Wire

end Transparency
