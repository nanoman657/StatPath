/-
Transitions.lean: the compiled transitions of core/tcp_transitions.mjs, modelled in Lean 4, with the
theorems that say when the compiled code computes the value that Bend's source means (Nat arithmetic).

The compiled code differs from Bend's Nat in two ways, and both are in the model:
  * subtraction is clamped at 0 (a < b ? 0 : a - b), which is Nat's truncated subtraction;
  * every addition is checked (nat_chk): a sum above 2^48 - 1 throws.
Bend's Nat is unbounded, so the theorems below are about the arguments that keep every sum within the limit.
The code keeps its counters at most 2^32 - 1 (MAX_COUNT) and its window and chunk sizes far below that,
so every argument is at most `bound` = 2^33, and every sum is at most 2^34 < 2^48 - 1.

The file also runs: `lean --run Transitions.lean` reads lines "name arg ..." from stdin and prints the
compiled result of each call, or THROW, which the test core/check tests compare with the JavaScript.
-/

namespace Transitions

/-- nat_chk: the largest sum the compiled code keeps. -/
def limit : Nat := 281474976710655

/-- The arguments the theorems cover: every counter the code keeps is at most 2^32 - 1, and every window or
chunk size is far below 2^33. -/
def bound : Nat := 8589934592

/-- nat_chk: a sum past the limit throws. -/
def natChk (n : Nat) : Except String Nat :=
  if n > limit then .error "nat_chk" else .ok n

/-- nat_in: an argument past 2^53 is not a host number the compiled code accepts. -/
def natIn (n : Nat) : Except String Nat :=
  if n ≤ 9007199254740992 then .ok n else .error "nat_in"

/-- The clamped subtraction of the compiled code. -/
def clampSub (a b : Nat) : Nat := if a < b then 0 else a - b

/-- The minimum of the compiled code. -/
def jsMin (a b : Nat) : Nat := if a < b then a else b

-- ---- the thirteen transitions, as the compiled code computes them ----

def pg_start (tail len : Nat) : Except String Nat := natChk (tail + len)

def pg_frame_n (sent wp win tail mx : Nat) : Nat :=
  let x0 := clampSub sent wp
  let x1 := clampSub win x0
  let x2 := clampSub tail sent
  let x3 := jsMin x1 x2
  jsMin mx x3

def pg_sent (sent n : Nat) : Except String Nat := natChk (sent + n)

def pg_take_n (taken recvd mx : Nat) : Nat := jsMin mx (clampSub recvd taken)

def pg_taken (taken n : Nat) : Except String Nat := natChk (taken + n)

def pg_recv_data (recvd k : Nat) : Except String Nat := natChk (recvd + k)

def rl_room (win q : Nat) : Nat := clampSub win q

def rl_over (n room : Nat) : Nat := if n < room then 0 else n - room

def rl_queue (q n : Nat) : Except String Nat := natChk (q + n)

def rl_written (wr m : Nat) : Except String Nat := natChk (wr + m)

def rl_unqueue (q m : Nat) : Nat := clampSub q m

def rl_read (rd k : Nat) : Except String Nat := natChk (rd + k)

def rl_grant (rd gr win n : Nat) : Except String Nat := do
  let x0 ← natChk (rd + win)
  let x1 ← natChk (gr + n)
  pure (jsMin x0 x1)

-- ---- the lemmas ----

theorem clampSub_eq (a b : Nat) : clampSub a b = a - b := by
  unfold clampSub
  split <;> omega

theorem jsMin_eq (a b : Nat) : jsMin a b = min a b := by
  unfold jsMin
  split <;> omega

theorem rl_over_eq (n room : Nat) : rl_over n room = n - room := by
  unfold rl_over
  split <;> omega

theorem natChk_ok (n : Nat) (h : n ≤ limit) : natChk n = .ok n := by
  unfold natChk
  split <;> first | rfl | (exfalso; unfold limit at *; omega)

theorem natChk_throws (n : Nat) (h : limit < n) : natChk n = .error "nat_chk" := by
  unfold natChk
  split <;> first | rfl | (exfalso; unfold limit at *; omega)

theorem natIn_ok (n : Nat) (h : n ≤ bound) : natIn n = .ok n := by
  unfold natIn
  split <;> first | rfl | (exfalso; unfold bound at *; omega)

-- the transitions that only subtract and take a minimum: always the Nat-level value
theorem pg_frame_n_eq (sent wp win tail mx : Nat) :
    pg_frame_n sent wp win tail mx = min mx (min (win - (sent - wp)) (tail - sent)) := by
  unfold pg_frame_n
  simp only [clampSub_eq, jsMin_eq]

theorem pg_take_n_eq (taken recvd mx : Nat) :
    pg_take_n taken recvd mx = min mx (recvd - taken) := by
  unfold pg_take_n
  simp only [clampSub_eq, jsMin_eq]

theorem rl_room_eq (win q : Nat) : rl_room win q = win - q := by
  unfold rl_room
  exact clampSub_eq win q

theorem rl_unqueue_eq (q m : Nat) : rl_unqueue q m = q - m := by
  unfold rl_unqueue
  exact clampSub_eq q m

-- the transitions with an addition: the compiled value is the Nat-level sum whenever the sum is within the limit
theorem pg_start_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : pg_start a b = .ok (a + b) := by
  unfold pg_start
  apply natChk_ok
  unfold limit bound at *
  omega

theorem pg_sent_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : pg_sent a b = .ok (a + b) := by
  unfold pg_sent
  apply natChk_ok
  unfold limit bound at *
  omega

theorem pg_taken_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : pg_taken a b = .ok (a + b) := by
  unfold pg_taken
  apply natChk_ok
  unfold limit bound at *
  omega

theorem pg_recv_data_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : pg_recv_data a b = .ok (a + b) := by
  unfold pg_recv_data
  apply natChk_ok
  unfold limit bound at *
  omega

theorem rl_queue_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : rl_queue a b = .ok (a + b) := by
  unfold rl_queue
  apply natChk_ok
  unfold limit bound at *
  omega

theorem rl_written_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : rl_written a b = .ok (a + b) := by
  unfold rl_written
  apply natChk_ok
  unfold limit bound at *
  omega

theorem rl_read_ok (a b : Nat) (ha : a ≤ bound) (hb : b ≤ bound) : rl_read a b = .ok (a + b) := by
  unfold rl_read
  apply natChk_ok
  unfold limit bound at *
  omega

theorem rl_grant_ok (rd gr win n : Nat) (h1 : rd ≤ bound) (h2 : gr ≤ bound) (h3 : win ≤ bound) (h4 : n ≤ bound) :
    rl_grant rd gr win n = .ok (min (rd + win) (gr + n)) := by
  unfold rl_grant
  have e1 : natChk (rd + win) = .ok (rd + win) := natChk_ok _ (by unfold limit bound at *; omega)
  have e2 : natChk (gr + n) = .ok (gr + n) := natChk_ok _ (by unfold limit bound at *; omega)
  rw [e1, e2]
  show Except.ok (jsMin (rd + win) (gr + n)) = _
  rw [jsMin_eq]

-- and the arguments that the code's own checks let through are within the bound (natIn accepts them)
theorem rl_over_is_zero_iff (n room : Nat) : rl_over n room = 0 ↔ n ≤ room := by
  unfold rl_over
  split <;> omega

-- ---- the executable model: lean --run reads "name arg ..." and prints the compiled result ----

def dispatch (name : String) (xs : List Nat) : Except String Nat :=
  match name, xs with
  | "pg_start", [a, b] => pg_start a b
  | "pg_frame_n", [a, b, c, d, e] => .ok (pg_frame_n a b c d e)
  | "pg_sent", [a, b] => pg_sent a b
  | "pg_take_n", [a, b, c] => .ok (pg_take_n a b c)
  | "pg_taken", [a, b] => pg_taken a b
  | "pg_recv_data", [a, b] => pg_recv_data a b
  | "rl_room", [a, b] => .ok (rl_room a b)
  | "rl_over", [a, b] => .ok (rl_over a b)
  | "rl_queue", [a, b] => rl_queue a b
  | "rl_written", [a, b] => rl_written a b
  | "rl_unqueue", [a, b] => .ok (rl_unqueue a b)
  | "rl_read", [a, b] => rl_read a b
  | "rl_grant", [a, b, c, d] => rl_grant a b c d
  | _, _ => .error "unknown"

def parseLine (s : String) : Option (String × List Nat) :=
  match s.trimAscii.toString.splitOn " " with
  | [] => none
  | name :: args => do
    let ns ← args.mapM String.toNat?
    pure (name, ns)

partial def loop' (h : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  match parseLine line with
  | none => IO.println "BAD"
  | some (name, args) =>
    let r : Except String Nat := do
      let ns ← args.mapM natIn
      dispatch name ns
    match r with
    | .ok v => IO.println (toString v)
    | .error _ => IO.println "THROW"
  loop' h

end Transitions

def main : IO Unit := do
  Transitions.loop' (← IO.getStdin)
