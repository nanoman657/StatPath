# tcp_contract_proof.bend: the arithmetic and the invariants that the browser TCP effects (effs/web_tcp.js)
# rely on, checked by Bend's kernel. Run:  bend tcp_contract_proof.bend   (ALL PROOFS CHECK)
#
# The model, with the JavaScript it stands for:
#   - a send of data (length len) begins at a connection count `start`; the relay reports `written`, the
#     count of bytes it took. The offset k = written - start is web_tcp.js's `from(written)`, and the
#     bytes not sent are drop(data, k). Nat.sub truncates at 0, like Math.max(0, ...).
#   - the page's window: `inflight` is sent minus the count last seen, and `slack` is WIN - inflight.
#   - the relay's read credit: `granted` is the relay's view of what the page granted, `read` is the
#     bytes read from the socket, and `buffered` is what the page holds.
# Where the JavaScript compares two numbers, the model writes the difference as a witness: a + d == b
# says a <= b, and d is the slack. No statement depends on an impossible case.
import Base
import ./frame_arith.bend as N

# ---- Nat facts ----

def sub_zero(+k: Nat) -> {Nat.sub(k, 0n) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (s + k) - s == k: the offset of a count that is s past the start
def sub_add(+s: Nat, +k: Nat) -> {Nat.sub(Nat.add(s, k), s) == k : Nat}:
  match s:
    case 0n:
      sub_zero(k)
    case 1n+q:
      sub_add(q, k)

# a - (a + e) == 0: a count that is past the end of the send has nothing left to send
def sub_addend(+a: Nat, +e: Nat) -> {Nat.sub(a, Nat.add(a, e)) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      sub_addend(p, e)

def sub_self(+a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

# ---- lists ----

# the bytes the relay took, then the bytes not taken, are the whole send
def take_drop(+xs: List<&2, Nat>, +k: Nat) -> {List.append(&2, Nat, List.take(&2, Nat, xs, k), List.drop(&2, Nat, xs, k)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match k:
        case 0n:
          {==}
        case 1n+p:
          %take_drop(t, p) : {x <> List.append(&2, Nat, List.take(&2, Nat, t, p), List.drop(&2, Nat, t, p)) == x <> _ : List<&2, Nat>}
          {==}

# the bytes not taken are as many as the send has, less the count taken
def drop_len(+xs: List<&2, Nat>, +k: Nat) -> {List.length(&2, Nat, List.drop(&2, Nat, xs, k)) == Nat.sub(List.length(&2, Nat, xs), k) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match k:
        case 0n:
          {==}
        case 1n+p:
          drop_len(t, p)

# ---- equality helpers ----

def pred(+n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def pred_congr(+x: Nat, +y: Nat, +h: {x == y : Nat}) -> {pred(x) == pred(y) : Nat}:
  %h : {pred(x) == pred(_) : Nat}
  {==}

def cong_add_l(+a: Nat, +b: Nat, +c: Nat, +h: {b == c : Nat}) -> {Nat.add(a, b) == Nat.add(a, c) : Nat}:
  %h : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

def cong_add_r(+x: Nat, +y: Nat, +z: Nat, +h: {y == z : Nat}) -> {Nat.add(y, x) == Nat.add(z, x) : Nat}:
  %h : {Nat.add(y, x) == Nat.add(_, x) : Nat}
  {==}

# a + x == a + y gives x == y
def add_cancel_l(+a: Nat, +x: Nat, +y: Nat, +h: {Nat.add(a, x) == Nat.add(a, y) : Nat}) -> {x == y : Nat}:
  match a:
    case 0n:
      h
    case 1n+p:
      add_cancel_l(p, x, y, pred_congr(Nat.add(1n+p, x), Nat.add(1n+p, y), h))

# a + (b + c) == b + (a + c)
def add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), N.add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      cong_add_r(c, Nat.add(a, b), Nat.add(b, a), N.add_comm(a, b)),
      N.add_assoc(b, a, c)))

# ---- the offset of a count ----

# the count the relay reports is start + k, and its offset in the send is k (from(count) in web_tcp.js)
def off(+s: Nat, +k: Nat) -> {k == Nat.sub(Nat.add(s, k), s) : Nat}:
  Equal.sym(Nat, Nat.sub(Nat.add(s, k), s), k, sub_add(s, k))

# ---- a send split at the relay's count ----

# the bytes the relay took, then the bytes not taken, are the whole send (no byte lost or repeated)
def resume_stream(+data: List<&2, Nat>, +start: Nat, +k: Nat) ->
  {List.append(&2, Nat, List.take(&2, Nat, data, Nat.sub(Nat.add(start, k), start)),
    List.drop(&2, Nat, data, Nat.sub(Nat.add(start, k), start))) == data : List<&2, Nat>}:
  %off(start, k) : {List.append(&2, Nat, List.take(&2, Nat, data, _), List.drop(&2, Nat, data, _)) == data : List<&2, Nat>}
  take_drop(data, k)

# the length of the bytes to resend is j, when the relay took k of a send and k + j is its length
def resume_sub(+data: List<&2, Nat>, +start: Nat, +k: Nat, +j: Nat, +h: {Nat.add(k, j) == List.length(&2, Nat, data) : Nat}) ->
  {Nat.sub(List.length(&2, Nat, data), Nat.sub(Nat.add(start, k), start)) == j : Nat}:
  %off(start, k) : {Nat.sub(List.length(&2, Nat, data), _) == j : Nat}
  %h : {Nat.sub(_, k) == j : Nat}
  sub_add(k, j)

def resume_len(+data: List<&2, Nat>, +start: Nat, +k: Nat, +j: Nat, +h: {Nat.add(k, j) == List.length(&2, Nat, data) : Nat}) ->
  {List.length(&2, Nat, List.drop(&2, Nat, data, Nat.sub(Nat.add(start, k), start))) == j : Nat}:
  Equal.trans(Nat, List.length(&2, Nat, List.drop(&2, Nat, data, Nat.sub(Nat.add(start, k), start))),
    Nat.sub(List.length(&2, Nat, data), Nat.sub(Nat.add(start, k), start)), j,
    drop_len(data, Nat.sub(Nat.add(start, k), start)),
    resume_sub(data, start, k, j, h))

# the stream position after the resend is the position at which the send ends: the count the
# relay reached, plus the bytes still to send, is where the send ends
def resume_pos(+data: List<&2, Nat>, +start: Nat, +k: Nat, +j: Nat, +h: {Nat.add(k, j) == List.length(&2, Nat, data) : Nat}) ->
  {Nat.add(Nat.add(start, k), List.length(&2, Nat, List.drop(&2, Nat, data, Nat.sub(Nat.add(start, k), start))))
    == Nat.add(start, List.length(&2, Nat, data)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(start, k), List.length(&2, Nat, List.drop(&2, Nat, data, Nat.sub(Nat.add(start, k), start)))),
    Nat.add(Nat.add(start, k), j), Nat.add(start, List.length(&2, Nat, data)),
    cong_add_l(Nat.add(start, k), List.length(&2, Nat, List.drop(&2, Nat, data, Nat.sub(Nat.add(start, k), start))), j,
      resume_len(data, start, k, j, h)),
    Equal.trans(Nat, Nat.add(Nat.add(start, k), j), Nat.add(start, Nat.add(k, j)), Nat.add(start, List.length(&2, Nat, data)),
      N.add_assoc(start, k, j),
      cong_add_l(start, Nat.add(k, j), List.length(&2, Nat, data), h)))

# ---- a send the relay has taken past its end ----

# taking the whole list from any count past its length takes all of it
def take_all(+xs: List<&2, Nat>, +e: Nat) -> {List.take(&2, Nat, xs, Nat.add(List.length(&2, Nat, xs), e)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %take_all(t, e) : {x <> List.take(&2, Nat, t, Nat.add(List.length(&2, Nat, t), e)) == x <> _ : List<&2, Nat>}
      {==}

# when the relay's count is past the end of the send (k == length + e), the send is complete: all of
# the data was taken, and none is left to send
def ready_taken(+data: List<&2, Nat>, +k: Nat, +e: Nat, +h: {Nat.add(List.length(&2, Nat, data), e) == k : Nat}) ->
  {List.take(&2, Nat, data, k) == data : List<&2, Nat>}:
  %h : {List.take(&2, Nat, data, _) == data : List<&2, Nat>}
  take_all(data, e)

def ready_rest(+data: List<&2, Nat>, +k: Nat, +e: Nat, +h: {Nat.add(List.length(&2, Nat, data), e) == k : Nat}) ->
  {List.length(&2, Nat, List.drop(&2, Nat, data, k)) == 0n : Nat}:
  %h : {List.length(&2, Nat, List.drop(&2, Nat, data, _)) == 0n : Nat}
  Equal.trans(Nat, List.length(&2, Nat, List.drop(&2, Nat, data, Nat.add(List.length(&2, Nat, data), e))),
    Nat.sub(List.length(&2, Nat, data), Nat.add(List.length(&2, Nat, data), e)), 0n,
    drop_len(data, Nat.add(List.length(&2, Nat, data), e)),
    sub_addend(List.length(&2, Nat, data), e))

# ---- sums in any order ----

# (a + b) + c == (a + c) + b
def add_end(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b),
    N.add_assoc(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b),
      cong_add_l(a, Nat.add(b, c), Nat.add(c, b), N.add_comm(b, c)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), N.add_assoc(a, c, b))))

# (a + b) + (c + d) == (a + c) + (b + d)
def interchange(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
    N.add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
      cong_add_l(a, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), N.add_assoc(a, c, Nat.add(b, d)))))

# ---- the send window ----

# The page has I bytes sent and not yet seen taken, and slack s, with I + s == WIN. It sends n bytes
# when n + r == s (n is at most the slack). After the send, the in-flight bytes I + n still fit: the
# slack left is r.
def pump_keeps(+I: Nat, +s: Nat, +n: Nat, +r: Nat, +WIN: Nat,
  h1: {Nat.add(I, s) == WIN : Nat}, h2: {Nat.add(n, r) == s : Nat}) -> {Nat.add(Nat.add(I, n), r) == WIN : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(I, n), r), Nat.add(I, Nat.add(n, r)), WIN,
    N.add_assoc(I, n, r),
    Equal.trans(Nat, Nat.add(I, Nat.add(n, r)), Nat.add(I, s), WIN,
      cong_add_l(I, Nat.add(n, r), s, h2),
      h1))

# The relay reports d more bytes taken, so the in-flight bytes fall to I2 (d + I2 == I), and the slack
# rises by d. The window invariant holds.
def written_keeps(+I: Nat, +s: Nat, +d: Nat, +I2: Nat, +WIN: Nat,
  h1: {Nat.add(I, s) == WIN : Nat}, h2: {Nat.add(d, I2) == I : Nat}) -> {Nat.add(I2, Nat.add(s, d)) == WIN : Nat}:
  Equal.trans(Nat, Nat.add(I2, Nat.add(s, d)), Nat.add(Nat.add(I2, s), d), WIN,
    Equal.sym(Nat, Nat.add(Nat.add(I2, s), d), Nat.add(I2, Nat.add(s, d)), N.add_assoc(I2, s, d)),
    Equal.trans(Nat, Nat.add(Nat.add(I2, s), d), Nat.add(d, Nat.add(I2, s)), WIN,
      N.add_comm(Nat.add(I2, s), d),
      Equal.trans(Nat, Nat.add(d, Nat.add(I2, s)), Nat.add(Nat.add(d, I2), s), WIN,
        Equal.sym(Nat, Nat.add(Nat.add(d, I2), s), Nat.add(d, Nat.add(I2, s)), N.add_assoc(d, I2, s)),
        Equal.trans(Nat, Nat.add(Nat.add(d, I2), s), Nat.add(I, s), WIN,
          cong_add_r(s, Nat.add(d, I2), I, h2),
          h1))))

# The relay accepts the page's send of n bytes: the bytes it holds, Q, with n more, fit in the window.
# Its count is d past the page's last view, so Q is what the page counts as in flight, less d.
def relay_accepts(+I: Nat, +s: Nat, +n: Nat, +r: Nat, +Q: Nat, +d: Nat, +WIN: Nat,
  h1: {Nat.add(I, s) == WIN : Nat}, h2: {Nat.add(n, r) == s : Nat}, h3: {Nat.add(d, Q) == I : Nat}) ->
  {Nat.add(Q, Nat.add(n, Nat.add(r, d))) == WIN : Nat}:
  Equal.trans(Nat, Nat.add(Q, Nat.add(n, Nat.add(r, d))), Nat.add(Q, Nat.add(s, d)), WIN,
    cong_add_l(Q, Nat.add(n, Nat.add(r, d)), Nat.add(s, d),
      Equal.trans(Nat, Nat.add(n, Nat.add(r, d)), Nat.add(Nat.add(n, r), d), Nat.add(s, d),
        Equal.sym(Nat, Nat.add(Nat.add(n, r), d), Nat.add(n, Nat.add(r, d)), N.add_assoc(n, r, d)),
        cong_add_r(d, Nat.add(n, r), s, h2))),
    written_keeps(I, s, d, Q, WIN, h1, h3))

# ---- the read credit ----

# The invariant: the bytes read from the socket, R, with slack z, satisfy R + z == G + C, where G is
# the relay's grant and C is the largest chunk (so R is at most G + C).

# a read of a chunk of k bytes (k + u == C), allowed while R is at most the grant (R + y == G)
def read_keeps(+R: Nat, +G: Nat, +y: Nat, +k: Nat, +u: Nat, +C: Nat,
  h1: {Nat.add(R, y) == G : Nat}, h2: {Nat.add(k, u) == C : Nat}) ->
  {Nat.add(Nat.add(R, k), Nat.add(y, u)) == Nat.add(G, C) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(R, k), Nat.add(y, u)), Nat.add(Nat.add(R, y), Nat.add(k, u)), Nat.add(G, C),
    interchange(R, k, y, u),
    Equal.trans(Nat, Nat.add(Nat.add(R, y), Nat.add(k, u)), Nat.add(G, Nat.add(k, u)), Nat.add(G, C),
      cong_add_r(Nat.add(k, u), Nat.add(R, y), G, h1),
      cong_add_l(G, Nat.add(k, u), C, h2)))

# A grant with no clamp: the grant becomes G + n, and the slack z grows by n.
def grant_keeps(+R: Nat, +G: Nat, +z: Nat, +n: Nat, +C: Nat, h1: {Nat.add(R, z) == Nat.add(G, C) : Nat}) ->
  {Nat.add(R, Nat.add(z, n)) == Nat.add(Nat.add(G, n), C) : Nat}:
  Equal.trans(Nat, Nat.add(R, Nat.add(z, n)), Nat.add(Nat.add(R, z), n), Nat.add(Nat.add(G, n), C),
    Equal.sym(Nat, Nat.add(Nat.add(R, z), n), Nat.add(R, Nat.add(z, n)), N.add_assoc(R, z, n)),
    Equal.trans(Nat, Nat.add(Nat.add(R, z), n), Nat.add(Nat.add(G, C), n), Nat.add(Nat.add(G, n), C),
      cong_add_r(n, Nat.add(R, z), Nat.add(G, C), h1),
      add_end(G, C, n)))

# A grant that the relay clamps to the window: the grant becomes R + WIN, and the slack is WIN + C.
def clamp_keeps(+R: Nat, +WIN: Nat, +C: Nat) -> {Nat.add(R, Nat.add(WIN, C)) == Nat.add(Nat.add(R, WIN), C) : Nat}:
  Equal.sym(Nat, Nat.add(Nat.add(R, WIN), C), Nat.add(R, Nat.add(WIN, C)), N.add_assoc(R, WIN, C))

# The credit left after a grant with no clamp (R + c == G + n) is at most the window: c + v == WIN,
# where v is the slack that the no-clamp test found (G + n + v == R + WIN).
def credit_le(+R: Nat, +G: Nat, +n: Nat, +c: Nat, +v: Nat, +WIN: Nat,
  hc: {Nat.add(R, c) == Nat.add(G, n) : Nat}, guard: {Nat.add(Nat.add(G, n), v) == Nat.add(R, WIN) : Nat}) ->
  {Nat.add(c, v) == WIN : Nat}:
  add_cancel_l(R, Nat.add(c, v), WIN,
    Equal.trans(Nat, Nat.add(R, Nat.add(c, v)), Nat.add(Nat.add(R, c), v), Nat.add(R, WIN),
      Equal.sym(Nat, Nat.add(Nat.add(R, c), v), Nat.add(R, Nat.add(c, v)), N.add_assoc(R, c, v)),
      Equal.trans(Nat, Nat.add(Nat.add(R, c), v), Nat.add(Nat.add(G, n), v), Nat.add(R, WIN),
        cong_add_r(v, Nat.add(R, c), Nat.add(G, n), hc),
        guard)))

# The page is honest: the relay's grant G, with u more, is the window plus what the page took, i.e.
# G + u == WIN + T. A grant without a clamp keeps that.
def honest_A(+G: Nat, +n: Nat, +u: Nat, +WIN: Nat, +T: Nat, hG: {Nat.add(G, u) == Nat.add(WIN, T) : Nat}) ->
  {Nat.add(Nat.add(G, n), u) == Nat.add(WIN, Nat.add(T, n)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(G, n), u), Nat.add(Nat.add(G, u), n), Nat.add(WIN, Nat.add(T, n)),
    add_end(G, n, u),
    Equal.trans(Nat, Nat.add(Nat.add(G, u), n), Nat.add(Nat.add(WIN, T), n), Nat.add(WIN, Nat.add(T, n)),
      cong_add_r(n, Nat.add(G, u), Nat.add(WIN, T), hG),
      N.add_assoc(WIN, T, n)))

# A grant that is clamped to R + WIN (the guard: R + WIN + w == G + n) keeps the grant at most the
# window plus what the page took: the new slack is w + u.
def honest_B(+R: Nat, +G: Nat, +n: Nat, +u: Nat, +w: Nat, +WIN: Nat, +T: Nat,
  guard: {Nat.add(Nat.add(R, WIN), w) == Nat.add(G, n) : Nat},
  hG: {Nat.add(G, u) == Nat.add(WIN, T) : Nat}) ->
  {Nat.add(Nat.add(R, WIN), Nat.add(w, u)) == Nat.add(WIN, Nat.add(T, n)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(R, WIN), Nat.add(w, u)), Nat.add(Nat.add(Nat.add(R, WIN), w), u), Nat.add(WIN, Nat.add(T, n)),
    Equal.sym(Nat, Nat.add(Nat.add(Nat.add(R, WIN), w), u), Nat.add(Nat.add(R, WIN), Nat.add(w, u)), N.add_assoc(Nat.add(R, WIN), w, u)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(R, WIN), w), u), Nat.add(Nat.add(G, n), u), Nat.add(WIN, Nat.add(T, n)),
      cong_add_r(u, Nat.add(Nat.add(R, WIN), w), Nat.add(G, n), guard),
      honest_A(G, n, u, WIN, T, hG)))

# THE BOUND: the page holds b bytes it has not taken. With R = T + b read from the socket, R + z == G + C
# (the relay reads no further ahead than the grant plus one chunk) and G + u == WIN + T (the grant is the
# window plus what the page took), the bytes held satisfy b + (z + u) == WIN + C: b is at most WIN + C.
def buffered_bound(+T: Nat, +b: Nat, +R: Nat, +G: Nat, +z: Nat, +u: Nat, +WIN: Nat, +C: Nat,
  hI: {Nat.add(R, z) == Nat.add(G, C) : Nat},
  hG: {Nat.add(G, u) == Nat.add(WIN, T) : Nat},
  hB: {Nat.add(T, b) == R : Nat}) ->
  {Nat.add(b, Nat.add(z, u)) == Nat.add(WIN, C) : Nat}:
  add_cancel_l(T, Nat.add(b, Nat.add(z, u)), Nat.add(WIN, C),
    Equal.trans(Nat, Nat.add(T, Nat.add(b, Nat.add(z, u))), Nat.add(Nat.add(T, b), Nat.add(z, u)), Nat.add(T, Nat.add(WIN, C)),
      Equal.sym(Nat, Nat.add(Nat.add(T, b), Nat.add(z, u)), Nat.add(T, Nat.add(b, Nat.add(z, u))), N.add_assoc(T, b, Nat.add(z, u))),
      Equal.trans(Nat, Nat.add(Nat.add(T, b), Nat.add(z, u)), Nat.add(Nat.add(Nat.add(T, b), z), u), Nat.add(T, Nat.add(WIN, C)),
        Equal.sym(Nat, Nat.add(Nat.add(Nat.add(T, b), z), u), Nat.add(Nat.add(T, b), Nat.add(z, u)), N.add_assoc(Nat.add(T, b), z, u)),
        Equal.trans(Nat, Nat.add(Nat.add(Nat.add(T, b), z), u), Nat.add(Nat.add(G, C), u), Nat.add(T, Nat.add(WIN, C)),
          cong_add_r(u, Nat.add(Nat.add(T, b), z), Nat.add(G, C),
            Equal.trans(Nat, Nat.add(Nat.add(T, b), z), Nat.add(R, z), Nat.add(G, C),
              cong_add_r(z, Nat.add(T, b), R, hB),
              hI)),
          Equal.trans(Nat, Nat.add(Nat.add(G, C), u), Nat.add(Nat.add(G, u), C), Nat.add(T, Nat.add(WIN, C)),
            add_end(G, C, u),
            Equal.trans(Nat, Nat.add(Nat.add(G, u), C), Nat.add(Nat.add(WIN, T), C), Nat.add(T, Nat.add(WIN, C)),
              cong_add_r(C, Nat.add(G, u), Nat.add(WIN, T), hG),
              Equal.trans(Nat, Nat.add(Nat.add(WIN, T), C), Nat.add(WIN, Nat.add(T, C)), Nat.add(T, Nat.add(WIN, C)),
                N.add_assoc(WIN, T, C),
                add_swap(WIN, T, C))))))))
