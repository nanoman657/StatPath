# tcp_model.bend: the proofs that the connection's transitions (tcp_transitions.bend, which the relay and the
# page's client call) keep the invariants below. Run:  bend tcp_model.bend   (ALL PROOFS CHECK)
#
# Each count is written with a witness (a + w == b says a <= b, with w the slack), and the witnesses that the
# code does not keep are ghosts. The invariants, after each transition:
#   page:  px: wp + px == sent (px: bytes in flight)    pz: px + pz == win (pz: window slack)
#          pt: sent + pt == tail (pt: bytes left to send)    pd: taken + pd == recvd (pd: received, not taken)
#          pr: recvd + pr == rd (pr: DATA in flight)
#   relay: pw: wp + pw == wr (pw: the relay's count ahead of the page's)   pf: wr + (q + f) == sent (f: in flight
#          or dropped)    ps: q + s2 == win (s2: the room for a SEND)    pc1: gr + c1 == rd + win (c1: credit slack)
#          pc2: rd + c2 == gr + C (c2: read slack)    pg1: gr + g1 == ti (g1: grant slack, ti: grants applied)
#          pg2: ti + g2 == win + taken (g2: grants in flight; the page's grants are the window plus what it took)
#   derived: rd - taken <= win + C (the page holds at most a window and a chunk, lemma bound_held)
#
# The transition -> lemma map:
#   start: start_pt (pt)                                  frame: frame_eq, frame_split_z, frame_split_t,
#                                                         frame_x (px), frame_z (pz), frame_t (pt), frame_f (pf)
#   the relay accepts a frame: room_eq, fits_zero (the test rl_over(n, rl_room(win, q)) === 0 passes), recv_f, recv_slack
#   the relay writes: write_f (pf), write_pw (pw), write_ps (ps), unqueue_eq (q' is the model's value)
#   DISCARD at the relay: discard_f (pf); the page's reply: reply_zero (pw, pt, px)
#   the program takes and grants: take_slack, take_pd (pd), take_g2 (pg2)
#   DATA arrives at the page: recv_pr (pr), recv_pd (pd)
#   the relay reads: C.read_keeps (pc2), read_pr (pr), read_pc1 (pc1)
#   the relay applies a grant: min_wit_l (pc1), grant_g1 (pg1), and the clamp keeps pc1 for any page
#   WRITTEN at the page: written_px (px), written_pz (pz), written_pw (pw)
#   the bound: honest_u, bound_hB, bound_held
#
# The assumptions about the environment (Bun's sockets, the WebSocket) are checked at run time by the code, and
# named in README.md; the bound uses only the chunk limit, the read window and an honest page's own memory.
import Base
import ./tcp_transitions.bend as T
import ./../tcp_contract_proof.bend as C
import ./../frame_arith.bend as N

# ---- congruence and min ----

def cong_succ(+A: Nat, +B: Nat, +h: {A == B : Nat}) -> {1n+A == 1n+B : Nat}:
  %h : {1n+A == 1n+_ : Nat}
  {==}

def cong_sub_l(+a: Nat, +b: Nat, +c: Nat, +h: {a == b : Nat}) -> {Nat.sub(a, c) == Nat.sub(b, c) : Nat}:
  %h : {Nat.sub(a, c) == Nat.sub(_, c) : Nat}
  {==}

def cong_sub_r(+a: Nat, +b: Nat, +c: Nat, +h: {b == c : Nat}) -> {Nat.sub(a, b) == Nat.sub(a, c) : Nat}:
  %h : {Nat.sub(a, b) == Nat.sub(a, _) : Nat}
  {==}

def cong_min_l(+a: Nat, +b: Nat, +c: Nat, +h: {a == b : Nat}) -> {Nat.min(a, c) == Nat.min(b, c) : Nat}:
  %h : {Nat.min(a, c) == Nat.min(_, c) : Nat}
  {==}

def cong_min_r(+a: Nat, +b: Nat, +c: Nat, +h: {b == c : Nat}) -> {Nat.min(a, b) == Nat.min(a, c) : Nat}:
  %h : {Nat.min(a, b) == Nat.min(a, _) : Nat}
  {==}

def min_comm(+a: Nat, +b: Nat) -> {Nat.min(a, b) == Nat.min(b, a) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          cong_succ(Nat.min(p, q), Nat.min(q, p), min_comm(p, q))

# min(a, b) plus what is left of b is b
def min_wit_r(+a: Nat, +b: Nat) -> {Nat.add(Nat.min(a, b), Nat.sub(b, Nat.min(a, b))) == b : Nat}:
  match a:
    case 0n:
      C.sub_zero(b)
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          cong_succ(Nat.add(Nat.min(p, q), Nat.sub(q, Nat.min(p, q))), q, min_wit_r(p, q))

# min(a, b) plus what is left of a is a
def min_wit_l(+a: Nat, +b: Nat) -> {Nat.add(Nat.min(a, b), Nat.sub(a, Nat.min(a, b))) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          cong_succ(Nat.add(Nat.min(p, q), Nat.sub(p, Nat.min(p, q))), p, min_wit_l(p, q))

# ---- the page: the frame, as a function of the window's slack z and the bytes left t1 ----
# (x is the page's bytes in flight, sent = wp + x; win = x + z; tail = sent + t1)

def slack_z(+sent: Nat, +wp: Nat, +win: Nat, +x: Nat, +z: Nat,
  +h1: {Nat.add(wp, x) == sent : Nat}, +h2: {Nat.add(x, z) == win : Nat}) ->
  {Nat.sub(win, Nat.sub(sent, wp)) == z : Nat}:
  Equal.trans(Nat, Nat.sub(win, Nat.sub(sent, wp)), Nat.sub(win, x), z,
    cong_sub_r(win, Nat.sub(sent, wp), x,
      Equal.trans(Nat, Nat.sub(sent, wp), Nat.sub(Nat.add(wp, x), wp), x,
        cong_sub_l(sent, Nat.add(wp, x), wp, Equal.sym(Nat, Nat.add(wp, x), sent, h1)),
        C.sub_add(wp, x))),
    Equal.trans(Nat, Nat.sub(win, x), Nat.sub(Nat.add(x, z), x), z,
      cong_sub_l(win, Nat.add(x, z), x, Equal.sym(Nat, Nat.add(x, z), win, h2)),
      C.sub_add(x, z)))

def slack_t(+sent: Nat, +tail: Nat, +t1: Nat, +h3: {Nat.add(sent, t1) == tail : Nat}) ->
  {Nat.sub(tail, sent) == t1 : Nat}:
  Equal.trans(Nat, Nat.sub(tail, sent), Nat.sub(Nat.add(sent, t1), sent), t1,
    cong_sub_l(tail, Nat.add(sent, t1), sent, Equal.sym(Nat, Nat.add(sent, t1), tail, h3)),
    C.sub_add(sent, t1))

# the frame is the least of mx, z and t1
def frame_eq(+sent: Nat, +wp: Nat, +win: Nat, +tail: Nat, +mx: Nat, +x: Nat, +z: Nat, +t1: Nat,
  +h1: {Nat.add(wp, x) == sent : Nat}, +h2: {Nat.add(x, z) == win : Nat}, +h3: {Nat.add(sent, t1) == tail : Nat}) ->
  {T.pg_frame_n(sent, wp, win, tail, mx) == Nat.min(mx, Nat.min(z, t1)) : Nat}:
  Equal.trans(Nat, T.pg_frame_n(sent, wp, win, tail, mx),
    Nat.min(mx, Nat.min(z, Nat.sub(tail, sent))), Nat.min(mx, Nat.min(z, t1)),
    cong_min_r(mx, Nat.min(Nat.sub(win, Nat.sub(sent, wp)), Nat.sub(tail, sent)), Nat.min(z, Nat.sub(tail, sent)),
      cong_min_l(Nat.sub(win, Nat.sub(sent, wp)), z, Nat.sub(tail, sent), slack_z(sent, wp, win, x, z, h1, h2))),
    cong_min_r(mx, Nat.min(z, Nat.sub(tail, sent)), Nat.min(z, t1),
      cong_min_r(z, Nat.sub(tail, sent), t1, slack_t(sent, tail, t1, h3))))

# the frame n = min(mx, min(z, t1)) splits z: n + (sub(m, n) + sub(z, m)) == z, with m = min(z, t1)
def frame_split_z(+mx: Nat, +z: Nat, +t1: Nat) ->
  {Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.add(Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(z, Nat.min(z, t1)))) == z : Nat}:
  Equal.trans(Nat, Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.add(Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(z, Nat.min(z, t1)))),
    Nat.add(Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.sub(z, Nat.min(z, t1))),
    z,
    Equal.sym(Nat, Nat.add(Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.sub(z, Nat.min(z, t1))),
      Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.add(Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(z, Nat.min(z, t1)))),
      N.add_assoc(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(z, Nat.min(z, t1)))),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.sub(z, Nat.min(z, t1))),
      Nat.add(Nat.min(z, t1), Nat.sub(z, Nat.min(z, t1))), z,
      C.cong_add_r(Nat.sub(z, Nat.min(z, t1)), Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.min(z, t1),
        min_wit_r(mx, Nat.min(z, t1))),
      min_wit_l(z, t1)))

# ---- the frame: the page's new counts, and the split of the window's slack and the bytes left ----

def frame_split_t(+mx: Nat, +z: Nat, +t1: Nat) ->
  {Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.add(Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(t1, Nat.min(z, t1)))) == t1 : Nat}:
  Equal.trans(Nat, Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.add(Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(t1, Nat.min(z, t1)))),
    Nat.add(Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.sub(t1, Nat.min(z, t1))),
    t1,
    Equal.sym(Nat, Nat.add(Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.sub(t1, Nat.min(z, t1))),
      Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.add(Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(t1, Nat.min(z, t1)))),
      N.add_assoc(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1))), Nat.sub(t1, Nat.min(z, t1)))),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.sub(t1, Nat.min(z, t1))),
      Nat.add(Nat.min(z, t1), Nat.sub(t1, Nat.min(z, t1))), t1,
      C.cong_add_r(Nat.sub(t1, Nat.min(z, t1)), Nat.add(Nat.min(mx, Nat.min(z, t1)), Nat.sub(Nat.min(z, t1), Nat.min(mx, Nat.min(z, t1)))), Nat.min(z, t1),
        min_wit_r(mx, Nat.min(z, t1))),
      min_wit_r(z, t1)))

# sent = wp + x, and the frame n is sent: the page's in-flight count is x + n
def frame_x(+wp: Nat, +x: Nat, +sent: Nat, +n: Nat, +h1: {Nat.add(wp, x) == sent : Nat}) ->
  {Nat.add(wp, Nat.add(x, n)) == Nat.add(sent, n) : Nat}:
  Equal.trans(Nat, Nat.add(wp, Nat.add(x, n)), Nat.add(Nat.add(wp, x), n), Nat.add(sent, n),
    Equal.sym(Nat, Nat.add(Nat.add(wp, x), n), Nat.add(wp, Nat.add(x, n)), N.add_assoc(wp, x, n)),
    C.cong_add_r(n, Nat.add(wp, x), sent, h1))

# x + z = win, and n + zz = z: after the frame the slack is zz
def frame_z(+x: Nat, +z: Nat, +win: Nat, +n: Nat, +zz: Nat, +h1: {Nat.add(x, z) == win : Nat},
  +h2: {Nat.add(n, zz) == z : Nat}) -> {Nat.add(Nat.add(x, n), zz) == win : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(x, n), zz), Nat.add(x, Nat.add(n, zz)), win,
    N.add_assoc(x, n, zz),
    Equal.trans(Nat, Nat.add(x, Nat.add(n, zz)), Nat.add(x, z), win,
      C.cong_add_l(x, Nat.add(n, zz), z, h2),
      h1))

# the page's tail: sent + t1 = tail, and n + tp = t1, so after the frame sent + n + tp = tail
def frame_t(+sent: Nat, +n: Nat, +t1: Nat, +tp: Nat, +tail: Nat, +h1: {Nat.add(sent, t1) == tail : Nat},
  +h2: {Nat.add(n, tp) == t1 : Nat}) -> {Nat.add(Nat.add(sent, n), tp) == tail : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(sent, n), tp), Nat.add(sent, Nat.add(n, tp)), tail,
    N.add_assoc(sent, n, tp),
    Equal.trans(Nat, Nat.add(sent, Nat.add(n, tp)), Nat.add(sent, t1), tail,
      C.cong_add_l(sent, Nat.add(n, tp), t1, h2),
      h1))

# the relay's in-flight count: wr + (q + f) = sent, and the frame adds n to both sides
def frame_f(+wr: Nat, +q: Nat, +f: Nat, +sent: Nat, +n: Nat, +h1: {Nat.add(wr, Nat.add(q, f)) == sent : Nat}) ->
  {Nat.add(wr, Nat.add(q, Nat.add(f, n))) == Nat.add(sent, n) : Nat}:
  Equal.trans(Nat, Nat.add(wr, Nat.add(q, Nat.add(f, n))), Nat.add(wr, Nat.add(Nat.add(q, f), n)), Nat.add(sent, n),
    C.cong_add_l(wr, Nat.add(q, Nat.add(f, n)), Nat.add(Nat.add(q, f), n), Equal.sym(Nat, Nat.add(Nat.add(q, f), n), Nat.add(q, Nat.add(f, n)), N.add_assoc(q, f, n))),
    Equal.trans(Nat, Nat.add(wr, Nat.add(Nat.add(q, f), n)), Nat.add(Nat.add(wr, Nat.add(q, f)), n), Nat.add(sent, n),
      Equal.sym(Nat, Nat.add(Nat.add(wr, Nat.add(q, f)), n), Nat.add(wr, Nat.add(Nat.add(q, f), n)), N.add_assoc(wr, Nat.add(q, f), n)),
      C.cong_add_r(n, Nat.add(wr, Nat.add(q, f)), sent, h1)))

# the relay receives n bytes that were in flight: the in-flight count f = n + f2 becomes f2
def recv_f(+wr: Nat, +q: Nat, +n: Nat, +f2: Nat, +sent: Nat, +h1: {Nat.add(wr, Nat.add(q, Nat.add(n, f2))) == sent : Nat}) ->
  {Nat.add(wr, Nat.add(Nat.add(q, n), f2)) == sent : Nat}:
  Equal.trans(Nat, Nat.add(wr, Nat.add(Nat.add(q, n), f2)), Nat.add(wr, Nat.add(q, Nat.add(n, f2))), sent,
    C.cong_add_l(wr, Nat.add(Nat.add(q, n), f2), Nat.add(q, Nat.add(n, f2)), N.add_assoc(q, n, f2)),
    h1)

# ---- the relay's room for a SEND: the bytes it holds, plus what is in flight, plus the window's slack ----

# (n + (f0 + pw)) is the same as (pw + (n + f0)), as the sum is commutative and associative
def rearr_inner(+B: Nat, +Nn: Nat, +F: Nat) ->
  {Nat.add(Nn, Nat.add(F, B)) == Nat.add(B, Nat.add(Nn, F)) : Nat}:
  Equal.trans(Nat, Nat.add(Nn, Nat.add(F, B)), Nat.add(Nn, Nat.add(B, F)), Nat.add(B, Nat.add(Nn, F)),
    C.cong_add_l(Nn, Nat.add(F, B), Nat.add(B, F), N.add_comm(F, B)),
    C.add_swap(Nn, B, F))

# A + (Q + (Nn + (F + B))) == (A + B) + (Q + (Nn + F))
def rearr_pw(+A: Nat, +Q: Nat, +Nn: Nat, +F: Nat, +B: Nat) ->
  {Nat.add(A, Nat.add(Q, Nat.add(Nn, Nat.add(F, B)))) == Nat.add(Nat.add(A, B), Nat.add(Q, Nat.add(Nn, F))) : Nat}:
  Equal.trans(Nat, Nat.add(A, Nat.add(Q, Nat.add(Nn, Nat.add(F, B)))),
    Nat.add(A, Nat.add(Q, Nat.add(B, Nat.add(Nn, F)))), Nat.add(Nat.add(A, B), Nat.add(Q, Nat.add(Nn, F))),
    C.cong_add_l(A, Nat.add(Q, Nat.add(Nn, Nat.add(F, B))), Nat.add(Q, Nat.add(B, Nat.add(Nn, F))),
      C.cong_add_l(Q, Nat.add(Nn, Nat.add(F, B)), Nat.add(B, Nat.add(Nn, F)), rearr_inner(B, Nn, F))),
    Equal.trans(Nat, Nat.add(A, Nat.add(Q, Nat.add(B, Nat.add(Nn, F)))),
      Nat.add(A, Nat.add(B, Nat.add(Q, Nat.add(Nn, F)))), Nat.add(Nat.add(A, B), Nat.add(Q, Nat.add(Nn, F))),
      C.cong_add_l(A, Nat.add(Q, Nat.add(B, Nat.add(Nn, F))), Nat.add(B, Nat.add(Q, Nat.add(Nn, F))),
        Equal.sym(Nat, Nat.add(B, Nat.add(Q, Nat.add(Nn, F))), Nat.add(Q, Nat.add(B, Nat.add(Nn, F))), C.add_swap(B, Q, Nat.add(Nn, F)))),
      Equal.sym(Nat, Nat.add(Nat.add(A, B), Nat.add(Q, Nat.add(Nn, F))), Nat.add(A, Nat.add(B, Nat.add(Q, Nat.add(Nn, F)))),
        N.add_assoc(A, B, Nat.add(Q, Nat.add(Nn, F))))))

# wp + (q + (n + (f0 + pw))) == sent: the page's sent, rewritten through the relay's count (wr = wp + pw)
def room_x1(+wr: Nat, +q: Nat, +n: Nat, +f0: Nat, +wp: Nat, +pw: Nat, +sent: Nat,
  +hA: {Nat.add(wr, Nat.add(q, Nat.add(n, f0))) == sent : Nat}, +hB: {Nat.add(wp, pw) == wr : Nat}) ->
  {Nat.add(wp, Nat.add(q, Nat.add(n, Nat.add(f0, pw)))) == sent : Nat}:
  Equal.trans(Nat, Nat.add(wp, Nat.add(q, Nat.add(n, Nat.add(f0, pw)))), Nat.add(Nat.add(wp, pw), Nat.add(q, Nat.add(n, f0))), sent,
    rearr_pw(wp, q, n, f0, pw),
    Equal.trans(Nat, Nat.add(Nat.add(wp, pw), Nat.add(q, Nat.add(n, f0))), Nat.add(wr, Nat.add(q, Nat.add(n, f0))), sent,
      C.cong_add_r(Nat.add(q, Nat.add(n, f0)), Nat.add(wp, pw), wr, hB),
      hA))

# px = q + (n + (f0 + pw)): the page's bytes in flight are the relay's queue plus the rest
def room_px(+wr: Nat, +q: Nat, +n: Nat, +f0: Nat, +wp: Nat, +pw: Nat, +px: Nat, +sent: Nat,
  +hA: {Nat.add(wr, Nat.add(q, Nat.add(n, f0))) == sent : Nat}, +hB: {Nat.add(wp, pw) == wr : Nat},
  +hC: {Nat.add(wp, px) == sent : Nat}) ->
  {px == Nat.add(q, Nat.add(n, Nat.add(f0, pw))) : Nat}:
  C.add_cancel_l(wp, px, Nat.add(q, Nat.add(n, Nat.add(f0, pw))),
    Equal.trans(Nat, Nat.add(wp, px), sent, Nat.add(wp, Nat.add(q, Nat.add(n, Nat.add(f0, pw)))),
      hC,
      Equal.sym(Nat, Nat.add(wp, Nat.add(q, Nat.add(n, Nat.add(f0, pw)))), sent,
        room_x1(wr, q, n, f0, wp, pw, sent, hA, hB))))

# q + s2 == q + (W + pz), with W = n + (f0 + pw): the relay's room is the page's bytes beyond its queue
def room_hq(+wr: Nat, +q: Nat, +n: Nat, +f0: Nat, +wp: Nat, +pw: Nat, +px: Nat, +pz: Nat, +win: Nat, +sent: Nat,
  +s2: Nat, +hA: {Nat.add(wr, Nat.add(q, Nat.add(n, f0))) == sent : Nat}, +hB: {Nat.add(wp, pw) == wr : Nat},
  +hC: {Nat.add(wp, px) == sent : Nat}, +hD: {Nat.add(px, pz) == win : Nat}, +hE: {Nat.add(q, s2) == win : Nat}) ->
  {Nat.add(q, s2) == Nat.add(q, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz)) : Nat}:
  Equal.trans(Nat, Nat.add(q, s2), win, Nat.add(q, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz)),
    hE,
    Equal.trans(Nat, win, Nat.add(px, pz), Nat.add(q, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz)),
      Equal.sym(Nat, Nat.add(px, pz), win, hD),
      Equal.trans(Nat, Nat.add(px, pz), Nat.add(Nat.add(q, Nat.add(n, Nat.add(f0, pw))), pz), Nat.add(q, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz)),
        C.cong_add_r(pz, px, Nat.add(q, Nat.add(n, Nat.add(f0, pw))),
          room_px(wr, q, n, f0, wp, pw, px, sent, hA, hB, hC)),
        N.add_assoc(q, Nat.add(n, Nat.add(f0, pw)), pz))))

# The frame n is in flight at the relay (f = n + f0): the relay's room, win - q, holds n and the rest of the
# page's bytes: n + (f0 + pw + pz) == win - q.
def room_eq(+wr: Nat, +q: Nat, +n: Nat, +f0: Nat, +wp: Nat, +pw: Nat, +px: Nat, +pz: Nat, +win: Nat, +sent: Nat,
  +s2: Nat, +hA: {Nat.add(wr, Nat.add(q, Nat.add(n, f0))) == sent : Nat}, +hB: {Nat.add(wp, pw) == wr : Nat},
  +hC: {Nat.add(wp, px) == sent : Nat}, +hD: {Nat.add(px, pz) == win : Nat}, +hE: {Nat.add(q, s2) == win : Nat}) ->
  {Nat.add(n, Nat.add(Nat.add(f0, pw), pz)) == s2 : Nat}:
  Equal.trans(Nat, Nat.add(n, Nat.add(Nat.add(f0, pw), pz)), Nat.add(Nat.add(n, Nat.add(f0, pw)), pz), s2,
    Equal.sym(Nat, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz), Nat.add(n, Nat.add(Nat.add(f0, pw), pz)),
      N.add_assoc(n, Nat.add(f0, pw), pz)),
    Equal.sym(Nat, s2, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz),
      C.add_cancel_l(q, s2, Nat.add(Nat.add(n, Nat.add(f0, pw)), pz),
        room_hq(wr, q, n, f0, wp, pw, px, pz, win, sent, s2, hA, hB, hC, hD, hE))))

# win = q + s2 gives win - q == s2
def room_s2(+win: Nat, +q: Nat, +s2: Nat, +hE: {Nat.add(q, s2) == win : Nat}) -> {Nat.sub(win, q) == s2 : Nat}:
  Equal.trans(Nat, Nat.sub(win, q), Nat.sub(Nat.add(q, s2), q), s2,
    cong_sub_l(win, Nat.add(q, s2), q, Equal.sym(Nat, Nat.add(q, s2), win, hE)),
    C.sub_add(q, s2))

# the relay's room, win - q, is s2, and n fits in it: sub(n, win - q) == 0. This is the relay's test
# (T.rl_over(n, T.rl_room(win, q)) == 0) passing for every frame a conforming page sends.
def fits_zero(+wr: Nat, +q: Nat, +n: Nat, +f0: Nat, +wp: Nat, +pw: Nat, +px: Nat, +pz: Nat, +win: Nat, +sent: Nat,
  +s2: Nat, +hA: {Nat.add(wr, Nat.add(q, Nat.add(n, f0))) == sent : Nat}, +hB: {Nat.add(wp, pw) == wr : Nat},
  +hC: {Nat.add(wp, px) == sent : Nat}, +hD: {Nat.add(px, pz) == win : Nat}, +hE: {Nat.add(q, s2) == win : Nat}) ->
  {Nat.sub(n, Nat.sub(win, q)) == 0n : Nat}:
  Equal.trans(Nat, Nat.sub(n, Nat.sub(win, q)), Nat.sub(n, s2), 0n,
    cong_sub_r(n, Nat.sub(win, q), s2, room_s2(win, q, s2, hE)),
    Equal.trans(Nat, Nat.sub(n, s2), Nat.sub(n, Nat.add(n, Nat.add(Nat.add(f0, pw), pz))), 0n,
      cong_sub_r(n, s2, Nat.add(n, Nat.add(Nat.add(f0, pw), pz)),
        Equal.sym(Nat, Nat.add(n, Nat.add(Nat.add(f0, pw), pz)), s2,
          room_eq(wr, q, n, f0, wp, pw, px, pz, win, sent, s2, hA, hB, hC, hD, hE))),
      C.sub_addend(n, Nat.add(Nat.add(f0, pw), pz))))

# ---- the relay's SEND: the room after accepting a frame, and the queue after it ----

# the frame's n is the room's first part (n + s' == s2): after accepting it the room is s'
def recv_slack(+q: Nat, +n: Nat, +s2: Nat, +sp: Nat, +win: Nat, h1: {Nat.add(n, sp) == s2 : Nat},
  hE: {Nat.add(q, s2) == win : Nat}) -> {Nat.add(Nat.add(q, n), sp) == win : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(q, n), sp), Nat.add(q, Nat.add(n, sp)), win,
    N.add_assoc(q, n, sp),
    Equal.trans(Nat, Nat.add(q, Nat.add(n, sp)), Nat.add(q, s2), win,
      C.cong_add_l(q, Nat.add(n, sp), s2, h1),
      hE))

# the relay's queue after it writes m bytes: the queue is m + qp (qp is what is left)
def unqueue_eq(+q: Nat, +m: Nat, +qp: Nat, hm: {Nat.add(m, qp) == q : Nat}) -> {Nat.sub(q, m) == qp : Nat}:
  Equal.trans(Nat, Nat.sub(q, m), Nat.sub(Nat.add(m, qp), m), qp,
    cong_sub_l(q, Nat.add(m, qp), m, Equal.sym(Nat, Nat.add(m, qp), q, hm)),
    C.sub_add(m, qp))

# the relay writes m bytes: sent = wr + (q + f) stays true with wr + m and q - m
def write_f(+wr: Nat, +q: Nat, +m: Nat, +qp: Nat, +f: Nat, +sent: Nat, hm: {Nat.add(m, qp) == q : Nat},
  hA: {Nat.add(wr, Nat.add(q, f)) == sent : Nat}) -> {Nat.add(Nat.add(wr, m), Nat.add(qp, f)) == sent : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(wr, m), Nat.add(qp, f)), Nat.add(wr, Nat.add(m, Nat.add(qp, f))), sent,
    N.add_assoc(wr, m, Nat.add(qp, f)),
    Equal.trans(Nat, Nat.add(wr, Nat.add(m, Nat.add(qp, f))), Nat.add(wr, Nat.add(q, f)), sent,
      C.cong_add_l(wr, Nat.add(m, Nat.add(qp, f)), Nat.add(q, f),
        Equal.trans(Nat, Nat.add(m, Nat.add(qp, f)), Nat.add(Nat.add(m, qp), f), Nat.add(q, f),
          Equal.sym(Nat, Nat.add(Nat.add(m, qp), f), Nat.add(m, Nat.add(qp, f)), N.add_assoc(m, qp, f)),
          C.cong_add_r(f, Nat.add(m, qp), q, hm))),
      hA))

# the page's relay count: wp + (pw + m) == wr + m
def write_pw(+wp: Nat, +pw: Nat, +wr: Nat, +m: Nat, hB: {Nat.add(wp, pw) == wr : Nat}) ->
  {Nat.add(wp, Nat.add(pw, m)) == Nat.add(wr, m) : Nat}:
  Equal.trans(Nat, Nat.add(wp, Nat.add(pw, m)), Nat.add(Nat.add(wp, pw), m), Nat.add(wr, m),
    Equal.sym(Nat, Nat.add(Nat.add(wp, pw), m), Nat.add(wp, Nat.add(pw, m)), N.add_assoc(wp, pw, m)),
    C.cong_add_r(m, Nat.add(wp, pw), wr, hB))

# the room after the write: qp + (m + s2) == win
def write_ps(+q: Nat, +qp: Nat, +m: Nat, +s2: Nat, +win: Nat, hm: {Nat.add(m, qp) == q : Nat},
  hE: {Nat.add(q, s2) == win : Nat}) -> {Nat.add(qp, Nat.add(m, s2)) == win : Nat}:
  Equal.trans(Nat, Nat.add(qp, Nat.add(m, s2)), Nat.add(Nat.add(qp, m), s2), win,
    Equal.sym(Nat, Nat.add(Nat.add(qp, m), s2), Nat.add(qp, Nat.add(m, s2)), N.add_assoc(qp, m, s2)),
    Equal.trans(Nat, Nat.add(Nat.add(qp, m), s2), Nat.add(Nat.add(m, qp), s2), win,
      C.cong_add_r(s2, Nat.add(qp, m), Nat.add(m, qp), N.add_comm(qp, m)),
      Equal.trans(Nat, Nat.add(Nat.add(m, qp), s2), Nat.add(q, s2), win,
        C.cong_add_r(s2, Nat.add(m, qp), q, hm),
        hE)))

# DISCARD at the relay: the queue is dropped (q becomes 0) and its bytes join the dropped count
def discard_f(+wr: Nat, +q: Nat, +f: Nat, +sent: Nat, hA: {Nat.add(wr, Nat.add(q, f)) == sent : Nat}) ->
  {Nat.add(wr, Nat.add(0n, Nat.add(f, q))) == sent : Nat}:
  Equal.trans(Nat, Nat.add(wr, Nat.add(0n, Nat.add(f, q))), Nat.add(wr, Nat.add(q, f)), sent,
    C.cong_add_l(wr, Nat.add(0n, Nat.add(f, q)), Nat.add(q, f), N.add_comm(f, q)),
    hA)

# the reply sets the page's count to wr, and the relay's bytes in flight and queue to 0: wr + 0 == wr
def reply_zero(+wr: Nat) -> {Nat.add(wr, 0n) == wr : Nat}:
  Equal.sym(Nat, wr, Nat.add(wr, 0n), N.add_zero(wr))

# ---- the relay's read credit and the page's data ----

# the page's data received plus the bytes in flight is the bytes read: D + pr == R
def read_pr(+D: Nat, +pr: Nat, +rd: Nat, +k: Nat, hR: {Nat.add(D, pr) == rd : Nat}) ->
  {Nat.add(D, Nat.add(pr, k)) == Nat.add(rd, k) : Nat}:
  Equal.trans(Nat, Nat.add(D, Nat.add(pr, k)), Nat.add(Nat.add(D, pr), k), Nat.add(rd, k),
    Equal.sym(Nat, Nat.add(Nat.add(D, pr), k), Nat.add(D, Nat.add(pr, k)), N.add_assoc(D, pr, k)),
    C.cong_add_r(k, Nat.add(D, pr), rd, hR))

# the relay reads k bytes: the credit left (c1) is the window less what was read, and it stays so
def read_pc1(+gr: Nat, +c1: Nat, +rd: Nat, +win: Nat, +k: Nat, hc: {Nat.add(gr, c1) == Nat.add(rd, win) : Nat}) ->
  {Nat.add(gr, Nat.add(c1, k)) == Nat.add(Nat.add(rd, k), win) : Nat}:
  Equal.trans(Nat, Nat.add(gr, Nat.add(c1, k)), Nat.add(Nat.add(gr, c1), k), Nat.add(Nat.add(rd, k), win),
    Equal.sym(Nat, Nat.add(Nat.add(gr, c1), k), Nat.add(gr, Nat.add(c1, k)), N.add_assoc(gr, c1, k)),
    Equal.trans(Nat, Nat.add(Nat.add(gr, c1), k), Nat.add(Nat.add(rd, win), k), Nat.add(Nat.add(rd, k), win),
      C.cong_add_r(k, Nat.add(gr, c1), Nat.add(rd, win), hc),
      C.add_end(rd, win, k)))

# the grant the relay applies is min(rd + win, gr + n); the ghost g1 (gr + g1 = win + ti) moves to
# sub(gr + n, min) + g1, so that gr' + g1' == win + ti + n
# ---- the page: the program takes bytes, the data arrives, WRITTEN reports, a send starts ----

# the page's slack, pd = D - T, is what the take is capped by: sub(D, T) == pd
def take_slack(+T: Nat, +D: Nat, +pd: Nat, hp: {Nat.add(T, pd) == D : Nat}) -> {Nat.sub(D, T) == pd : Nat}:
  Equal.trans(Nat, Nat.sub(D, T), Nat.sub(Nat.add(T, pd), T), pd,
    cong_sub_l(D, Nat.add(T, pd), T, Equal.sym(Nat, Nat.add(T, pd), D, hp)),
    C.sub_add(T, pd))

# the program takes n = min(mx, pd) bytes: T + n is still at most D, and pd' = pd - n is what is left
def take_pd(+T: Nat, +pd: Nat, +D: Nat, +mx: Nat, hp: {Nat.add(T, pd) == D : Nat}) ->
  {Nat.add(Nat.add(T, Nat.min(mx, pd)), Nat.sub(pd, Nat.min(mx, pd))) == D : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(T, Nat.min(mx, pd)), Nat.sub(pd, Nat.min(mx, pd))), Nat.add(T, Nat.add(Nat.min(mx, pd), Nat.sub(pd, Nat.min(mx, pd)))), D,
    N.add_assoc(T, Nat.min(mx, pd), Nat.sub(pd, Nat.min(mx, pd))),
    Equal.trans(Nat, Nat.add(T, Nat.add(Nat.min(mx, pd), Nat.sub(pd, Nat.min(mx, pd)))), Nat.add(T, pd), D,
      C.cong_add_l(T, Nat.add(Nat.min(mx, pd), Nat.sub(pd, Nat.min(mx, pd))), pd, min_wit_r(mx, pd)),
      hp))

# the take issues a grant of n: the grants applied (ti) plus the grant in flight (g2) is the total taken (T)
def take_g2(+ti: Nat, +g2: Nat, +T: Nat, +n: Nat, hg2: {Nat.add(ti, g2) == T : Nat}) ->
  {Nat.add(ti, Nat.add(g2, n)) == Nat.add(T, n) : Nat}:
  Equal.trans(Nat, Nat.add(ti, Nat.add(g2, n)), Nat.add(Nat.add(ti, g2), n), Nat.add(T, n),
    Equal.sym(Nat, Nat.add(Nat.add(ti, g2), n), Nat.add(ti, Nat.add(g2, n)), N.add_assoc(ti, g2, n)),
    C.cong_add_r(n, Nat.add(ti, g2), T, hg2))

# the page receives k of the data in flight (pr = k + prr): the data received grows by k, and the rest in flight is prr
def recv_pr(+D: Nat, +k: Nat, +prr: Nat, +pr: Nat, +R: Nat, hk: {Nat.add(k, prr) == pr : Nat}, hR: {Nat.add(D, pr) == R : Nat}) ->
  {Nat.add(Nat.add(D, k), prr) == R : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(D, k), prr), Nat.add(D, Nat.add(k, prr)), R,
    N.add_assoc(D, k, prr),
    Equal.trans(Nat, Nat.add(D, Nat.add(k, prr)), Nat.add(D, pr), R,
      C.cong_add_l(D, Nat.add(k, prr), pr, hk),
      hR))

def recv_pd(+T: Nat, +pd: Nat, +D: Nat, +k: Nat, hp: {Nat.add(T, pd) == D : Nat}) ->
  {Nat.add(T, Nat.add(pd, k)) == Nat.add(D, k) : Nat}:
  Equal.trans(Nat, Nat.add(T, Nat.add(pd, k)), Nat.add(Nat.add(T, pd), k), Nat.add(D, k),
    Equal.sym(Nat, Nat.add(Nat.add(T, pd), k), Nat.add(T, Nat.add(pd, k)), N.add_assoc(T, pd, k)),
    C.cong_add_r(k, Nat.add(T, pd), D, hp))

# WRITTEN w = wp + d (w is a count the relay had): the page's in-flight bytes fall to pxp, where d + pxp = px
def written_px(+wp: Nat, +px: Nat, +sent: Nat, +d: Nat, +pxp: Nat, +w: Nat, hw: {Nat.add(wp, d) == w : Nat},
  hdx: {Nat.add(d, pxp) == px : Nat}, hC: {Nat.add(wp, px) == sent : Nat}) -> {Nat.add(w, pxp) == sent : Nat}:
  Equal.trans(Nat, Nat.add(w, pxp), Nat.add(Nat.add(wp, d), pxp), sent,
    C.cong_add_r(pxp, w, Nat.add(wp, d), Equal.sym(Nat, Nat.add(wp, d), w, hw)),
    Equal.trans(Nat, Nat.add(Nat.add(wp, d), pxp), Nat.add(wp, Nat.add(d, pxp)), sent,
      N.add_assoc(wp, d, pxp),
      Equal.trans(Nat, Nat.add(wp, Nat.add(d, pxp)), Nat.add(wp, px), sent,
        C.cong_add_l(wp, Nat.add(d, pxp), px, hdx),
        hC)))

# the page's window slack after the WRITTEN: pxp + (pz + d) == win
def written_pz(+px: Nat, +pz: Nat, +win: Nat, +d: Nat, +pxp: Nat, hdx: {Nat.add(d, pxp) == px : Nat},
  hD: {Nat.add(px, pz) == win : Nat}) -> {Nat.add(pxp, Nat.add(pz, d)) == win : Nat}:
  Equal.trans(Nat, Nat.add(pxp, Nat.add(pz, d)), Nat.add(Nat.add(pxp, pz), d), win,
    Equal.sym(Nat, Nat.add(Nat.add(pxp, pz), d), Nat.add(pxp, Nat.add(pz, d)), N.add_assoc(pxp, pz, d)),
    Equal.trans(Nat, Nat.add(Nat.add(pxp, pz), d), Nat.add(d, Nat.add(pxp, pz)), win,
      N.add_comm(Nat.add(pxp, pz), d),
      Equal.trans(Nat, Nat.add(d, Nat.add(pxp, pz)), Nat.add(Nat.add(d, pxp), pz), win,
        Equal.sym(Nat, Nat.add(Nat.add(d, pxp), pz), Nat.add(d, Nat.add(pxp, pz)), N.add_assoc(d, pxp, pz)),
        Equal.trans(Nat, Nat.add(Nat.add(d, pxp), pz), Nat.add(px, pz), win,
          C.cong_add_r(pz, Nat.add(d, pxp), px, hdx),
          hD))))

# the relay's count moves with WRITTEN the same way: w + pwp == wr
def written_pw(+wp: Nat, +pw: Nat, +wr: Nat, +d: Nat, +pwp: Nat, +w: Nat, hw: {Nat.add(wp, d) == w : Nat},
  hdp: {Nat.add(d, pwp) == pw : Nat}, hB: {Nat.add(wp, pw) == wr : Nat}) -> {Nat.add(w, pwp) == wr : Nat}:
  Equal.trans(Nat, Nat.add(w, pwp), Nat.add(Nat.add(wp, d), pwp), wr,
    C.cong_add_r(pwp, w, Nat.add(wp, d), Equal.sym(Nat, Nat.add(wp, d), w, hw)),
    Equal.trans(Nat, Nat.add(Nat.add(wp, d), pwp), Nat.add(wp, Nat.add(d, pwp)), wr,
      N.add_assoc(wp, d, pwp),
      Equal.trans(Nat, Nat.add(wp, Nat.add(d, pwp)), Nat.add(wp, pw), wr,
        C.cong_add_l(wp, Nat.add(d, pwp), pw, hdp),
        hB)))

# a send starts at the tail: the page's sent and tail move together with its accepted length
def start_pt(+sent: Nat, +pt: Nat, +tail: Nat, +len: Nat, hpt: {Nat.add(sent, pt) == tail : Nat}) ->
  {Nat.add(sent, Nat.add(pt, len)) == Nat.add(tail, len) : Nat}:
  Equal.trans(Nat, Nat.add(sent, Nat.add(pt, len)), Nat.add(Nat.add(sent, pt), len), Nat.add(tail, len),
    Equal.sym(Nat, Nat.add(Nat.add(sent, pt), len), Nat.add(sent, Nat.add(pt, len)), N.add_assoc(sent, pt, len)),
    C.cong_add_r(len, Nat.add(sent, pt), tail, hpt))

# ---- the buffer bound, from the invariants ----

# the grant the relay has is the window plus what was applied (gr + g1 = win + ti), and the applied
# grants are the grants issued (ti + g2 = T): then gr + (g1 + g2) = win + T
# the page holds (R - T) bytes: pd + pr is what was received and not taken, and T + (pd + pr) == R
def bound_hB(+T: Nat, +pd: Nat, +pr: Nat, +D: Nat, +R: Nat, hpd: {Nat.add(T, pd) == D : Nat},
  hpr: {Nat.add(D, pr) == R : Nat}) -> {Nat.add(T, Nat.add(pd, pr)) == R : Nat}:
  Equal.trans(Nat, Nat.add(T, Nat.add(pd, pr)), Nat.add(Nat.add(T, pd), pr), R,
    Equal.sym(Nat, Nat.add(Nat.add(T, pd), pr), Nat.add(T, Nat.add(pd, pr)), N.add_assoc(T, pd, pr)),
    Equal.trans(Nat, Nat.add(Nat.add(T, pd), pr), Nat.add(D, pr), R,
      C.cong_add_r(pr, Nat.add(T, pd), D, hpd),
      hpr))

# THE BOUND ON WHAT THE PAGE HOLDS: the bytes received and not taken, pd + pr, satisfy
# (pd + pr) + (c2 + (g1 + g2)) == win + Cc, so they are at most win + Cc (the window, plus one chunk)

# The relay applies a grant of n: its credit's line moves to min(rd + win, gr + n), and the grant ghost g1
# (gr + g1 == ti) becomes sub(gr + n, min) + g1, so that gr' + g1' == ti + n.
def grant_g1(+rd: Nat, +gr: Nat, +win: Nat, +n: Nat, +ti: Nat, +g1: Nat, hg1: {Nat.add(gr, g1) == ti : Nat}) ->
  {Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.add(Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n))), g1))
    == Nat.add(ti, n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.add(Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n))), g1)),
    Nat.add(Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n)))), g1),
    Nat.add(ti, n),
    Equal.sym(Nat, Nat.add(Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n)))), g1),
      Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.add(Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n))), g1)),
      N.add_assoc(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n))), g1)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n)))), g1),
      Nat.add(Nat.add(gr, n), g1), Nat.add(ti, n),
      C.cong_add_r(g1, Nat.add(Nat.min(Nat.add(rd, win), Nat.add(gr, n)), Nat.sub(Nat.add(gr, n), Nat.min(Nat.add(rd, win), Nat.add(gr, n)))), Nat.add(gr, n),
        min_wit_r(Nat.add(rd, win), Nat.add(gr, n))),
      Equal.trans(Nat, Nat.add(Nat.add(gr, n), g1), Nat.add(Nat.add(gr, g1), n), Nat.add(ti, n),
        C.add_end(gr, n, g1),
        Equal.trans(Nat, Nat.add(Nat.add(gr, g1), n), Nat.add(ti, n), Nat.add(ti, n),
          C.cong_add_r(n, Nat.add(gr, g1), ti, hg1),
          {==}))))

# the relay's grant is at most the grants applied (gr + g1 == ti), and those are the grants issued
# (ti + g2 == WIN + T: the window at the start, then one grant for each byte taken), so gr + (g1 + g2) == WIN + T
def honest_u(+gr: Nat, +g1: Nat, +g2: Nat, +ti: Nat, +WT: Nat, hg1: {Nat.add(gr, g1) == ti : Nat},
  hg2: {Nat.add(ti, g2) == WT : Nat}) -> {Nat.add(gr, Nat.add(g1, g2)) == WT : Nat}:
  Equal.trans(Nat, Nat.add(gr, Nat.add(g1, g2)), Nat.add(Nat.add(gr, g1), g2), WT,
    Equal.sym(Nat, Nat.add(Nat.add(gr, g1), g2), Nat.add(gr, Nat.add(g1, g2)), N.add_assoc(gr, g1, g2)),
    Equal.trans(Nat, Nat.add(Nat.add(gr, g1), g2), Nat.add(ti, g2), WT,
      C.cong_add_r(g2, Nat.add(gr, g1), ti, hg1),
      hg2))

# THE BOUND ON WHAT THE PAGE HOLDS. The bytes received and not taken, pd + pr, and the relay's read
# slack c2 satisfy (pd + pr) + (c2 + (g1 + g2)) == WIN + Cc: the page holds at most WIN + Cc bytes
# (the read window, plus one chunk). WT is WIN + T, the grants issued.
def bound_held(+T: Nat, +pd: Nat, +pr: Nat, +D: Nat, +R: Nat, +gr: Nat, +c2: Nat, +g1: Nat, +g2: Nat,
  +WIN: Nat, +Cc: Nat, +ti: Nat, hpd: {Nat.add(T, pd) == D : Nat}, hpr: {Nat.add(D, pr) == R : Nat},
  hc2: {Nat.add(R, c2) == Nat.add(gr, Cc) : Nat}, hg1: {Nat.add(gr, g1) == ti : Nat},
  hg2: {Nat.add(ti, g2) == Nat.add(WIN, T) : Nat}) ->
  {Nat.add(Nat.add(pd, pr), Nat.add(c2, Nat.add(g1, g2))) == Nat.add(WIN, Cc) : Nat}:
  C.buffered_bound(T, Nat.add(pd, pr), R, gr, c2, Nat.add(g1, g2), WIN, Cc,
    hc2, honest_u(gr, g1, g2, ti, Nat.add(WIN, T), hg1, hg2), bound_hB(T, pd, pr, D, R, hpd, hpr))
