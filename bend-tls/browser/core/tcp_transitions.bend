# tcp_transitions.bend: the state transitions of a browser TCP connection, the functions that the relay
# (relay.ts) and the page's client (tcp_relay_client.js) call for every change to a count the invariants
# talk about. The lemmas about them are in tcp_model.bend.
#
#   bend tcp_transitions.bend -o tcp_transitions.mjs     the JavaScript the code imports
#
# The page keeps: tail (bytes accepted by startSend), sent (SEND bytes framed), wp (the relay's written
# count as the page last saw it), taken (bytes given to the program, each one granted to the relay by a READ),
# recvd (DATA bytes received). The relay keeps: wr (bytes the socket took), q (SEND bytes queued), rd (bytes
# read from the socket), gr (the credit the page granted, clamped to the window).
import Base

# ---- the transitions the code calls ----

# the page accepts a send of len bytes
def pg_start(+tail: Nat, +len: Nat) -> Nat:
  Nat.add(tail, len)

# the bytes of the next SEND frame: at most MAX_BODY, the window's slack, and the bytes left to send
def pg_frame_n(+sent: Nat, +wp: Nat, +win: Nat, +tail: Nat, +mx: Nat) -> Nat:
  Nat.min(mx, Nat.min(Nat.sub(win, Nat.sub(sent, wp)), Nat.sub(tail, sent)))

def pg_sent(+sent: Nat, +n: Nat) -> Nat:
  Nat.add(sent, n)

# the bytes the program takes: at most max, and no more than were received and not yet taken
def pg_take_n(+taken: Nat, +recvd: Nat, +mx: Nat) -> Nat:
  Nat.min(mx, Nat.sub(recvd, taken))

def pg_taken(+taken: Nat, +n: Nat) -> Nat:
  Nat.add(taken, n)

def pg_recv_data(+recvd: Nat, +k: Nat) -> Nat:
  Nat.add(recvd, k)

# the room the relay has for a SEND: win - q
def rl_room(+win: Nat, +q: Nat) -> Nat:
  Nat.sub(win, q)

# the relay's test for a SEND of n bytes: 0 when n fits in the room, else more than 0
def rl_over(+n: Nat, +room: Nat) -> Nat:
  Nat.sub(n, room)

def rl_queue(+q: Nat, +n: Nat) -> Nat:
  Nat.add(q, n)

def rl_written(+wr: Nat, +m: Nat) -> Nat:
  Nat.add(wr, m)

def rl_unqueue(+q: Nat, +m: Nat) -> Nat:
  Nat.sub(q, m)

def rl_read(+rd: Nat, +k: Nat) -> Nat:
  Nat.add(rd, k)

# the credit after a READ of n: the grant, clamped so that it never runs past the window
def rl_grant(+rd: Nat, +gr: Nat, +win: Nat, +n: Nat) -> Nat:
  Nat.min(Nat.add(rd, win), Nat.add(gr, n))

