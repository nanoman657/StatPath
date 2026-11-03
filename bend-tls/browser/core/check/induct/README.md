# Induction over the composed relay model (work in progress)

Lean 4.34.0 (no Mathlib). The development proves, for the composed page/relay system in the timed (clock)
model, that the invariant `Inv` (structure in `ind_defs.lean`) holds in every reachable state. The window
claim (`WQ`: a connection's queued bytes plus the SEND frames in flight stay within `SEND_WINDOW`) follows
from `Inv`. The model itself is `../Relay.lean` (unchanged here); `timed_section.lean` is the clocked
composition, copied from the session's scratch model.

## Status

`Inv` has 40 fields: the 24 proved earlier, the ten ordering fields (`failNone`, `closedNone`, `closedClosing`,
`closedOrd`, `closeClosing`, `closedNoConn`, `openRel`, `okOpen`, `okNoDisc`, `discRel`), `closingNone`,
`closedNoClose`, and `failOrd`. `failOrd` says that after a FAIL of an id, the only frames of that id still queued are
CLOSED frames. (The first statement, with no frame of the id at all, was refuted by the bounded search: a CLOSE after
a socket failure queues a CLOSED behind the FAIL. The corrected statement passes depth 9.) Three more, for the OK frame:
`connPend` (while a CONNECT of an id waits in the relay's queue, the page's queue holds no frame of that id; the relay
consumes its queue in order, and the page issues a CONNECT only when it has no connection and is not closing),
`okRel` (an OK frame finds its id's relay connection gone, or open with the frame's generation), and `okOrd` (no two
OK frames of an id are queued). All three hold through every clock step, environment socket event, page call and page
frame proved so far (`sockStep_ok_post`, `stepK_sock_ok_post`, `sockStep_okpw`, `stepK_sock_okpw`).

Proved, no `sorry`:
- `inv_init`; the clock steps (`inv_flush`, `inv_tick`); the environment's socket events (`inv_env_gen`,
  `inv_sock`, `inv_env`), using `stepK_sock_fail_fact`, `stepK_sock_ok_fact`, and `stepK_sock_outs_pw` (the
  socket step's frames are ordered so a FAIL is last).
- The page's calls: `inv_tPageConnect`, `inv_tPageClose`, `inv_tPageDiscard`, `inv_tPageRecv`, `inv_tPageSend`.
- The page's frames (`ind_frames.lean`): an ignored frame (`inv_tDoPage_ignored`, via `inv_shrink`), CLOSED
  (`inv_tDoPage_closed`), FAIL (`inv_tDoPage_fail`).

Not yet proved:
- The page's frames OK (the page's connection becomes open; with `okOpen` and `okOrd` this keeps the page's open state
  consistent), DATA, EOF, WRITTEN (flag 0 and 1). DATA and EOF need a spec of the page's `wake` (a loop over the readers). WRITTEN needs the pump and
  the discard reset.
- The relay's queue steps (`Client.doRelay`): CONNECT, SEND, DISCARD, READ, CLOSE, and the closed relay.
- The reachability induction and the final theorem (reachable implies `WQ`, so the relay's window check never
  fires for a page SEND).

The candidate fields were checked by the bounded search (`inv_checks.lean`, `search_main.lean`) to depth 9 (23,387
states). The depth-11 run is not committed.

## Build

    python3 build_ind.py ind_defs.lean ind_relay.lean ind_flush.lean ind_transport.lean ind_tick.lean \
      ind_env.lean ind_sock.lean ind_envsock.lean ind_invsock.lean ind_envcomp.lean ind_pagecall.lean ind_frames.lean
    lean Ind.lean

The bounded search (a check of candidate invariants over the composed model, not a proof):

    python3 build_search.py && lean --run Search.lean 9

`Ind.lean` and `Search.lean` are build outputs and are not committed.
