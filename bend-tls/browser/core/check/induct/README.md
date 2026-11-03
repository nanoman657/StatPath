# Induction over the composed relay model (work in progress)

Lean 4.34.0 (no Mathlib). The development proves, for the composed page/relay system in the timed (clock)
model, that the invariant `Inv` (structure in `ind_defs.lean`) holds in every reachable state. The window
claim (`WQ`: a connection's queued bytes plus the SEND frames in flight stay within `SEND_WINDOW`) follows
from `Inv`. The model itself is `../Relay.lean` (unchanged here); `timed_section.lean` is the clocked
composition, copied from the session's scratch model.

## Status

`Inv` has 36 fields: the 24 proved earlier, the ten ordering fields (`failNone`, `closedNone`, `closedClosing`,
`closedOrd` (now strict: nothing of an id follows a CLOSED of that id), `closeClosing`, `closedNoConn`, `openRel`,
`okOpen`, `okNoDisc`, `discRel`), and two more (`closingNone`, `closedNoClose`). `FwdEv` forbids a CONNECT or a
CLOSE behind a CLOSE of the same id.

Proved, no `sorry`:
- `inv_init`; the clock steps (`inv_flush`, `inv_tick`); the environment's socket events (`inv_env_gen`,
  `inv_sock`, `inv_env`), using `stepK_sock_fail_fact` and `stepK_sock_ok_fact` (in `ind_envsock.lean`).
- The page's calls: `inv_tPageConnect`, `inv_tPageClose` (needs `fixed`), `inv_tPageDiscard`, `inv_tPageRecv`,
  `inv_tPageSend` (the send's window argument uses `pump_props`, `pump_shape`).
- The page's frames, the first ones (`ind_frames.lean`): a frame the page ignores (`inv_tDoPage_ignored`, via
  `inv_shrink`), and a CLOSED frame (`inv_tDoPage_closed`, via `inv_closed_core`).

Not yet proved:
- The page's frames FAIL, OK, DATA, EOF, WRITTEN (flag 0 and 1). FAIL needs one more ordering field: after a FAIL
  of an id, no frame of that id is queued (`failOrd`, the same shape as `closedOrd`); the other frames append READ
  frames (ok, data, eof) or SEND frames (written).
- The relay's queue steps (`Client.doRelay`): CONNECT, SEND, DISCARD, READ, CLOSE, and the closed relay.
- The reachability induction and the final theorem (reachable implies `WQ`, so the relay's window check never
  fires for a page SEND).

The candidate fields were checked by the bounded search (`inv_checks.lean`, `search_main.lean`) to depth 9 (23,387
states, no violation): the ones above, and `closingNone`, `closedNoClose`, the strict `closedOrd`. The depth-11 run
is not committed.

## Build

    python3 build_ind.py ind_defs.lean ind_relay.lean ind_flush.lean ind_transport.lean ind_tick.lean \
      ind_env.lean ind_sock.lean ind_envsock.lean ind_invsock.lean ind_envcomp.lean ind_pagecall.lean
    lean Ind.lean

The bounded search (a check of candidate invariants over the composed model, not a proof):

    python3 build_search.py && lean --run Search.lean 9

`Ind.lean` and `Search.lean` are build outputs and are not committed.
