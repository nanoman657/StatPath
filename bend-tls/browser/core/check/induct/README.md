# Induction over the composed relay model (work in progress)

Lean 4.34.0 (no Mathlib). The development proves, for the composed page/relay system in the timed (clock)
model, that the invariant `Inv` (structure in `ind_defs.lean`) holds in every reachable state. The window
claim (`WQ`: a connection's queued bytes plus the SEND frames in flight stay within `SEND_WINDOW`) follows
from `Inv`. The model itself is `../Relay.lean` (unchanged here); `timed_section.lean` is the clocked
composition, copied from the session's scratch model.

## Status

Proved, no `sorry`:
- `inv_init`: the initial state satisfies `Inv`.
- The clock steps: `inv_flush` (flush), `inv_tick` (time passes); the environment's socket events:
  `inv_env_gen`, `inv_sock`, `inv_env`.
- The page's calls: `inv_tPageConnect`, `inv_tPageClose` (needs `fixed`), `inv_tPageDiscard`,
  `inv_tPageRecv`, `inv_tPageSend` (the send's window argument uses `pump_props`, `pump_shape`).

Not yet proved:
- The page's frame steps (CLOSED, FAIL, OK, DATA, EOF, WRITTEN with flag 0 and 1, WSCLOSE). These are
  `Client.doPage`; the frames they append are READ frames (ok, data, eof) and SEND frames (written).
- The relay's queue steps (`Client.doRelay`): CONNECT, SEND, DISCARD, READ, CLOSE, and the closed relay.
- The reachability induction and the final theorem (reachable implies `WQ`, so the relay's window check
  never fires for a page SEND).

Fields the frame and queue steps need, beyond the 24 in `Inv`. Each passes the bounded search (`inv_checks.lean`,
`search_main.lean`) to depth 9 (23,387 states, no violation). None is in `Inv` or proved yet:
- `failNone`, `closedNone`: a FAIL or CLOSED frame in the page's queue finds the relay's connection gone.
- `closedClosing`: a CLOSED frame in the page's queue means its id's page is closing. `closeClosing`: a queued
  CLOSE means its id's page is closing.
- `closedOrd`: after a CLOSED frame of an id, the queue has no other frame of that id (except a CLOSED).
- `closedNoConn`: a CLOSED frame in the page's queue means no CONNECT of its id is queued. This needs the
  barrier to forbid a CONNECT behind a CLOSE of the same id (`fwdB` in `inv_checks.lean` already has it).
- `openRel`: an open page connection has an open relay connection. `okOpen`: an OK frame (page not closing)
  finds its page connection not open. `okNoDisc`: such an OK frame finds no DISCARD of its id queued.
- `discRel`: a queued DISCARD finds its id's relay connection gone, or its page connection open, or the page closing.

Proving these also needs the socket spec (`SockSpec` in `ind_sock.lean`) to say that a FAIL frame leaves the relay
connection gone and an OK frame comes only from a connection that was not open. It says neither today.

## Build

    python3 build_ind.py ind_defs.lean ind_relay.lean ind_flush.lean ind_transport.lean ind_tick.lean \
      ind_env.lean ind_sock.lean ind_envsock.lean ind_invsock.lean ind_envcomp.lean ind_pagecall.lean
    lean Ind.lean

The bounded search (a check of candidate invariants over the composed model, not a proof):

    python3 build_search.py && lean --run Search.lean 9

`Ind.lean` and `Search.lean` are build outputs and are not committed.
