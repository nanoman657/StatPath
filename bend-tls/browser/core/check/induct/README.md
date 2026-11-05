# Induction over the composed relay model

Lean 4.34.0 (no Mathlib). The development proves, for the composed page/relay system in the timed (clock)
model, that the invariant `Inv` (structure in `ind_defs.lean`, 52 fields) holds in every reachable state, and that
the window claim holds in every reachable state. The model itself is `../Relay.lean` (unchanged here);
`timed_section.lean` is the clocked composition, copied from the session's scratch model.

## Status

Every statement below is in the monolith build (`python3 build_ind.py ...` then `lean Ind.lean`): exit 0, no
`sorry`.

- `inv_init`: the start (the fixed page client, `TSys.init true cps bps`) satisfies `Inv`.
- Every transition keeps `Inv` (`inv_step`, `TStep` in `ind_step.lean`): the five page calls
  (`inv_tPageConnect`, `inv_tPageClose`, `inv_tPageDiscard`, `inv_tPageRecv`, `inv_tPageSend`, `ind_pagecall.lean`);
  the page's frames (`inv_tDoPage`, through `inv_tDoPage_head`, over the OK, DATA, EOF, WRITTEN, FAIL, CLOSED and
  ignored frames); the relay's head event (`inv_tDoRelay`, over CONNECT, SEND, DISCARD, READ and CLOSE; a DENY or a
  socket event is not queued, by `noDeny`); the environment's socket events (`inv_env`); and the clock (`inv_tick`,
  `inv_flush`).
- `reach_inv` (`ind_step.lean`): every state reachable from the start, by `TReach`, satisfies `Inv` and keeps the
  page's fixed flag (`ind_fixed.lean` shows each page operation and each transition keeps the flag).
- The window claim (`ind_step.lean`): `window_queue`, for every connection, `queued + qs <= SEND_WINDOW` (the
  connection's queued bytes plus the SEND frames in the relay's queue for its id), and `window_head`, the head SEND of
  an id is within its connection's window, so the relay's window check does not fire. Both hold in every reachable
  state.

The relay's queue steps are in `ind_relayq.lean` (the generic keep step, READ), `ind_relayclose.lean` (CLOSE),
`ind_relaydisc.lean` (DISCARD), `ind_relaysend.lean` and `ind_relaysendf.lean` (SEND, successful and failed),
`ind_sendstep.lean` and `ind_sendtdo.lean` (the SEND helpers and dispatch), and `ind_connect.lean` (CONNECT, with the
keep and create steps). `connAux` (`ind_defs.lean`) is the field that CONNECT needed: a queued CONNECT has a positive
sequence number, and a queued WRITTEN frame's generation is below the relay's next generation.

Scope, and what is not covered:
- Out of scope: the theorems are for the fixed page client (`TSys.init true`) only. The unfixed mode
  (`TSys.init false`), which `Search.lean` also explores, is not proven and is not part of the window claim.
- The window claim is the relay's window check only. The cap check (FAIL 27, when the written bytes plus the queued
  and sent bytes pass the cap) is not part of it, and no theorem states a cap assumption.
- The bounded search (`Search.lean`, `iInv18`, depth 9) was rerun after `connAux` was added: 23,387 states, no violation.
- The model is the timed composition in `timed_section.lean`; the JavaScript relay is checked against it by the tests
  (`core/check/relay_conformance.test.ts`), not proven.

## Build

    python3 build_ind.py ind_defs.lean ind_relay.lean ind_flush.lean ind_transport.lean ind_tick.lean \
      ind_env.lean ind_sock.lean ind_envsock.lean ind_invsock.lean ind_envcomp.lean ind_pagecall.lean ind_frames.lean \
      ind_ok.lean ind_wake.lean ind_pump.lean ind_written.lean ind_wcore.lean ind_relayq.lean ind_relayclose.lean ind_relaydisc.lean ind_relaysend.lean \
      ind_relaysendf.lean ind_sendstep.lean ind_sendtdo.lean \
      ind_connect.lean ind_fixed.lean ind_step.lean
    lean Ind.lean

The bounded search (a check of candidate invariants over the composed model, not a proof):

    python3 build_search.py && lean --run Search.lean 9

`Ind.lean` and `Search.lean` are build outputs and are not committed.
