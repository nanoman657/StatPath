# Induction over the composed relay model (work in progress)

Lean 4.34.0 (no Mathlib). The development proves, for the composed page/relay system in the timed (clock)
model, that the invariant `Inv` (structure in `ind_defs.lean`) holds in every reachable state. The window
claim (`WQ`: a connection's queued bytes plus the SEND frames in flight stay within `SEND_WINDOW`) follows
from `Inv`. The model itself is `../Relay.lean` (unchanged here); `timed_section.lean` is the clocked
composition, copied from the session's scratch model.

## Status

`Inv` has 45 fields (the four WRITTEN fields are proved at every site): the 24 proved earlier, the ten ordering fields (`failNone`, `closedNone`, `closedClosing`,
`closedOrd`, `closeClosing`, `closedNoConn`, `openRel`, `okOpen`, `okNoDisc`, `discRel`), `closingNone`,
`closedNoClose`, `failOrd`, and `genFun` (a sequence number belongs to one generation only). `failOrd` says that after a FAIL of an id, the only frames of that id still queued are
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
- The page's DATA and EOF frames (`inv_tDoPage_data`, `inv_tDoPage_eof`, `ind_wake.lean`): the wake loop is an induction
  over the readers (`wake_loop_inv`), and `wake_spec` gives the new connection's fields.
- The page's OK frame (`inv_tDoPage_ok`, `ind_ok.lean`): the page's connection opens, one READ is queued.
- The page's calls: `inv_tPageConnect`, `inv_tPageClose`, `inv_tPageDiscard`, `inv_tPageRecv`, `inv_tPageSend`.
- The page's frames (`ind_frames.lean`): an ignored frame (`inv_tDoPage_ignored`, via `inv_shrink`), CLOSED
  (`inv_tDoPage_closed`), FAIL (`inv_tDoPage_fail`).

Done since the last status: the four WRITTEN-related fields (`discOnce`, `discUniq`, `wrMono`, `wrOrd`) are proved
at every construction site, including `inv_flush` and `inv_env_gen`. The flush and environment steps need the count
facts, which are proved in `ind_flush.lean` (`flushIds_spec`, `flushIds_outs_uniq`, `flushOne_outs_pre`), `ind_tick.lean`
(`tickK_spec`, `tick_outs_uniq`) and `ind_envsock.lean` (`sockStep_wr_ge`, `sockStep_one_wr`, `stepK_sock_wr`,
`stepK_sock_one_wr`).
- The WRITTEN frame (`ind_pump.lean`, `ind_written.lean`): `pump_spec` (the SEND entries the pump queues sum to the increase
  of `sent`, and `PInv` is kept) and `wr_frame_spec` (the frame's connection, its SEND entries and the discard case).
  Still to do: `inv_written_core`, the 45 fields over the frame, and its page-frame wrapper.
- The relay's queue steps (`Client.doRelay`: CONNECT, SEND, DISCARD, READ, CLOSE), the dispatch over all transitions,
  the reachability induction, and the final theorem (reachable implies `WQ`, so the relay's window check never fires).

The candidate fields were checked by the bounded search (`inv_checks.lean`, `search_main.lean`) to depth 9 (23,387
states). The depth-11 run is not committed.

## Build

    python3 build_ind.py ind_defs.lean ind_relay.lean ind_flush.lean ind_transport.lean ind_tick.lean \
      ind_env.lean ind_sock.lean ind_envsock.lean ind_invsock.lean ind_envcomp.lean ind_pagecall.lean ind_frames.lean \
      ind_ok.lean ind_wake.lean ind_pump.lean ind_written.lean
    lean Ind.lean

The bounded search (a check of candidate invariants over the composed model, not a proof):

    python3 build_search.py && lean --run Search.lean 9

`Ind.lean` and `Search.lean` are build outputs and are not committed.
