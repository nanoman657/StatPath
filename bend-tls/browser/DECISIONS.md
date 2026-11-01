# Decisions

Each decision with the reason it was made, and whether it is approved.

## The Bend runtime patch

- **Where it lives:** the branch `browser-async-scheduler` of this repository, as a patch on
  bendlang/bend at `9d514f3bb0d77524fcaa652645c902e4524eb838`, with a script that applies it to a
  fresh clone (`patches/bend/apply.sh`). Not proposed upstream.
- **Why:** the browser TCP effects and the page runtime need the scheduler and the host-neutral I/O
  the patch adds; the installed toolchain has neither.
- **Approved:** nanoman657, the repository owner, 2026-11-01, for use from that branch.

## The relay

Approved for real use, with the design below, by nanoman657, 2026-11-01. Each item is a decision
the relay's code and tests carry out (see `RELAY.md` and `PROTOCOL.md`).

| Decision | Reason |
|----------|--------|
| Authentication is mandatory: the first frame is AUTH, with a token the relay has the SHA-256 of | A relay with no authentication lets anyone reach the destinations it allows; hashes mean a leaked configuration does not leak tokens |
| The token travels in a frame, not in the URL | A URL is written to proxy and server logs |
| An allowed origin is required, exactly | Stops other sites from using the relay with a user's token |
| wss:// is required to listen beyond loopback | A relay beyond the machine would carry plaintext for the users |
| The example configuration is refused until a real token replaces its placeholder | A copied example must not run with a known digest |
| Default-deny destinations stay, with the allowlist in the operator's hands | The operator decides where the relay may connect; the relay is not a general proxy |
| Limits: connects per second, connections per WebSocket and in total, bytes per second, sessions, upgrades per address, send buffer, idle WebSockets | Bound the cost of one user and of the whole relay; defaults are in `relay/config.ts` |
| Byte limit delays rather than fails | A page should slow down, not lose its connection, when it is over its share |
| Logs name the user, origin, address and destination; never tokens or data | Operators need to know who connected where; tokens and data are not theirs to keep |
| No per-user destination lists, and no multi-tenant isolation beyond tokens and limits | Not needed for one operator's users; a second trust domain gets its own relay |

## Open for the owner

- Whether to put the relay behind a TLS-terminating proxy (which changes the client address the
  upgrade limit sees; see `RELAY.md`).
- Whether a second token for the same user, or a rotation procedure, is needed before the relay has
  users other than the owner.
