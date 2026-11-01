# Browser TCP

A page cannot open TCP connections, so this folder has a relay that opens them for the page, the
page's side of the protocol, and the effects that give a page's Bend program its TCP operations.

| File | What it is | How it is checked |
|------|------------|-------------------|
| `frame.bend` | The frame format as Bend code: encode, decode, completeness | `frame_proof.bend` (laws) |
| `frame_proof.bend` | Laws: a frame decodes to itself, and is complete | Bend's kernel: `bend frame_proof.bend` prints `ALL PROOFS CHECK` |
| `frame_arith.bend` | Euclid's identity for the division routine of the base library, from its invariant | the same checker |
| `frame_lists.bend` | List lemmas (append, take, drop) and `le` on sums | the same checker |
| `tcp_contract_proof.bend` | The arithmetic and invariants of the TCP effects: the send split and resume, the send window, the read credit and the bound on what the page holds (33 lemmas) | Bend's kernel: `bend tcp_contract_proof.bend` prints `ALL PROOFS CHECK` |
| `tcp_contract_false.bend` | A false claim, to show the checker rejects it | `bend tcp_contract_false.bend` must print `SOME PROOFS FAIL` |
| `core/tcp_transitions.bend` | The transitions the code calls: every change to a connection's counts (the page's `startSend`, frames, WRITTEN, takes and READs; the relay's SEND check, writes, DISCARD, READ and grants). Compiled to `core/tcp_transitions.mjs`, which `relay.ts` and `tcp_relay_client.js` import | `core/tcp_model.bend` and `test/model.test.ts` |
| `core/tcp_model.bend` | The proofs that the transitions keep the invariants (48 lemmas and their helpers, all checked, using the 33 of `tcp_contract_proof.bend`): see "The code, proven against its model" below | `bend core/tcp_model.bend` prints `ALL PROOFS CHECK` |
| `test/model.test.ts` | The compiled transitions compute the intended arithmetic; random protocol traces, with an adversarial page too, keep every invariant after every step; the committed `.mjs` is the compiler's output for the proven file | `bun test browser/test` (needs `bend` on the PATH) |
| `PROTOCOL.md` | The wire protocol: frames, operations, authentication and the origin, the windows and limits, errors | read it |
| `RELAY.md` | Running the relay for real use: the configuration, tokens, TLS, limits, the log, the checklist | read it |
| `DECISIONS.md` | The decisions, and their approval | read it |
| `relay/relay.ts` | The relay: a WebSocket server (Bun) that opens TCP connections, default-deny, with tokens, origins, TLS and limits | `test/relay*.test.ts`, `test/flow.test.ts` |
| `relay/config.ts` | The configuration: loaded and checked, every mistake named | `test/relay_safety.test.ts` |
| `relay/token.ts` | Makes a token for a user, and its digest for the configuration | `test/relay_safety.test.ts` |
| `relay/config.example.json` | The shape of a configuration (its placeholder digest is refused on purpose) | |
| `tcp_relay_client.js` | The page's side: `RelayTcp`, with callback calls for the effects and promises for JavaScript | `test/*.test.ts` |
| `vectors.bend` | Frames encoded by the Bend definitions | `test/frame_vectors.json` is its output |
| `tcp.bend` | The `WebTCP.*` declarations: Base's TCP signatures, each importing `effs/web_tcp.js` | `tests/decl_listen.bend`, the page programs |
| `effs/web_tcp.js` | The effects of `WebTCP.*`, over the page's relay | `test/web_tcp.test.ts` |
| `tests/web/*.bend.tpl` | Page programs (templates: the ports are filled in by the test) | `test/web_tcp.test.ts` |
| `test/relay.test.ts` | 12 tests over real TCP, with a token: echo, 300 KB both ways, default-deny (13), refused (111), end of stream, 20 connections, id reuse, the connection limit (24), protocol errors | `bun test browser/test` |
| `test/relay_safety.test.ts` | 17 tests: the configuration, the example's placeholder, a token from `token.ts`, the origin, AUTH first and wrong tokens, the authentication deadline, TLS (wss), /healthz, the connect rate, the connection caps, the session and upgrade caps, the byte rate, shutdown, and no token in the log | `bun test browser/test` |
| `test/support.ts` | The test token and origin, `PageSocket` (a WebSocket with the origin), `rawSocket` (authenticated), and the relay built from a checked configuration | used by the tests |
| `test/flow.test.ts` | Partial writes (a slow peer gets every byte), a dropped send reports exactly what was taken, the read window, EPIPE after a peer's close, the protocol rules for READ and freed ids | `bun test browser/test` |
| `test/errno.test.ts` | The page's failure texts are libc's `strerror` for their errnos, as the native effects give | `bun test browser/test` |
| `test/web_tcp.test.ts` | The page programs run under the Bend runtime, against the relay | `bun test browser/test` (needs the async runtime, below) |
| `test/preload.js` | Opens the page's relay before a program runs (`globalThis.bend_relay`) | used by the page program tests |
| `page/index.html`, `page/app.js` | A page: opens the relay, makes it `globalThis.bend_relay`, and runs the program's `page_main`. Its output goes to `#bend-output` | `test/page.test.ts` |
| `test/page.test.ts`, `test/page_e2e.cjs` | Builds the page with the Bend CLI, serves it, and runs it in Chromium (Playwright): the program's output must reach the page | `bun test browser/test` (needs Node and the Playwright Chromium) |

## Run the tests

    cd bend-tls
    bun test browser/test                # the relay, the flow rules, the errno texts, the page programs
    bend browser/frame_proof.bend        # ALL PROOFS CHECK

    bun browser/relay/token.ts alice                                # a token for a user
    bun browser/relay/relay.ts <config.json>                        # the relay (RELAY.md)

The page programs and the page need the Bend toolchain with the patch (below), at the path in
`BEND_MAIN`. Make it with `sh patches/bend/apply.sh <dir>` on the branch `browser-async-scheduler`,
then:

    BEND_MAIN=<dir>/bend2/main.ts bun test browser/test

The default `BEND_MAIN` is `/tmp/claude-0/src/bend-async/bend2/main.ts`. Without a Bend toolchain
the page tests are skipped; the page's end-to-end test also needs Node and Playwright's Chromium.

## What is proven, and what is tested

Proven by Bend's kernel (the checker reads the definitions, not a model of them):
- the division identity `(n div 256)*256 + (n mod 256) == n`, from the long-division routine
  the base library uses;
- a frame decodes to the frame that was encoded, followed by any bytes, for payloads of fewer
  than 65536 bytes;
- a complete frame is recognised as complete.

A false version of the round-trip law is rejected by the checker (checked when this was built).

Tested, not proven: the relay, the page's client, the effects and the sockets. The Bend encodings
of sample frames (`frame_vectors.json`) match the JavaScript encoder byte for byte.

## The contract, proven (tcp_contract_proof.bend)

`bend tcp_contract_proof.bend` checks the arithmetic and invariants that the TCP effects rely on,
in the model below. Each law is an equation over naturals and lists, with the relay's counts as
witnesses, so no statement needs an impossible case.

| Law | The JavaScript it stands for | What it says |
|-----|------------------------------|--------------|
| `off`, `sub_add` | `from(w) = Math.max(0, w - start)` in `web_tcp.js` | a count `start + k` is at offset `k` in the send |
| `take_drop` | `bytes.subarray(from)` in `wt_send` | what the relay took, then what is left, is the whole send |
| `resume_stream`, `resume_len`, `resume_pos` | the resend after a `Wait` | nothing is lost or sent twice: the resend has exactly the bytes not taken, and the position where it starts plus its length is the send's end |
| `ready_taken`, `ready_rest` | the `left >= bytes.length` test | past the end of the send, all the data was taken and none is left |
| `pump_keeps`, `written_keeps`, `relay_accepts` | the window in `pump` and the relay's check for a SEND past `SEND_WINDOW` | the page's in-flight bytes stay within the window after a send and after a WRITTEN, and the relay accepts every send a page makes within its window |
| `read_keeps`, `grant_keeps`, `clamp_keeps`, `credit_le` | the read credit in `relay.ts` (`READ`, the clamp, the pause) | the relay reads no further ahead than the page's grant plus one chunk, and its credit is at most the window |
| `honest_A`, `honest_B` | the grants of an honest page | the grant stays the window plus what the page took, through a clamp |
| `buffered_bound` | the bound on what a page holds | the page holds at most `READ_WINDOW` plus one chunk of unread bytes |

Assumptions the proof takes as given: the chunk size `C` (the largest read from the socket) is a
parameter, and its value is the socket's, not proven; the relay's guard for reading is weaker than its
code (`R <= G` where the code checks `credit > 0`), so the proof covers the code.

**Not proven:**
- That the JavaScript computes these formulas. The correspondence above is by reading the code; the
  tests in `test/` check its behaviour, not the formulas.
- The relay as a whole: the order of frames, DISCARD and CLOSE together, and the WebSocket. The laws
  hold for each step; the claim that every interleaving of steps keeps them is not checked.
- Progress: that a send completes or a read returns. The laws say nothing about liveness.
- Timing: whether a `try_` call answers Ready or Wait before its deadline. The laws give the shape of
  each answer for the relay's count, not when it arrives.
- The Lean recheck (`--verdict`) is run for every proof file (see "The Lean recheck" below); its result
  is that the kernel accepts each file, and the false claim is rejected.

## The page's TCP operations

`tcp.bend` declares the operations of a page build under the names `WebTCP.*`, with Base's TCP
signatures. A page program imports it and calls `WebTCP.connect` where a native program calls
`TCP.connect`; the native declarations are untouched. Each declaration imports `effs/web_tcp.js`,
and none imports C, so a native build of a page program stops with "no .c import".

| Operations | Behaviour in a page |
|------------|---------------------|
| `connect` | opens through the relay; the relay's refusals and denials come back as errnos (111, 13, ...) |
| `send`, `send_bytes`, `recv`, `recv_bytes`, `close` | as the native ones, over the relay |
| `try_send`, `try_send_bytes`, `try_recv`, `try_recv_bytes` | a deadline: `Wait` carries the bytes not taken, or nothing for a receive |
| `listen`, `accept`, `try_accept`, `close_listener` | answer EOPNOTSUPP (95): a page cannot accept connections |

What the effects do about the points the native contract calls out (Base's TCP comments):

- **Sent means taken by the kernel**, here by the relay's socket: a send completes on WRITTEN, not
  when the peer reads it.
- **A failed or timed-out send returns the exact unsent bytes.** The relay's count says how many
  bytes it took; a dropped send (DISCARD) is final, and the rest is given back as a List of bytes.
  A String send encodes UTF-8 once, so the rest may stop inside a character: resume with
  `send_bytes`, as Base says.
- **A receive String decodes each read on its own**, as the native one does.
- **Flow control:** a page holds at most 128 KB of unsent data per connection, and the relay reads
  from a socket only while the page has granted credit (128 KB ahead of its reads).
- **Half-close** is not in the contract, so the page has none. A send after the peer has closed fails
  with EPIPE (or ECONNRESET, when the reset arrives first), as native.
- **Failure texts** are libc's `strerror` for the errno, as in the native build (checked by
  `test/errno.test.ts` against this host's libc).

Timing: a try_ call answers as soon as the relay's answer comes back, so a send that completes
within its deadline may still answer `Wait` if the answer arrives after the deadline; the bytes it
reports are exact in either case.

## The asynchronous scheduler (a patch, on its own branch)

The Bend runtime change is on the branch `browser-async-scheduler` of this repository, as
`patches/bend/0001-…patch` on bendlang/bend `9d514f3`, with `patches/bend/apply.sh` to apply it to a
fresh clone. It lets a program wait on an event that is not a file descriptor, such as a WebSocket
message or a host timer, without blocking the host's event loop: an external wait parks with no fd,
and its event calls `io_notify`; a notice re-checks every external wait. A nested run keeps the
blocking poll. The patch also makes the runtime host-neutral and adds `page_main` to page modules.
Approved for use from that branch (`DECISIONS.md`); not proposed upstream.

A wait that no event will ever complete hangs the program under Bun (the process stays alive).

## A page

`page/index.html` and `page/app.js` are a page. The build is the Bend CLI's page bundle, from the
patched toolchain (the installed `bend` does not have the scheduler):

    bun <dir>/bend2/main.ts browser/page/index.html -o dist

The page imports a program (`page/program.bend`), opens the relay at `?relay=wss://...`, with the
token its server puts in `<meta name="bend-relay-token">`, sets `globalThis.bend_relay` to it, and
runs the program's `page_main()` (its `main`, through the scheduler). The page is served from one
of the relay's `origins`. The page's output goes to `#bend-output`; `body[data-exit]` holds the exit code when
the program has finished.

What changed in the runtime for a page (the patch above): no Node or Bun module is named in the
code (`io_node` looks them up when used), so the bundler resolves nothing it cannot. A page's output
goes to the page, not a file descriptor, and a system call throws, since a page has none. The
`page_main` export is added to the module only when the program has a `main`.

## Not done

- **Output and effects outside TCP.** A page's output is text (`#bend-output`, or
  `globalThis.bend_stdout`). The file, process and environment effects are not in a page: a program
  that calls them fails there.
- Listen and accept are not in the protocol.
- The relay is ready for real use as `RELAY.md` describes; what it does not do is listed there, and
  the open decisions are in `DECISIONS.md`.

## The code, proven against its model

The relay and the page's client do not do the arithmetic of their counts themselves. Every change to a
count that the invariants talk about is a call to a function of `core/tcp_transitions.bend`, compiled to
`core/tcp_transitions.mjs`. The lemmas in `core/tcp_model.bend` are about those same functions, so what
the code executes is what the proofs cover, given the compiler and the assumptions below.

The invariants, and the lemma for each transition that keeps each one, are in the header of
`core/tcp_model.bend`. In short, after every transition:

- the page never frames more than its window (`sent - wp <= WIN`), and what it has framed is within what
  it has accepted (`sent <= tail`);
- the relay's queue never exceeds the window, and a SEND from a conforming page always passes the relay's
  test (`fits_zero`);
- the counts the page and the relay keep agree, up to the bytes in flight and the bytes dropped by a
  DISCARD (`wp <= wr`, `wr + q + f == sent`);
- the relay's credit is at most the window, whatever the page asks for (the clamp), and the relay reads
  no further ahead than the grant plus one chunk;
- for an honest page, what the page holds is at most the window plus one chunk.

Assumptions about the environment. The code checks each one at run time and fails the connection closed
(an errno of 5 or 22) if it is broken; none is assumed silently:

1. The socket takes at most the bytes it was given (`write` returns no more than the chunk).
2. The socket delivers data only while the relay's credit is positive (Bun's `pause` is honoured).
3. A chunk is at most 1 MiB (`CHUNK_MAX`, the model's `C`).
4. The WebSocket and the TCP socket deliver in order (the FIFO channels of the model).
5. The page does not frame while a DISCARD is pending (the page's `pump` checks it).
6. The page's own bound (what it holds) assumes an honest page: a page that asks for more than it takes
   only fills its own memory; the relay's bounds hold for it regardless.
7. The relay's WRITTEN counts are not ahead of the bytes it took, and the page trusts them.

Not proven:
- That the compiler and the JavaScript runtime are correct (the proofs are about Bend's definitions;
  the test checks that the committed `.mjs` is the compiler's output and computes the intended arithmetic).
- The timing and liveness of anything: that a send completes, that a read returns, when a `try_` answers.
- Bun's socket and WebSocket behaviour beyond the assumptions above, and the glue (the event handlers
  that call the model), which is tested, not proven.
- The Lean recheck is done (see below), but it checks Bend's kernel's proofs, not the compiler.

## The Lean recheck

`bend <file>.bend --verdict` checks the file with Bend's own checker, then rechecks every proof with
BendTT, the kernel that is written in Lean (`bendtt.lean`). The kernel is built once, with Lean 4.34.0,
and cached in `~/.bend/bendtt/`.

The Lean toolchain comes from GitHub, not from the Lean project's own download host: that host is
refused by this sandbox's network policy, and GitHub is not. The archive is the release asset
`lean-4.34.0-linux.tar.zst` from github.com/leanprover/lean4 (580 MB). It was unpacked into
`~/.elan/toolchains/leanprover--lean4---v4.34.0/`, where Bend looks for it. Its checksum was not verified
against a published value, so the trust is in the TLS connection to GitHub and the release itself.

Results (`--verdict`, Lean 4.34.0):

| File | Result |
|------|--------|
| `frame_proof.bend`, `frame_arith.bend` | ALL PROOFS CHECK (kernel accepts) |
| `tcp_contract_proof.bend` | ALL PROOFS CHECK |
| `core/tcp_transitions.bend`, `core/tcp_model.bend` | ALL PROOFS CHECK |
| `tcp_contract_false.bend` | SOME PROOFS FAIL (the claim is false; rejected before the kernel) |

The kernel's check is an independent recheck of the proofs, not of the code generator: the JavaScript
the relay runs is still produced by Bend's compiler, which no check here covers.
