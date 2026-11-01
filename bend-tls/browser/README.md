# Browser TCP (in progress)

A page cannot open TCP connections, so this folder has a relay that opens them for the page, the
page's side of the protocol, and the effects that give a page's Bend program its TCP operations.

| File | What it is | How it is checked |
|------|------------|-------------------|
| `frame.bend` | The frame format as Bend code: encode, decode, completeness | `frame_proof.bend` (laws) |
| `frame_proof.bend` | Laws: a frame decodes to itself, and is complete | Bend's kernel: `bend frame_proof.bend` prints `ALL PROOFS CHECK` |
| `frame_arith.bend` | Euclid's identity for the division routine of the base library, from its invariant | the same checker |
| `frame_lists.bend` | List lemmas (append, take, drop) and `le` on sums | the same checker |
| `PROTOCOL.md` | The wire protocol: frames, operations, the send and read windows, errors, the access rule | read it |
| `relay/relay.ts` | The relay: a WebSocket server (Bun) that opens TCP connections, default-deny | `test/relay.test.ts`, `test/flow.test.ts` |
| `relay/config.example.json` | Which destinations the relay may connect to | |
| `tcp_relay_client.js` | The page's side: `RelayTcp`, with callback calls for the effects and promises for JavaScript | `test/*.test.ts` |
| `vectors.bend` | Frames encoded by the Bend definitions | `test/frame_vectors.json` is its output |
| `tcp.bend` | The `WebTCP.*` declarations: Base's TCP signatures, each importing `effs/web_tcp.js` | `tests/decl_listen.bend`, the page programs |
| `effs/web_tcp.js` | The effects of `WebTCP.*`, over the page's relay | `test/web_tcp.test.ts` |
| `tests/web/*.bend.tpl` | Page programs (templates: the ports are filled in by the test) | `test/web_tcp.test.ts` |
| `test/relay.test.ts` | 12 tests over real TCP: echo, 300 KB both ways, default-deny (13), refused (111), end of stream, 20 connections, id reuse, the connection limit (24), protocol errors | `bun test browser/test` |
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

    bun browser/relay/relay.ts browser/relay/config.example.json   # the relay, on port 8765

The page programs need the asynchronous runtime (below), at the path in `BEND_MAIN`
(default `/tmp/claude-0/src/bend-async/bend2/main.ts`). They are skipped without it.

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

## The asynchronous scheduler (done as a patch)

`runtime/async-scheduler.patch` changes Bend's JavaScript runtime (bend2/comp.ts, bend2/main.ts) so a
program can wait on an event that is not a file descriptor, such as a WebSocket message or a host
timer, without blocking the host's event loop. An external wait parks with no fd, and its event calls
`io_notify`; a notice re-checks every external wait, one with a deadline too. The top-level run
awaits; a nested run (from inside an effect) keeps the blocking poll, as before. The patch is one
commit on the branch `browser-async-scheduler` of the Bend checkout at /tmp/claude-0/src/bend-async
(not pushed; the installed `bend` is unchanged). It applies to Bend's `main`.

Checked earlier: the 234 I/O tests of tests/io give the same results under the patched runtime,
except three that name the checkout's path and one fork_join ordering that flips under parallel load
(it matches its expected order alone). `runtime/async_wake.bend` checks host timers.

A wait that no event will ever complete hangs the program under Bun (the process stays alive).

## A page

`page/index.html` and `page/app.js` are a page. The build is the Bend CLI's page bundle, from the
async-scheduler checkout (the installed `bend` does not have the scheduler yet):

    bun /tmp/claude-0/src/bend-async/bend2/main.ts browser/page/index.html -o dist

The page imports a program (`page/program.bend`), opens the relay at `?relay=ws://...`, sets
`globalThis.bend_relay` to it, and runs the program's `page_main()` (its `main`, through the
scheduler). The page's output goes to `#bend-output`; `body[data-exit]` holds the exit code when
the program has finished.

What changed in the runtime for a page (the patch above): no Node or Bun module is named in the
code (`io_node` looks them up when used), so the bundler resolves nothing it cannot. A page's output
goes to the page, not a file descriptor, and a system call throws, since a page has none. The
`page_main` export is added to the module only when the program has a `main`.

## Not done

- **Output and effects outside TCP.** A page's output is text (`#bend-output`, or
  `globalThis.bend_stdout`). The file, process and environment effects are not in a page: a program
  that calls them fails there.
- **The Lean recheck** (`bend frame_proof.bend --verdict`) is not run: the Lean toolchain download is
  blocked by the sandbox's network policy.
- Listen and accept are not in the protocol.
- A relay in production needs an owner, an allowlist, and TLS (wss) and an origin check, decided by
  you (see `PROTOCOL.md`).
