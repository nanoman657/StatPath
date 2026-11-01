# Browser TCP (in progress)

A page cannot open TCP connections, so this folder has a relay that opens them for the page,
and the page's side of the protocol. The pieces:

| File | What it is | How it is checked |
|------|------------|-------------------|
| `frame.bend` | The frame format as Bend code: encode, decode, completeness | `frame_proof.bend` (laws) |
| `frame_proof.bend` | Laws: a frame decodes to itself, and is complete | Bend's kernel: `bend frame_proof.bend` prints `ALL PROOFS CHECK` |
| `frame_arith.bend` | Euclid's identity for the division routine of the base library, from its invariant | the same checker |
| `frame_lists.bend` | List lemmas (append, take, drop) and `le` on sums | the same checker |
| `PROTOCOL.md` | The wire protocol: frames, operations, errors, the access rule | read it |
| `relay/relay.ts` | The relay: a WebSocket server (Bun) that opens TCP connections, default-deny | `test/relay.test.ts` |
| `relay/config.example.json` | Which destinations the relay may connect to | |
| `tcp_relay_client.js` | The page's side: `RelayTcp` with connect, send, recv and close | `test/relay.test.ts` |
| `vectors.bend` | Frames encoded by the Bend definitions | `test/frame_vectors.json` is its output |
| `test/relay.test.ts` | 12 tests over real TCP: echo, 300 KB both ways, default-deny (errno 13), refused (111), end of stream, 20 connections, id reuse, the connection limit (24), protocol errors | `bun test browser/test` |

## Run the tests

    cd bend-tls
    bun test browser/test
    bend browser/frame_proof.bend        # ALL PROOFS CHECK

    bun browser/relay/relay.ts browser/relay/config.example.json   # the relay, on port 8765

## What is proven, and what is tested

Proven by Bend's kernel (the checker reads the definitions, not a model of them):
- the division identity `(n div 256)*256 + (n mod 256) == n`, from the long-division routine
  the base library uses;
- a frame decodes to the frame that was encoded, followed by any bytes, for payloads of fewer
  than 65536 bytes;
- a complete frame is recognised as complete.

A false version of the round-trip law is rejected by the checker (checked when this was built).

Tested, not proven: the relay, the page's client, and the sockets. The Bend encodings of sample
frames (`frame_vectors.json`) match the JavaScript encoder byte for byte.

## Page declarations (item 1)

`tcp.bend` declares the TCP operations of a page build, with the signatures of Base's TCP under the
names `WebTCP.*`. A page program imports it and calls `WebTCP.connect` where a native program calls
`TCP.connect`; the native declarations are untouched. Each declaration imports a browser effect in
`effs/`, and none imports C, so a native build of a page program stops with "no .c import".

| Declaration | Status |
|-------------|--------|
| `WebTCP.listen`, `accept`, `try_accept` | answer EOPNOTSUPP (95): a page cannot accept connections |
| `WebTCP.connect`, `send`/`try_send`/`send_bytes`/`try_send_bytes`, `recv`/`try_recv`/`recv_bytes`/`try_recv_bytes` | placeholders answering ENOSYS (38) until item 3 |
| `WebTCP.close`, `close_listener` | no-ops returning Unit (there is no native socket to close yet) |

    bend tests/decl_listen.bend     # prints: 95 Operation not supported
    bend tests/decl_connect.bend    # prints: 38

`bend tcp.bend --check-only` reports the declarations as foreign effects. That is the checker's
verdict for host code outside Base; the module has no laws, so nothing is unsound. Keep such
declarations out of files that proofs import.

## The asynchronous scheduler (done as a patch)

`runtime/async-scheduler.patch` changes Bend's JavaScript runtime (bend2/comp.ts, bend2/main.ts) so a
program can wait on an event that is not a file descriptor, such as a WebSocket message or a host
timer, without blocking the host's event loop. An external wait parks with no fd and at = Infinity,
and its event calls `io_notify`. The top-level run awaits; a nested run (from inside an effect)
keeps the blocking poll, as before. The patch is a commit on the branch `browser-async-scheduler`
of the Bend checkout at /tmp/claude-0/src/bend-async (not pushed; the installed `bend` is unchanged).

Checked: the 234 I/O tests of tests/io give the same results under the patched runtime, except
three that name the checkout's path and one fork_join ordering that flips under parallel load
(it matches its expected order alone). A program waiting on a host timer completes
(`runtime/async_wake.bend`), and the relay demo completes:

    BEND_MAIN=/path/to/bend2/main.ts sh runtime/run_relay_demo.sh      # prints "echoed 5"

A wait that no event will ever complete hangs the program under Bun (the process stays alive).

## Not done

- **The TCP effects as Bend effects.** The demo calls the relay from one JavaScript effect. The
  real effects (`TCP.connect`, send, recv, close and the `try_` forms, with a socket handle type
  instead of a U32 id) still need writing and registering, with their error results.
- **A page runtime.** The patched runtime still uses Bun's FFI, `fs`, `Buffer` and `process`
  (see the earlier list). A page needs those replaced.
- **The Lean recheck** (`bend frame_proof.bend --verdict`) is not run: the Lean toolchain download is
  blocked by the sandbox's network policy.
- Listen and accept are not in the protocol.
- A relay in production needs an owner and an allowlist decided by you (see `PROTOCOL.md`).
