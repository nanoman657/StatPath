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

## Not done

- **The Bend runtime does not use these yet.** Bend 2's TCP effects are host code registered with
  `io_eff`, and their waits block in `select`. A page needs an asynchronous scheduler before these
  client calls can stand in for `TCP.connect` and the others. That is the next piece of work.
- **The Lean recheck** (`bend frame_proof.bend --verdict`) is not run: the Lean toolchain download is
  blocked by the sandbox's network policy.
- Listen and accept are not in the protocol.
- A relay in production needs an owner and an allowlist decided by you (see `PROTOCOL.md`).
