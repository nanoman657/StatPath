# bend-tls

TLS 1.3 in pure Bend 2, built up one verified layer at a time. Nothing here
uses `@unsafe` or foreign code. Only the first layers exist so far.

## Status

| Layer | File | Status |
|---|---|---|
| SHA-256 (FIPS 180-4) | `sha256.bend` | done, tested |
| HMAC-SHA256 (RFC 2104) | `hmac.bend` | done, tested |
| HKDF (RFC 5869) | | not started |
| AES-128-GCM, ChaCha20-Poly1305 | | not started |
| X25519 / P-256 key agreement | | not started |
| Signature verification (RSA-PSS, ECDSA, Ed25519) | | not started |
| X.509 parsing and chain validation | | not started |
| Record layer and handshake state machine | | not started |

## Running

```
bend tests.bend                        -> sha256: 16 passed, 0 failed
bend tests.bend -o tests && ./tests    (native: same output)
bend hmac_tests.bend                   -> hmac-sha256: 10 passed, 0 failed
bend bench.bend <file>                 SHA-256 digest and time for one file
```

`sha256.bend`, `tests.bend` and `hmac_tests.bend` are generated: run
`python3 -I gen_sha256.py`, `python3 -I gen_tests.py` and
`python3 -I gen_hmac_tests.py`. The generators compute the round constants
from the primes and the expected digests from Python's `hashlib` and `hmac`.

## What is checked

- **SHA-256:** the NIST `""`, `"abc"` and 56-byte vectors, every padding
  boundary (lengths 1, 3, 55, 56, 57, 63, 64, 65, 119, 120, 128, 1000), and a
  700-plus-256-byte message with every byte value. Digests match `hashlib` on
  JS and native.
- **HMAC-SHA256:** RFC 4231 test cases 1, 2, 3 and 6 (case 6 needs a key longer
  than the 64-byte block). The generator asserts that Python's digests equal
  the RFC's printed ones. Key lengths 0, 1, 63, 64, 65 and 200 are checked
  against Python too.
- The harness fails when a digest is wrong, which was checked by planting a
  wrong digest.

## Performance

| | JS | native |
|---|---|---|
| SHA-256, 1,017,347 bytes | 258 ms | 19 ms |

Hashing is about 4 MB/s on JS and 53 MB/s natively. The JS figure is with the
tail-recursive message pass. The first version overflowed the JS stack somewhere
between 16 KB and 64 KB.

## Limits and cautions

- **Not constant time.** Bend compiles to C and JS, and nothing in the code
  guards against timing or cache side channels. This is not safe for handling
  secrets until it has been reviewed.
- **No streaming API.** `sha256_bytes` and `hmac` take the whole message at
  once. HMAC joins the key and message with `List.append`, which is not
  tail-recursive; 64 KB works on JS, larger inputs are untested there.
- **No audit.** Test vectors show the arithmetic is right. They don't show the
  code is secure.

## TLS 1.3: what remains

RFC 8446 section 9.1 requires `TLS_AES_128_GCM_SHA256` and recommends
`TLS_CHACHA20_POLY1305_SHA256`. Roughly in order of difficulty:

1. **HKDF** (RFC 5869) and the TLS 1.3 key schedule. This is small on top of
   HMAC.
2. **AEAD.** AES-128 needs its S-box and GHASH over GF(2^128), which is bit
   arithmetic. ChaCha20 is 32-bit operations. Poly1305 needs arithmetic mod
   2^130 - 5, which the bignat code can support once multiplication and
   reduction are added.
3. **Key agreement.** X25519 needs field arithmetic mod 2^255 - 19 with
   full-size multiplication, and `bignat.bend` only divides by small numbers
   so far. P-256 needs the same. This is the main performance risk in pure Bend.
4. **Certificate verification.** The server's certificate must be parsed (DER /
   ASN.1), its signature checked (RSA-PSS, ECDSA or Ed25519, which need big
   modular exponentiation or elliptic-curve arithmetic), and the chain checked
   against trust anchors with validity dates and hostname matching. The trust
   anchors would be data in the program. `IO.now()` gives the clock in
   milliseconds.
5. **Record layer and handshake.** Framing on `TCP.send_bytes` and
   `TCP.recv_bytes`, nonces from sequence numbers, and the state machine for
   ClientHello through Finished, with the transcript hash.

Step 4 is the largest, and the current effects can't test it against a real
server until it's there.
