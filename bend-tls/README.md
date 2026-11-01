# bend-tls

TLS 1.3 in pure Bend 2. Nothing here uses `@unsafe` or foreign code. The
client completes a real handshake with `openssl s_server` and fetches a page,
but it implements two cipher suites and RSA certificates only. See "Limits".

## Status

| Layer | File | Status |
|---|---|---|
| SHA-256 (FIPS 180-4) | `sha256.bend` | done, tested |
| HMAC-SHA256 (RFC 2104) | `hmac.bend` | done, tested |
| HKDF (RFC 5869) and the TLS 1.3 key schedule | `hkdf.bend` | done, tested |
| ChaCha20, Poly1305, ChaCha20-Poly1305 (RFC 8439) | `chacha20.bend`, `poly1305.bend`, `aead.bend` | done, tested |
| AES-128 and AES-128-GCM (FIPS 197, SP 800-38D) | `aes.bend`, `gcm.bend` | done, tested |
| X25519 key agreement (RFC 7748) | `x25519.bend` | done, tested |
| P-256 key agreement | | not started |
| RSA-PSS and PKCS#1 v1.5 verification (SHA-256) | `rsa.bend`, `bigint.bend` | done, tested |
| ECDSA, Ed25519 signatures | | not started |
| DER / ASN.1 and X.509 chain, validity and hostname checks | `asn1.bend`, `x509.bend` | done for RSA chains |
| Record layer and client handshake | `tls.bend`, `handshake.bend`, `client.bend` | done for two suites; see the e2e test |

## Running

```
bend tests.bend                        -> sha256: 16 passed, 0 failed
bend hmac_tests.bend                   -> hmac-sha256: 10 passed, 0 failed
bend hkdf_tests.bend                   -> hkdf: 22 passed, 0 failed
bend aead_tests.bend                   -> aead: 29 passed, 0 failed
bend x25519_tests.bend                 -> x25519: 7 passed, 0 failed
bend bigint_tests.bend                 -> bigint: 10 passed, 0 failed
bend rsa_tests.bend                    -> rsa: 4 passed, 0 failed
bend rsa_sig_tests.bend                -> rsa-sig: 24 passed, 0 failed
bend x509_tests.bend                   -> x509: 17 passed, 0 failed
bend tls_tests.bend                    -> tls: 19 passed, 0 failed
bend aes_tests.bend                    -> aes-gcm: 39 passed, 0 failed
bash e2e/run.sh                        -> e2e (js): 8 passed, 0 failed
bash e2e/run.sh native                 -> e2e (native): 8 passed, 0 failed
```

Each suite also runs natively (`bend X.bend -o X && ./X`) with the same output.

The client:

```
bend client.bend -o client
./client <server-name> <ip> <port> <anchor.der> <unix-time>
./client example.test 127.0.0.1 4433 root.der 1793495136
```

It sends `GET /` over TLS 1.3 and prints the response (HTTP headers and body).
`<server-name>` goes in the ClientHello and must match the certificate. `<ip>`
is the address to connect to, because the TCP kit has no DNS. `<anchor.der>` is
the trust anchor, a DER certificate. `<unix-time>` is the current time in
seconds, because Bend has no wall clock: `IO.now()` is monotonic.

`client.bend` is generated from `client_body.bend` by `gen_client.py`, and its
definitions must be in dependency order, so run:

```
python3 -I gen_client.py && python3 -I sortfile.py client.bend
```

The other generated files are `sha256.bend`, `tests.bend`, `hmac_tests.bend`,
`hkdf_tests.bend`, `chacha20.bend`, `poly1305.bend`, `x25519.bend`,
`bigint_tests.bend`, `rsa_tests.bend`, `rsa_sig_tests.bend`, `aead_tests.bend`,
`x25519_tests.bend`, `x509_tests.bend`, `tls_tests.bend`, `aes_tests.bend`, and
`aes.bend` (from `aes_body.bend` by `gen_aes.py`). Each generator is the
`gen_*.py` file with the same stem. They compute expected values with Python:
`hashlib`, `hmac`, and the `cryptography` package (for X.509, RSA, X25519,
ChaCha20-Poly1305 and AES-GCM).

## End-to-end test

`e2e/run.sh` makes a PKI (root, intermediate, and a leaf for `example.test`).
For each suite, `TLS_AES_128_GCM_SHA256` and `TLS_CHACHA20_POLY1305_SHA256`, it
starts `openssl s_server` with TLS 1.3 and X25519 (allowing only that suite), and
runs the client against it:

- **valid:** the root is the anchor and the host is `example.test`. The page is
  fetched.
- **wrong anchor:** the leaf is the anchor. The handshake is rejected.
- **wrong host:** the host is `other.test`. Rejected.
- **expired:** the time is in 2100. Rejected.

The positive case checks the handshake from start to finish: the ServerHello
key share, the handshake traffic keys, decryption of the encrypted flight, the
chain check, the CertificateVerify signature (RSA-PSS over the transcript), the
server Finished, our client Finished, and decryption of the response. It passes
on JS and native.

## What is checked

- **SHA-256:** the NIST `""`, `"abc"` and 56-byte vectors, every padding
  boundary (lengths 1, 3, 55, 56, 57, 63, 64, 65, 119, 120, 128, 1000), and a
  700-plus-256-byte message with every byte value. Digests match `hashlib` on
  JS and native.
- **HMAC-SHA256:** RFC 4231 test cases 1, 2, 3 and 6 (case 6 needs a key longer
  than the 64-byte block). Key lengths 0, 1, 63, 64, 65 and 200 are checked
  against Python too.
- **HKDF and the key schedule:** RFC 5869 vectors, and the TLS 1.3 secrets
  (early, handshake, master, traffic keys and IVs, Finished key) checked against
  the `cryptography` package.
- **ChaCha20-Poly1305:** the RFC 8439 vectors, and seal/open round trips with
  tampered input rejected.
- **X25519:** the RFC 7748 vectors and an Alice-and-Bob exchange.
- **RSA:** PSS and PKCS#1 v1.5 verification of real signatures, and rejection of
  altered messages and signatures.
- **X.509:** a PKI made with `cryptography` (root, intermediate, leaf with SAN,
  and an expired certificate). The tests cover validity dates, hostname matching
  against SAN, chain signatures, and a chain that ends at the wrong anchor.
- **TLS encoding:** the ClientHello layout, the record header and nonce, and
  ServerHello and certificate-list parsing.
- The harness fails when a value is wrong. This was checked by planting a
  wrong expected value.

## Performance

| | JS | native |
|---|---|---|
| SHA-256, 1,017,347 bytes | 258 ms | 19 ms |

Hashing is about 4 MB/s on JS and 53 MB/s natively. The JS figure is with the
tail-recursive message pass. The first version overflowed the JS stack somewhere
between 16 KB and 64 KB.

The e2e run is about 16 s on JS for eight handshakes. The native build takes
about 35 s and each run is faster. AES-GCM speed has not been measured.

## Limits and cautions

- **Two cipher suites.** The client offers `TLS_AES_128_GCM_SHA256` and
  `TLS_CHACHA20_POLY1305_SHA256` with X25519, and accepts either. AES-256-GCM is
  not implemented, nor P-256 key shares, so a server that allows only those will
  fail the handshake.
- **RSA certificates only.** ECDSA and Ed25519 keys are not verified. A server
  with an ECDSA certificate will be rejected.
- **Certificate checks are partial.** Validity dates and hostname matching (DNS
  SAN, case-insensitive, no wildcards) are checked, and chain signatures back to
  a trust anchor given as DER. basicConstraints, keyUsage and name constraints
  are not checked. There is no revocation check.
- **Bounded reads.** The handshake flight may use at most 24 records, and the
  response at most 24 records (each up to 16 KB). A longer response is cut off
  and the client still exits 0. A longer handshake fails with "did not check".
- **No HelloRetryRequest, no session resumption, no client certificates, no
  key update.** NewSessionTicket messages are read and ignored.
- **No HTTP parsing.** The output is the raw response, headers included.
- **Time and names come from the command line.** See the usage above.
- **Not constant time.** Bend compiles to C and JS, and nothing in the code
  guards against timing or cache side channels. This is not safe for handling
  secrets until it has been reviewed.
- **No streaming API for hashing.** `sha256_bytes` and `hmac` take the whole
  message at once. HMAC joins the key and message with `List.append`, which is
  not tail-recursive; 64 KB works on JS, larger inputs are untested there.
- **No audit.** Test vectors and the e2e test show the arithmetic and the
  protocol are right for these inputs. They don't show the code is secure.

## What remains

Roughly in order of difficulty:

1. **P-256**, and ECDSA verification (needs modular inversion and point
   arithmetic on the curve). Most public servers now use ECDSA certificates,
   so this is the main gap for real sites.
2. **Ed25519** and certificates signed with ECDSA or Ed25519.
3. **Certificate extensions:** basicConstraints and keyUsage, and wildcard names.
4. **AES-256-GCM** and **P-256** key shares, if the client should offer them.
5. **Bounded reads:** a stream that outlasts the 24-record limit should be an
   error, not a silent cut.
