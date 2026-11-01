# bend-tls

TLS 1.3 in pure Bend 2. Nothing here uses `@unsafe` or foreign code. The client
completes a TLS 1.3 handshake with `openssl s_server` (and with a Python TLS
server for the response-size test), verifies the server's certificate chain, and
fetches a page. It supports three cipher suites, three key-exchange groups and four
certificate key types. See "Limits" for what is missing.

## Status

| Layer | File | Status |
|---|---|---|
| SHA-256 (FIPS 180-4) | `sha256.bend` | done, tested |
| HMAC-SHA256 and HMAC-SHA384 (RFC 2104) | `hmac.bend`, `hmac384.bend` | done, tested |
| HKDF (RFC 5869) and the TLS 1.3 key schedule, for SHA-256 and SHA-384 | `hkdf.bend` | done, tested |
| ChaCha20, Poly1305, ChaCha20-Poly1305 (RFC 8439) | `chacha20.bend`, `poly1305.bend`, `aead.bend` | done, tested |
| AES-128 and AES-256, with GCM (FIPS 197, SP 800-38D) | `aes.bend`, `gcm.bend` | done, tested |
| SHA-384 and SHA-512 (FIPS 180-4) | `sha512.bend` | done, tested |
| X25519 key agreement (RFC 7748) | `x25519.bend` | done, tested |
| P-256 ECDH and ECDSA verification (SEC 1, FIPS 186-4) | `p256.bend` | done, tested |
| P-384 ECDH and ECDSA verification (SEC 1, FIPS 186-4) | `p384.bend` | done, tested |
| Ed25519 verification (RFC 8032) | `ed25519.bend` | done, tested |
| RSA-PSS and PKCS#1 v1.5 verification (SHA-256) | `rsa.bend`, `bigint.bend` | done, tested |
| DER/ASN.1 and X.509 (RFC 5280): chains, validity, names, CA, path length, EKU | `asn1.bend`, `x509.bend` | done for RSA, ECDSA P-256 and P-384, and Ed25519 keys |
| TLS 1.3 record layer and client handshake (RFC 8446) | `tls.bend`, `handshake.bend`, `client.bend` | done: 3 suites, 3 groups (HelloRetryRequest for secp384r1), 4 certificate key types |
| HTTP/1.1 GET and POST over TCP to IP-literal `http://` URLs (for CRL and OCSP) | `http.bend` | done, tested |
| OCSP request and response check (RFC 6960), CRL distribution points and OCSP URIs | `revoc.bend` | done, tested |
| Revocation fetching in the client (`fetch` argument) | `client.bend`, `crl.bend` | done on the native client: all 9 cases of `e2e/fetch.py` pass; the JS run is not done |
| Proofs of the branch-free selects (`LAWS.bend`, `PROOF.bend`) | `LAWS.bend`, `PROOF.bend` | 4 laws, `ALL PROOFS CHECK`; Lean recheck not run |

The client's three suites are `TLS_AES_128_GCM_SHA256`, `TLS_AES_256_GCM_SHA384` and
`TLS_CHACHA20_POLY1305_SHA256`. Its key shares are x25519, secp256r1 and secp384r1. Its
signature algorithms are `rsa_pss_rsae_sha256`, `rsa_pkcs1_sha256` (offered, not
used for CertificateVerify), `ecdsa_secp256r1_sha256`, `ecdsa_secp384r1_sha384`
and `ed25519`.

## Running

Each unit suite prints a line like `sha256: 16 passed, 0 failed`. Each runs
natively too (`bend X.bend -o X && ./X`), with the same output.

```
bend tests.bend                 -> sha256: 16 passed, 0 failed
bend hmac_tests.bend            -> hmac-sha256: 10 passed, 0 failed
bend hkdf_tests.bend            -> hkdf: 41 passed, 0 failed
bend hmac384_tests.bend         -> hmac-sha384: 42 passed, 0 failed
bend aead_tests.bend            -> aead: 29 passed, 0 failed
bend aes_tests.bend             -> aes-gcm: 48 passed, 0 failed
bend sha512_tests.bend          -> sha512: 27 passed, 0 failed
bend x25519_tests.bend          -> x25519: 7 passed, 0 failed
bend p256_tests.bend            -> p256: 51 passed, 0 failed
bend p384_tests.bend            -> p384: 47 passed, 0 failed
bend ed25519_tests.bend         -> ed25519: 30 passed, 0 failed
bend bigint_tests.bend          -> bigint: 10 passed, 0 failed
bend rsa_tests.bend             -> rsa: 4 passed, 0 failed
bend rsa_sig_tests.bend         -> rsa-sig: 24 passed, 0 failed
bend x509_tests.bend            -> x509: 17 passed, 0 failed
bend x509_ext_tests.bend        -> x509-ext: 45 passed, 0 failed
bend ec_tests.bend              -> ec: 27 passed, 0 failed
bend crl_tests.bend             -> crl: 13 passed, 0 failed
bend fuzz_tests.bend            -> fuzz: 190 passed, 0 failed (a FAIL is a mutated input accepted)
bend fuzz_tls_tests.bend        -> fuzz-tls: 298 passed, 0 failed
bend tls_tests.bend             -> tls: 33 passed, 0 failed
bash e2e/run.sh                 -> e2e (js): 180 passed, 0 failed
bash e2e/run.sh native          -> e2e (native): 180 passed, 0 failed
bash e2e/big.sh                 -> big (js): 2 passed, 0 failed
bash e2e/crl.sh                 -> e2e crl (js): 15 passed, 0 failed (native: 15)
python3 -I e2e/rejects.py       -> rejects (js): 7 passed, 0 failed
```

The client:

```
bend client.bend -o client
./client <server-name> <ip> <port> <anchor.der> <unix-time> [crl.der]
./client example.test 127.0.0.1 4433 root.der 1793495136
./client example.test 127.0.0.1 4433 root.der 1793495136 crl.der
```

It sends `GET /` over TLS 1.3 and prints the response, HTTP headers included.
`<server-name>` goes in the ClientHello (SNI) and must match the certificate.
`<ip>` is the address to connect to, because the TCP kit has no DNS.
`<anchor.der>` is the trust anchor, a DER certificate. `<unix-time>` is the
current time in seconds, because Bend has no wall clock: `IO.now()` is
monotonic. `[crl.der]` is an optional certificate revocation list (DER), or `""` for none,
and a further `fetch` makes the client fetch the revocation status of the chain over HTTP;
see "Revocation" below. Exit status is 0 on success and 1 on any error, with a message.

### Generated files

Several modules are generated; the source is the file with the `_body` or the
`gen_` name, and the generator writes the module:

| Generated | From | Command |
|---|---|---|
| `client.bend` | `client_body.bend` | `python3 -I gen_client.py && python3 -I sortfile.py client.bend` |
| `aes.bend` | `aes_body.bend` | `python3 -I gen_aes.py` |
| `sha512.bend` | `sha512_body.bend` | `python3 -I gen_sha512.py` |
| `p256.bend` | `p256_body.bend` | `python3 -I gen_p256.py` |
| `ed25519.bend` | `ed25519_body.bend` | `python3 -I gen_ed25519.py` |
| `p384.bend` | `p256_body.bend` | `python3 -I gen_p384.py` |
| `fuzz_tests.bend` | `gen_fuzz_tests.py` | `python3 -I gen_fuzz_tests.py` (fresh random keys each run) |
| `fuzz_tls_tests.bend` | `gen_fuzz_tls_tests.py` | `python3 -I gen_fuzz_tls_tests.py` |
| `hmac384_tests.bend` | `gen_hmac384_tests.py` | `python3 -I gen_hmac384_tests.py` |
| `crl_tests.bend` | `gen_crl_tests.py` | `python3 -I gen_crl_tests.py` |
| `*_tests.bend` | `gen_*_tests.py` | `python3 -I gen_X_tests.py` |

Bend requires definitions in dependency order, so the generated files that
define many functions are then sorted with `python3 -I sortfile.py FILE`. The
generators compute expected values with `hashlib`, `hmac` and the
`cryptography` package, and check constants against independent code (see
"What is checked").

## End-to-end tests

`e2e/run.sh` makes a PKI with `e2e/mkpki.py`, starts `openssl s_server` for each
combination of:

- PKI kind: `rsa` (RSA keys throughout), `ec` (P-256 keys throughout, so every
  signature is ECDSA), `mixed` (RSA root, P-256 intermediate, RSA leaf), `ed`
  (Ed25519 keys throughout) and `ec384` (P-384 keys, signed with SHA-384);
- cipher suite: `TLS_AES_128_GCM_SHA256`, `TLS_AES_256_GCM_SHA384` or
  `TLS_CHACHA20_POLY1305_SHA256`;
- group: X25519, P-256 or P-384 (the server allows only that group, so the client must
  use it).

For each, the client runs four cases:

- **valid:** the root is the anchor and the host is `example.test`. The page is
  fetched and printed (`HTTP/1.0 200`).
- **wrong anchor:** the leaf is the anchor. The handshake is rejected.
- **wrong host:** the host is `other.test`. Rejected.
- **expired:** the time is in 2100. Rejected.

That is 5 x 3 x 3 x 4 = 180 runs. All 180 pass on the native client. The JS interpreter's run of the matrix was
done before the revocation changes and is not recorded here; it has not been rerun. A valid run goes through the whole handshake:
the ServerHello key share and group, the handshake traffic keys, decryption of
the encrypted flight, the chain check, the CertificateVerify signature (RSA-PSS,
ECDSA or Ed25519, as the leaf's key requires), the server Finished, our Finished,
and decryption of the response.

`e2e/big.sh` checks the response-size limits with a TLS 1.3 server
(`e2e/big_server.py`). A 200 KB body is printed in full. A 500 KB body, which is
more than the client reads, is refused with `the stream was cut`.

`e2e/crl.sh` runs the client with a CRL file (clean, revoked, or none) for five PKIs: 15
of 15 pass on the native client.
`e2e/rejects.py` runs the rejection paths against a scripted fake server (see "What is
checked"): 7 of 7 pass on the native client. `e2e/fetch.py` runs the revocation fetch against `openssl ocsp` and a CRL HTTP
server, nine cases, with `native` for the native binary and the default for the interpreter.

## What is checked

- **SHA-256:** the NIST `""`, `"abc"` and 56-byte vectors, every padding boundary
  (lengths 1, 3, 55, 56, 57, 63, 64, 65, 119, 120, 128, 1000), and a message with
  every byte value. Digests match `hashlib` on JS and native.
- **SHA-512 and SHA-384:** 27 cases against `hashlib`: the empty message, `abc`,
  the padding boundaries (111, 112, 113, 127, 128, 129), and multi-block messages.
  The constants are the roots of the first primes, computed exactly and checked
  against `hashlib` by the generator.
- **HMAC-SHA256:** RFC 4231 test cases 1, 2, 3 and 6. Key lengths 0, 1, 63, 64,
  65 and 200 are checked against Python too.
- **HKDF and the key schedule:** RFC 5869 vectors, and the TLS 1.3 secrets (early,
  handshake, master, traffic keys and IVs, Finished key) against `cryptography`.
- **ChaCha20-Poly1305:** the RFC 8439 vectors, and seal and open round trips, with
  tampered input rejected.
- **AES-128 and GCM:** FIPS 197 C.1, the McGrew-Viega GCM cases 1 and 2, and random
  seal and open against `cryptography`. Changed tags, bodies and AAD are rejected.
- **X25519:** the RFC 7748 vectors and an Alice-and-Bob exchange.
- **P-256:** field arithmetic, `k G` for several `k` (including `(n-1) G = -G`),
  ECDH against `cryptography`'s exchange, and ECDSA with SHA-256 against
  signatures from `cryptography`. Rejected: a changed message, r and s changed,
  r or s zero or equal to n, another key, an off-curve key, and s replaced by n-s
  (valid, since ECDSA has no low-s rule). The constants are checked by the
  generator against `cryptography` and an independent affine implementation.
- **P-384:** the same kinds of checks as P-256 (field arithmetic, `k G` against
  `cryptography`, ECDH against `cryptography`'s exchange, malformed peers and scalars
  refused, and ECDSA with SHA-384 and SHA-256 digests from `cryptography`, with the
  rejections). The constants are checked by the generator as well.
- **Ed25519:** RFC 8032 test 1 (the key and signature are checked against
  `cryptography` first), valid signatures from `cryptography`, a changed message,
  R or S, a non-reduced S (S + L), another key, a key or signature of the wrong
  length, a non-canonical key, the base multiplication against the public key of a
  seed, and the reduction mod L. The base point's order is checked by the generator.
- **RSA:** PSS and PKCS#1 v1.5 verification of real signatures, and rejection of
  altered messages and signatures.
- **Rejection paths:** `e2e/rejects.py` runs the client against a fake server that
  sends one scripted reply, and the client must refuse it: a HelloRetryRequest that
  selects a group the first ClientHello already shared (x25519, secp256r1), one that
  selects a group we do not offer, one with a cipher suite we do not offer, a second
  HelloRetryRequest, a ServerHello that selects secp384r1 without a retry, and a
  HelloRetryRequest whose cookie must be echoed in the second ClientHello.
- **Revocation:** `crl_tests.bend` (13 cases) builds CRLs with `cryptography` and checks
  them along a chain: a listed leaf or intermediate is refused; a CRL past its
  nextUpdate, not yet current, signed by another key, tampered, or for another
  name is no use; the anchor in the chain is not checked. `e2e/crl.sh` runs the
  client with a clean CRL, with a CRL that lists the leaf, and without a CRL, for
  five PKIs (RSA, P-256, mixed, Ed25519, P-384).
- **OCSP and fetching:** `revoc_tests.bend` (15 cases) builds the OCSP request with
  `cryptography`, and its bytes match `cryptography`'s exactly. It checks the CRL and
  OCSP URIs of a certificate, and replies made by `cryptography`: good; revoked;
  unknown; for another certificate; tampered; outside the time window; a delegated
  responder with the OCSP-signing purpose (accepted) and without it (refused); and a
  try-later status. `e2e/fetch.py` runs the native client with the `fetch` argument
  against `openssl ocsp`, with a status index, and a CRL HTTP server. Its nine cases:
  a good, a revoked and an unknown OCSP status; an unreachable responder; a clean CRL;
  a CRL that lists the leaf; an unreachable CRL server; a certificate with no revocation
  URI (accepted); and a revoked certificate without the argument (accepted). All nine
  pass on the native client.
- **HTTP:** `http_tests.bend` (8 cases) for URL and reply parsing, and
  `e2e/http_test.py` (3 cases) against a local server.
- **X.509:** certificates made with `cryptography`, with RSA, ECDSA P-256 and
  Ed25519 keys, each in its own chain: validity dates, hostnames (SAN, with wildcard
  names matching one label), chain signatures to a DER anchor, `basicConstraints`
  (a non-CA issuer, a missing `basicConstraints`, an anchor that is not a CA),
  `keyUsage` (a CA without `keyCertSign`), `pathLenConstraint`, extended key usage
  (`serverAuth`, `anyExtendedKeyUsage`, and a leaf with `clientAuth` only), and
  tampered or wrong-anchor chains.
- **CertificateVerify:** RSA-PSS, ECDSA P-256, ECDSA P-384 and Ed25519 over a transcript hash, each
  with a changed transcript, a wrong algorithm code, and a key of the wrong type.
- **TLS encoding:** the ClientHello layout (three key shares, three groups, all the
  signature algorithms), the record header and nonce, and ServerHello and
  certificate-list parsing, including a ServerHello with a P-384 key share.
- **Robustness (fuzzing):** valid certificate chains (RSA, ECDSA P-256, Ed25519)
  and CertificateVerify signatures, mutated by byte flips, truncations, insertions
  and duplicated slices. Every mutated input must be refused, and none may fault
  the runtime. The fuzzing found three faults or leniencies, all fixed: an ASN.1
  long-form length with more than six bytes overflowed the 2^48 Nat (a runtime
  fault, a denial of service); bytes after a certificate or an ECDSA signature were
  ignored; and a CertificateVerify length prefix was not checked. Each now has a
  regression case. `fuzz_tls_tests.bend` does the same for the record layer and the
  message parsers: a mutated sealed record must not open (both suites), mutated
  ServerHello and Certificate bodies must parse to bounded values, and random keys
  and signatures of the right lengths must verify False for P-256, P-384 and Ed25519.
  Boundary values (the field prime, the prime plus one, all ones) are tried in each
  position of the P-256 and P-384 verifiers, and Ed25519 keys with a non-canonical y
  are refused. A valid Ed25519 signature with S replaced by S + L is refused (RFC 8032
  requires S < L), while the unmodified signature verifies.
- The harness fails when a value is wrong. This was checked by planting a wrong
  expected value.

Several of these are reproducible: the e2e PKIs are generated fresh each run, and
the unit vectors are generated by the `gen_*.py` scripts.

## Performance

| | JS | native |
|---|---|---|
| SHA-256, 1,017,347 bytes | 258 ms | 19 ms |
| one TLS handshake and page fetch (`client.bend`), including process start | 1.9 s | 0.6 s |
| the P-256 suite (51 cases, including ECDSA and base multiplications) | about 4.6 s | |
| the Ed25519 suite (30 cases) | about 1.5 s | |

Hashing is about 4 MB/s on JS and 53 MB/s natively. The JS figure is with the
tail-recursive message pass; the first version overflowed the JS stack between
16 KB and 64 KB. The e2e run (64 handshakes) takes about two minutes on JS. The
native build takes about 35 s. AES-GCM throughput has not been measured.

## Constant-time review

This is a reading of the source, with the proofs listed below. It is not a timing
measurement. The question is whether any branch or memory access depends on a secret.
The secrets are the X25519 and ECDH private scalars and their shared secrets, the
traffic keys and IVs, the AES and ChaCha20 keys, the GCM hash key H and the GCM running
product, the Poly1305 key and accumulator, and the Finished keys. Lengths, certificates,
signatures, transcripts and record headers are public.

### What was changed

Each secret-dependent branch was replaced by arithmetic on a 0/1 value (`a * (1 - s) + b * s`
for a select, or a masked `xor`), so that every input takes the same path:

| Where | Before | Now |
|---|---|---|
| `x25519.bend`, the ladder (`fe.sel`) | a `match` on the swap bit | an arithmetic select of each limb; the swap is applied to both points |
| `x25519.bend`, canonical reduction (`fe.cfold`) | a `match` on the carry | the fold always runs at fixed length, and the result is selected |
| `bigint.bend`, `bi.sel` and `bi.csub` | a conditional subtraction on the borrow | both results are computed and the borrow selects one |
| `poly1305.bend`, `pl.sel` and `pl.canon` | a `match` on whether the value reaches p | the fold always runs for its fixed number of limbs; the reduced value is selected |
| `gcm.bend`, `gcm.reduce` and `gcm.cond` | a `match` on a bit of the running product | a masked `xor` (`U32.mul(bit, 225)`), and byte-wise arithmetic selects |
| `aes_body.bend`, `aes.xtime` and `aes.sbox` | a comparison tree per byte; a `Bool.pick` on the top bit | `xtime` is a masked `xor`; the S-box is x^254 by a fixed square-and-multiply chain of GF(2^8) products |
| `p256_body.bend` (also `p384.bend`), scalar multiplication | a point addition only for a 1 bit | the complete projective addition formulas (Renes, Costello and Batina 2016, algorithm 1, a = -3); each bit always adds, then the sum is selected; the affine conversion inverts Z by a fixed exponent |

The selects are exact: each is checked by the unit suites (x25519 7/7, bigint 10/10,
aead 29/29, AES-GCM 48/48, P-256 51/51, P-384 47/47, ECDSA and X.509 suites), and the
select laws below.

### What remains

1. **Timing.** The constant-time claims are about the source. The next step is to measure
   the compiled client (the runtime's big-number arithmetic and C division are not
   constant-time), and to remove the zero test on the ECDH scalar if that matters.
2. **Fetching.** `https://` URLs and host names (which need TLS for HTTP and DNS), more
   than the first revocation URI of a certificate, delta CRLs, OCSP nonces, caching, a
   read timeout, and a response size limit below about 1 MB. The fetch matrix has run on
   the native client only; the JS interpreter has not run it.
