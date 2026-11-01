# The browser relay: running it for real use

The relay (`relay/relay.ts`) opens TCP connections for a page in a browser, over a WebSocket. This
guide is for whoever runs one. The protocol is in `PROTOCOL.md`.

## What the relay enforces

| Protection | How | Setting |
|------------|-----|---------|
| Where it may connect | default-deny: only the listed host and ports | `allow` |
| Who may use it | a token per user, the relay keeps only its SHA-256 | `tokens` |
| Which pages may use it | the page's Origin must be listed, exactly | `origins` |
| Plaintext off the machine | wss:// with a certificate, required to listen beyond this machine | `tls` |
| Connections per page | open connections, and the whole relay | `limits.maxConnections`, `limits.maxConnectionsTotal` |
| Connects per second | a burst of twice the rate, then FAIL 11 | `limits.connectsPerSecond` |
| Bytes per second | both ways together; the relay waits, it does not fail | `limits.bytesPerSecond` |
| Pages and clients | sessions at once; upgrades per address per minute | `limits.maxSessions`, `limits.upgradesPerMinute` |
| Idle WebSockets | ping every idle period; closed after it with no reply | `limits.idleSeconds` |
| Slow pages | reads stop while the page's send buffer is full | `limits.maxBufferedBytes` |
| A token that never comes | closed after authSeconds | `limits.authSeconds` |

## The configuration

A JSON file. `relay/config.example.json` shows the shape. Unknown settings are refused, and every
mistake is reported at once.

```json
{
  "host": "0.0.0.0",
  "port": 8765,
  "tls": { "cert": "/etc/relay/fullchain.pem", "key": "/etc/relay/privkey.pem" },
  "origins": ["https://page.example"],
  "tokens": [{ "name": "alice", "sha256": "<64 hex digits>" }],
  "allow": [{ "host": "db.internal.example", "ports": [4433] }],
  "limits": { "maxConnections": 64, "bytesPerSecond": 16777216 }
}
```

- `host`: `127.0.0.1` (the default) for a relay on the same machine as the page. Anything else
  needs `tls`, or the relay refuses to start.
- `origins`: the pages allowed to connect, each exactly `scheme://host[:port]`, with no path.
- `tokens`: one per user. `name` is for the log; `sha256` is the digest of the token.
- `allow`: where the relay may connect. Keep it to the destinations you mean to serve. A host name
  here is trusted as the operator's: the relay does not check what it resolves to.
- `limits`: each optional, the defaults are in `relay/config.ts` (`DEFAULT_LIMITS`).

## Making a token

    bun relay/token.ts alice

It prints the token once, and the config entry to put in `tokens`. Give the token to alice over a
channel you trust, and keep the config entry's digest; the relay never holds the token itself.
A token is a secret: it belongs in the page's server configuration (the page's
`<meta name="bend-relay-token">`), not in the page's source.

## TLS

Use a certificate for the host name the page connects to (for example from Let's Encrypt). The
relay reads the two files at start: restart it after a renewal. Without `tls` the relay listens on
loopback only.

## Running it

    bun relay/relay.ts /etc/relay/config.json

The relay logs one JSON line per event to standard output and stops cleanly on SIGINT or SIGTERM,
closing every WebSocket with code 1001. It answers `GET /healthz` with `ok`.

Run it under a process supervisor (systemd, or a container) that restarts it and keeps its output.

## The log

Each line is `{ "time", "event", ... }`. Events: `session_open`, `session_close`, `auth_ok`,
`auth_fail`, `auth_timeout`, `connect`, `connect_denied`, `connect_limited`, `origin_denied`,
`upgrade_limited`, `sessions_full`, `listening`.

The log names the token holder (`name`), the origin, the client address and the destination of each
CONNECT (`host`, `port`). It never holds a token or any data the page sent or received. Keep the
log as you would any record of who connected where.

## What the relay does not do

- **It is not the protection for the data.** The relay sees the bytes of every connection in
  plain form. A page that sends secrets over a connection should use TLS to the destination (as the
  TLS client in `bend-tls` does), so the relay cannot read them.
- **It does not isolate users from one another** beyond their tokens, limits and allowlists. Give
  each trust domain its own relay.
- **It does not know the page's identity.** An origin is what a browser says it is; a token holder
  may run any page from an origin you listed. Make the origins and the tokens match your intent.
- **The client address is the address the relay sees.** Behind a proxy or load balancer every
  client shares the proxy's address, and the upgrade limit then applies to all of them together. Run
  the relay on its own TLS listener (as above), or change `upgradesPerMinute` to suit.
- **Listen and accept are not offered.** A page cannot accept connections through the relay.

## Checklist before a relay serves users

1. `bun test browser/test` passes on the machine that will run the relay.
2. The configuration loads: `bun relay/relay.ts <config>` prints `listening`, not a configuration
   error. The example's placeholder digest is refused on purpose.
3. `allow` lists only the destinations you mean to serve.
4. `origins` lists only the pages you mean to serve.
5. Every token is made with `relay/token.ts`, and its digest is the only copy the relay keeps.
6. With `host` beyond loopback, `tls` is set and the certificate covers the host name the pages use.
7. `GET /healthz` answers `ok` through the same address the pages use.
