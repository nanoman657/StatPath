# Relay protocol (browser TCP)

A browser page cannot open TCP connections, so a relay does it for the page. The page talks to the
relay over one WebSocket. Each WebSocket message carries exactly one frame.

## Frame

| field  | size      | meaning                                   |
|--------|-----------|-------------------------------------------|
| op     | 1 byte    | what the frame does (table below)         |
| id     | 1 byte    | the connection, 0..255, chosen by the page |
| len    | 2 bytes   | payload length, big-endian: high, then low |
| body   | len bytes | the payload (at most 65535 bytes)         |

The message must be exactly one frame: a short or long message is a protocol error, and the relay
closes the WebSocket (code 1002).

## Operations

| op | name    | direction | body                                              |
|----|---------|-----------|---------------------------------------------------|
| 1  | CONNECT | page->relay | port (2 bytes, big-endian), then the host name or address (UTF-8) |
| 2  | SEND    | page->relay | data to write to the connection                 |
| 3  | CLOSE   | page->relay | none; the connection is closed and the id is free |
| 10 | OK      | relay->page | none; the CONNECT succeeded                     |
| 11 | FAIL    | relay->page | errno (2 bytes, big-endian), then a message (UTF-8) |
| 12 | DATA    | relay->page | data read from the connection                   |
| 13 | EOF     | relay->page | none; the remote end has finished sending       |

## Rules

- An id is free until the page sends CONNECT for it, and is used until the page sends CLOSE or
  receives FAIL. The page must not reuse an id before then.
- The page sends SEND only after OK. A SEND before OK is a protocol error.
- The relay sends FAIL at most once per id, and frees the id after it.
- After CLOSE, the relay sends nothing more for that id.
- Payloads are at most 65535 bytes. The page splits larger writes; the relay splits large reads.
- Errors use Linux errno numbers: 13 EACCES (destination not allowed), 111 ECONNREFUSED,
  110 ETIMEDOUT, 113 EHOSTUNREACH, 101 ENETUNREACH, 99 EADDRNOTAVAIL, 24 EMFILE (too many
  connections), 5 EIO (anything else).

## Access

The relay is default-deny. It connects only to a destination listed in its config
(`config.example.json`): a host (exact string, as the page gives it) and a list of ports. Anything
else gets FAIL with errno 13 and is not connected.

## Limits

- At most 256 connections per WebSocket (ids are one byte).
- No flow control beyond the WebSocket's own buffering. A page that reads slowly can use memory.
- Listen and accept are not in the protocol: a page cannot accept incoming connections.
