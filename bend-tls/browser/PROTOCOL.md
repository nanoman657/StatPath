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

| op | name    | direction   | body                                                       |
|----|---------|-------------|------------------------------------------------------------|
| 1  | CONNECT | page->relay | port (2 bytes, big-endian), then the host name or address (UTF-8) |
| 2  | SEND    | page->relay | data to write to the connection                            |
| 3  | CLOSE   | page->relay | none; the connection is closed and the id is free          |
| 4  | DISCARD | page->relay | none; drop the SEND data not yet taken, and answer with WRITTEN (flag 1) |
| 5  | READ    | page->relay | credit: how many more bytes the relay may read (4 bytes, big-endian) |
| 10 | OK      | relay->page | none; the CONNECT succeeded                                |
| 11 | FAIL    | relay->page | errno (2 bytes, big-endian), then a message (UTF-8)        |
| 12 | DATA    | relay->page | data read from the connection                              |
| 13 | EOF     | relay->page | none; the remote end has finished sending                  |
| 14 | WRITTEN | relay->page | count (4 bytes, big-endian), then a flag byte: 1 answers a DISCARD, 0 does not |

## Rules

- An id is free until the page sends CONNECT for it, and is used until the page sends CLOSE or
  receives FAIL. The page must not reuse an id before then.
- The page sends SEND, DISCARD and READ only after OK. Before OK, a SEND is a protocol error.
- The relay sends FAIL at most once per id, and frees the id after it.
- After CLOSE, the relay sends nothing more for that id.
- Payloads are at most 65535 bytes. The page splits larger writes; the relay splits large reads.

### Counts and the send window

A connection counts the bytes of SEND data from its connect: the first SEND byte is byte 0.

- **WRITTEN** is sent after OK each time the socket has taken more of that data. Its count is how
  many bytes the socket has taken. Before a FAIL on an open connection the relay sends a WRITTEN, so
  the page knows how much of a failed send was taken.
- The relay holds at most **131072** bytes of SEND data it has not yet taken (the send window). The
  page sends no more than that beyond the count of the last WRITTEN it has seen; a relay that
  receives more closes the WebSocket (1002).
- **DISCARD** drops the SEND data the relay has not taken yet, and the relay answers with a WRITTEN
  whose flag is 1. That count is final: the bytes after it were not taken, and the page continues
  its count from there. The page sends no SEND until the reply.
- A count is four bytes, so a connection moves at most 4 GiB each way. Past that the relay fails the
  connection with EFBIG.

### Reading and the read window

- After OK the page grants credit: READ(131072). After each read that takes n bytes, it grants READ(n).
- The relay reads from the socket only while its credit is above zero. So the page holds at most
  about 131072 bytes it has not taken, plus one read from the socket.

### Ends of a connection

- When the remote end finishes sending, the relay sends EOF. A page's recv after its data is taken
  answers the end of the data.
- When the peer has closed the socket and the page sends SEND, the relay fails the connection with
  EPIPE (32). A write after a peer's close may first be taken by the socket and fail on the next
  write (ECONNRESET, 104, or EPIPE): either arrives as FAIL.
- CLOSE drops the SEND data not yet taken. A page that needs the data sent waits for the send before
  it closes.
- Half-close is not in the protocol: the page cannot finish its sending and go on reading. (Base's
  TCP has no shutdown, so a program does not ask for one.)

### Frames for a freed id

The page sends frames for an id before it sees the FAIL or the CLOSE that freed the id. The relay
drops a SEND, DISCARD or READ for an id that was connected and has been freed. An id this WebSocket
never connected is a protocol error (1002).

## Errors

Errors use Linux errno numbers: 13 EACCES (destination not allowed), 111 ECONNREFUSED,
110 ETIMEDOUT, 113 EHOSTUNREACH, 101 ENETUNREACH, 99 EADDRNOTAVAIL, 24 EMFILE (too many
connections), 32 EPIPE (the peer has closed), 104 ECONNRESET, 27 EFBIG (a count past 4 GiB),
5 EIO (anything else).

## Access

The relay is default-deny. It connects only to a destination listed in its config
(`config.example.json`): a host (exact string, as the page gives it) and a list of ports. Anything
else gets FAIL with errno 13 and is not connected.

## Limits

- At most 256 connections per WebSocket (ids are one byte).
- Each connection holds at most 131072 bytes of unsent SEND data and at most about 131072 bytes of
  unread DATA beyond the page's reads, so a WebSocket holds at most about 64 MiB in each direction
  with 256 connections.
- Listen and accept are not in the protocol: a page cannot accept incoming connections.
