// Browser TCP: the effects of WebTCP.* (tcp.bend), over the page's relay (tcp_relay_client.js,
// PROTOCOL.md). The page sets globalThis.bend_relay to an open RelayTcp before the program runs.
//
// As the native effects do, a call answers at once or parks until the relay answers; the relay's
// messages call io_notify. A try_ call parks with a deadline. Past it, a send the relay has not
// finished is dropped, and the call answers Wait with the bytes the relay did not take; a receive
// that has nothing is cancelled and answers Wait. Listen and accept are not in the protocol, so
// they answer EOPNOTSUPP, as a page cannot accept a connection.
//
// A failure reads the glibc text for its errno on Linux, as the native effects give it. An errno
// this table does not have keeps the relay's own message.

const WT_TEXT = {
  1: "Operation not permitted",
  5: "Input/output error",
  9: "Bad file descriptor",
  11: "Resource temporarily unavailable",
  13: "Permission denied",
  22: "Invalid argument",
  24: "Too many open files",
  27: "File too large",
  32: "Broken pipe",
  38: "Function not implemented",
  95: "Operation not supported",
  99: "Cannot assign requested address",
  101: "Network is unreachable",
  104: "Connection reset by peer",
  107: "Transport endpoint is not connected",
  110: "Connection timed out",
  111: "Connection refused",
  113: "No route to host",
};

// The failure answer (Result): the errno and its text, then the rest of the call's input.
function wt_fail(code, message, ...rest) {
  const text = WT_TEXT[code] ?? message ?? "errno " + code;
  return { $: "Fail", error: io_tup(io_tup(code >>> 0, text), ...rest) };
}

// The page's relay, or null when the page has none.
function wt_relay() {
  return globalThis.bend_relay ?? null;
}

// The bytes of b from index from to the end, as a Bend list.
function wt_rest(b, from) {
  return io_list(b.subarray(from), b.length - from);
}

// Parks the call: more() runs again on each notice and at the deadline at (Infinity: no deadline).
// more() answers with the call's value, or parks again.
function wt_park(k, more, at = Infinity) {
  io_park_on(undefined, false, k, more, at);
  return undefined;
}

// Sends bytes (a Uint8Array) on sock: all of them, or, past the deadline at, as many as the relay
// has taken, with the rest given back (a try_ call answers Wait with it).
function wt_send(sock, bytes, k, at) {
  const relay = wt_relay();
  if (relay === null) return io_tup(sock, io_ready(at, wt_fail(107, undefined, wt_rest(bytes, 0))));
  if (bytes.length === 0) return io_tup(sock, io_ready(at, io_done({ $: CID(Unit) })));
  const st = { settled: null, dropping: false, dropped: null };
  const start = relay.startSend(sock, bytes, (r) => {
    st.settled = r;
    io_notify();
  });
  // bytes of the connection's count, from the start of this send: the index into bytes
  const from = (written) => Math.max(0, (written ?? start) - start);
  const more = () => {
    if (st.settled === null && !st.dropping && at !== undefined && io_late(at)) {
      st.dropping = true;
      relay.discard(sock, (r) => {
        st.dropped = r;
        io_notify();
      });
    }
    if (st.dropping ? st.dropped === null : st.settled === null) {
      return wt_park(k, more, st.dropping ? Infinity : at);
    }
    if (st.settled !== null && st.settled.ok) {
      return io_tup(sock, io_ready(at, io_done({ $: CID(Unit) })));
    }
    if (st.dropping) {
      const d = st.dropped;
      if (d.error) {
        return io_tup(sock, io_ready(at, wt_fail(d.error.errno, d.error.message, wt_rest(bytes, from(d.error.written)))));
      }
      const left = from(d.written);
      if (left >= bytes.length) return io_tup(sock, io_ready(at, io_done({ $: CID(Unit) })));
      return io_tup(sock, { $: CID(Wait), rest: wt_rest(bytes, left) });
    }
    const e = st.settled.error;
    return io_tup(sock, io_ready(at, wt_fail(e.errno, e.message, wt_rest(bytes, from(e.written)))));
  };
  return wt_park(k, more, at);
}

// A List of bytes (0..255 each) as the bytes to send; a value past 255 fails with EINVAL before
// any byte is sent, and the list comes back.
function wt_send_list(sock, data, k, at) {
  const b = io_unlist(data);
  if (b === null) return io_tup(sock, io_ready(at, wt_fail(22, undefined, data)));
  return wt_send(sock, b, k, at);
}

// Receives up to max bytes on sock, as read(bytes, n) gives them. A call with nothing to read parks
// until the relay has data, the end or a failure, or until the deadline at.
function wt_recv(sock, max, k, at, read) {
  const n = Number(max);
  if (n === 0) return io_tup(sock, io_ready(at, wt_fail(22, undefined)));
  const relay = wt_relay();
  if (relay === null) return io_tup(sock, io_ready(at, wt_fail(107, undefined)));
  let outcome = null; // { bytes }, { eof: true } or { error } once a read can answer
  let cancel = () => {};
  const look = () => {
    try {
      const r = relay.takeNow(sock, n);
      if (r !== null) outcome = r;
    } catch (e) {
      outcome = { error: e };
    }
    return outcome !== null;
  };
  const again = () => {
    if (look()) io_notify();
    else cancel = relay.onReadable(sock, again);
  };
  const value = () => {
    if (outcome.error) return wt_fail(outcome.error.errno, outcome.error.message);
    if (outcome.eof) return io_done({ $: CID(None) });
    return io_done({ $: CID(Some), value: read(outcome.bytes, outcome.bytes.length) });
  };
  if (look()) return io_tup(sock, io_ready(at, value()));
  cancel = relay.onReadable(sock, again);
  const more = () => {
    if (outcome === null && at !== undefined && io_late(at)) {
      cancel();
      return io_tup(sock, { $: CID(Wait), rest: { $: CID(Unit) } });
    }
    if (outcome === null) return wt_park(k, more, at);
    return io_tup(sock, io_ready(at, value()));
  };
  return wt_park(k, more, at);
}

function wt_connect(host, port, k) {
  const relay = wt_relay();
  if (relay === null) return wt_fail(107, undefined);
  let got = null;
  relay.connectAt(str_out(host), Number(port), (r) => {
    got = r;
    io_notify();
  });
  const more = () => {
    if (got === null) return wt_park(k, more);
    return got.error ? wt_fail(got.error.errno, got.error.message) : io_done(got.id);
  };
  return wt_park(k, more);
}

// Closing never waits: the relay is told, and the id is free.
function wt_close(sock) {
  const relay = wt_relay();
  if (relay !== null) relay.close(sock);
  return { $: CID(Unit) };
}

io_eff(CID(WebTCP.listen), (host, port, k) => wt_fail(95, undefined));
io_eff(CID(WebTCP.accept), (listener, k) => io_tup(listener, wt_fail(95, undefined)));
io_eff(CID(WebTCP.try_accept), (listener, ms, k) =>
  io_tup(listener, io_ready(io_until(ms), wt_fail(95, undefined))));
io_eff(CID(WebTCP.connect), wt_connect);
io_eff(CID(WebTCP.send), (sock, data, k) => wt_send(sock, io_bytes(data), k, undefined));
io_eff(CID(WebTCP.try_send), (sock, data, ms, k) => wt_send(sock, io_bytes(data), k, io_until(ms)));
io_eff(CID(WebTCP.send_bytes), (sock, data, k) => wt_send_list(sock, data, k, undefined));
io_eff(CID(WebTCP.try_send_bytes), (sock, data, ms, k) => wt_send_list(sock, data, k, io_until(ms)));
io_eff(CID(WebTCP.recv), (sock, max, k) => wt_recv(sock, max, k, undefined, io_text));
io_eff(CID(WebTCP.try_recv), (sock, max, ms, k) => wt_recv(sock, max, k, io_until(ms), io_text));
io_eff(CID(WebTCP.recv_bytes), (sock, max, k) => wt_recv(sock, max, k, undefined, io_list));
io_eff(CID(WebTCP.try_recv_bytes), (sock, max, ms, k) => wt_recv(sock, max, k, io_until(ms), io_list));
io_eff(CID(WebTCP.close), (sock, k) => wt_close(sock));
io_eff(CID(WebTCP.close_listener), (listener, k) => ({ $: CID(Unit) }));
