// Relay.roundtrip (IO(U32)): sends "hello" through the browser relay (browser/relay/relay.ts), to the TCP
// address 127.0.0.1:port, and returns how many bytes come back (0 when the relay refuses or fails; the reason goes to stderr). The relay's WebSocket messages
// are external events: they call io_notify, and more() reports the result once it is complete.
// The relay's URL is in BEND_RELAY.
function relay_roundtrip(port, k) {
  const frame = (op, id, body = []) => {
    const out = new Uint8Array(4 + body.length);
    out[0] = op;
    out[1] = id;
    out[2] = body.length >> 8;
    out[3] = body.length & 255;
    out.set(body, 4);
    return out;
  };
  const host = new TextEncoder().encode("127.0.0.1");
  const hello = new TextEncoder().encode("hello");
  let result;
  let phase = 0;
  let got = 0;
  const ws = new WebSocket(process.env.BEND_RELAY);
  ws.binaryType = "arraybuffer";
  ws.onopen = () => ws.send(frame(1, 0, [Number(port) >> 8, Number(port) & 255, ...host]));
  ws.onmessage = (ev) => {
    const msg = new Uint8Array(ev.data);
    const op = msg[0];
    if (op === 10 && phase === 0) {
      phase = 1;
      ws.send(frame(2, 0, hello));
    } else if (op === 12 && phase === 1) {
      got += (msg[2] << 8) | msg[3];
      if (got >= hello.length) {
        phase = 2;
        ws.send(frame(3, 0));
        result = got;
        ws.close();
        io_notify();
      }
    } else {
      console.error("relay: " + (msg[0] === 11 ? new TextDecoder().decode(msg.subarray(6)) : "unexpected frame " + op));
      result = 0;
      ws.close();
      io_notify();
    }
  };
  ws.onerror = () => {
    console.error("relay: the WebSocket failed");
    result = 0;
    io_notify();
  };
  io_park_on(undefined, false, k, more, Infinity);
  function more() {
    if (result === undefined) {
      io_park_on(undefined, false, k, more, Infinity);
      return undefined;
    }
    return result;
  }
}

io_eff(CID(Relay.roundtrip), relay_roundtrip);
