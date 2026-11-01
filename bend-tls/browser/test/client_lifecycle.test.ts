// The page client's connection ids, when a frame of a closed connection is still in flight (PROTOCOL.md).
// The relay sends a frame before it processes the CLOSE that follows it, so the frame can reach the page
// after the page has closed the id and connected it again. The page must not hand that frame to the new
// connection. The relay here is scripted: it answers what the test says, and delivers its frames when the
// test says, so the test decides what is in flight.
import { test, expect } from "bun:test";
import { RelayTcp, encodeFrame, decodeFrame, OP } from "../tcp_relay_client.js";

const enc = new TextEncoder();
const dec = new TextDecoder();
const TOKEN = "token-for-the-client-tests";

// A WebSocket stand-in for the relay. The page's frames arrive in send() and go to holder.respond, which
// delivers whatever replies the test wants (deliver() calls onmessage synchronously).
function scriptedRelay(respond) {
  const holder = { ws: null, respond };
  class Scripted {
    constructor(_url) {
      holder.ws = this;
      this.readyState = 0;
      this.binaryType = "";
      this.onopen = null;
      this.onmessage = null;
      this.onclose = null;
      this.onerror = null;
      this.sent = [];
      queueMicrotask(() => {
        this.readyState = 1;
        this.onopen?.();
      });
    }
    send(data) {
      const f = decodeFrame(new Uint8Array(data));
      this.sent.push(f);
      holder.respond(f, this);
    }
    close() {
      this.readyState = 3;
    }
    deliver(op, id, body = new Uint8Array(0)) {
      this.onmessage?.({ data: encodeFrame(op, id, body).buffer });
    }
  }
  return { WebSocketImpl: Scripted, holder };
}

// the replies of a relay that answers AUTH and OK, and nothing else
function basicReplies(f, r) {
  if (f.op === OP.AUTH) r.deliver(OP.AUTHOK, 0);
  else if (f.op === OP.CONNECT) r.deliver(OP.OK, f.id);
}

test("a frame of a closed connection that arrives after the id is reused does not reach the new connection", async () => {
  const { WebSocketImpl, holder } = scriptedRelay(basicReplies);
  const net = new RelayTcp("ws://scripted", WebSocketImpl);
  await net.open(TOKEN);
  const id = await net.connect("h", 1);
  expect(id).toBe(0);
  // The relay sent DATA "OLD" for connection 0 before it processed the CLOSE, so the frame is in flight when
  // the page closes the id and connects again. The new connection is answered, and its own data "NEW" follows.
  net.close(0);
  holder.respond = (f, r) => {
    if (f.op === OP.CONNECT) {
      r.deliver(OP.DATA, 0, enc.encode("OLD")); // the stale frame, arriving after the page's new CONNECT
      r.deliver(OP.OK, f.id);
      r.deliver(OP.DATA, f.id, enc.encode("NEW"));
    } else basicReplies(f, r);
  };
  const id2 = await net.connect("h", 2);
  const first = await net.recv(id2, 100);
  expect(dec.decode(first)).toBe("NEW");
  net.shutdown();
});

test("an id is not reused until the relay confirms its close", async () => {
  // Once the relay has dropped the connection it answers CLOSE with CLOSED (op 17). Until that arrives the
  // page does not hand the id out again, so a connect after a close takes another id.
  const { WebSocketImpl, holder } = scriptedRelay(basicReplies);
  const net = new RelayTcp("ws://scripted", WebSocketImpl);
  await net.open(TOKEN);
  const id = await net.connect("h", 1);
  net.close(id); // the relay does not answer yet
  const id2 = await net.connect("h", 1);
  expect(id2).not.toBe(id);
  net.shutdown();
});

test("once the relay has confirmed the close, the id is free again", async () => {
  const CLOSED = 17;
  const { WebSocketImpl, holder } = scriptedRelay(basicReplies);
  const net = new RelayTcp("ws://scripted", WebSocketImpl);
  await net.open(TOKEN);
  const id = await net.connect("h", 1);
  holder.respond = (f, r) => {
    basicReplies(f, r);
    if (f.op === OP.CLOSE) r.deliver(CLOSED, f.id);
  };
  net.close(id);
  const id2 = await net.connect("h", 1);
  expect(id2).toBe(id);
  net.shutdown();
});

test("a FAIL in flight for a closed id does not fail the connection that reuses the id", async () => {
  const { WebSocketImpl, holder } = scriptedRelay(basicReplies);
  const net = new RelayTcp("ws://scripted", WebSocketImpl);
  await net.open(TOKEN);
  await net.connect("h", 1);
  net.close(0);
  holder.respond = (f, r) => {
    if (f.op === OP.CONNECT) {
      r.deliver(OP.FAIL, 0, new Uint8Array([0, 111])); // the relay failed connection 0 before the CLOSE
      r.deliver(OP.OK, f.id);
    } else basicReplies(f, r);
  };
  const id2 = await net.connect("h", 2);
  // the new connection works: nothing it was not sent has failed it
  expect(id2).not.toBe(0);
  net.shutdown();
});

test("the relay and the page client agree on the protocol's op codes", async () => {
  // relay/relay.ts keeps its own copy of the table: the two must not drift apart
  const { OP: relayOP } = await import("../relay/relay.ts");
  const { OP: clientOP } = await import("../tcp_relay_client.js");
  expect(relayOP).toEqual(clientOP);
});
