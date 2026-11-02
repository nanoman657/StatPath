// One discard at a time (tcp_relay_client.js discard, and Relay.lean's model of it): a discard while one is pending is
// refused with EBUSY (16) and is not sent. A second DISCARD would overwrite the first one's callback, and the relay's
// reply to the first would then reset the page's count while a send is still queued at the relay. The test calls
// discard twice with no await between, so the second call finds the first still pending.
import { test, expect } from "bun:test";
import { RelayTcp, OP, decodeFrame } from "../tcp_relay_client.js";
import { testRelay, PageSocket, TEST_TOKEN } from "./support.ts";

class Counting extends PageSocket {
  static discards = 0;
  send(data: any) {
    const f = decodeFrame(new Uint8Array(data));
    if (f && f.op === OP.DISCARD) Counting.discards++;
    return super.send(data);
  }
}

test("a discard while one is pending is refused, and is not sent", async () => {
  const peer = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: { open() {}, data() {}, close() {}, error() {} },
  });
  const r = testRelay([{ host: "127.0.0.1", ports: [peer.port] }], {}, {}, {});
  Counting.discards = 0;
  const net = new RelayTcp(r.url, Counting as any);
  try {
    await net.open(TEST_TOKEN);
    const id = await net.connect("127.0.0.1", peer.port);
    const first = new Promise((res) => net.discard(id, res));
    let second: any = null;
    net.discard(id, (res: any) => (second = res));
    expect(second).not.toBeNull();
    expect(second.error.errno).toBe(16);
    const d1: any = await first;
    expect(d1.error).toBeUndefined();
    expect(Counting.discards).toBe(1);
    // once the first has completed, a discard is allowed again
    const d2: any = await new Promise((res) => net.discard(id, res));
    expect(d2.error).toBeUndefined();
    expect(Counting.discards).toBe(2);
  } finally {
    net.close?.();
    peer.stop(true);
    r.close?.();
  }
});
