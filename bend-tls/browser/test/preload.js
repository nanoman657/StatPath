// Loaded before a Bend program (bun --preload): the relay a page would have open, as the effects
// (effs/web_tcp.js) expect it: globalThis.bend_relay, opened at BEND_RELAY, before the program runs.
import { RelayTcp } from "../tcp_relay_client.js";

const url = process.env.BEND_RELAY;
if (url) {
  const relay = new RelayTcp(url);
  await relay.open();
  globalThis.bend_relay = relay;
}
