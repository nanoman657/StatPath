// Loaded before a Bend program (bun --preload): the relay a page would have open, as the effects
// (effs/web_tcp.js) expect it: globalThis.bend_relay, opened at BEND_RELAY with BEND_RELAY_TOKEN,
// before the program runs. The WebSocket presents the test origin, as a page's browser does.
import { RelayTcp } from "../tcp_relay_client.js";
import { PageSocket } from "./support.ts";

const url = process.env.BEND_RELAY;
if (url) {
  const relay = new RelayTcp(url, PageSocket);
  await relay.open(process.env.BEND_RELAY_TOKEN);
  globalThis.bend_relay = relay;
}
