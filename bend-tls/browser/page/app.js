// The page: opens the relay and makes it the page's bend_relay, then runs the program's main
// through the scheduler. The relay's URL is in ?relay= (else ws://127.0.0.1:8765), and the token
// the relay accepts is in <meta name="bend-relay-token"> (the server that serves the page puts it
// there). The program's output goes to #bend-output; body[data-exit] holds the exit code once the
// program has finished.
import { RelayTcp } from "../tcp_relay_client.js";
import { page_main } from "./program.bend";

const url = new URLSearchParams(location.search).get("relay") ?? "ws://127.0.0.1:8765";
const token = document.querySelector('meta[name="bend-relay-token"]')?.content;
const relay = new RelayTcp(url);
await relay.open(token);
globalThis.bend_relay = relay;
const code = await page_main();
document.body.dataset.exit = String(code);
