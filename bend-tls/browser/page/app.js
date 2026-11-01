// The page: opens the relay (the URL is in ?relay=, else ws://127.0.0.1:8765), makes it the page's
// bend_relay, then runs the program's main through the scheduler. The program's output goes to
// #bend-output; the page's exit code is in body[data-exit] when the program has finished.
import { RelayTcp } from "../tcp_relay_client.js";
import { page_main } from "./program.bend";

const url = new URLSearchParams(location.search).get("relay") ?? "ws://127.0.0.1:8765";
const relay = new RelayTcp(url);
await relay.open();
globalThis.bend_relay = relay;
const code = await page_main();
document.body.dataset.exit = String(code);
