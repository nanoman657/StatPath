// Conformance of the page client (tcp_relay_client.js) to its model (Page in Relay.lean, in this folder).
//
// Random traces of the page's calls and of the relay's frames run through the client, over a fake WebSocket
// that logs the frames the client sends and delivers the frames the trace gives. The same traces run through
// the model (`lean --run Relay.lean page`). Every frame the client sends and every callback it makes, in
// order, must be the model's: the observable behaviour, for any inputs the trace has.
//
// Needs the Lean 4.34.0 toolchain (LEAN, or the elan toolchain). Skipped without it.
import { test, expect } from "bun:test";
import { existsSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { RelayTcp, encodeFrame, decodeFrame, OP, MAX_BODY, TcpError } from "../../tcp_relay_client.js";

const here = dirname(fileURLToPath(import.meta.url));
const MODEL = join(here, "Relay.lean");
const PINNED_LEAN = join(homedir(), ".elan", "toolchains", "leanprover--lean4---v4.34.0", "bin", "lean");
const LEAN = [process.env.LEAN, PINNED_LEAN, Bun.which("lean")].find((c) => c && existsSync(c)) ?? null;
const TRACES = Number(process.env.CLIENT_TRACES ?? 300);
const STEPS = 40;
const TOKEN = "token-for-the-client-conformance";

// ---- the traces ----

function prng(seed: number) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const ERRNOS = [111, 104, 110, 32, 5];

function genTrace(seed: number): string[] {
  const r = prng(seed);
  const int = (n: number) => Math.floor(r() * n);
  const out: string[] = [];
  const ids = [0, 1, 2];
  for (let i = 0; i < STEPS; i++) {
    const x = r();
    const id = ids[int(ids.length)];
    if (x < 0.14) out.push("connect");
    else if (x < 0.2) out.push(`close ${id}`);
    else if (x < 0.32) {
      // sends: small ones, and some that the client frames in several SEND frames
      const n = r() < 0.2 ? MAX_BODY + int(150000) : int(3000);
      out.push(`send ${id} ${n}`);
    } else if (x < 0.4) out.push(`recv ${id} ${1 + int(r() < 0.3 ? 70000 : 3000)}`);
    else if (x < 0.44) {
      out.push(`discard ${id}`);
      // the relay answers a DISCARD with a WRITTEN whose flag is 1; often at once
      if (r() < 0.5) out.push(`frame WRITTEN ${id} ${int(200000)} 1`);
    }
    else if (x < 0.52) out.push(`frame OK ${id}`);
    else if (x < 0.56) out.push(`frame FAIL ${id} ${ERRNOS[int(ERRNOS.length)]}`);
    else if (x < 0.66) out.push(`frame WRITTEN ${id} ${int(200000)} ${r() < 0.4 ? 1 : 0}`);
    else if (x < 0.82) out.push(`frame DATA ${id} ${1 + int(3000)}`);
    else if (x < 0.86) out.push(`frame EOF ${id}`);
    else out.push(`frame CLOSED ${id}`);
  }
  return out;
}

// ---- the model ----

async function modelOutputs(traces: string[][]): Promise<string[][]> {
  const input = traces.map((t) => ["trace", ...t].join("\n")).join("\n") + "\n";
  const proc = Bun.spawn([LEAN!, "--run", MODEL, "page"], { stdin: new Blob([input]), stdout: "pipe", stderr: "pipe" });
  const [out, err, code] = await Promise.all([
    new Response(proc.stdout).text(),
    new Response(proc.stderr).text(),
    proc.exited,
  ]);
  if (code !== 0) throw new Error(`lean --run page failed (${code}): ${err}`);
  const res: string[][] = [];
  let cur: string[] = [];
  for (const line of out.split("\n")) {
    if (line === "") continue;
    if (line === "end") {
      res.push(cur);
      cur = [];
    } else cur.push(line);
  }
  return res;
}

// ---- the client ----

const enc = new TextEncoder();

function u32(n: number): Uint8Array {
  return new Uint8Array([(n >>> 24) & 255, (n >>> 16) & 255, (n >>> 8) & 255, n & 255]);
}

function readU32(b: Uint8Array): number {
  return b[0] * 0x1000000 + (b[1] << 16) + (b[2] << 8) + b[3];
}

// the WebSocket the client talks through: it logs the frames the client sends, and delivers the trace's
// frames when the test calls deliver()
function fakeSocket(log: (s: string) => void) {
  const holder: { ws: any } = { ws: null };
  class Fake {
    readyState = 0;
    binaryType = "";
    onopen: any = null;
    onmessage: any = null;
    onclose: any = null;
    onerror: any = null;
    constructor(_url: string) {
      holder.ws = this;
      queueMicrotask(() => {
        this.readyState = 1;
        this.onopen?.();
      });
    }
    send(data: Uint8Array) {
      const f = decodeFrame(new Uint8Array(data));
      if (!f) return;
      if (f.op === OP.AUTH) {
        this.deliver(OP.AUTHOK, 0);
        return;
      }
      if (f.op === OP.CONNECT) log(`out CONNECT ${f.id}`);
      else if (f.op === OP.SEND) log(`out SEND ${f.id} ${f.body.length}`);
      else if (f.op === OP.READ) log(`out READ ${f.id} ${readU32(f.body)}`);
      else if (f.op === OP.DISCARD) log(`out DISCARD ${f.id}`);
      else if (f.op === OP.CLOSE) log(`out CLOSE ${f.id}`);
    }
    close() {
      this.readyState = 3;
    }
    deliver(op: number, id: number, body: Uint8Array = new Uint8Array(0)) {
      const frame = new Uint8Array(4 + body.length);
      frame[0] = op;
      frame[1] = id;
      frame[2] = body.length >> 8;
      frame[3] = body.length & 255;
      frame.set(body, 4);
      this.onmessage?.({ data: frame.buffer });
    }
  }
  return { WebSocketImpl: Fake, holder };
}

// runs one trace through the client; returns the frames and callbacks, in order
async function clientOutputs(trace: string[]): Promise<string[]> {
  const out: string[] = [];
  const log = (s: string) => out.push(s);
  const { WebSocketImpl, holder } = fakeSocket(log);
  const net = new RelayTcp("ws://page-model", WebSocketImpl);
  await net.open(TOKEN);
  const ws = holder.ws;
  let lastConnect = -1;
  // the frames of a connect are logged synchronously; remember which id it chose
  const origSend = ws.send.bind(ws);
  ws.send = (data: Uint8Array) => {
    const f = decodeFrame(new Uint8Array(data));
    if (f && f.op === OP.CONNECT) lastConnect = f.id;
    return origSend(data);
  };
  for (const line of trace) {
    const w = line.split(" ");
    if (w[0] === "connect") {
      let myId = -1;
      try {
        net.connectAt("127.0.0.1", 4242, (r: any) => {
          if (r.error) log(`connectErr ${myId} ${r.error.errno}`);
          else log(`connected ${r.id}`);
        });
        myId = lastConnect;
      } catch {
        log("thrown");
      }
    } else if (w[0] === "close") {
      net.close(Number(w[1]));
    } else if (w[0] === "send") {
      const id = Number(w[1]);
      const n = Number(w[2]);
      try {
        net.startSend(id, new Uint8Array(n), (r: any) => {
          if (r.error) log(`sendErr ${id} ${r.error.errno} ${r.error.written === undefined ? "-" : r.error.written}`);
          else log(`sent ${id}`);
        });
      } catch {
        log("thrown");
      }
    } else if (w[0] === "recv") {
      const id = Number(w[1]);
      const max = Number(w[2]);
      // the same steps as recv(): take what is there, or wait for the next change
      const attempt = () => {
        let res: any;
        try {
          res = net.takeNow(id, max);
        } catch (e: any) {
          log(`recvErr ${id} ${e.errno}`);
          return;
        }
        if (res === null) {
          net.onReadable(id, attempt);
          return;
        }
        log(res.eof ? `eof ${id}` : `data ${id} ${res.bytes.length}`);
      };
      attempt();
    } else if (w[0] === "discard") {
      const id = Number(w[1]);
      try {
        net.discard(id, (r: any) => {
          if (r.error) log(`discardErr ${id} ${r.error.errno}`);
          else log(`discarded ${id} ${r.written}`);
        });
      } catch {
        log("thrown");
      }
    } else if (w[0] === "frame") {
      const kind = w[1];
      const id = Number(w[2]);
      if (kind === "OK") ws.deliver(OP.OK, id);
      else if (kind === "FAIL") {
        const e = Number(w[3]);
        ws.deliver(OP.FAIL, id, new Uint8Array([e >> 8, e & 255]));
      } else if (kind === "WRITTEN") {
        const body = new Uint8Array(5);
        body.set(u32(Number(w[3])));
        body[4] = Number(w[4]);
        ws.deliver(OP.WRITTEN, id, body);
      } else if (kind === "DATA") ws.deliver(OP.DATA, id, new Uint8Array(Number(w[3])));
      else if (kind === "EOF") ws.deliver(OP.EOF, id);
      else if (kind === "CLOSED") ws.deliver(17, id);
    }
  }
  // the trace ends here: no shutdown, which would hear the open connections
  return out;
}

// ---- the test ----

test.skipIf(LEAN === null)(
  "the page client does what the model says, on random traces of calls and frames",
  async () => {
    const traces: string[][] = [];
    for (let seed = 1; seed <= TRACES; seed++) traces.push(genTrace(seed));
    const expected = await modelOutputs(traces);
    expect(expected.length).toBe(traces.length);
    // every kind of frame and callback must occur, or the traces do not test it
    const kinds = new Map<string, number>();
    for (const t of expected) {
      for (const l of t) {
        const w = l.split(" ");
        const key = w[0] === "out" ? `out ${w[1]}` : w[0];
        kinds.set(key, (kinds.get(key) ?? 0) + 1);
      }
    }
    for (const k of ["out CONNECT", "out SEND", "out READ", "out DISCARD", "out CLOSE", "connected", "connectErr",
      "sent", "sendErr", "discarded", "discardErr", "data", "eof", "recvErr", "thrown"]) {
      expect(kinds.get(k) ?? 0, `lines of kind ${k}`).toBeGreaterThan(0);
    }
    let lines = 0;
    for (let i = 0; i < traces.length; i++) {
      const actual = await clientOutputs(traces[i]);
      lines += actual.length;
      if (JSON.stringify(actual) !== JSON.stringify(expected[i])) {
        let at = 0;
        while (at < actual.length && at < expected[i].length && actual[at] === expected[i][at]) at++;
        throw new Error(
          `trace ${i + 1} differs at line ${at}: client ${JSON.stringify(actual.slice(at, at + 3))}, ` +
            `model ${JSON.stringify(expected[i].slice(at, at + 3))}`,
        );
      }
    }
    const tally = [...kinds].sort().map(([k, n]) => `${k}:${n}`).join(" ");
    console.log(`client conformance: ${traces.length} traces, ${lines} frames and callbacks\n  ${tally}`);
  },
  600_000,
);
