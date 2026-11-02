// The transparency and the operation codes (Transparency.lean, in this folder), and the code they describe.
// The Lean file proves that the relay's byte operations never change, drop or reorder a byte, and that the
// operation codes it lists are distinct, one byte each, and have no LISTEN or ACCEPT. Those statements are about
// the Lean copies, so the other tests here check the copies against the sources: the operation table in
// PROTOCOL.md, and the OP maps of relay/relay.ts and tcp_relay_client.js. The file compiles with no sorry; the
// compile is skipped when no Lean 4 toolchain is found (set LEAN to choose one), as transitions.test.ts does.
import { test, expect } from "bun:test";
import { existsSync, readFileSync } from "node:fs";
import { homedir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const MODEL = join(here, "Transparency.lean");
const PROTOCOL = join(here, "..", "..", "PROTOCOL.md");
const RELAY = join(here, "..", "..", "relay", "relay.ts");
const CLIENT = join(here, "..", "..", "tcp_relay_client.js");

const PINNED_LEAN = join(homedir(), ".elan", "toolchains", "leanprover--lean4---v4.34.0", "bin", "lean");
function findLean(): string | null {
  const candidates = [process.env.LEAN, PINNED_LEAN, Bun.which("lean")];
  for (const c of candidates) if (c && existsSync(c)) return c;
  return null;
}
const lean = findLean();

// the operation table of PROTOCOL.md: rows "| 15 | AUTH | ..."
function protocolTable(): Map<string, number> {
  const rows = new Map<string, number>();
  for (const line of readFileSync(PROTOCOL, "utf8").split("\n")) {
    const m = line.match(/^\|\s*(\d+)\s*\|\s*([A-Z]+)\s*\|/);
    if (m) rows.set(m[2], Number(m[1]));
  }
  return rows;
}

// the OP object of a source file: "NAME: n" pairs inside "export const OP = { ... }"
function opMap(path: string): Map<string, number> {
  const src = readFileSync(path, "utf8");
  const block = src.match(/const OP\s*=\s*\{([\s\S]*?)\}/);
  expect(block).not.toBeNull();
  const ops = new Map<string, number>();
  for (const m of block![1].matchAll(/([A-Z]+)\s*:\s*(\d+)/g)) ops.set(m[1], Number(m[2]));
  return ops;
}

// the codes the Lean file lists: (n, "NAME") pairs in namespace Wire
function leanCodes(): Map<string, number> {
  const src = readFileSync(MODEL, "utf8");
  const block = src.match(/def codes : List \(Nat × String\) :=([\s\S]*?)\n\n/);
  expect(block).not.toBeNull();
  const ops = new Map<string, number>();
  for (const m of block![1].matchAll(/\((\d+),\s*"([A-Z]+)"\)/g)) ops.set(m[2], Number(m[1]));
  return ops;
}

function sameMap(a: Map<string, number>, b: Map<string, number>): boolean {
  if (a.size !== b.size) return false;
  for (const [k, v] of a) if (b.get(k) !== v) return false;
  return true;
}

test("PROTOCOL.md's operation table is the one the Lean file lists", () => {
  expect(sameMap(protocolTable(), leanCodes())).toBe(true);
});

test("relay/relay.ts and tcp_relay_client.js use the codes of the table", () => {
  const table = protocolTable();
  // the relay has every operation the page can send or receive; the client has the ones the page uses
  expect(sameMap(opMap(RELAY), table)).toBe(true);
  for (const [name, code] of opMap(CLIENT)) expect(table.get(name)).toBe(code);
});

test("LISTEN and ACCEPT are in neither the table nor the code", () => {
  const all = [protocolTable(), opMap(RELAY), opMap(CLIENT)];
  for (const m of all) {
    expect(m.has("LISTEN")).toBe(false);
    expect(m.has("ACCEPT")).toBe(false);
  }
  const src = [PROTOCOL, RELAY, CLIENT].map((p) => readFileSync(p, "utf8")).join("\n");
  expect(/\bLISTEN\b|\bACCEPT\b/.test(src)).toBe(false);
});

test.skipIf(lean === null)("Transparency.lean compiles with no sorry", async () => {
  const proc = Bun.spawn([lean!, MODEL], { stdout: "pipe", stderr: "pipe" });
  const [out, err] = await Promise.all([new Response(proc.stdout).text(), new Response(proc.stderr).text()]);
  const code = await proc.exited;
  expect(code).toBe(0);
  expect(out + err).not.toContain("sorry");
  expect(out + err).not.toContain("error");
}, 600_000);
