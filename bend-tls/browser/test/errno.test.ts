// The page's failure texts (effs/web_tcp.js, WT_TEXT) are the texts the native effects give:
// libc's strerror, as on this host (Linux). A failure reads the same in both builds.
import { test, expect } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { dlopen, FFIType } from "bun:ffi";

const HERE = import.meta.dir;
const src = readFileSync(resolve(HERE, "../effs/web_tcp.js"), "utf8");
const found = src.match(/const WT_TEXT = (\{[\s\S]*?\n\});/);
const table: Record<string, string> = found ? new Function(`return ${found[1]};`)() : {};

const libc = dlopen(process.platform === "darwin" ? "libSystem.dylib" : "libc.so.6", {
  strerror: { args: [FFIType.i32], returns: FFIType.cstring },
});

test("the page's errno table is found and not empty", () => {
  expect(Object.keys(table).length).toBeGreaterThan(10);
});

test("each page text is libc's strerror for its errno", () => {
  for (const [code, text] of Object.entries(table)) {
    expect({ code, text }).toEqual({ code, text: libc.symbols.strerror(Number(code)) });
  }
});
