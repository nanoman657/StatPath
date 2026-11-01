// The page, built by the Bend CLI (bend page/index.html -o dir), served, and run in Chromium
// (Playwright): the program talks to a relay, and what it prints is on the page.
import { test, expect } from "bun:test";
import { testRelay, TEST_TOKEN } from "./support.ts";
import { resolve, join } from "node:path";
import { existsSync, readFileSync, writeFileSync, unlinkSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";

const HERE = import.meta.dir;
const PAGE = resolve(HERE, "../page");
const MAIN = process.env.BEND_MAIN ?? "/tmp/claude-0/src/bend-async/bend2/main.ts";
const E2E = resolve(HERE, "page_e2e.cjs");

test.skipIf(!existsSync(MAIN))("the page runs a program that talks to the relay; its output is on the page", async () => {
  const echo = Bun.listen({
    hostname: "127.0.0.1",
    port: 0,
    socket: { open() {}, data(s, d) { s.write(d); }, close() {}, error() {} },
  });
  // the program: the echo page program, with the echo peer's port and this folder's import path
  const program = join(PAGE, "program.bend");
  writeFileSync(
    program,
    readFileSync(resolve(HERE, "../tests/web/echo.bend.tpl"), "utf8")
      .replace("__ECHO__", String(echo.port))
      .replace("../../tcp.bend", "../tcp.bend"),
  );
  const dist = mkdtempSync(join(tmpdir(), "bend-page-"));
  let server: ReturnType<typeof Bun.serve> | null = null;
  let relay: ReturnType<typeof testRelay> | null = null;
  try {
    const build = Bun.spawnSync([process.execPath, MAIN, join(PAGE, "index.html"), "-o", dist], {
      stdout: "pipe",
      stderr: "pipe",
    });
    expect(build.stderr.toString()).toBe("");
    expect(build.exitCode).toBe(0);

    // the page is served with the token in its meta tag, as the page's server would put it
    server = Bun.serve({
      hostname: "127.0.0.1",
      port: 0,
      async fetch(req) {
        const path = new URL(req.url).pathname;
        const name = path === "/" ? "index.html" : path.slice(1);
        const file = Bun.file(join(dist, name));
        if (!(await file.exists())) return new Response("not found", { status: 404 });
        if (name !== "index.html") return new Response(file);
        const html = (await file.text()).replace(
          "</head>",
          `<meta name="bend-relay-token" content="${TEST_TOKEN}"></head>`,
        );
        return new Response(html, { headers: { "content-type": "text/html; charset=utf-8" } });
      },
    });
    // the relay accepts the page's origin: the address the page is served from
    relay = testRelay(
      [{ host: "127.0.0.1", ports: [echo.port] }],
      {},
      { origins: [`http://127.0.0.1:${server.port}`] },
    );
    const url = `http://127.0.0.1:${server.port}/index.html?relay=${encodeURIComponent(relay.url)}`;
    const run = Bun.spawn(["node", E2E, url], { stdout: "pipe", stderr: "pipe" });
    const [out, err] = await Promise.all([new Response(run.stdout).text(), new Response(run.stderr).text()]);
    await run.exited;
    expect(err).toBe("");
    const got = JSON.parse(out.trim().split("\n").pop()!);
    expect(got.problems).toEqual([]);
    expect(got.output.trim()).toBe("recv: hé");
    expect(got.exit).not.toBeNull();
  } finally {
    server?.stop(true);
    unlinkSync(program);
    rmSync(dist, { recursive: true, force: true });
    relay?.stop();
    echo.stop(true);
  }
}, 240000);
