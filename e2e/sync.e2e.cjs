// Drives a sync through the built app in Chromium. The app is served by `vite preview` from dist/, GitHub's API
// is answered by this script, and the script checks what the app sent to GitHub and what it stored locally.
// Run with `npm run test:browser`, which builds first.
const { spawn } = require("node:child_process");
const { readFileSync, readdirSync } = require("node:fs");
const { join } = require("node:path");
const assert = require("node:assert/strict");
const { chromium } = require("playwright");

const ROOT = join(__dirname, "..");
const PORT = 4173;
const BASE = `http://127.0.0.1:${PORT}/`;
const GIST_ID = "abc123def456";
const FILE = "statpath-progress.json";

// This device: one lesson and one card the other device has never seen, and XP for a day it did not play.
const LOCAL = {
  version: 1,
  xp: 20,
  xpByDay: { "2026-05-02": 20 },
  lastActiveDay: "2026-05-02",
  streak: 1,
  longestStreak: 1,
  hearts: 5,
  heartsRefillAt: null,
  dailyGoal: 10,
  name: "Ada",
  lessons: { l1: { crowns: 2, attempts: 5, bestAccuracy: 0.8, lastPlayed: 100 } },
  srs: { c1: { id: "c1", lessonId: "l1", interval: 3, ease: 2.5, due: 1000, lapses: 0, reps: 2, lastReview: 200 } },
  achievements: [],
  updatedAt: 200,
};

// The copy already in the gist, from the other device: a different lesson, a later review of the same card, and XP for another day.
const REMOTE = {
  version: 1,
  xp: 30,
  xpByDay: { "2026-05-01": 30 },
  lastActiveDay: "2026-05-01",
  streak: 1,
  longestStreak: 1,
  hearts: 5,
  heartsRefillAt: null,
  dailyGoal: 50,
  name: "Bo",
  lessons: { l2: { crowns: 3, attempts: 1, bestAccuracy: 1, lastPlayed: 60 } },
  srs: { c1: { id: "c1", lessonId: "l1", interval: 4, ease: 2.6, due: 2000, lapses: 0, reps: 3, lastReview: 300 } },
  achievements: ["first"],
  updatedAt: 300,
};

const SYNC = { token: "ghp_e2e_placeholder", gistId: GIST_ID, lastSyncedAt: null, lastError: null };

const CORS = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Headers": "*",
  "Access-Control-Allow-Methods": "GET,PATCH,POST,OPTIONS",
};

const until = async (cond, what, ms = 20_000) => {
  const end = Date.now() + ms;
  while (!cond()) {
    if (Date.now() > end) throw new Error(`timed out waiting for ${what}`);
    await new Promise((r) => setTimeout(r, 100));
  }
};

const waitForServer = async (url) => {
  const end = Date.now() + 60_000;
  for (;;) {
    try {
      if ((await fetch(url)).ok) return;
    } catch {
      /* not up yet */
    }
    if (Date.now() > end) throw new Error(`the preview server did not start at ${url}`);
    await new Promise((r) => setTimeout(r, 300));
  }
};

async function main() {
  // The built app must contain the compiled Bend merge, or this would not be testing it.
  const assets = join(ROOT, "dist", "assets");
  const bundle = readdirSync(assets)
    .filter((f) => f.endsWith(".js"))
    .map((f) => readFileSync(join(assets, f), "utf8"))
    .join("\n");
  assert.ok(bundle.includes("merge_state"), "the built app does not contain the compiled Bend merge");

  const preview = spawn(
    process.execPath,
    [join(ROOT, "node_modules", "vite", "bin", "vite.js"), "preview", "--host", "127.0.0.1", "--port", String(PORT), "--strictPort"],
    { cwd: ROOT, stdio: "ignore" },
  );

  let browser;
  try {
    await waitForServer(BASE);
    browser = await chromium.launch();
    const page = await browser.newPage();

    // Seed both stores once per tab, so a reload does not undo what the app has saved since.
    await page.addInitScript(
      ({ local, sync }) => {
        if (sessionStorage.getItem("e2e-seeded")) return;
        sessionStorage.setItem("e2e-seeded", "1");
        localStorage.setItem("statpath.progress.v1", JSON.stringify(local));
        localStorage.setItem("statpath.sync.v1", JSON.stringify(sync));
      },
      { local: LOCAL, sync: SYNC },
    );

    // GitHub, as the app sees it: GET returns what is stored, PATCH stores what was sent.
    let stored = REMOTE;
    const patches = [];
    await page.route("https://api.github.com/**", async (route) => {
      const req = route.request();
      const path = new URL(req.url()).pathname;
      if (req.method() === "OPTIONS") return route.fulfill({ status: 204, headers: CORS });
      if (req.method() === "GET" && path === `/gists/${GIST_ID}`) {
        return route.fulfill({
          status: 200,
          headers: CORS,
          contentType: "application/json",
          body: JSON.stringify({ id: GIST_ID, files: { [FILE]: { content: JSON.stringify(stored) } } }),
        });
      }
      if (req.method() === "PATCH" && path === `/gists/${GIST_ID}`) {
        const content = JSON.parse(JSON.parse(req.postData()).files[FILE].content);
        patches.push(content);
        stored = content;
        return route.fulfill({ status: 200, headers: CORS, contentType: "application/json", body: JSON.stringify({ id: GIST_ID }) });
      }
      return route.fulfill({ status: 404, headers: CORS, contentType: "application/json", body: "{}" });
    });

    // Opening the app syncs once on its own.
    await page.goto(BASE);
    await until(() => patches.length >= 1, "the first push to GitHub");
    const sent = patches[0];
    assert.deepEqual(sent.lessons.l1, { crowns: 2, attempts: 5, bestAccuracy: 0.8, lastPlayed: 100 }, "this device's lesson");
    assert.deepEqual(sent.lessons.l2, { crowns: 3, attempts: 1, bestAccuracy: 1, lastPlayed: 60 }, "the other device's lesson");
    assert.equal(sent.srs.c1.ease, 2.6, "the card keeps the larger ease");
    assert.equal(sent.srs.c1.lastReview, 300, "the card keeps the later review");
    assert.deepEqual(sent.xpByDay, { "2026-05-01": 30, "2026-05-02": 20 }, "XP per day from both devices");
    assert.equal(sent.xp, 50, "total XP is the sum of the days");

    // The Profile page shows the outcome, and the merged copy is what the device now keeps.
    await page.getByRole("button", { name: /Profile$/ }).click();
    await page.getByText("☁️ Connected").waitFor();
    await until(
      () => page.evaluate(() => document.body.innerText.split("\n").some((l) => l.trim() === "Synced")).then(Boolean, () => false),
      'the "Synced" status',
    );
    const kept = await page.evaluate(() => JSON.parse(localStorage.getItem("statpath.progress.v1")));
    assert.equal(kept.xp, 50, "the device keeps the merged XP");
    assert.ok(kept.lessons.l1 && kept.lessons.l2, "the device keeps both lessons");

    // A second sync finds nothing new, so it does not push again.
    await page.getByRole("button", { name: "Sync now" }).click();
    await until(
      () => page.evaluate(() => document.body.innerText.split("\n").some((l) => l.trim() === "Up to date")).then(Boolean, () => false),
      'the "Up to date" status',
    );
    assert.equal(patches.length, 1, "a sync with nothing new must not push");
    console.log("browser sync test passed: one push with both devices' work, then Up to date");
  } finally {
    if (browser) await browser.close();
    preview.kill();
  }
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
