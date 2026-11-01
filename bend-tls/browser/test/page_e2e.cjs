// Opens the built page in Chromium (Playwright, pre-installed), waits for the program to finish,
// and prints what it printed and the exit code as JSON. Usage: node page_e2e.cjs <page url>
const { chromium } = require("playwright");

(async () => {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  const problems = [];
  page.on("pageerror", (e) => problems.push("pageerror: " + e.message));
  page.on("console", (m) => {
    if (m.type() === "error") problems.push("console: " + m.text());
  });
  await page.goto(process.argv[2]);
  let exit = null;
  try {
    await page.waitForSelector("body[data-exit]", { timeout: 30000 });
    exit = await page.getAttribute("body", "data-exit");
  } catch (e) {
    problems.push("the program did not finish: " + e.message.split("\n")[0]);
  }
  const output = await page.textContent("#bend-output");
  await browser.close();
  process.stdout.write(JSON.stringify({ exit, output, problems }) + "\n");
})().catch((e) => {
  process.stderr.write(String(e && e.stack || e) + "\n");
  process.exit(1);
});
