import { describe, expect, it } from "vitest";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { mergeProgress } from "../src/engine/merge";
import { defaultProgress, type LessonProgress, type Progress, type SrsCard } from "../src/engine/progress";
import bend from "../bend-engine/merge.mjs";

// The Bend merge (bend-engine/merge.bend, compiled to merge.mjs) against mergeProgress. The Bend data is
// the compiler's own shapes: a constructor is { $: name, field: value }, a List is Con/Nil, a Maybe is
// Some/None, a Nat is a number and a String is a string.

const ROOT = join(__dirname, "..", "bend-engine");

// A deterministic generator, so a failure can be reproduced from its trial number.
const rng = (seed: number) => () => {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};

const LESSON_IDS = ["l1", "l2", "l3", "l4"];
const CARD_IDS = ["c1", "c2", "c3", "c4", "c5"];
const DAYS = ["2026-05-01", "2026-05-02", "2026-05-03", "2026-05-04"];

// Small values make ties common; a large timestamp sometimes makes them rare.
const pick = <T,>(r: () => number, xs: T[]): T => xs[Math.floor(r() * xs.length)];
const stamp = (r: () => number): number => (r() < 0.5 ? Math.floor(r() * 4) : 1_750_000_000_000 + Math.floor(r() * 3));
const subset = (r: () => number, ids: string[]): string[] => ids.filter(() => r() < 0.6);

function randomProgress(r: () => number): Progress {
  const lessons: Record<string, LessonProgress> = {};
  for (const id of subset(r, LESSON_IDS)) {
    lessons[id] = {
      crowns: Math.floor(r() * 6),
      attempts: Math.floor(r() * 5),
      bestAccuracy: Math.floor(r() * 4) * 25,
      lastPlayed: stamp(r),
    };
  }
  const srs: Record<string, SrsCard> = {};
  for (const id of subset(r, CARD_IDS)) {
    const card: SrsCard = {
      id,
      lessonId: pick(r, LESSON_IDS),
      interval: Math.floor(r() * 4),
      ease: 130 + Math.floor(r() * 3) * 50,
      due: stamp(r),
      lapses: Math.floor(r() * 3),
      reps: Math.floor(r() * 3),
    };
    if (r() < 0.7) card.lastReview = stamp(r);
    srs[id] = card;
  }
  const xpByDay: Record<string, number> = {};
  for (const d of subset(r, DAYS)) xpByDay[d] = Math.floor(r() * 4) * 10;
  return { ...defaultProgress(), lessons, srs, xpByDay };
}

// The Bend shapes of a Progress's learning data, with each map's keys in String order.
const byKey = (a: string, b: string): number => (a < b ? -1 : a > b ? 1 : 0);
const list = (xs: unknown[]): unknown => xs.reduceRight<unknown>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
const maybe = (v: number | undefined): unknown => (v === undefined ? { $: "None" } : { $: "Some", value: v });

function toBend(p: Progress): unknown {
  const lessons = Object.keys(p.lessons).sort(byKey).map((key) => {
    const l = p.lessons[key];
    return { $: "LEntry", key, val: { $: "Lp", crowns: l.crowns, attempts: l.attempts, best: l.bestAccuracy, played: l.lastPlayed } };
  });
  const srs = Object.keys(p.srs).sort(byKey).map((key) => {
    const c = p.srs[key];
    return {
      $: "CEntry",
      key,
      val: { $: "Card", id: c.id, lessonId: c.lessonId, interval: c.interval, ease: c.ease, due: c.due, lapses: c.lapses, reps: c.reps, last: maybe(c.lastReview) },
    };
  });
  const xp = Object.keys(p.xpByDay).sort(byKey).map((key) => ({ $: "XEntry", key, val: p.xpByDay[key] }));
  return { $: "St", lessons: list(lessons), srs: list(srs), xpByDay: list(xp) };
}

// The result of mergeProgress in the same fields, from the Bend output.
function fromBendOut(out: any): Pick<Progress, "lessons" | "srs" | "xpByDay" | "xp"> {
  const items = (l: any): any[] => {
    const xs: any[] = [];
    for (let x = l; x.$ === "Con"; x = x.tail) xs.push(x.head);
    return xs;
  };
  const lessons: Record<string, LessonProgress> = {};
  for (const e of items(out.lessons)) {
    lessons[e.key] = { crowns: e.val.crowns, attempts: e.val.attempts, bestAccuracy: e.val.best, lastPlayed: e.val.played };
  }
  const srs: Record<string, SrsCard> = {};
  for (const e of items(out.srs)) {
    const c = e.val;
    const card: SrsCard = { id: c.id, lessonId: c.lessonId, interval: c.interval, ease: c.ease, due: c.due, lapses: c.lapses, reps: c.reps };
    if (c.last.$ === "Some") card.lastReview = c.last.value;
    srs[e.key] = card;
  }
  const xpByDay: Record<string, number> = {};
  for (const e of items(out.xpByDay)) xpByDay[e.key] = e.val;
  return { lessons, srs, xpByDay, xp: out.xp };
}

const inScope = (p: Progress) => ({ lessons: p.lessons, srs: p.srs, xpByDay: p.xpByDay, xp: p.xp });

describe("the Bend learning-data merge against mergeProgress", () => {
  it("agrees with mergeProgress on 10,000 random pairs, with ties and missing entries", () => {
    const r = rng(20260505);
    let mismatch: string | null = null;
    for (let trial = 0; trial < 10_000 && mismatch === null; trial++) {
      const a = randomProgress(r);
      const b = randomProgress(r);
      const want = inScope(mergeProgress(a, b));
      const got = fromBendOut(bend.merge_state(toBend(a), toBend(b)));
      if (JSON.stringify(want) !== JSON.stringify(got) && JSON.stringify(sortedJson(want)) !== JSON.stringify(sortedJson(got))) {
        mismatch = `trial ${trial}\na: ${JSON.stringify(a)}\nb: ${JSON.stringify(b)}\nwant: ${JSON.stringify(want)}\ngot:  ${JSON.stringify(got)}`;
      }
    }
    expect(mismatch).toBeNull();
  });

  it("orders keys as JavaScript orders them, on random strings", () => {
    const r = rng(7);
    const alphabet = "abcXYZ019-_ é";
    const word = () => Array.from({ length: Math.floor(r() * 4) }, () => pick(r, [...alphabet])).join("");
    for (let i = 0; i < 2000; i++) {
      const a = word();
      const b = word();
      const got = (bend.skey_cmp(a, b) as { $: string }).$;
      const want = a < b ? "LT" : a === b ? "EQ" : "GT";
      expect(got, `${JSON.stringify(a)} vs ${JSON.stringify(b)}`).toBe(want);
    }
  });

  it("the compiled merges are commutative on random pairs, the SRS merge included", () => {
    // Lean: lessons_comm, xp_comm, xsum_comm, srs_comm and state_comm.
    const r = rng(20260506);
    for (let trial = 0; trial < 10_000; trial++) {
      const a = toBend(randomProgress(r));
      const b = toBend(randomProgress(r));
      const ab = fromBendOut(bend.merge_state(a, b));
      const ba = fromBendOut(bend.merge_state(b, a));
      expect(sortedJson(ab.lessons), `lessons, trial ${trial}`).toEqual(sortedJson(ba.lessons));
      expect(ab.xp, `xp, trial ${trial}`).toBe(ba.xp);
      expect(sortedJson(ab.xpByDay), `xpByDay, trial ${trial}`).toEqual(sortedJson(ba.xpByDay));
      expect(sortedJson(ab.srs), `srs, trial ${trial}`).toEqual(sortedJson(ba.srs));
    }
  });

  it("the tie-break keeps the card with the larger content, in either order (ease)", () => {
    // Two cards that tie on lastReview, reps and due, differing only in ease: the larger content wins.
    const card = (ease: number): SrsCard => ({ id: "c1", lessonId: "l1", interval: 1, ease, due: 5, lapses: 0, reps: 1, lastReview: 7 });
    const a: Progress = { ...defaultProgress(), srs: { c1: card(200) } };
    const b: Progress = { ...defaultProgress(), srs: { c1: card(250) } };
    expect(mergeProgress(a, b).srs.c1.ease).toBe(250);
    expect(mergeProgress(b, a).srs.c1.ease).toBe(250);
    expect(fromBendOut(bend.merge_state(toBend(a), toBend(b))).srs.c1.ease).toBe(250);
    expect(fromBendOut(bend.merge_state(toBend(b), toBend(a))).srs.c1.ease).toBe(250);
  });

  it("the tie-break counts an absent lastReview as before any time (absent against 0)", () => {
    const base = { id: "c1", lessonId: "l1", interval: 1, ease: 200, due: 5, lapses: 0, reps: 1 };
    const a: Progress = { ...defaultProgress(), srs: { c1: { ...base } as SrsCard } };
    const b: Progress = { ...defaultProgress(), srs: { c1: { ...base, lastReview: 0 } as SrsCard } };
    expect(mergeProgress(a, b).srs.c1.lastReview).toBe(0);
    expect(mergeProgress(b, a).srs.c1.lastReview).toBe(0);
    expect(fromBendOut(bend.merge_state(toBend(a), toBend(b))).srs.c1.lastReview).toBe(0);
    expect(fromBendOut(bend.merge_state(toBend(b), toBend(a))).srs.c1.lastReview).toBe(0);
  });

  it("the compiled merges are idempotent: merging a copy with itself gives the copy", () => {
    // Lean: lessons_idem, xp_idem and srs_idem.
    const r = rng(20260507);
    for (let trial = 0; trial < 2_000; trial++) {
      const p = randomProgress(r);
      const got = fromBendOut(bend.merge_state(toBend(p), toBend(p)));
      expect(sortedJson(got.lessons), `lessons, trial ${trial}`).toEqual(sortedJson(p.lessons));
      expect(sortedJson(got.srs), `srs, trial ${trial}`).toEqual(sortedJson(p.srs));
      expect(sortedJson(got.xpByDay), `xpByDay, trial ${trial}`).toEqual(sortedJson(p.xpByDay));
      expect(got.xp, `xp, trial ${trial}`).toBe(Object.values(p.xpByDay).reduce((t, v) => t + v, 0));
    }
  });

});

// Sorting keys inside JSON, so a comparison does not depend on the order an object was built in.
function sortedJson(v: unknown): unknown {
  if (Array.isArray(v)) return v.map(sortedJson);
  if (v && typeof v === "object") {
    return Object.fromEntries(Object.keys(v).sort().map((k) => [k, sortedJson((v as Record<string, unknown>)[k])]));
  }
  return v;
}

const bendInstalled = (() => {
  try {
    execFileSync("bend", ["version"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
})();

describe("the generated module", () => {
  it("is the output of the current merge.bend (regenerate with bend-engine/gen.sh)", () => {
    // A missing bend is a failure, not a skip: without it the staleness of merge.mjs cannot be checked.
    if (!bendInstalled) throw new Error("bend is not on PATH: install it to check that merge.mjs is current");
    const dir = mkdtempSync(join(tmpdir(), "merge-bend-"));
    try {
      const out = join(dir, "merge.mjs");
      execFileSync("bend", [join(ROOT, "merge.bend"), "-o", out], { stdio: "ignore", timeout: 120_000 });
      expect(readFileSync(out, "utf8")).toBe(readFileSync(join(ROOT, "merge.mjs"), "utf8"));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 150_000);
});

describe("the rows of bend-engine/README.md", () => {
  it("every row points to a real theorem, function and test", () => {
    const readme = readFileSync(join(ROOT, "README.md"), "utf8");
    const lean = readFileSync(join(ROOT, "Merge.lean"), "utf8");
    const bendSrc = readFileSync(join(ROOT, "merge.bend"), "utf8");
    const tsSrc = readFileSync(join(ROOT, "..", "src", "engine", "merge.ts"), "utf8");
    const testSrc = readFileSync(join(__dirname, "merge_bend.test.ts"), "utf8");
    const table = readme.slice(readme.indexOf("## Lean theorems"), readme.indexOf("## What is not mechanized"));
    const rows = table.split("\n").filter((l) => l.startsWith("| `"));
    expect(rows.length).toBeGreaterThan(5);
    // the identifiers in backticks in a cell, each by its first word: `merge_state` (output `xp`) gives both
    const ids = (cell: string): string[] => [...cell.matchAll(/`([A-Za-z_][A-Za-z0-9_]*)/g)].map((m) => m[1]);
    for (const row of rows) {
      const [leanCell, bendCell, tsCell, testCell] = row.split("|").slice(1, -1).map((c) => c.trim());
      const theorem = ids(leanCell)[0];
      expect(lean, `Lean theorem ${theorem}`).toMatch(new RegExp(`theorem\\s+${theorem}\\b`));
      for (const f of ids(bendCell).filter((x) => x.includes("_") || x === "xsum")) {
        expect(bendSrc, `Bend function ${f}`).toMatch(new RegExp(`def\\s+${f}\\b`));
      }
      for (const f of ids(tsCell)) {
        expect(tsSrc, `TypeScript ${f}`).toMatch(new RegExp(`\\b${f}\\b`));
      }
      for (const t of [...testCell.matchAll(/"([^"]+)"/g)].map((m) => m[1])) {
        expect(testSrc, `test "${t}"`).toContain(t);
      }
    }
  });
});

// The Lean model's results on every pair of maps in the bounded domain (bend-engine/model_vectors.py).
// Each vector line is V|kind|map a|map b|result, the maps as the model prints them: key=fields;key=fields.
describe("the compiled merges against the Lean model, on every pair of the bounded domain", () => {
  const VECTORS = join(ROOT, "model_vectors.txt");
  const pairsOf = (s: string): string[][] => (s === "" ? [] : s.split(";").map((e) => e.split("=")));
  const lessonList = (s: string): unknown =>
    list(pairsOf(s).map(([key, f]) => {
      const [crowns, attempts, best, played] = f.split(",").map(Number);
      return { $: "LEntry", key, val: { $: "Lp", crowns, attempts, best, played } };
    }));
  const cardList = (s: string): unknown =>
    list(pairsOf(s).map(([key, f]) => {
      const [id, lessonId, interval, ease, due, lapses, reps, last] = f.split(",");
      return {
        $: "CEntry",
        key,
        val: {
          $: "Card", id, lessonId, interval: +interval, ease: +ease, due: +due, lapses: +lapses, reps: +reps,
          last: last === "-" ? { $: "None" } : { $: "Some", value: +last },
        },
      };
    }));
  const xpList = (s: string): unknown => list(pairsOf(s).map(([key, v]) => ({ $: "XEntry", key, val: +v })));
  const showOut = (l: any, f: (v: any) => string): string => {
    const xs: string[] = [];
    for (let x = l; x.$ === "Con"; x = x.tail) xs.push(`${x.head.key}=${f(x.head.val)}`);
    return xs.join(";");
  };
  const showLesson = (v: any): string => `${v.crowns},${v.attempts},${v.best},${v.played}`;
  const showCard = (v: any): string =>
    `${v.id},${v.lessonId},${v.interval},${v.ease},${v.due},${v.lapses},${v.reps},${v.last.$ === "Some" ? v.last.value : "-"}`;

  it("agree with the model's result on every vector", () => {
    const rows = readFileSync(VECTORS, "utf8").split("\n").filter((l) => l.startsWith("V|"));
    expect(rows.length).toBeGreaterThan(1000);
    const mismatches: string[] = [];
    for (const row of rows) {
      const [, kind, a, b, want] = row.split("|");
      let got: string;
      if (kind === "L") got = showOut(bend.merge_lessons(lessonList(a), lessonList(b)), showLesson);
      else if (kind === "C") got = showOut(bend.merge_srs(cardList(a), cardList(b)), showCard);
      else got = showOut(bend.merge_xp(xpList(a), xpList(b)), String);
      if (got !== want) mismatches.push(`${row}\n  compiled Bend: ${got}`);
    }
    expect(mismatches.slice(0, 3)).toEqual([]);
  });

  it("model_vectors.txt is the output of model_vectors.py from Merge.lean", () => {
    const dir = mkdtempSync(join(tmpdir(), "model-vectors-"));
    try {
      const out = join(dir, "vectors.txt");
      execFileSync("python3", [join(ROOT, "model_vectors.py"), "--out", out], { stdio: "pipe", timeout: 600_000 });
      expect(readFileSync(out, "utf8")).toBe(readFileSync(VECTORS, "utf8"));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 700_000);
});

describe("the translation-validation report", () => {
  it("compiler_check_report.txt is the output of compiler_check.py on the compiled merge.mjs", () => {
    const dir = mkdtempSync(join(tmpdir(), "compiler-check-"));
    try {
      const out = join(dir, "report.txt");
      execFileSync("python3", [join(ROOT, "compiler_check.py"), "--out", out], { stdio: "pipe", timeout: 600_000 });
      expect(readFileSync(out, "utf8")).toBe(readFileSync(join(ROOT, "compiler_check_report.txt"), "utf8"));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 700_000);
});
