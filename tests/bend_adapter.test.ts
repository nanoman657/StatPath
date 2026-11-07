import { describe, expect, it, vi } from "vitest";
import bend from "../bend-engine/merge.mjs";
import { mergeProgress } from "../src/engine/merge";
import { byCodePoint, mergeLearning } from "../src/engine/bendMerge";
import { mergeProgress as referenceMerge } from "./reference/mergeProgressTs";
import { defaultProgress, type LessonProgress, type Progress, type SrsCard } from "../src/engine/progress";

// The app's merge, which runs the compiled Bend module for lessons, SRS cards and XP per day, checked against
// the TypeScript reference on the values the app really produces: fractional ease and accuracy, ties, and keys
// outside the Basic Multilingual Plane, where UTF-16 order and code-point order differ.

// A deterministic generator, so a failure can be reproduced from its trial number.
const rng = (seed: number) => () => {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};

const pick = <T,>(r: () => number, xs: T[]): T => xs[Math.floor(r() * xs.length)];
const subset = <T,>(r: () => number, xs: T[]): T[] => xs.filter(() => r() < 0.6);

// Ease moves by 0.1 from 2.5 in the app; accuracy is correct over total.
const EASES = [1.3, 2.5, 2.5 + 0.1, 2.5 + 0.1 + 0.1, 2.6, 2.7, 3.0];
const ACCURACIES = [0, 1 / 3, 2 / 3, 0.8, 1];
const KEYS = ["a", "b", "é", "\uE000", "\u{1F600}", "\u{10FFFF}"];
const DAYS = ["2026-05-01", "2026-05-02", "2026-05-03", "2026-05-04"];
const STAMPS = [0, 50, 100, 1_750_000_000_000];

function randomProgress(r: () => number): Progress {
  const lessons: Record<string, LessonProgress> = {};
  for (const id of subset(r, KEYS)) {
    lessons[id] = {
      crowns: Math.floor(r() * 6),
      attempts: Math.floor(r() * 5),
      bestAccuracy: pick(r, ACCURACIES),
      lastPlayed: pick(r, STAMPS),
    };
  }
  const srs: Record<string, SrsCard> = {};
  for (const id of subset(r, KEYS)) {
    const card: SrsCard = {
      id,
      lessonId: pick(r, KEYS),
      interval: Math.floor(r() * 4),
      ease: pick(r, EASES),
      due: pick(r, STAMPS),
      lapses: Math.floor(r() * 3),
      reps: Math.floor(r() * 3),
    };
    if (r() < 0.7) card.lastReview = pick(r, STAMPS);
    srs[id] = card;
  }
  const xpByDay: Record<string, number> = {};
  for (const d of subset(r, DAYS)) xpByDay[d] = Math.floor(r() * 4) * 10;
  return {
    ...defaultProgress(),
    lessons,
    srs,
    xpByDay,
    hearts: Math.floor(r() * 6),
    lastActiveDay: pick(r, [null, ...DAYS]),
    achievements: subset(r, ["first", "perfect"]),
    name: pick(r, ["Ada", "Bo"]),
    dailyGoal: pick(r, [10, 50]),
    updatedAt: pick(r, STAMPS),
  };
}

// Sorting keys inside JSON, so a comparison does not depend on the order an object was built in.
function sortedJson(v: unknown): unknown {
  if (Array.isArray(v)) return v.map(sortedJson);
  if (v && typeof v === "object") {
    return Object.fromEntries(Object.keys(v).sort().map((k) => [k, sortedJson((v as Record<string, unknown>)[k])]));
  }
  return v;
}

describe("the app's merge, which runs the Bend module, against the TypeScript reference", () => {
  it("gives the reference's whole record on random progress, with fractions, ties and astral keys", () => {
    const r = rng(20260507);
    for (let trial = 0; trial < 3_000; trial++) {
      const a = randomProgress(r);
      const b = randomProgress(r);
      expect(sortedJson(mergeProgress(a, b)), `trial ${trial}\na: ${JSON.stringify(a)}\nb: ${JSON.stringify(b)}`).toEqual(
        sortedJson(referenceMerge(a, b)),
      );
    }
  });

  it("keeps the exact fraction of the larger ease, not a rounded or ranked value", () => {
    const card = (ease: number): SrsCard => ({ id: "c1", lessonId: "l1", interval: 3, ease, due: 1000, lapses: 0, reps: 2, lastReview: 300 });
    const a: Progress = { ...defaultProgress(), srs: { c1: card(2.6) } };
    const b: Progress = { ...defaultProgress(), srs: { c1: card(2.5) } };
    expect(mergeProgress(a, b).srs.c1.ease).toBe(2.6);
    expect(mergeProgress(b, a).srs.c1.ease).toBe(2.6);
  });

  it("returns the values that were put in: every ease and accuracy in the output was an input", () => {
    const r = rng(11);
    for (let trial = 0; trial < 500; trial++) {
      const a = randomProgress(r);
      const b = randomProgress(r);
      const inputEases = new Set([...Object.values(a.srs), ...Object.values(b.srs)].map((c) => c.ease));
      const inputAcc = new Set([...Object.values(a.lessons), ...Object.values(b.lessons)].map((l) => l.bestAccuracy));
      const out = mergeLearning(a, b);
      for (const c of Object.values(out.srs)) expect(inputEases.has(c.ease), `trial ${trial}`).toBe(true);
      for (const l of Object.values(out.lessons)) expect(inputAcc.has(l.bestAccuracy), `trial ${trial}`).toBe(true);
    }
  });

  it("refuses a NaN ease rather than merging it", () => {
    const card: SrsCard = { id: "c1", lessonId: "l1", interval: 1, ease: Number.NaN, due: 1, lapses: 0, reps: 1 };
    const a: Progress = { ...defaultProgress(), srs: { c1: card } };
    expect(() => mergeLearning(a, defaultProgress())).toThrow(/NaN/);
  });

  it("passes each map to Bend strictly increasing by code point, the order its proofs assume", () => {
    // Keys above U+FFFF sort before U+E000 in UTF-16 but after it in code-point order, so a UTF-16 sort fails here.
    const spy = vi.spyOn(bend, "merge_state");
    try {
      const r = rng(31);
      for (let trial = 0; trial < 300; trial++) {
        mergeLearning(randomProgress(r), randomProgress(r));
        const args = spy.mock.calls[spy.mock.calls.length - 1];
        for (const state of args) {
          for (const field of ["lessons", "srs", "xpByDay"]) {
            const keys: string[] = [];
            for (let x: any = (state as any)[field]; x.$ === "Con"; x = x.tail) keys.push(x.head.key);
            for (let i = 1; i < keys.length; i++) {
              expect(byCodePoint(keys[i - 1], keys[i]) < 0, `trial ${trial}, ${field}: ${keys.join(" ")}`).toBe(true);
            }
          }
        }
      }
    } finally {
      spy.mockRestore();
    }
  });
});
