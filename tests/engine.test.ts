import { describe, expect, it } from "vitest";
import * as S from "../src/engine/stats";
import { grade, parseNumber } from "../src/engine/lesson";
import { completeLesson, defaultProgress, loseHeart, refillHearts, reviewCard, touchStreak, streakIsAlive, HEART_REFILL_MS, MAX_HEARTS, xpForResult, isoDay } from "../src/engine/progress";

describe("stats helpers", () => {
  it("computes center and spread", () => {
    expect(S.mean([2, 4, 4, 4, 5, 5, 7, 9])).toBe(5);
    expect(S.median([3, 1, 2])).toBe(2);
    expect(S.median([4, 1, 3, 2])).toBe(2.5);
    expect(S.mode([1, 2, 2, 3])).toEqual([2]);
    expect(S.mode([1, 2, 3])).toEqual([]);
    expect(S.sampleVariance([2, 4, 4, 4, 5, 5, 7, 9])).toBeCloseTo(32 / 7, 6);
    expect(S.populationSD([2, 4, 4, 4, 5, 5, 7, 9])).toBeCloseTo(2, 6);
  });
  it("computes quartiles using halves", () => {
    const q = S.quartiles([3, 5, 7, 8, 10, 12, 14, 15, 18]);
    expect(q.q1).toBe(6); expect(q.q2).toBe(10); expect(q.q3).toBe(14.5); expect(q.iqr).toBe(8.5);
  });
  it("computes discrete distributions", () => {
    expect(S.choose(5, 2)).toBe(10);
    expect(S.binomialPMF(4, 0.5, 2)).toBeCloseTo(0.375, 6);
    expect(S.binomialCDF(10, 0.3, 10)).toBeCloseTo(1, 6);
    expect(S.geometricPMF(0.2, 3)).toBeCloseTo(0.128, 6);
    expect(S.poissonPMF(4, 2)).toBeCloseTo(0.1465, 3);
    expect(S.hypergeometricPMF(10, 4, 3, 1)).toBeCloseTo(0.5, 6);
  });
  it("computes normal, t, chi-square, and F areas", () => {
    expect(S.normalCDF(0)).toBeCloseTo(0.5, 6);
    expect(S.normalCDF(1.96)).toBeCloseTo(0.975, 3);
    expect(S.normalInv(0.975)).toBeCloseTo(1.96, 2);
    expect(S.tCDF(2.131, 15)).toBeCloseTo(0.975, 2);
    expect(S.tInv(0.975, 15)).toBeCloseTo(2.131, 2);
    expect(S.chiSquareCDF(3.841, 1)).toBeCloseTo(0.95, 2);
    expect(S.chiSquareInv(0.95, 10)).toBeCloseTo(18.307, 1);
    expect(S.fCDF(4.5, 2, 21)).toBeCloseTo(0.976, 2);
    expect(S.fInv(0.95, 3, 20)).toBeCloseTo(3.098, 1);
  });
  it("fits a regression line", () => {
    const { a, b, r } = S.regression([1, 2, 3, 4], [3, 5, 7, 9]);
    expect(a).toBeCloseTo(1, 6); expect(b).toBeCloseTo(2, 6); expect(r).toBeCloseTo(1, 6);
  });
});

describe("grading", () => {
  it("parses fractions and percentages", () => {
    expect(parseNumber("3/8")).toBeCloseTo(0.375);
    expect(parseNumber("25%")).toBeCloseTo(0.25);
    expect(parseNumber("1,234")).toBe(1234);
    expect(parseNumber("abc")).toBeNull();
    expect(parseNumber("1/0")).toBeNull();
  });
  it("applies numeric tolerance", () => {
    const ex = { kind: "numeric" as const, id: "x", prompt: "", answer: 0.375, tolerance: 0.001, explanation: "" };
    expect(grade(ex, { kind: "numeric", value: "0.3751" })).toBe(true);
    expect(grade(ex, { kind: "numeric", value: "0.38" })).toBe(false);
    expect(grade(ex, { kind: "numeric", value: "3/8" })).toBe(true);
  });
  it("normalizes text answers", () => {
    const ex = { kind: "text" as const, id: "x", prompt: "", answers: ["sample space"], explanation: "" };
    expect(grade(ex, { kind: "text", value: "  Sample   Space. " })).toBe(true);
    expect(grade(ex, { kind: "text", value: "population" })).toBe(false);
  });
});

describe("progress", () => {
  const day = 86400000;
  it("tracks streaks across consecutive days", () => {
    let p = defaultProgress();
    const t0 = Date.UTC(2026, 0, 1, 12);
    p = touchStreak(p, t0);
    expect(p.streak).toBe(1);
    p = touchStreak(p, t0 + 3600000);
    expect(p.streak).toBe(1);
    p = touchStreak(p, t0 + day);
    expect(p.streak).toBe(2);
    p = touchStreak(p, t0 + 3 * day);
    expect(p.streak).toBe(1);
    expect(p.longestStreak).toBe(2);
    expect(streakIsAlive(p, t0 + 3 * day)).toBe(true);
    expect(streakIsAlive(p, t0 + 6 * day)).toBe(false);
  });
  it("loses and refills hearts", () => {
    let p = defaultProgress();
    const t = 1000;
    p = loseHeart(p, t);
    p = loseHeart(p, t);
    expect(p.hearts).toBe(MAX_HEARTS - 2);
    expect(p.heartsRefillAt).toBe(t + HEART_REFILL_MS);
    p = refillHearts(p, t + HEART_REFILL_MS);
    expect(p.hearts).toBe(MAX_HEARTS - 1);
    p = refillHearts(p, t + 10 * HEART_REFILL_MS);
    expect(p.hearts).toBe(MAX_HEARTS);
    expect(p.heartsRefillAt).toBeNull();
  });
  it("schedules spaced repetition", () => {
    const now = 0;
    let c = reviewCard(undefined, "e1", "l1", true, now);
    expect(c.interval).toBe(1);
    c = reviewCard(c, "e1", "l1", true, now);
    expect(c.interval).toBe(3);
    c = reviewCard(c, "e1", "l1", true, now);
    expect(c.interval).toBeGreaterThan(3);
    const failed = reviewCard(c, "e1", "l1", false, now);
    expect(failed.interval).toBe(0);
    expect(failed.lapses).toBe(1);
    expect(failed.due).toBeLessThan(c.due);
  });
  it("awards XP, crowns and achievements on lesson completion", () => {
    const p = defaultProgress();
    const r = { lessonId: "u1.1", correct: 10, total: 10, answers: [{ id: "a", correct: true }], perfect: true };
    const out = completeLesson(p, r, Date.UTC(2026, 0, 1, 12));
    expect(out.xpGained).toBe(xpForResult(r));
    expect(out.progress.lessons["u1.1"].crowns).toBe(1);
    expect(out.newAchievements).toContain("first-lesson");
    expect(out.newAchievements).toContain("perfect");
    expect(out.progress.xpByDay[isoDay(Date.UTC(2026, 0, 1, 12))]).toBe(out.xpGained);
    const low = completeLesson(out.progress, { ...r, correct: 5, perfect: false }, Date.UTC(2026, 0, 2, 12));
    expect(low.progress.lessons["u1.1"].crowns).toBe(1);
  });
});
