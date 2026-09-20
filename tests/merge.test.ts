import { describe, expect, it } from "vitest";
import { longestRun, mergeProgress, prevDay, recencyOf, streakEndingAt } from "../src/engine/merge";
import { completeLesson, defaultProgress, reviewCard, MAX_HEARTS, type Progress } from "../src/engine/progress";
import { SYNC_KEY, defaultSync } from "../src/engine/sync";

const DAY = 86400000;
const T = Date.UTC(2026, 4, 10, 12);

const played = (p: Progress, lessonId: string, correct: number, at: number): Progress =>
  completeLesson(p, {
    lessonId,
    correct,
    total: 10,
    answers: [{ id: `${lessonId}.a`, correct: correct >= 8 }],
    perfect: correct === 10,
  }, at).progress;

describe("day arithmetic", () => {
  it("steps back across month and year boundaries", () => {
    expect(prevDay("2026-05-10")).toBe("2026-05-09");
    expect(prevDay("2026-05-01")).toBe("2026-04-30");
    expect(prevDay("2026-01-01")).toBe("2025-12-31");
    expect(prevDay("2028-03-01")).toBe("2028-02-29"); // leap year
  });
  it("counts a streak and the longest run from daily XP", () => {
    const xp = { "2026-05-01": 10, "2026-05-02": 10, "2026-05-03": 10, "2026-05-08": 10, "2026-05-09": 10 };
    expect(streakEndingAt(xp, "2026-05-09")).toBe(2);
    expect(longestRun(xp)).toBe(3);
    expect(streakEndingAt(xp, "2026-05-05")).toBe(0);
    expect(streakEndingAt({}, null)).toBe(0);
  });
});

describe("mergeProgress", () => {
  it("is idempotent and commutative", () => {
    const a = played(played(defaultProgress(), "u1.1", 10, T), "u1.2", 9, T + DAY);
    const b = played(defaultProgress(), "u2.1", 7, T + 2 * DAY);
    expect(mergeProgress(a, a)).toEqual(a);
    expect(mergeProgress(a, b)).toEqual(mergeProgress(b, a));
  });

  it("keeps a lesson finished on one device when the other is stale", () => {
    // The failure that last-write-wins would cause: phone earns a crown, then a
    // laptop holding the older state syncs.
    const base = defaultProgress();
    const phone = played(base, "u1.1", 10, T);
    const laptop = base;
    const merged = mergeProgress(laptop, phone);
    expect(merged.lessons["u1.1"].crowns).toBe(1);
    expect(merged.xp).toBe(phone.xp);
  });

  it("keeps work done on both devices at once", () => {
    const base = played(defaultProgress(), "u1.1", 10, T);
    const phone = played(base, "u1.2", 10, T + DAY);
    const laptop = played(base, "u1.3", 10, T + DAY);
    const merged = mergeProgress(phone, laptop);
    expect(merged.lessons["u1.1"].crowns).toBe(1);
    expect(merged.lessons["u1.2"].crowns).toBe(1);
    expect(merged.lessons["u1.3"].crowns).toBe(1);
  });

  it("never lowers crowns, best accuracy, or longest streak", () => {
    const a = { ...defaultProgress(), longestStreak: 9, lessons: { x: { crowns: 4, attempts: 9, bestAccuracy: 1, lastPlayed: T } } };
    const b = { ...defaultProgress(), longestStreak: 3, lessons: { x: { crowns: 1, attempts: 2, bestAccuracy: 0.5, lastPlayed: T - DAY } } };
    const m = mergeProgress(a, b);
    expect(m.lessons.x.crowns).toBe(4);
    expect(m.lessons.x.bestAccuracy).toBe(1);
    expect(m.longestStreak).toBe(9);
  });

  it("takes daily XP per day and derives the total from it", () => {
    const a = { ...defaultProgress(), xp: 30, xpByDay: { "2026-05-01": 20, "2026-05-02": 10 } };
    const b = { ...defaultProgress(), xp: 45, xpByDay: { "2026-05-02": 25, "2026-05-03": 20 } };
    const m = mergeProgress(a, b);
    expect(m.xpByDay).toEqual({ "2026-05-01": 20, "2026-05-02": 25, "2026-05-03": 20 });
    expect(m.xp).toBe(65); // recomputed, never double counted
  });

  it("recomputes the streak across days earned on different devices", () => {
    const a = { ...defaultProgress(), xpByDay: { "2026-05-01": 10, "2026-05-03": 10 }, lastActiveDay: "2026-05-03", streak: 1 };
    const b = { ...defaultProgress(), xpByDay: { "2026-05-02": 10 }, lastActiveDay: "2026-05-02", streak: 1 };
    const m = mergeProgress(a, b);
    expect(m.lastActiveDay).toBe("2026-05-03");
    expect(m.streak).toBe(3); // 1st, 2nd and 3rd are now all active
  });

  it("keeps the most recent review of an exercise, including a lapse", () => {
    const passed = reviewCard(undefined, "e1", "u1.1", true, T);
    const passedTwice = reviewCard(passed, "e1", "u1.1", true, T + DAY);
    const lapsed = reviewCard(passedTwice, "e1", "u1.1", false, T + 2 * DAY);
    const a = { ...defaultProgress(), srs: { e1: lapsed } };
    const b = { ...defaultProgress(), srs: { e1: passedTwice } };
    // The lapse is newer, so it must survive even though it has fewer reps.
    expect(mergeProgress(a, b).srs.e1).toEqual(lapsed);
    expect(mergeProgress(b, a).srs.e1).toEqual(lapsed);
  });

  it("unions achievements and keeps them stable in order", () => {
    const a = { ...defaultProgress(), achievements: ["perfect", "first-lesson"] };
    const b = { ...defaultProgress(), achievements: ["streak-3", "first-lesson"] };
    expect(mergeProgress(a, b).achievements).toEqual(["first-lesson", "perfect", "streak-3"]);
  });

  it("takes the lower heart count so syncing cannot refill them", () => {
    const a = { ...defaultProgress(), hearts: 5, heartsRefillAt: null };
    const b = { ...defaultProgress(), hearts: 2, heartsRefillAt: T };
    const m = mergeProgress(a, b);
    expect(m.hearts).toBe(2);
    expect(m.heartsRefillAt).toBe(T);
    expect(mergeProgress(a, a).hearts).toBe(MAX_HEARTS);
  });

  it("takes settings from whichever copy changed most recently", () => {
    const older = { ...defaultProgress(), name: "Old", dailyGoal: 10, updatedAt: T };
    const newer = { ...defaultProgress(), name: "New", dailyGoal: 50, updatedAt: T + DAY };
    expect(mergeProgress(older, newer).name).toBe("New");
    expect(mergeProgress(newer, older).dailyGoal).toBe(50);
  });

  it("derives recency from lesson and review times when no stamp is present", () => {
    const p = { ...defaultProgress(), updatedAt: 0, lessons: { x: { crowns: 1, attempts: 1, bestAccuracy: 1, lastPlayed: T } } };
    expect(recencyOf(p)).toBe(T);
  });

  it("merges a full real session without losing anything", () => {
    let phone = defaultProgress();
    for (const id of ["u1.1", "u1.2", "u1.3"]) phone = played(phone, id, 10, T);
    let laptop = defaultProgress();
    for (const id of ["u1.1", "u2.1"]) laptop = played(laptop, id, 9, T + DAY);
    const m = mergeProgress(phone, laptop);
    expect(Object.keys(m.lessons).sort()).toEqual(["u1.1", "u1.2", "u1.3", "u2.1"]);
    expect(m.xp).toBe(Object.values(m.xpByDay).reduce((t, v) => t + v, 0));
    expect(m.achievements).toContain("first-lesson");
  });
});

describe("sync settings storage", () => {
  it("keeps the token in its own key, never inside progress", () => {
    expect(SYNC_KEY).not.toBe("statpath.progress.v1");
    const p = played(defaultProgress(), "u1.1", 10, T);
    expect(JSON.stringify(p)).not.toContain("token");
    expect(Object.keys(defaultSync())).toContain("token");
    expect(Object.keys(p)).not.toContain("token");
  });
});
