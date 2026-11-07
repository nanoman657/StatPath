/**
 * Merging two copies of a learner's progress.
 *
 * Sync is offline-first: each device keeps writing locally and reconciles with
 * a shared copy later. Last-write-wins would silently destroy work, because a
 * device holding stale state can overwrite a lesson finished elsewhere. Every
 * field here instead has an unambiguous winner, so no conflict ever has to be
 * shown to the user.
 *
 * The merge is commutative and idempotent for all learning data:
 *   merge(a, b) equals merge(b, a), and merge(a, a) equals a.
 * That means it does not matter which device syncs first, and repeated syncs
 * never drift. The one deliberate exception is cosmetic settings (display name
 * and daily goal), which take the value from whichever copy changed last.
 *
 * Lessons, SRS cards and XP per day are merged by the compiled Bend module
 * (see bendMerge.ts and bend-engine/merge.bend). The rest of the record is
 * merged here.
 */
import { MAX_HEARTS, type Progress } from "./progress";
import { mergeLearning } from "./bendMerge";

const maxNum = (a: number | undefined, b: number | undefined): number => Math.max(a ?? 0, b ?? 0);

/** Step one calendar day back, matching the local-time format isoDay produces. */
export const prevDay = (iso: string): string => {
  const [y, m, d] = iso.split("-").map(Number);
  const dt = new Date(y, m - 1, d);
  dt.setDate(dt.getDate() - 1);
  return `${dt.getFullYear()}-${String(dt.getMonth() + 1).padStart(2, "0")}-${String(dt.getDate()).padStart(2, "0")}`;
};

/** Days on which any XP was earned, oldest first. */
const activeDays = (xpByDay: Record<string, number>): string[] =>
  Object.entries(xpByDay).filter(([, v]) => v > 0).map(([k]) => k).sort();

/** Consecutive active days ending at the most recent one. */
export const streakEndingAt = (xpByDay: Record<string, number>, lastDay: string | null): number => {
  if (!lastDay || !(xpByDay[lastDay] > 0)) return 0;
  let n = 0;
  let day = lastDay;
  while (xpByDay[day] > 0) {
    n += 1;
    day = prevDay(day);
  }
  return n;
};

/** Longest run of consecutive active days anywhere in the history. */
export const longestRun = (xpByDay: Record<string, number>): number => {
  const days = activeDays(xpByDay);
  let best = 0;
  let run = 0;
  let previous: string | null = null;
  for (const day of days) {
    run = previous !== null && prevDay(day) === previous ? run + 1 : 1;
    previous = day;
    if (run > best) best = run;
  }
  return best;
};

/** Best available signal for when a copy last changed. */
export const recencyOf = (p: Progress): number => {
  let t = p.updatedAt ?? 0;
  for (const l of Object.values(p.lessons)) t = Math.max(t, l.lastPlayed ?? 0);
  for (const c of Object.values(p.srs)) t = Math.max(t, c.lastReview ?? 0);
  return t;
};

export const mergeProgress = (a: Progress, b: Progress): Progress => {
  // XP is always recorded per day as well as in the total, so the per-day map
  // is the source of truth and the total is derived from it. The Bend merge takes
  // the larger value per day, so nothing is double counted or lost.
  const learning = mergeLearning(a, b);
  const xpByDay = learning.xpByDay;

  const days = activeDays(xpByDay);
  const lastActiveDay =
    [a.lastActiveDay, b.lastActiveDay, days.length ? days[days.length - 1] : null]
      .filter((d): d is string => !!d)
      .sort()
      .pop() ?? null;

  // Hearts take the lower count so syncing can never be used to refill them,
  // and the later refill time so a stale clock cannot grant one early.
  const hearts = Math.min(a.hearts, b.hearts);
  const heartsRefillAt = hearts >= MAX_HEARTS ? null : maxNum(a.heartsRefillAt ?? 0, b.heartsRefillAt ?? 0) || null;

  // Settings are the one field pair without a natural ordering, so the copy
  // that changed last wins. Exact ties are broken deterministically to keep
  // the merge commutative.
  const ra = recencyOf(a);
  const rb = recencyOf(b);
  const newer = ra !== rb ? (ra > rb ? a : b) : JSON.stringify(a) >= JSON.stringify(b) ? a : b;

  return {
    version: 1,
    xp: learning.xp,
    xpByDay,
    lastActiveDay,
    streak: streakEndingAt(xpByDay, lastActiveDay),
    longestStreak: Math.max(a.longestStreak, b.longestStreak, longestRun(xpByDay)),
    hearts,
    heartsRefillAt,
    dailyGoal: newer.dailyGoal,
    name: newer.name,
    lessons: learning.lessons,
    srs: learning.srs,
    achievements: [...new Set([...a.achievements, ...b.achievements])].sort(),
    updatedAt: Math.max(ra, rb),
  };
};
