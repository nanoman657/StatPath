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
 */
import { MAX_HEARTS, type LessonProgress, type Progress, type SrsCard } from "./progress";

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

const mergeLesson = (a: LessonProgress | undefined, b: LessonProgress | undefined): LessonProgress => ({
  // Crowns and best accuracy only ever climb, so the larger value is the true one.
  crowns: maxNum(a?.crowns, b?.crowns),
  bestAccuracy: Math.max(a?.bestAccuracy ?? 0, b?.bestAccuracy ?? 0),
  // Without per-device counters an exact total is not recoverable; the larger
  // count is the safe choice, since it never invents attempts that did not happen.
  attempts: maxNum(a?.attempts, b?.attempts),
  lastPlayed: maxNum(a?.lastPlayed, b?.lastPlayed),
});

/**
 * The scheduling state from whichever device answered this exercise most
 * recently, so a lapse recorded on one device is not undone by an older pass
 * on another. Falls back to repetition count, then due date, for cards saved
 * before review timestamps existed.
 */
const mergeCard = (a: SrsCard | undefined, b: SrsCard | undefined): SrsCard => {
  if (!a) return b!;
  if (!b) return a;
  const ta = a.lastReview ?? 0;
  const tb = b.lastReview ?? 0;
  if (ta !== tb) return ta > tb ? a : b;
  if (a.reps !== b.reps) return a.reps > b.reps ? a : b;
  if (a.due !== b.due) return a.due > b.due ? a : b;
  return a;
};

export const mergeProgress = (a: Progress, b: Progress): Progress => {
  // XP is always recorded per day as well as in the total, so the per-day map
  // is the source of truth and the total is derived from it. Taking the larger
  // value per day avoids both double counting and loss.
  const xpByDay: Record<string, number> = { ...a.xpByDay };
  for (const [day, v] of Object.entries(b.xpByDay)) xpByDay[day] = Math.max(xpByDay[day] ?? 0, v);
  const xp = Object.values(xpByDay).reduce((t, v) => t + v, 0);

  const days = activeDays(xpByDay);
  const lastActiveDay =
    [a.lastActiveDay, b.lastActiveDay, days.length ? days[days.length - 1] : null]
      .filter((d): d is string => !!d)
      .sort()
      .pop() ?? null;

  const lessons: Record<string, LessonProgress> = {};
  for (const id of new Set([...Object.keys(a.lessons), ...Object.keys(b.lessons)])) {
    lessons[id] = mergeLesson(a.lessons[id], b.lessons[id]);
  }

  const srs: Record<string, SrsCard> = {};
  for (const id of new Set([...Object.keys(a.srs), ...Object.keys(b.srs)])) {
    srs[id] = mergeCard(a.srs[id], b.srs[id]);
  }

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
    xp,
    xpByDay,
    lastActiveDay,
    streak: streakEndingAt(xpByDay, lastActiveDay),
    longestStreak: Math.max(a.longestStreak, b.longestStreak, longestRun(xpByDay)),
    hearts,
    heartsRefillAt,
    dailyGoal: newer.dailyGoal,
    name: newer.name,
    lessons,
    srs,
    achievements: [...new Set([...a.achievements, ...b.achievements])].sort(),
    updatedAt: Math.max(ra, rb),
  };
};
