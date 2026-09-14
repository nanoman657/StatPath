/**
 * Player progress: XP, streaks, hearts, lesson crowns, and a light spaced
 * repetition schedule (SM-2 style) per exercise id. Persisted to localStorage.
 */

export interface SrsCard {
  /** Exercise/generator id */
  id: string;
  lessonId: string;
  interval: number; // days
  ease: number;
  due: number; // epoch ms
  lapses: number;
  reps: number;
}

export interface LessonProgress {
  /** 0 = untouched, 1..5 = crown level */
  crowns: number;
  attempts: number;
  bestAccuracy: number;
  lastPlayed: number;
}

export interface Progress {
  version: 1;
  xp: number;
  streak: number;
  longestStreak: number;
  /** ISO date (YYYY-MM-DD) of the last day a lesson was completed */
  lastActiveDay: string | null;
  hearts: number;
  heartsRefillAt: number | null;
  dailyGoal: number;
  /** XP earned per ISO day */
  xpByDay: Record<string, number>;
  lessons: Record<string, LessonProgress>;
  srs: Record<string, SrsCard>;
  achievements: string[];
  name: string;
}

export const MAX_HEARTS = 5;
export const HEART_REFILL_MS = 30 * 60 * 1000; // one heart per 30 minutes
export const MAX_CROWNS = 5;
export const STORAGE_KEY = "statpath.progress.v1";

export const isoDay = (t: number = Date.now()): string => {
  const d = new Date(t);
  const y = d.getFullYear();
  const m = String(d.getMonth() + 1).padStart(2, "0");
  const day = String(d.getDate()).padStart(2, "0");
  return `${y}-${m}-${day}`;
};

export const defaultProgress = (): Progress => ({
  version: 1,
  xp: 0,
  streak: 0,
  longestStreak: 0,
  lastActiveDay: null,
  hearts: MAX_HEARTS,
  heartsRefillAt: null,
  dailyGoal: 30,
  xpByDay: {},
  lessons: {},
  srs: {},
  achievements: [],
  name: "Learner",
});

export const loadProgress = (): Progress => {
  try {
    const raw = typeof localStorage !== "undefined" ? localStorage.getItem(STORAGE_KEY) : null;
    if (!raw) return defaultProgress();
    const parsed = JSON.parse(raw) as Progress;
    return refillHearts({ ...defaultProgress(), ...parsed });
  } catch {
    return defaultProgress();
  }
};

export const saveProgress = (p: Progress): void => {
  try {
    if (typeof localStorage !== "undefined") localStorage.setItem(STORAGE_KEY, JSON.stringify(p));
  } catch {
    /* ignore quota / private mode */
  }
};

/** Regenerate hearts based on elapsed time. Pure. */
export const refillHearts = (p: Progress, now: number = Date.now()): Progress => {
  if (p.hearts >= MAX_HEARTS || p.heartsRefillAt === null) return { ...p, heartsRefillAt: p.hearts >= MAX_HEARTS ? null : p.heartsRefillAt };
  let hearts = p.hearts;
  let refillAt = p.heartsRefillAt;
  while (hearts < MAX_HEARTS && now >= refillAt) {
    hearts += 1;
    refillAt += HEART_REFILL_MS;
  }
  return { ...p, hearts, heartsRefillAt: hearts >= MAX_HEARTS ? null : refillAt };
};

export const loseHeart = (p: Progress, now: number = Date.now()): Progress => {
  const hearts = Math.max(0, p.hearts - 1);
  return { ...p, hearts, heartsRefillAt: p.heartsRefillAt ?? now + HEART_REFILL_MS };
};

/** Day-boundary streak logic. */
export const touchStreak = (p: Progress, now: number = Date.now()): Progress => {
  const today = isoDay(now);
  if (p.lastActiveDay === today) return p;
  const yesterday = isoDay(now - 24 * 60 * 60 * 1000);
  const streak = p.lastActiveDay === yesterday ? p.streak + 1 : 1;
  return { ...p, streak, longestStreak: Math.max(p.longestStreak, streak), lastActiveDay: today };
};

/** Has the streak been broken (i.e., last activity before yesterday)? */
export const streakIsAlive = (p: Progress, now: number = Date.now()): boolean => {
  if (!p.lastActiveDay) return false;
  const today = isoDay(now);
  const yesterday = isoDay(now - 24 * 60 * 60 * 1000);
  return p.lastActiveDay === today || p.lastActiveDay === yesterday;
};

export const addXp = (p: Progress, amount: number, now: number = Date.now()): Progress => {
  const day = isoDay(now);
  return { ...p, xp: p.xp + amount, xpByDay: { ...p.xpByDay, [day]: (p.xpByDay[day] ?? 0) + amount } };
};

export const xpToday = (p: Progress, now: number = Date.now()): number => p.xpByDay[isoDay(now)] ?? 0;

/** SM-2 style update. quality: 0 (wrong) .. 5 (perfect, instant). */
export const reviewCard = (card: SrsCard | undefined, id: string, lessonId: string, correct: boolean, now: number = Date.now()): SrsCard => {
  const c: SrsCard = card ?? { id, lessonId, interval: 0, ease: 2.5, due: now, lapses: 0, reps: 0 };
  const day = 24 * 60 * 60 * 1000;
  if (!correct) {
    return { ...c, interval: 0, reps: 0, lapses: c.lapses + 1, ease: Math.max(1.3, c.ease - 0.2), due: now + 10 * 60 * 1000 };
  }
  const reps = c.reps + 1;
  const interval = reps === 1 ? 1 : reps === 2 ? 3 : Math.round(c.interval * c.ease);
  return { ...c, reps, interval, ease: Math.min(3.0, c.ease + 0.1), due: now + interval * day };
};

export const dueCards = (p: Progress, now: number = Date.now()): SrsCard[] =>
  Object.values(p.srs).filter((c) => c.due <= now).sort((a, b) => a.due - b.due);

export interface LessonResult {
  lessonId: string;
  correct: number;
  total: number;
  /** ids of exercises answered, with correctness */
  answers: { id: string; correct: boolean }[];
  perfect: boolean;
}

export const XP_PER_LESSON = 10;
export const XP_PERFECT_BONUS = 5;
export const XP_PER_CORRECT = 1;

export const xpForResult = (r: LessonResult): number =>
  XP_PER_LESSON + r.correct * XP_PER_CORRECT + (r.perfect ? XP_PERFECT_BONUS : 0);

/** Apply a completed lesson to progress. Pure. */
export const completeLesson = (p: Progress, r: LessonResult, now: number = Date.now()): { progress: Progress; xpGained: number; newAchievements: string[] } => {
  const accuracy = r.total ? r.correct / r.total : 0;
  const prev = p.lessons[r.lessonId] ?? { crowns: 0, attempts: 0, bestAccuracy: 0, lastPlayed: 0 };
  // Earn a crown when accuracy >= 80%; lose nothing otherwise.
  const crowns = accuracy >= 0.8 ? Math.min(MAX_CROWNS, prev.crowns + 1) : prev.crowns;
  const lessons = { ...p.lessons, [r.lessonId]: { crowns, attempts: prev.attempts + 1, bestAccuracy: Math.max(prev.bestAccuracy, accuracy), lastPlayed: now } };
  const srs = { ...p.srs };
  for (const a of r.answers) srs[a.id] = reviewCard(srs[a.id], a.id, r.lessonId, a.correct, now);
  const xpGained = xpForResult(r);
  let next: Progress = { ...p, lessons, srs };
  next = addXp(next, xpGained, now);
  next = touchStreak(next, now);
  // Perfect lessons restore one heart
  if (r.perfect && next.hearts < MAX_HEARTS) next = { ...next, hearts: next.hearts + 1 };
  const newAchievements = checkAchievements(next).filter((a) => !p.achievements.includes(a));
  next = { ...next, achievements: [...p.achievements, ...newAchievements] };
  return { progress: next, xpGained, newAchievements };
};

export const ACHIEVEMENTS: Record<string, { title: string; description: string; icon: string }> = {
  "first-lesson": { title: "First Steps", description: "Complete your first lesson", icon: "🎯" },
  "streak-3": { title: "Warming Up", description: "Reach a 3-day streak", icon: "🔥" },
  "streak-7": { title: "On Fire", description: "Reach a 7-day streak", icon: "🔥" },
  "streak-30": { title: "Unstoppable", description: "Reach a 30-day streak", icon: "🌋" },
  "xp-100": { title: "Century", description: "Earn 100 XP", icon: "💯" },
  "xp-1000": { title: "Statistician", description: "Earn 1,000 XP", icon: "🎓" },
  "crowns-10": { title: "Crowned", description: "Earn 10 crowns", icon: "👑" },
  "unit-1": { title: "Sampler", description: "Earn a crown on every lesson of a unit", icon: "🏅" },
  "perfect": { title: "Flawless", description: "Complete a lesson with no mistakes", icon: "✨" },
};

/** Set by the curriculum module so unit completion can be checked without a circular import. */
export let unitLessonIds: Record<string, string[]> = {};
export const registerUnits = (m: Record<string, string[]>): void => { unitLessonIds = m; };

export const totalCrowns = (p: Progress): number => Object.values(p.lessons).reduce((a, l) => a + l.crowns, 0);

export const checkAchievements = (p: Progress): string[] => {
  const got: string[] = [];
  const lessonsDone = Object.values(p.lessons).filter((l) => l.attempts > 0).length;
  if (lessonsDone >= 1) got.push("first-lesson");
  if (p.longestStreak >= 3) got.push("streak-3");
  if (p.longestStreak >= 7) got.push("streak-7");
  if (p.longestStreak >= 30) got.push("streak-30");
  if (p.xp >= 100) got.push("xp-100");
  if (p.xp >= 1000) got.push("xp-1000");
  if (totalCrowns(p) >= 10) got.push("crowns-10");
  if (Object.values(p.lessons).some((l) => l.bestAccuracy >= 1)) got.push("perfect");
  for (const ids of Object.values(unitLessonIds)) {
    if (ids.length && ids.every((id) => (p.lessons[id]?.crowns ?? 0) >= 1)) { got.push("unit-1"); break; }
  }
  return got;
};
