/** Build a lesson session from a pool and grade answers. */
import type { Exercise, Lesson, PoolItem } from "./types";
import { mulberry32, shuffle } from "./rng";

export const LESSON_LENGTH = 10;

export const materialize = (item: PoolItem, rng: () => number): Exercise =>
  item.kind === "generator" ? item.make(rng) : item;

/**
 * Draw `count` exercises from the pool. Hand-written items are preferred on
 * first plays; generators fill remaining slots and supply variety. With
 * `weights` (e.g. from spaced repetition), overdue items are drawn first.
 */
export const buildSession = (lesson: Lesson, seed: number, count = LESSON_LENGTH, priority: string[] = []): Exercise[] => {
  const rng = mulberry32(seed);
  const pool = shuffle(rng, lesson.pool);
  const prioritized = [...pool.filter((p) => priority.includes(p.id)), ...pool.filter((p) => !priority.includes(p.id))];
  const chosen: Exercise[] = [];
  const usedIds = new Set<string>();
  // First pass: unique items
  for (const item of prioritized) {
    if (chosen.length >= count) break;
    if (usedIds.has(item.id)) continue;
    usedIds.add(item.id);
    chosen.push(materialize(item, rng));
  }
  // Second pass: re-draw generators (fresh numbers) to fill the lesson
  const generators = pool.filter((p) => p.kind === "generator");
  let guard = 0;
  while (chosen.length < count && generators.length && guard++ < 50) {
    const g = generators[Math.floor(rng() * generators.length)];
    chosen.push(materialize(g, rng));
  }
  return chosen;
};

/** Build a mixed review session from several lessons (used by "Practice" and SRS review). */
export const buildReviewSession = (lessons: Lesson[], seed: number, count = LESSON_LENGTH, priorityIds: string[] = []): { exercise: Exercise; lessonId: string }[] => {
  const rng = mulberry32(seed);
  const items = shuffle(rng, lessons.flatMap((l) => l.pool.map((p) => ({ item: p, lessonId: l.id }))));
  const prioritized = [...items.filter((x) => priorityIds.includes(x.item.id)), ...items.filter((x) => !priorityIds.includes(x.item.id))];
  const out: { exercise: Exercise; lessonId: string }[] = [];
  const used = new Set<string>();
  for (const { item, lessonId } of prioritized) {
    if (out.length >= count) break;
    if (used.has(item.id)) continue;
    used.add(item.id);
    out.push({ exercise: materialize(item, rng), lessonId });
  }
  return out;
};

export type Answer =
  | { kind: "mc"; index: number }
  | { kind: "tf"; value: boolean }
  | { kind: "numeric"; value: string }
  | { kind: "text"; value: string }
  | { kind: "match"; pairs: Record<string, string> }
  | { kind: "order"; steps: string[] }
  | { kind: "classify"; assignment: Record<string, string> };

const normalizeText = (s: string): string => s.trim().toLowerCase().replace(/\s+/g, " ").replace(/[.,!?]$/g, "");

/** Parse numbers typed as "1/4", "25%", "0.25", "1,234". */
export const parseNumber = (s: string): number | null => {
  const t = s.trim().replace(/,/g, "");
  if (!t) return null;
  const frac = t.match(/^(-?\d+(?:\.\d+)?)\s*\/\s*(-?\d+(?:\.\d+)?)$/);
  if (frac) {
    const d = Number(frac[2]);
    return d === 0 ? null : Number(frac[1]) / d;
  }
  const pct = t.match(/^(-?\d+(?:\.\d+)?)\s*%$/);
  if (pct) return Number(pct[1]) / 100;
  const n = Number(t);
  return Number.isFinite(n) ? n : null;
};

export const grade = (ex: Exercise, ans: Answer): boolean => {
  switch (ex.kind) {
    case "mc":
      return ans.kind === "mc" && !!ex.choices[ans.index]?.correct;
    case "tf":
      return ans.kind === "tf" && ans.value === ex.answer;
    case "numeric": {
      if (ans.kind !== "numeric") return false;
      const v = parseNumber(ans.value);
      if (v === null) return false;
      const tol = ex.tolerance ?? Math.max(0.01, Math.abs(ex.answer) * 0.01);
      return Math.abs(v - ex.answer) <= tol + 1e-9;
    }
    case "text":
      return ans.kind === "text" && ex.answers.map(normalizeText).includes(normalizeText(ans.value));
    case "match":
      return ans.kind === "match" && ex.pairs.every((p) => ans.pairs[p.left] === p.right);
    case "order":
      return ans.kind === "order" && ans.steps.length === ex.steps.length && ans.steps.every((s, i) => s === ex.steps[i]);
    case "classify":
      return ans.kind === "classify" && ex.items.every((it) => ans.assignment[it.text] === it.category);
  }
};

/** Human-readable correct answer for feedback. */
export const correctAnswerText = (ex: Exercise): string => {
  switch (ex.kind) {
    case "mc":
      return ex.choices.find((c) => c.correct)?.text ?? "";
    case "tf":
      return ex.answer ? "True" : "False";
    case "numeric":
      return `${ex.answer}${ex.unit ? " " + ex.unit : ""}`;
    case "text":
      return ex.answers[0];
    case "match":
      return ex.pairs.map((p) => `${p.left} → ${p.right}`).join("; ");
    case "order":
      return ex.steps.map((s, i) => `${i + 1}. ${s}`).join(" ");
    case "classify":
      return ex.categories.map((c) => `${c}: ${ex.items.filter((i) => i.category === c).map((i) => i.text).join(", ")}`).join(" | ");
  }
};
