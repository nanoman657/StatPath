/**
 * The learning data (lessons, SRS cards and XP per day) merged by the compiled
 * Bend module: bend-engine/merge.bend, compiled to bend-engine/merge.mjs.
 *
 * Bend's numbers are Nat, but two fields are fractions in the app: a card's
 * ease (2.5 and up, in steps of 0.1) and a lesson's bestAccuracy (correct over
 * total). The merge only compares these fields and never computes with them, so
 * each distinct value is replaced by its rank among the values of the two
 * copies. Ranks keep the order exactly, and the result is mapped back to the
 * original numbers, so nothing is rounded. A NaN has no place in the order and
 * is refused.
 *
 * Bend and the Lean model compare strings by code point. Each map is passed in
 * strictly increasing by key in that order, the representation the Bend proofs
 * assume (bend-engine/merge.bend). The merge also builds its result by inserting
 * each entry into a sorted list (lins, cins, xins), so the order of its input
 * lists is not what makes the result sorted.
 */
import bend from "../../bend-engine/merge.mjs";
import type { LessonProgress, Progress, SrsCard } from "./progress";

/** Code-point order of two strings: the order Bend's String.cmp and Lean's String order use. */
export const byCodePoint = (a: string, b: string): number => {
  const x = Array.from(a);
  const y = Array.from(b);
  for (let i = 0; i < Math.min(x.length, y.length); i++) {
    const p = x[i].codePointAt(0)!;
    const q = y[i].codePointAt(0)!;
    if (p !== q) return p - q;
  }
  return x.length - y.length;
};

interface Ranks {
  rankOf: Map<number, number>;
  valueOf: number[];
}

/** The rank of each distinct value in ascending order. Equal numbers, including 0 and -0, share a rank. */
const ranksOf = (values: number[]): Ranks => {
  if (values.some((v) => Number.isNaN(v))) throw new Error("A NaN cannot be merged: it has no place in the order.");
  const valueOf = [...new Set(values)].sort((x, y) => (x < y ? -1 : x > y ? 1 : 0));
  return { rankOf: new Map(valueOf.map((v, i): [number, number] => [v, i])), valueOf };
};

const list = (xs: unknown[]): unknown => xs.reduceRight<unknown>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
const maybe = (v: number | undefined): unknown => (v === undefined ? { $: "None" } : { $: "Some", value: v });
const sortedKeys = (m: object): string[] => Object.keys(m).sort(byCodePoint);

/** One copy's learning data in the Bend shape, with ease and accuracy replaced by their ranks. */
const toBend = (p: Progress, ease: Ranks, best: Ranks): unknown => ({
  $: "St",
  lessons: list(
    sortedKeys(p.lessons).map((key) => {
      const l = p.lessons[key];
      return { $: "LEntry", key, val: { $: "Lp", crowns: l.crowns, attempts: l.attempts, best: best.rankOf.get(l.bestAccuracy)!, played: l.lastPlayed } };
    }),
  ),
  srs: list(
    sortedKeys(p.srs).map((key) => {
      const c = p.srs[key];
      return {
        $: "CEntry",
        key,
        val: {
          $: "Card",
          id: c.id,
          lessonId: c.lessonId,
          interval: c.interval,
          ease: ease.rankOf.get(c.ease)!,
          due: c.due,
          lapses: c.lapses,
          reps: c.reps,
          last: maybe(c.lastReview),
        },
      };
    }),
  ),
  xpByDay: list(sortedKeys(p.xpByDay).map((key) => ({ $: "XEntry", key, val: p.xpByDay[key] }))),
});

/** The elements of a Bend list, read into an array. */
const items = (l: any): any[] => {
  const xs: any[] = [];
  for (let x = l; x.$ === "Con"; x = x.tail) xs.push(x.head);
  return xs;
};

export interface LearningData {
  lessons: Record<string, LessonProgress>;
  srs: Record<string, SrsCard>;
  xpByDay: Record<string, number>;
  xp: number;
}

/** The lessons, SRS cards and XP per day of two copies, merged by the compiled Bend module. */
export const mergeLearning = (a: Progress, b: Progress): LearningData => {
  const ease = ranksOf([...Object.values(a.srs), ...Object.values(b.srs)].map((c) => c.ease));
  const best = ranksOf([...Object.values(a.lessons), ...Object.values(b.lessons)].map((l) => l.bestAccuracy));
  const out: any = bend.merge_state(toBend(a, ease, best), toBend(b, ease, best));

  const lessons: Record<string, LessonProgress> = {};
  for (const e of items(out.lessons)) {
    lessons[e.key] = {
      crowns: e.val.crowns,
      attempts: e.val.attempts,
      bestAccuracy: best.valueOf[e.val.best],
      lastPlayed: e.val.played,
    };
  }

  const srs: Record<string, SrsCard> = {};
  for (const e of items(out.srs)) {
    const c = e.val;
    const card: SrsCard = {
      id: c.id,
      lessonId: c.lessonId,
      interval: c.interval,
      ease: ease.valueOf[c.ease],
      due: c.due,
      lapses: c.lapses,
      reps: c.reps,
    };
    if (c.last.$ === "Some") card.lastReview = c.last.value;
    srs[e.key] = card;
  }

  const xpByDay: Record<string, number> = {};
  for (const e of items(out.xpByDay)) xpByDay[e.key] = e.val;

  return { lessons, srs, xpByDay, xp: out.xp };
};
