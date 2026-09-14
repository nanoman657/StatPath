/** Compact constructors for authoring exercises. */
import type { Choice, Classify, Lesson, MatchPairs, MultipleChoice, Numeric, Ordering, PoolItem, ShortText, TrueFalse, Unit } from "../engine/types";

let counter = 0;
const nextId = (prefix: string) => `${prefix}.${++counter}`;

/** Multiple choice: first option is correct; the UI shuffles. */
export const mc = (prefix: string, prompt: string, options: string[], explanation: string, context?: string): MultipleChoice => ({
  kind: "mc",
  id: nextId(prefix),
  prompt,
  choices: options.map((text, i): Choice => (i === 0 ? { text, correct: true } : { text })),
  explanation,
  context,
});

export const tf = (prefix: string, statement: string, answer: boolean, explanation: string, context?: string): TrueFalse => ({
  kind: "tf",
  id: nextId(prefix),
  statement,
  answer,
  explanation,
  context,
});

export const num = (prefix: string, prompt: string, answer: number, explanation: string, opts: { tolerance?: number; unit?: string; context?: string } = {}): Numeric => ({
  kind: "numeric",
  id: nextId(prefix),
  prompt,
  answer,
  explanation,
  ...opts,
});

export const text = (prefix: string, prompt: string, answers: string[], explanation: string, context?: string): ShortText => ({
  kind: "text",
  id: nextId(prefix),
  prompt,
  answers,
  explanation,
  context,
});

export const match = (prefix: string, prompt: string, pairs: [string, string][], explanation: string): MatchPairs => ({
  kind: "match",
  id: nextId(prefix),
  prompt,
  pairs: pairs.map(([left, right]) => ({ left, right })),
  explanation,
});

export const order = (prefix: string, prompt: string, steps: string[], explanation: string): Ordering => ({
  kind: "order",
  id: nextId(prefix),
  prompt,
  steps,
  explanation,
});

export const classify = (prefix: string, prompt: string, categories: string[], items: [string, string][], explanation: string): Classify => ({
  kind: "classify",
  id: nextId(prefix),
  prompt,
  categories,
  items: items.map(([t, c]) => ({ text: t, category: c })),
  explanation,
});

export const lesson = (id: string, section: string, title: string, summary: string, keyPoints: string[], pool: PoolItem[]): Lesson => ({
  id,
  section,
  title,
  summary,
  keyPoints,
  pool,
});

/** A capstone lesson that pools every item of the unit's lessons. */
export const reviewLesson = (unitId: string, chapter: number, lessons: Lesson[], extra: PoolItem[] = []): Lesson => ({
  id: `${unitId}.review`,
  section: `${chapter}.R`,
  title: "Chapter challenge",
  summary: "A mixed challenge drawn from every lesson in this unit. Earn crowns here to prove mastery of the whole chapter.",
  keyPoints: ["Mixed exercises from every lesson in this unit", ...lessons.map((l) => `${l.section} ${l.title}`)],
  pool: [...lessons.flatMap((l) => l.pool), ...extra],
});

export const unit = (number: number, title: string, description: string, icon: string, color: string, lessons: Lesson[]): Unit => {
  const id = `u${number}`;
  return { id, number, title, description, icon, color, lessons: [...lessons, reviewLesson(id, number, lessons)] };
};
