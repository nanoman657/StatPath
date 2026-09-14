/**
 * Core exercise and curriculum types for StatPath.
 *
 * Every lesson is built from a pool of *exercises*. An exercise is either a
 * hand-authored item or a generator that produces a fresh randomized item each
 * time it is drawn (so numeric drills never repeat exactly).
 */

export type Choice = { text: string; correct?: boolean };

/** Pick one of several options. */
export interface MultipleChoice {
  kind: "mc";
  id: string;
  prompt: string;
  choices: Choice[];
  explanation: string;
  /** Optional data table, formula, or scenario displayed above the prompt. */
  context?: string;
}

/** Pick "True" or "False". */
export interface TrueFalse {
  kind: "tf";
  id: string;
  statement: string;
  answer: boolean;
  explanation: string;
  context?: string;
}

/** Type a number (checked with a tolerance) or a short word/phrase. */
export interface Numeric {
  kind: "numeric";
  id: string;
  prompt: string;
  answer: number;
  /** Absolute tolerance. Defaults to 0.01 or ~1% of the answer, whichever is larger. */
  tolerance?: number;
  unit?: string;
  explanation: string;
  context?: string;
}

/** Type a short text answer; any of `answers` (case-insensitive, trimmed) is accepted. */
export interface ShortText {
  kind: "text";
  id: string;
  prompt: string;
  answers: string[];
  explanation: string;
  context?: string;
}

/** Match items on the left to items on the right. */
export interface MatchPairs {
  kind: "match";
  id: string;
  prompt: string;
  pairs: { left: string; right: string }[];
  explanation: string;
}

/** Put steps into the correct order. */
export interface Ordering {
  kind: "order";
  id: string;
  prompt: string;
  /** In the correct order. Shuffled for display. */
  steps: string[];
  explanation: string;
}

/** Classify each item into one of a few categories (drag-into-bucket style). */
export interface Classify {
  kind: "classify";
  id: string;
  prompt: string;
  categories: string[];
  items: { text: string; category: string }[];
  explanation: string;
}

export type Exercise =
  | MultipleChoice
  | TrueFalse
  | Numeric
  | ShortText
  | MatchPairs
  | Ordering
  | Classify;

/** A generator produces a new concrete Exercise from a random source. */
export interface Generator {
  kind: "generator";
  id: string;
  /** Called with a seeded RNG in [0,1). Must return an Exercise whose id starts with the generator id. */
  make: (rng: () => number) => Exercise;
}

export type PoolItem = Exercise | Generator;

export interface Lesson {
  id: string;
  /** e.g. "1.2" */
  section: string;
  title: string;
  /** 2-4 sentence summary shown before the lesson starts (a "tip" card). */
  summary: string;
  /** Key terms and formulas for the tip card. */
  keyPoints: string[];
  pool: PoolItem[];
}

export interface Unit {
  id: string;
  /** Chapter number */
  number: number;
  title: string;
  description: string;
  /** Emoji used as the unit badge. */
  icon: string;
  color: string;
  lessons: Lesson[];
}

export interface Curriculum {
  units: Unit[];
}
