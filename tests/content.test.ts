import { describe, expect, it } from "vitest";
import { curriculum, allLessons } from "../src/content";
import { allGenerators } from "../src/engine/generators";
import { mulberry32 } from "../src/engine/rng";
import { grade, buildSession, buildReviewSession, correctAnswerText } from "../src/engine/lesson";
import type { Exercise } from "../src/engine/types";

const validate = (ex: Exercise) => {
  expect(ex.id).toBeTruthy();
  expect(ex.explanation.length).toBeGreaterThan(10);
  switch (ex.kind) {
    case "mc": {
      expect(ex.choices.length).toBeGreaterThanOrEqual(2);
      expect(ex.choices.filter((c) => c.correct).length).toBe(1);
      const texts = ex.choices.map((c) => c.text);
      expect(new Set(texts).size).toBe(texts.length);
      break;
    }
    case "numeric":
      expect(Number.isFinite(ex.answer)).toBe(true);
      break;
    case "text":
      expect(ex.answers.length).toBeGreaterThan(0);
      break;
    case "match": {
      expect(ex.pairs.length).toBeGreaterThanOrEqual(3);
      expect(new Set(ex.pairs.map((p) => p.right)).size).toBe(ex.pairs.length);
      expect(new Set(ex.pairs.map((p) => p.left)).size).toBe(ex.pairs.length);
      break;
    }
    case "order":
      expect(ex.steps.length).toBeGreaterThanOrEqual(3);
      expect(new Set(ex.steps).size).toBe(ex.steps.length);
      break;
    case "classify":
      expect(ex.items.length).toBeGreaterThanOrEqual(3);
      for (const it of ex.items) expect(ex.categories).toContain(it.category);
      expect(new Set(ex.items.map((i) => i.text)).size).toBe(ex.items.length);
      break;
    case "tf":
      expect(typeof ex.answer).toBe("boolean");
  }
};

describe("curriculum structure", () => {
  it("covers all 13 chapters of Introductory Statistics 2e", () => {
    expect(curriculum.units.map((u) => u.number)).toEqual([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]);
  });

  it("has unique lesson ids and a review lesson per unit", () => {
    const ids = allLessons.map((l) => l.id);
    expect(new Set(ids).size).toBe(ids.length);
    for (const u of curriculum.units) expect(u.lessons[u.lessons.length - 1].id).toBe(`${u.id}.review`);
  });

  it("every lesson has enough material for a 10-exercise session", () => {
    for (const l of allLessons) {
      expect(l.pool.length, l.id).toBeGreaterThanOrEqual(6);
      expect(l.summary.length, l.id).toBeGreaterThan(40);
      expect(l.keyPoints.length, l.id).toBeGreaterThanOrEqual(3);
      const session = buildSession(l, 42);
      expect(session.length, l.id).toBe(10);
    }
  });

  it("all hand-written exercises are well formed with unique ids", () => {
    const ids: string[] = [];
    for (const l of allLessons) {
      if (l.id.endsWith(".review")) continue;
      for (const item of l.pool) {
        if (item.kind === "generator") continue;
        validate(item);
        ids.push(item.id);
      }
    }
    expect(new Set(ids).size).toBe(ids.length);
    expect(ids.length).toBeGreaterThan(400);
  });

  it("the correct answer grades as correct for every hand-written exercise", () => {
    for (const l of allLessons) {
      for (const item of l.pool) {
        if (item.kind === "generator") continue;
        expect(grade(item, correctAnswerFor(item)), item.id).toBe(true);
      }
    }
  });
});

describe("generators", () => {
  it("produce valid, gradable exercises across many seeds", () => {
    for (const g of allGenerators) {
      for (let seed = 1; seed <= 60; seed++) {
        const ex = g.make(mulberry32(seed));
        expect(ex.id.startsWith(g.id), g.id).toBe(true);
        validate(ex);
        expect(grade(ex, correctAnswerFor(ex)), `${g.id} seed ${seed}`).toBe(true);
        if (ex.kind === "numeric") expect(Number.isNaN(ex.answer), `${g.id} seed ${seed}`).toBe(false);
      }
    }
  });

  it("are deterministic for a given seed", () => {
    for (const g of allGenerators) {
      expect(JSON.stringify(g.make(mulberry32(7)))).toBe(JSON.stringify(g.make(mulberry32(7))));
    }
  });

  it("every generator is used by at least one lesson", () => {
    const used = new Set(allLessons.flatMap((l) => l.pool.filter((p) => p.kind === "generator").map((p) => p.id)));
    for (const g of allGenerators) expect(used.has(g.id), g.id).toBe(true);
  });
});

describe("session building", () => {
  it("does not repeat hand-written exercises within a session", () => {
    for (const l of allLessons) {
      const s = buildSession(l, 3);
      const fixed = s.filter((e) => !e.id.startsWith("g.")).map((e) => e.id);
      expect(new Set(fixed).size).toBe(fixed.length);
    }
  });

  it("prioritizes requested ids", () => {
    const l = allLessons[0];
    const target = l.pool.find((p) => p.kind !== "generator")!.id;
    const s = buildSession(l, 99, 3, [target]);
    expect(s.map((e) => e.id)).toContain(target);
  });

  it("builds mixed review sessions across lessons", () => {
    const s = buildReviewSession(allLessons.slice(0, 5), 11, 10);
    expect(s.length).toBe(10);
    expect(new Set(s.map((x) => x.lessonId)).size).toBeGreaterThan(1);
  });
});

/** Derive the correct Answer object for any exercise. */
function correctAnswerFor(ex: Exercise) {
  switch (ex.kind) {
    case "mc": return { kind: "mc" as const, index: ex.choices.findIndex((c) => c.correct) };
    case "tf": return { kind: "tf" as const, value: ex.answer };
    case "numeric": return { kind: "numeric" as const, value: String(ex.answer) };
    case "text": return { kind: "text" as const, value: ex.answers[0] };
    case "match": return { kind: "match" as const, pairs: Object.fromEntries(ex.pairs.map((p) => [p.left, p.right])) };
    case "order": return { kind: "order" as const, steps: [...ex.steps] };
    case "classify": return { kind: "classify" as const, assignment: Object.fromEntries(ex.items.map((i) => [i.text, i.category])) };
  }
}

describe("correctAnswerText", () => {
  it("renders something for every kind", () => {
    for (const l of allLessons.slice(0, 3)) for (const p of l.pool) if (p.kind !== "generator") expect(correctAnswerText(p).length).toBeGreaterThan(0);
  });
});

import { bookSections, chapterPages } from "../src/content/bookPages";

describe("book page index", () => {
  it("maps every numbered lesson to a section of the textbook with a page range", () => {
    for (const l of allLessons) {
      if (l.id.endsWith(".review")) continue;
      const sec = bookSections[l.section];
      expect(sec, `${l.id} (${l.section})`).toBeDefined();
      expect(sec.end).toBeGreaterThanOrEqual(sec.start);
      expect(sec.url).toMatch(/^https:\/\/openstax\.org\/books\/introductory-statistics-2e\/pages\//);
    }
  });
  it("has increasing page numbers through the book and a range for every chapter", () => {
    const keys = Object.keys(bookSections);
    for (let i = 1; i < keys.length; i++) expect(bookSections[keys[i]].start).toBeGreaterThanOrEqual(bookSections[keys[i - 1]].start);
    for (const u of curriculum.units) expect(chapterPages(u.number)).toBeDefined();
  });
});
