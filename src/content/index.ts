import type { Curriculum, Lesson, Unit } from "../engine/types";
import { registerUnits } from "../engine/progress";
import { unit1 } from "./ch01";
import { unit2 } from "./ch02";
import { unit3 } from "./ch03";
import { unit4 } from "./ch04";
import { unit5 } from "./ch05";
import { unit6 } from "./ch06";
import { unit7 } from "./ch07";
import { unit8 } from "./ch08";
import { unit9 } from "./ch09";
import { unit10 } from "./ch10";
import { unit11 } from "./ch11";
import { unit12 } from "./ch12";
import { unit13 } from "./ch13";

/**
 * The full course, structured after the 13 chapters of OpenStax
 * Introductory Statistics 2e (CC BY 4.0). Every lesson corresponds to a
 * numbered section of the book; each unit ends with a mixed "Chapter challenge".
 */
export const curriculum: Curriculum = {
  units: [unit1, unit2, unit3, unit4, unit5, unit6, unit7, unit8, unit9, unit10, unit11, unit12, unit13],
};

registerUnits(Object.fromEntries(curriculum.units.map((u) => [u.id, u.lessons.map((l) => l.id)])));

export const allLessons: Lesson[] = curriculum.units.flatMap((u) => u.lessons);

export const findLesson = (id: string): { unit: Unit; lesson: Lesson } | undefined => {
  for (const u of curriculum.units) {
    const l = u.lessons.find((x) => x.id === id);
    if (l) return { unit: u, lesson: l };
  }
  return undefined;
};
