import { useEffect, useMemo, useRef, useState } from "react";
import type { Exercise, Lesson } from "../engine/types";
import { type Answer, correctAnswerText, grade } from "../engine/lesson";
import { ExerciseView } from "./ExerciseView";
import type { LessonResult } from "../engine/progress";
import { bookSections, chapterPages, BOOK_TITLE } from "../content/bookPages";

interface Props {
  lesson: Lesson;
  /** Pre-built exercises (with lesson ids for review sessions). */
  items: { exercise: Exercise; lessonId: string }[];
  hearts: number;
  /** Practice mode ignores hearts. */
  practice: boolean;
  onLoseHeart: () => void;
  onFinish: (r: LessonResult, seconds: number) => void;
  onQuit: () => void;
  seed: number;
}

export function LessonPlayer({ lesson, items, hearts, practice, onLoseHeart, onFinish, onQuit, seed }: Props) {
  const [stage, setStage] = useState<"tip" | "play" | "out">("tip");
  const [queue, setQueue] = useState(items);
  const [idx, setIdx] = useState(0);
  const [answer, setAnswer] = useState<Answer | null>(null);
  const [revealed, setRevealed] = useState<null | boolean>(null);
  const [answers, setAnswers] = useState<{ id: string; correct: boolean }[]>([]);
  const [firstTryCorrect, setFirstTryCorrect] = useState(0);
  const [mistakes, setMistakes] = useState(0);
  const start = useRef(Date.now());
  const sheetRef = useRef<HTMLDivElement>(null);

  const total = items.length;
  const current = queue[idx];
  const progress = Math.min(1, (idx - (queue.length - total)) / total);
  const answeredOriginal = answers.length;

  useEffect(() => {
    const h = (e: KeyboardEvent) => {
      if (e.key === "Enter") {
        if (stage === "tip") setStage("play");
        else if (stage === "play") (revealed === null ? check() : next());
      }
    };
    window.addEventListener("keydown", h);
    return () => window.removeEventListener("keydown", h);
  });

  const check = () => {
    if (!current || !answer || revealed !== null) return;
    const ok = grade(current.exercise, answer);
    setRevealed(ok);
    const isRetry = current.exercise.id.startsWith("retry:");
    if (!isRetry) {
      setAnswers((a) => [...a, { id: baseId(current.exercise.id), correct: ok }]);
      if (ok) setFirstTryCorrect((n) => n + 1);
    }
    if (!ok) {
      setMistakes((m) => m + 1);
      if (!practice) onLoseHeart();
      // Re-queue a retry of the missed exercise at the end (Duolingo style)
      setQueue((q) => [...q, { exercise: { ...current.exercise, id: `retry:${current.exercise.id}` } as Exercise, lessonId: current.lessonId }]);
    }
  };

  const next = () => {
    if (revealed === null) return;
    const heartsLeft = practice ? Infinity : hearts;
    if (!practice && revealed === false && heartsLeft <= 0) { setStage("out"); return; }
    if (idx + 1 >= queue.length) {
      const r: LessonResult = { lessonId: lesson.id, correct: firstTryCorrect, total, answers, perfect: mistakes === 0 };
      onFinish(r, Math.round((Date.now() - start.current) / 1000));
      return;
    }
    setIdx(idx + 1);
    setAnswer(null);
    setRevealed(null);
  };

  const exerciseSeed = useMemo(() => seed + idx * 7919, [seed, idx]);

  if (stage === "tip") {
    return (
      <div>
        <div className="lesson-top">
          <button className="x" onClick={onQuit} aria-label="quit">✕</button>
          <div>
            <div className="muted small">Lesson {lesson.section}</div>
            <h2 style={{ margin: 0 }}>{lesson.title}</h2>
          </div>
        </div>
        <div className="card tip">
          <div className="pill">Tip</div>
          <p>{lesson.summary}</p>
          <ul className="keypoints">
            {lesson.keyPoints.map((k, i) => <li key={i}>{k}</li>)}
          </ul>
        </div>
        <BookRef section={lesson.section} />
        <div className="muted small center">{total} exercises · {practice ? "practice mode (no hearts)" : `${hearts} hearts`}</div>
        <div className="mt"><button className="btn wide" onClick={() => setStage("play")}>Start lesson</button></div>
      </div>
    );
  }

  if (stage === "out") {
    return (
      <div className="results">
        <div className="big">💔</div>
        <h2>Out of hearts</h2>
        <p className="muted">Hearts refill over time (one every 30 minutes), or earn one back with a perfect lesson. You can keep going in Practice mode, which never costs hearts.</p>
        <div className="mt"><button className="btn wide" onClick={onQuit}>Back to path</button></div>
      </div>
    );
  }

  return (
    <div style={{ paddingBottom: 140 }}>
      <div className="lesson-top">
        <button className="x" onClick={onQuit} aria-label="quit">✕</button>
        <div className={"progress" + (practice ? " blue" : "")}><div style={{ width: `${progress * 100}%` }} /></div>
        {!practice ? <div className="stat hearts">❤️ {hearts}</div> : <div className="pill">Practice</div>}
      </div>
      {current.exercise.id.startsWith("retry:") ? <div className="pill" style={{ marginBottom: 6 }}>Second chance</div> : null}
      <ExerciseView key={current.exercise.id + idx} exercise={current.exercise} onChange={setAnswer} revealed={revealed !== null} seed={exerciseSeed} />
      <div ref={sheetRef} className={"sheet " + (revealed === null ? "neutral" : revealed ? "good" : "bad")}>
        <div className="inner">
          {revealed === null ? (
            <div className="row spread">
              <button className="btn ghost" onClick={() => { setAnswer(null); setRevealed(false); setMistakes((m) => m + 1); if (!practice) onLoseHeart(); setAnswers((a) => current.exercise.id.startsWith("retry:") ? a : [...a, { id: baseId(current.exercise.id), correct: false }]); setQueue((q) => [...q, { exercise: { ...current.exercise, id: `retry:${current.exercise.id}` } as Exercise, lessonId: current.lessonId }]); }}>Skip</button>
              <button className="btn" onClick={check} disabled={!answer}>Check</button>
            </div>
          ) : (
            <div>
              <h3>{revealed ? pickPraise(idx) : "Not quite"}</h3>
              {!revealed ? <div className="expl"><b>Correct answer:</b> {correctAnswerText(current.exercise)}</div> : null}
              <div className="expl">{current.exercise.explanation}</div>
              <button className={"btn wide " + (revealed ? "" : "red")} onClick={next}>Continue</button>
            </div>
          )}
        </div>
      </div>
      <div className="muted small center" style={{ marginTop: 10 }}>{answeredOriginal}/{total} answered</div>
    </div>
  );
}

const baseId = (id: string) => id.replace(/^retry:/, "");

/** "Read the book" pointer: the section (or whole chapter for a challenge) with printed page numbers. */
function BookRef({ section }: { section: string }) {
  const sec = bookSections[section];
  const chapterMatch = section.match(/^(\d+)\.R$/);
  const ch = chapterMatch ? chapterPages(Number(chapterMatch[1])) : undefined;
  if (!sec && !ch) return null;
  const pages = sec ? `pp. ${sec.start}–${sec.end}` : `pp. ${ch!.start}–${ch!.end}`;
  const label = sec ? `Section ${section}: ${sec.title}` : `Chapter ${chapterMatch![1]}`;
  return (
    <div className="card bookref">
      <span className="pill">📖 In the book</span>
      <div className="small" style={{ marginTop: 6 }}>
        {sec ? <a href={sec.url} target="_blank" rel="noreferrer">{label}</a> : label}, {pages} of <i>{BOOK_TITLE}</i>.
      </div>
    </div>
  );
}

const praises = ["Nice!", "Correct!", "Great job!", "Exactly right!", "You got it!", "Excellent!", "Spot on!"];
const pickPraise = (i: number) => praises[i % praises.length];
