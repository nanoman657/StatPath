import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { curriculum, allLessons, findLesson } from "./content";
import { buildReviewSession, buildSession } from "./engine/lesson";
import { randomSeed } from "./engine/rng";
import { type LessonResult, type Progress, completeLesson, dueCards, loadProgress, loseHeart, refillHearts, saveProgress, streakIsAlive, xpToday, reviewCard, touchStreak, defaultProgress, isoDay, MAX_HEARTS, ACHIEVEMENTS } from "./engine/progress";
import type { Lesson } from "./engine/types";
import { LessonPlayer } from "./ui/LessonPlayer";
import { Path } from "./ui/Path";
import { Profile } from "./ui/Profile";
import { SyncError, type SyncSettings, clearSync, defaultSync, loadSync, saveSync, syncNow } from "./engine/sync";

type Screen =
  | { name: "path" }
  | { name: "practice" }
  | { name: "profile" }
  | { name: "lesson"; lesson: Lesson; items: ReturnType<typeof buildReviewSession>; practice: boolean; seed: number }
  | { name: "results"; result: LessonResult; xp: number; seconds: number; achievements: string[]; practice: boolean };

export function App() {
  const [progress, setProgress] = useState<Progress>(() => loadProgress());
  const [screen, setScreen] = useState<Screen>({ name: "path" });
  const [, tick] = useState(0);
  const [sync, setSync] = useState<SyncSettings>(() => loadSync());
  const [syncing, setSyncing] = useState(false);
  const [syncStatus, setSyncStatus] = useState("");

  useEffect(() => { saveProgress(progress); }, [progress]);
  useEffect(() => { saveSync(sync); }, [sync]);

  // Latest values for callbacks that must not close over a stale render.
  const progressRef = useRef(progress);
  const syncRef = useRef(sync);
  useEffect(() => { progressRef.current = progress; }, [progress]);
  useEffect(() => { syncRef.current = sync; }, [sync]);

  /**
   * Pull the shared copy, merge, push back. Passing the just-updated progress
   * avoids racing the state update that follows a finished lesson.
   */
  const doSync = useCallback(async (p?: Progress) => {
    const settings = syncRef.current;
    if (!settings.token) return;
    setSyncing(true);
    setSyncStatus("Syncing…");
    try {
      const out = await syncNow(p ?? progressRef.current, settings);
      setProgress(out.progress);
      setSync(out.settings);
      setSyncStatus({ created: "Sync set up", pushed: "Synced", pulled: "Updated from your other device", "in-sync": "Up to date" }[out.action]);
    } catch (e) {
      const message = e instanceof SyncError ? e.message : "Sync failed.";
      setSync((prev) => ({ ...prev, lastError: message }));
      setSyncStatus(message);
    } finally {
      setSyncing(false);
    }
  }, []);

  // Sync once on open so a device picks up whatever happened elsewhere.
  useEffect(() => { if (loadSync().token) void doSync(); }, [doSync]);
  // Refill hearts over time and re-render the countdown
  useEffect(() => {
    const t = setInterval(() => { setProgress((p) => refillHearts(p)); tick((n) => n + 1); }, 30_000);
    return () => clearInterval(t);
  }, []);

  const update = (fn: (p: Progress) => Progress) => setProgress((p) => ({ ...fn(p), updatedAt: Date.now() }));

  const startLesson = (lessonId: string, practice = false) => {
    const found = findLesson(lessonId);
    if (!found) return;
    const seed = randomSeed();
    const due = dueCards(progress).filter((c) => c.lessonId === lessonId).map((c) => c.id);
    const exercises = buildSession(found.lesson, seed, 10, due);
    setScreen({ name: "lesson", lesson: found.lesson, items: exercises.map((exercise) => ({ exercise, lessonId })), practice, seed });
    window.scrollTo(0, 0);
  };

  const startReview = (mode: "due" | "weak" | "random" | "unit", unitId?: string) => {
    const seed = randomSeed();
    const unlocked = allLessons.filter((l) => (progress.lessons[l.id]?.attempts ?? 0) > 0);
    let lessons: Lesson[];
    let priority: string[] = [];
    if (mode === "unit" && unitId) lessons = curriculum.units.find((u) => u.id === unitId)?.lessons ?? [];
    else if (mode === "due") { lessons = unlocked.length ? unlocked : allLessons.slice(0, 1); priority = dueCards(progress).map((c) => c.id); }
    else if (mode === "weak") {
      lessons = unlocked.length ? unlocked : allLessons.slice(0, 1);
      priority = Object.values(progress.srs).filter((c) => c.lapses > 0).sort((a, b) => b.lapses - a.lapses).map((c) => c.id);
    } else lessons = unlocked.length ? unlocked : allLessons.slice(0, 1);
    if (!lessons.length) return;
    const items = buildReviewSession(lessons, seed, 10, priority);
    const pseudo: Lesson = { id: "review", section: "★", title: mode === "unit" ? `Unit practice` : mode === "due" ? "Spaced review" : mode === "weak" ? "Weak spots" : "Mixed practice", summary: "Practice never costs hearts. Mistakes here still update your review schedule, so they make future lessons smarter.", keyPoints: [`${lessons.length} lesson${lessons.length === 1 ? "" : "s"} in the mix`, `${priority.length} prioritized exercise${priority.length === 1 ? "" : "s"}`], pool: [] };
    setScreen({ name: "lesson", lesson: pseudo, items, practice: true, seed });
    window.scrollTo(0, 0);
  };

  const onFinish = (r: LessonResult, seconds: number) => {
    if (screen.name !== "lesson") return;
    const practice = screen.practice;
    if (practice) {
      // Practice: update SRS and give reduced XP, no crowns.
      const perLesson = new Map<string, LessonResult>();
      for (const { exercise, lessonId } of screen.items) {
        const a = r.answers.find((x) => x.id === exercise.id);
        if (!a) continue;
        const cur = perLesson.get(lessonId) ?? { lessonId, correct: 0, total: 0, answers: [], perfect: false };
        cur.total += 1; cur.correct += a.correct ? 1 : 0; cur.answers.push(a);
        perLesson.set(lessonId, cur);
      }
      let next = progress;
      for (const pr of perLesson.values()) {
        const srs = { ...next.srs };
        for (const a of pr.answers) srs[a.id] = reviewCard(srs[a.id], a.id, pr.lessonId, a.correct);
        next = { ...next, srs };
      }
      const xp = 5 + r.correct;
      const day = isoDay();
      next = { ...next, xp: next.xp + xp, xpByDay: { ...next.xpByDay, [day]: (next.xpByDay[day] ?? 0) + xp } };
      next = touchStreak(next);
      next = { ...next, updatedAt: Date.now() };
      setProgress(next);
      void doSync(next);
      setScreen({ name: "results", result: r, xp, seconds, achievements: [], practice: true });
    } else {
      const out = completeLesson(progress, r);
      setProgress(out.progress);
      void doSync(out.progress);
      setScreen({ name: "results", result: r, xp: out.xpGained, seconds, achievements: out.newAchievements, practice: false });
    }
    window.scrollTo(0, 0);
  };

  const heartsInfo = useMemo(() => {
    if (progress.hearts >= MAX_HEARTS || !progress.heartsRefillAt) return "";
    const ms = Math.max(0, progress.heartsRefillAt - Date.now());
    const m = Math.ceil(ms / 60000);
    return `next ❤️ in ${m} min`;
  }, [progress.hearts, progress.heartsRefillAt, screen]);

  const due = dueCards(progress).length;
  const started = Object.keys(progress.lessons).length > 0;
  const nextLesson = allLessons.find((l) => (progress.lessons[l.id]?.crowns ?? 0) === 0);

  if (screen.name === "lesson") {
    return (
      <div className="app">
        <LessonPlayer
          lesson={screen.lesson}
          items={screen.items}
          hearts={progress.hearts}
          practice={screen.practice}
          onLoseHeart={() => update((p) => loseHeart(p))}
          onFinish={onFinish}
          onQuit={() => setScreen({ name: "path" })}
          seed={screen.seed}
        />
      </div>
    );
  }

  return (
    <div className="app">
      <header className="topbar">
        <div className="brand">📐 StatPath</div>
        <div className="stats">
          <span className={"stat streak" + (streakIsAlive(progress) ? "" : " dim")} title="Day streak">🔥 {streakIsAlive(progress) ? progress.streak : 0}</span>
          <span className="stat xp" title="Total XP">⚡ {progress.xp}</span>
          <span className="stat hearts" title={heartsInfo || "Hearts"}>❤️ {progress.hearts}</span>
          {sync.token ? (
            <button
              className={"stat sync" + (sync.lastError ? " bad" : "")}
              title={syncing ? "Syncing…" : sync.lastError ? sync.lastError : sync.lastSyncedAt ? `Last synced ${new Date(sync.lastSyncedAt).toLocaleTimeString()}` : "Sync"}
              onClick={() => void doSync()}
              disabled={syncing}
            >
              {syncing ? "⏳" : sync.lastError ? "⚠️" : "☁️"}
            </button>
          ) : null}
        </div>
      </header>

      {screen.name === "results" ? (
        <Results screen={screen} onContinue={() => setScreen({ name: "path" })} onPractice={() => startReview("weak")} />
      ) : screen.name === "path" ? (
        <>
          <div className="card">
            <div className="row spread wrap">
              <div>
                <div className="muted small">Daily goal · {xpToday(progress)}/{progress.dailyGoal} XP{heartsInfo ? ` · ${heartsInfo}` : ""}</div>
                <div className="progress yellow" style={{ marginTop: 6, width: 220 }}><div style={{ width: `${Math.min(100, (xpToday(progress) / progress.dailyGoal) * 100)}%` }} /></div>
              </div>
              {nextLesson ? <button className="btn small blue" onClick={() => startLesson(nextLesson.id)}>{started ? "Continue" : "Start learning"} →</button> : <span className="pill">Course complete 🎉</span>}
            </div>
            {due > 0 ? <div className="small mt">🔁 <b>{due}</b> exercise{due === 1 ? "" : "s"} due for review. <a href="#" onClick={(e) => { e.preventDefault(); startReview("due"); }}>Review now</a></div> : null}
          </div>
          <Path units={curriculum.units} progress={progress} onStart={(id) => startLesson(id)} />
        </>
      ) : screen.name === "practice" ? (
        <div>
          <h2>Practice</h2>
          <p className="muted small">Practice never costs hearts and earns a little XP. Spaced review brings back exercises right before you would forget them.</p>
          <div className="card">
            <div className="row spread wrap">
              <div><b>🔁 Spaced review</b><div className="muted small">{due} exercise{due === 1 ? "" : "s"} due</div></div>
              <button className="btn small blue" onClick={() => startReview("due")} disabled={!started}>Start</button>
            </div>
          </div>
          <div className="card">
            <div className="row spread wrap">
              <div><b>🎯 Weak spots</b><div className="muted small">Exercises you have missed before</div></div>
              <button className="btn small blue" onClick={() => startReview("weak")} disabled={!started}>Start</button>
            </div>
          </div>
          <div className="card">
            <div className="row spread wrap">
              <div><b>🎲 Mixed practice</b><div className="muted small">Random exercises from every lesson you have started</div></div>
              <button className="btn small blue" onClick={() => startReview("random")} disabled={!started}>Start</button>
            </div>
          </div>
          <h3 className="mt">Practice a unit</h3>
          {curriculum.units.map((u) => (
            <div key={u.id} className="card" style={{ padding: "10px 14px" }}>
              <div className="row spread">
                <div className="row"><span style={{ fontSize: 22 }}>{u.icon}</span><b>{u.number}. {u.title}</b></div>
                <button className="btn small ghost" onClick={() => startReview("unit", u.id)}>Practice</button>
              </div>
            </div>
          ))}
          {!started ? <p className="muted small">Complete a lesson first to unlock review modes; unit practice is always available.</p> : null}
        </div>
      ) : (
        <Profile
          progress={progress}
          units={curriculum.units}
          onSetGoal={(g) => update((p) => ({ ...p, dailyGoal: g }))}
          onSetName={(n) => update((p) => ({ ...p, name: n }))}
          onReset={() => setProgress(defaultProgress())}
          sync={sync}
          syncing={syncing}
          syncStatus={syncStatus}
          onConnect={(token) => { const next = { ...defaultSync(), token: token.trim() }; setSync(next); syncRef.current = next; void doSync(); }}
          onSyncNow={() => void doSync()}
          onDisconnect={() => { clearSync(); setSync(defaultSync()); setSyncStatus(""); }}
        />
      )}

      <nav className="nav">
        <button className={screen.name === "path" || screen.name === "results" ? "active" : ""} onClick={() => setScreen({ name: "path" })}><span className="ico">🏠</span>Learn</button>
        <button className={screen.name === "practice" ? "active" : ""} onClick={() => setScreen({ name: "practice" })}><span className="ico">🔁</span>Practice{due ? ` (${due})` : ""}</button>
        <button className={screen.name === "profile" ? "active" : ""} onClick={() => setScreen({ name: "profile" })}><span className="ico">👤</span>Profile</button>
      </nav>
    </div>
  );
}

function Results({ screen, onContinue, onPractice }: { screen: Extract<Screen, { name: "results" }>; onContinue: () => void; onPractice: () => void }) {
  const { result, xp, seconds, achievements, practice } = screen;
  const acc = result.total ? Math.round((result.correct / result.total) * 100) : 0;
  const emoji = result.perfect ? "🌟" : acc >= 80 ? "🎉" : acc >= 50 ? "👍" : "💪";
  const title = result.perfect ? "Perfect lesson!" : acc >= 80 ? (practice ? "Practice complete!" : "Lesson complete, crown earned!") : acc >= 50 ? "Good effort" : "Keep practicing";
  return (
    <div className="results">
      <div className="big pulse">{emoji}</div>
      <h2>{title}</h2>
      {!practice && acc < 80 ? <p className="muted small">Score 80% or more on the first try to earn a crown. Every mistake is scheduled for review.</p> : null}
      <div className="tiles">
        <div className="tile xp"><div className="v">+{xp}</div><div className="k">XP</div></div>
        <div className="tile acc"><div className="v">{acc}%</div><div className="k">Accuracy</div></div>
        <div className="tile time"><div className="v">{Math.floor(seconds / 60)}:{String(seconds % 60).padStart(2, "0")}</div><div className="k">Time</div></div>
      </div>
      {achievements.length ? (
        <div className="card" style={{ textAlign: "left" }}>
          <b>New achievement{achievements.length > 1 ? "s" : ""}!</b>
          {achievements.map((a) => <div key={a} className="row mt"><span style={{ fontSize: 26 }}>{ACHIEVEMENTS[a]?.icon}</span><div><b>{ACHIEVEMENTS[a]?.title}</b><div className="muted small">{ACHIEVEMENTS[a]?.description}</div></div></div>)}
        </div>
      ) : null}
      <div className="row" style={{ justifyContent: "center", gap: 10, flexWrap: "wrap" }}>
        {result.correct < result.total ? <button className="btn ghost" onClick={onPractice}>Practice mistakes</button> : null}
        <button className="btn" onClick={onContinue}>Continue</button>
      </div>
    </div>
  );
}
