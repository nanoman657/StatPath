import type { Unit } from "../engine/types";
import type { Progress } from "../engine/progress";
import { MAX_CROWNS } from "../engine/progress";

interface Props {
  units: Unit[];
  progress: Progress;
  onStart: (lessonId: string) => void;
}

/** A lesson is unlocked when the previous lesson has at least one crown (first lesson always open). */
export const isUnlocked = (units: Unit[], progress: Progress, lessonId: string): boolean => {
  const all = units.flatMap((u) => u.lessons);
  const i = all.findIndex((l) => l.id === lessonId);
  if (i <= 0) return true;
  return (progress.lessons[all[i - 1].id]?.crowns ?? 0) >= 1;
};

export function Path({ units, progress, onStart }: Props) {
  return (
    <div>
      {units.map((u) => {
        const crowns = u.lessons.reduce((a, l) => a + (progress.lessons[l.id]?.crowns ?? 0), 0);
        const max = u.lessons.length * MAX_CROWNS;
        return (
          <section key={u.id} id={u.id}>
            <div className="unit-header" style={{ background: u.color }}>
              <div>
                <div className="sub">Unit {u.number}</div>
                <h2>{u.title}</h2>
                <div className="sub">{u.description}</div>
                <div className="sub" style={{ marginTop: 6 }}>👑 {crowns}/{max}</div>
              </div>
              <div className="badge">{u.icon}</div>
            </div>
            <div className="path">
              {u.lessons.map((l, i) => {
                const lp = progress.lessons[l.id];
                const unlocked = isUnlocked(units, progress, l.id);
                const done = (lp?.crowns ?? 0) >= 1;
                const isReview = l.id.endsWith(".review");
                const cls = "node" + (unlocked ? "" : " locked") + (done ? " done" : "") + (isReview ? " review" : "");
                const offset = isReview ? 0 : Math.round(Math.sin(i * 1.1) * 40);
                return (
                  <button key={l.id} className={cls} style={{ transform: `translateX(${offset}px)` }} onClick={() => unlocked && onStart(l.id)} disabled={!unlocked} title={unlocked ? l.title : "Complete the previous lesson to unlock"}>
                    <div className="circle" style={unlocked && !done ? { background: u.color } : undefined}>
                      {isReview ? "🏆" : !unlocked ? "🔒" : done ? "★" : "▶"}
                    </div>
                    {lp && lp.crowns > 0 ? <span className="crowns">👑 {lp.crowns}</span> : null}
                    <span className="section">{l.section}</span>
                    <span className="label">{l.title}</span>
                  </button>
                );
              })}
            </div>
          </section>
        );
      })}
    </div>
  );
}
