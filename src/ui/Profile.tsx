import { ACHIEVEMENTS, MAX_CROWNS, type Progress, dueCards, isoDay, streakIsAlive, totalCrowns, xpToday } from "../engine/progress";
import type { Unit } from "../engine/types";
import { TOKEN_URL, type SyncSettings } from "../engine/sync";
import { useState } from "react";

interface Props {
  progress: Progress;
  units: Unit[];
  onSetGoal: (g: number) => void;
  onSetName: (n: string) => void;
  onReset: () => void;
  sync: SyncSettings;
  syncing: boolean;
  syncStatus: string;
  onConnect: (token: string) => void;
  onSyncNow: () => void;
  onDisconnect: () => void;
}

export function Profile({ progress, units, onSetGoal, onSetName, onReset, sync, syncing, syncStatus, onConnect, onSyncNow, onDisconnect }: Props) {
  const totalLessons = units.reduce((a, u) => a + u.lessons.length, 0);
  const done = Object.values(progress.lessons).filter((l) => l.crowns > 0).length;
  const crowns = totalCrowns(progress);
  const due = dueCards(progress).length;
  const days = Array.from({ length: 42 }, (_, i) => isoDay(Date.now() - (41 - i) * 86400000));
  const level = (xp: number) => (xp >= 200 ? Math.min(4, Math.ceil(xp / 100)) : xp >= 60 ? 2 : xp > 0 ? 1 : 0);
  return (
    <div>
      <div className="card">
        <div className="row spread wrap">
          <div>
            <h2>{progress.name}</h2>
            <div className="muted small">Learning statistics since {progress.lastActiveDay ? "you started" : "today"}</div>
          </div>
          <div className="row">
            <input className="answer" style={{ fontSize: 15, padding: "8px 10px", width: 160 }} value={progress.name} onChange={(e) => onSetName(e.target.value)} aria-label="name" />
          </div>
        </div>
        <div className="results" style={{ padding: "12px 0 0" }}>
          <div className="tiles" style={{ gridTemplateColumns: "repeat(4, 1fr)" }}>
            <div className="tile xp"><div className="v">{progress.xp}</div><div className="k">Total XP</div></div>
            <div className="tile"><div className="v" style={{ color: "var(--orange)" }}>{streakIsAlive(progress) ? progress.streak : 0}</div><div className="k">Day streak</div></div>
            <div className="tile acc"><div className="v">{crowns}</div><div className="k">Crowns</div></div>
            <div className="tile time"><div className="v">{done}/{totalLessons}</div><div className="k">Lessons</div></div>
          </div>
        </div>
      </div>

      <div className="card">
        <h3>Daily goal</h3>
        <div className="row" style={{ marginBottom: 8 }}>
          <div className="progress yellow"><div style={{ width: `${Math.min(100, (xpToday(progress) / progress.dailyGoal) * 100)}%` }} /></div>
          <div className="small"><b>{xpToday(progress)}</b>/{progress.dailyGoal} XP</div>
        </div>
        <div className="row wrap">
          {[10, 20, 30, 50].map((g) => (
            <button key={g} className={"btn small " + (progress.dailyGoal === g ? "" : "ghost")} onClick={() => onSetGoal(g)}>{g} XP</button>
          ))}
        </div>
      </div>

      <div className="card">
        <h3>Activity (last 6 weeks)</h3>
        <div className="heat">
          {days.map((d) => <div key={d} className={"l" + level(progress.xpByDay[d] ?? 0)} title={`${d}: ${progress.xpByDay[d] ?? 0} XP`} />)}
        </div>
        <div className="muted small mt">Longest streak: {progress.longestStreak} days · {due} exercise{due === 1 ? "" : "s"} due for review</div>
      </div>

      <div className="card">
        <h3>Achievements</h3>
        <div className="ach">
          {Object.entries(ACHIEVEMENTS).map(([k, a]) => (
            <div key={k} className={"a" + (progress.achievements.includes(k) ? "" : " off")}>
              <div className="ic">{a.icon}</div>
              <div className="t">{a.title}</div>
              <div className="d">{a.description}</div>
            </div>
          ))}
        </div>
      </div>

      <div className="card">
        <h3>Course coverage</h3>
        {units.map((u) => {
          const c = u.lessons.reduce((a, l) => a + (progress.lessons[l.id]?.crowns ?? 0), 0);
          return (
            <div key={u.id} className="row" style={{ marginBottom: 6 }}>
              <span style={{ width: 28 }}>{u.icon}</span>
              <span className="small" style={{ width: 210 }}>{u.number}. {u.title}</span>
              <div className="progress"><div style={{ width: `${(c / (u.lessons.length * MAX_CROWNS)) * 100}%`, background: u.color }} /></div>
            </div>
          );
        })}
      </div>

      <SyncCard sync={sync} syncing={syncing} status={syncStatus} onConnect={onConnect} onSyncNow={onSyncNow} onDisconnect={onDisconnect} />

      <div className="card">
        <h3>About</h3>
        <p className="small muted">StatPath's curriculum follows the 13 chapters of <i>Introductory Statistics 2e</i> by OpenStax (Rice University), licensed CC BY 4.0. Progress is stored only in this browser.</p>
        <button className="btn small red" onClick={() => { if (confirm("Reset all progress? This cannot be undone.")) onReset(); }}>Reset progress</button>
      </div>
    </div>
  );
}

/**
 * Cross-device sync setup. The token is a classic GitHub token limited to the
 * gist scope; fine-grained tokens are not accepted by the Gists API. It is kept
 * in this browser only and is never written into the synced file.
 */
function SyncCard({ sync, syncing, status, onConnect, onSyncNow, onDisconnect }: {
  sync: SyncSettings;
  syncing: boolean;
  status: string;
  onConnect: (token: string) => void;
  onSyncNow: () => void;
  onDisconnect: () => void;
}) {
  const [token, setToken] = useState("");
  const connected = !!sync.token;
  return (
    <div className="card">
      <h3>Sync across devices</h3>
      {!connected ? (
        <>
          <p className="small muted">
            Progress lives in this browser only. To carry it between your phone and computer, StatPath can keep a copy
            in a secret <b>GitHub Gist</b> on your own account. Nothing is sent anywhere else.
          </p>
          <ol className="small" style={{ paddingLeft: 20, marginTop: 8 }}>
            <li>
              <a href={TOKEN_URL} target="_blank" rel="noreferrer">Create a token</a>. The <b>gist</b> scope is
              preselected; leave every other box unticked and set <b>Expiration</b> to <b>No expiration</b>.
            </li>
            <li>It must be a <b>classic</b> token. Fine-grained tokens cannot access gists.</li>
            <li>Paste it below, then repeat on your other device with the same token.</li>
          </ol>
          <div className="row" style={{ marginTop: 10, gap: 8 }}>
            <input
              className="answer"
              style={{ fontSize: 14, padding: "10px 12px" }}
              type="password"
              autoComplete="off"
              spellCheck={false}
              placeholder="ghp_…"
              value={token}
              onChange={(e) => setToken(e.target.value)}
            />
            <button className="btn small" disabled={!token.trim() || syncing} onClick={() => { onConnect(token); setToken(""); }}>
              Connect
            </button>
          </div>
        </>
      ) : (
        <>
          <div className="row spread wrap">
            <div>
              <div className="small">
                <b>{sync.lastError ? "⚠️ Needs attention" : "☁️ Connected"}</b>
              </div>
              <div className="muted small">
                {sync.lastSyncedAt ? `Last synced ${new Date(sync.lastSyncedAt).toLocaleString()}` : "Not synced yet"}
                {sync.gistId ? ` · gist ${sync.gistId.slice(0, 8)}` : ""}
              </div>
            </div>
            <div className="row" style={{ gap: 8 }}>
              <button className="btn small" onClick={onSyncNow} disabled={syncing}>{syncing ? "Syncing…" : "Sync now"}</button>
              <button className="btn small ghost" onClick={onDisconnect} disabled={syncing}>Disconnect</button>
            </div>
          </div>
          <p className="small muted mt">
            Syncs when you open StatPath and after each lesson. Work done on two devices is combined rather than
            overwritten, so nothing is lost if one of them was out of date.
          </p>
        </>
      )}
      {status ? <div className={"small mt " + (sync.lastError ? "" : "muted")}>{status}</div> : null}
      {sync.lastError ? <div className="small" style={{ color: "var(--red)" }}>{sync.lastError}</div> : null}
    </div>
  );
}
